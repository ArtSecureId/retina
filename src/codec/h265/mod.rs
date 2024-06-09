pub(crate) mod nal;
pub(crate) mod nalu;
pub(crate) mod nalu_reader;
pub(crate) mod parser;
pub(crate) mod rbsp;

use std::fmt;

use base64::Engine;
use bytes::{BufMut, Bytes, BytesMut};
use log::debug;

use crate::codec::{CodecItem, ParametersRef, VideoFrame, VideoParameters};
use crate::rtp::ReceivedPacket;

use self::parser::NaluHeader;

#[derive(PartialEq, Hash, Debug, Copy, Clone)]
pub enum NalUnitType {
    VPS = 32,
    SPS = 33,
    PPS = 34,
    IDR = 19,
    NonIDR = 20,
    // Add more as needed
}

#[derive(Debug)]
pub enum UnitTypeError {
    /// if the value was outside the range `0` - `31`.
    ValueOutOfRange(u8),
}

impl NalUnitType {
    pub fn for_id(id: u8) -> Result<NalUnitType, UnitTypeError> {
        Err(UnitTypeError::ValueOutOfRange(id))
    }
}

#[derive(Debug)]
pub enum NalHeaderError {
    /// The most significant bit of the header, called `forbidden_zero_bit`, was set to 1.
    ForbiddenZeroBit,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct NalHeader(u16);

impl NalHeader {
    pub fn new(header_value: [u8; 2]) -> Result<NalHeader, NalHeaderError> {
        let header_value = u16::from_be_bytes([header_value[0], header_value[1]]); // Convert u8 array to u16
        if header_value & 0b1000_0000_0000_0000 != 0 {
            Err(NalHeaderError::ForbiddenZeroBit)
        } else {
            Ok(NalHeader(header_value))
        }
    }
    pub fn nal_unit_type(&self) -> NalUnitType {
        let nal_type = (self.0 >> 9) & 0b0000_0011_1111;
        match nal_type {
            32 => NalUnitType::VPS,
            33 => NalUnitType::SPS,
            34 => NalUnitType::PPS,
            19 => NalUnitType::IDR,
            20 => NalUnitType::NonIDR,
            _ => panic!("Unknown NAL unit type: {}", nal_type),
            // Add more cases as needed
        }
    }
    pub fn nal_layer_id(&self) -> u16 {
        (self.0 >> 3) & 0b0000_0011_1111
    }
}

impl fmt::Debug for NalHeader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("NalHeader")
            //.field("nal_ref_idc", &self.nal_ref_idc())
            //.field("nal_unit_type", &self.nal_unit_type())
            .finish()
    }
}

#[derive(Debug)]
struct Nal {
    hdr: NalHeader,

    /// The length of `Depacketizer::pieces` as this NAL finishes.
    next_piece_idx: u32,

    /// The total length of this NAL, including the header byte.
    len: u32,
}

#[derive(Clone, Debug)]
struct InternalParameters {
    generic_parameters: crate::codec::VideoParameters,

    /// The (single) SPS NAL.
    sps_nal: Bytes,

    /// The (single) PPS NAL.
    pps_nal: Bytes,

    /// The (single) VPS NAL.
    vps_nal: Option<Bytes>,

    /// The (single) SEI NAL.
    sei_nal: Option<Bytes>,

    seen_extra_trailing_data: bool,
}

impl InternalParameters {
    /// Parses metadata from the `format-specific-params` of a SDP `fmtp` media attribute.
    fn parse_format_specific_params(format_specific_params: &str) -> Result<Self, String> {
        let mut sprop_picture_parameter_sets = None;
        let mut sprop_sequence_parameter_sets = None;
        let mut sprop_video_parameter_sets = None;

        for p in format_specific_params.split(';') {
            match p.trim().split_once('=') {
                Some(("sprop-pps", value)) => sprop_picture_parameter_sets = Some(value),
                Some(("sprop-sps", value)) => sprop_sequence_parameter_sets = Some(value),
                Some(("sprop-vps", value)) => sprop_video_parameter_sets = Some(value),
                // None => return Err("key without value".into()),
                _ => (),
            }
        }
        let sprop_picture_parameter_sets = sprop_picture_parameter_sets
            .ok_or_else(|| "no sprop-pps in H.265 format-specific-params".to_string())?;

        let sprop_sequence_parameter_sets = sprop_sequence_parameter_sets
            .ok_or_else(|| "no sprop-sps in H.265 format-specific-params".to_string())?;

        let sprop_video_parameter_sets = sprop_video_parameter_sets
            .ok_or_else(|| "no sprop-vps in H.265 format-specific-params".to_string())?;

        let mut sps_nal = None;
        let mut pps_nal = None;
        let mut vps_nal = None;
        //let mut vps_nal = None;

        for nal in [
            sprop_sequence_parameter_sets,
            sprop_video_parameter_sets,
            sprop_picture_parameter_sets,
        ] {
            let mut nal = base64::engine::general_purpose::STANDARD
                .decode(nal)
                .map_err(|_| {
                    "bad sprop-parameter-sets: NAL has invalid base64 encoding".to_string()
                })?;
            if nal.is_empty() {
                return Err("bad sprop-parameter-sets: empty NAL".into());
            }
            let header = NalHeader::new([nal[0], nal[1]])
                .map_err(|_| format!("bad sprop-parameter-sets: bad NAL header {:0x}", nal[0]))?;
            let layer_id = header.nal_layer_id();
            match header.nal_unit_type() {
                NalUnitType::SPS => {
                    if sps_nal.is_some() {
                        return Err("multiple SPSs".into());
                    }
                    //nal.drain(..2);
                    sps_nal = Some(nal);
                }
                NalUnitType::PPS => {
                    if pps_nal.is_some() {
                        return Err("multiple PPSs".into());
                    }
                    //nal.drain(..2);
                    pps_nal = Some(nal);
                }
                NalUnitType::VPS => {
                    if vps_nal.is_some() {
                        return Err("multiple VPSs".into());
                    }
                    //nal.drain(..2);
                    vps_nal = Some(nal);
                }
                _ => return Err("only SPS, PPS and VPS expected in parameter sets".into()),
            }
        }
        let mut sps_nal = sps_nal.ok_or_else(|| "no sps".to_string())?;
        let mut pps_nal = pps_nal.ok_or_else(|| "no pps".to_string())?;
        let mut vps_nal = vps_nal.ok_or_else(|| "no vps".to_string())?;
        // TODO: Create extractor
        let nalu_reader = nalu_reader::NaluReader::new(&sps_nal);
        let mut parser = parser::Parser::default();

        //Adding start bytes to properly extract Nalu from the below find_nalu_by_type
        sps_nal.insert(0, 1);
        sps_nal.insert(0, 0);
        sps_nal.insert(0, 0);
        let sps_nalu = Self::find_nalu_by_type(&sps_nal, parser::NaluType::SpsNut, 0).unwrap();
        let sps = parser.parse_sps(&sps_nalu).unwrap();

        pps_nal.insert(0, 1);
        pps_nal.insert(0, 0);
        pps_nal.insert(0, 0);
        let pps_nalu = Self::find_nalu_by_type(&pps_nal, parser::NaluType::PpsNut, 0).unwrap();
        let pps = parser.parse_pps(&pps_nalu).unwrap();

        vps_nal.insert(0, 1);
        vps_nal.insert(0, 0);
        vps_nal.insert(0, 0);
        let vps_nalu = Self::find_nalu_by_type(&vps_nal, parser::NaluType::VpsNut, 0).unwrap();
        let vps = parser.parse_vps(&vps_nalu).unwrap();

        Self::parse_sps_and_pps(&sps_nal, &pps_nal, false)
    }

    fn find_nalu_by_type(
        bitstream: &[u8],
        nalu_type: parser::NaluType,
        mut nskip: i32,
    ) -> Option<nalu::Nalu<parser::NaluHeader>> {
        let mut cursor = std::io::Cursor::new(bitstream);
        while let Ok(nalu) = nalu::Nalu::<parser::NaluHeader>::next(&mut cursor) {
            if nalu.header.type_ == nalu_type {
                if nskip == 0 {
                    return Some(nalu);
                } else {
                    nskip -= 1;
                }
            }
        }
        None
    }

    fn parse_sps_and_pps(
        sps_nal: &[u8],
        pps_nal: &[u8],
        mut seen_extra_trailing_data: bool,
    ) -> Result<InternalParameters, String> {
        let sps_rbsp = rbsp::decode_nal(sps_nal).map_err(|_| "bad sps")?;
        if sps_rbsp.len() < 5 {
            return Err("bad sps".into());
        }
        let rfc6381_codec = format!(
            "avc1.{:02X}{:02X}{:02X}",
            sps_rbsp[0], sps_rbsp[1], sps_rbsp[2]
        );

        let mut sps_has_extra_trailing_data = false;
        let sps_hex = crate::hex::LimitedHex::new(sps_nal, 256);
        let sps = nal::sps265::SeqParameterSet::from_bits(TolerantBitReader {
            inner: rbsp::BitReader::new(&*sps_rbsp),
            has_extra_trailing_data: &mut sps_has_extra_trailing_data,
        })
        .map_err(|e| format!("Bad SPS {sps_hex}: {e:?}"))?;
        debug!("SPS {sps_hex}: {:#?}", &sps);
        if sps_has_extra_trailing_data && !seen_extra_trailing_data {
            log::warn!("Ignoring trailing data in SPS {sps_hex}; will not log about trailing data again for this stream.");
            seen_extra_trailing_data = true;
        }

        let pixel_dimensions = sps
            .pixel_dimensions()
            .map_err(|e| format!("SPS has invalid pixel dimensions: {e:?}"))?;

        // Create the AVCDecoderConfiguration, ISO/IEC 14496-15 section 5.2.4.1.
        // The beginning of the AVCDecoderConfiguration takes a few values from
        // the SPS (ISO/IEC 14496-10 section 7.3.2.1.1).
        let mut avc_decoder_config = BytesMut::with_capacity(11 + sps_nal.len() + pps_nal.len());
        avc_decoder_config.put_u8(1); // configurationVersion
        avc_decoder_config.extend(&sps_rbsp[0..=2]); // profile_idc . AVCProfileIndication
                                                     // ...misc bits... . profile_compatibility
                                                     // level_idc . AVCLevelIndication

        // Hardcode lengthSizeMinusOne to 3, matching TransformSampleData's 4-byte
        // lengths.
        avc_decoder_config.put_u8(0xff);

        // Only support one SPS and PPS.
        // ffmpeg's ff_isom_write_avcc has the same limitation, so it's probably
        // fine. This next byte is a reserved 0b111 + a 5-bit # of SPSs (1).
        avc_decoder_config.put_u8(0xe1);
        avc_decoder_config.extend(
            &u16::try_from(sps_nal.len())
                .map_err(|_| format!("SPS NAL is {} bytes long; must fit in u16", sps_nal.len()))?
                .to_be_bytes()[..],
        );
        let sps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(sps_nal);
        let sps_nal_end = avc_decoder_config.len();
        avc_decoder_config.put_u8(1); // # of PPSs.
        avc_decoder_config.extend(
            &u16::try_from(pps_nal.len())
                .map_err(|_| format!("PPS NAL is {} bytes long; must fit in u16", pps_nal.len()))?
                .to_be_bytes()[..],
        );
        let pps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(pps_nal);
        let pps_nal_end = avc_decoder_config.len();
        assert_eq!(avc_decoder_config.len(), 11 + sps_nal.len() + pps_nal.len());

        let (pixel_aspect_ratio, frame_rate);
        match sps.vui_parameters {
            Some(ref vui) => {
                pixel_aspect_ratio = vui
                    .aspect_ratio_info
                    .as_ref()
                    .and_then(|a| a.clone().get())
                    .map(|(h, v)| (u32::from(h), (u32::from(v))));

                // TODO: study H.264, (E-34). This quick'n'dirty calculation isn't always right.
                frame_rate = vui.timing_info.as_ref().and_then(|t| {
                    t.num_units_in_tick
                        .checked_mul(2)
                        .map(|doubled| (doubled, t.time_scale))
                });
            }
            None => {
                pixel_aspect_ratio = None;
                frame_rate = None;
            }
        }
        let avc_decoder_config = avc_decoder_config.freeze();
        let sps_nal = avc_decoder_config.slice(sps_nal_start..sps_nal_end);
        let pps_nal = avc_decoder_config.slice(pps_nal_start..pps_nal_end);
        Ok(InternalParameters {
            generic_parameters: VideoParameters {
                rfc6381_codec,
                pixel_dimensions,
                pixel_aspect_ratio,
                frame_rate,
                extra_data: avc_decoder_config,
            },
            sps_nal,
            pps_nal,
            vps_nal: None,
            sei_nal: None,
            seen_extra_trailing_data,
        })
    }
}

/// A [super::Depacketizer] implementation which finds access unit boundaries
/// and produces unfragmented NAL units as specified in [RFC
/// 6184](https://tools.ietf.org/html/rfc6184).
///
/// This doesn't inspect the contents of the NAL units, so it doesn't depend on or
/// verify compliance with H.264 section 7.4.1.2.3 "Order of NAL units and coded
/// pictures and association to access units".
///
/// Currently expects that the stream starts at an access unit boundary unless
/// packet loss is indicated.
#[derive(Debug)]
pub(crate) struct Depacketizer {
    //input_state: DepacketizerInputState,
    /// A complete video frame ready for pull.
    pending: Option<VideoFrame>,
    parameters: Option<InternalParameters>,

    /// In state `PreMark`, pieces of NALs, excluding their header bytes.
    /// Kept around (empty) in other states to re-use the backing allocation.
    pieces: Vec<Bytes>,

    /// In state `PreMark`, an entry for each NAL.
    /// Kept around (empty) in other states to re-use the backing allocation.
    nals: Vec<Nal>,
}

impl Depacketizer {
    pub(super) fn new(
        clock_rate: u32,
        format_specific_params: Option<&str>,
    ) -> Result<Self, String> {
        if clock_rate != 90_000 {
            return Err(format!(
                "invalid H.264 clock rate {clock_rate}; must always be 90000"
            ));
        }

        let parameters = match format_specific_params {
            None => None,
            Some(fp) => match InternalParameters::parse_format_specific_params(fp) {
                Ok(p) => Some(p),
                Err(e) => {
                    log::warn!("Ignoring bad H.265 format-specific-params {:?}: {}", fp, e);
                    None
                }
            },
        };
        Ok(Depacketizer {
            //input_state: DepacketizerInputState::New,
            pending: None,
            pieces: Vec::new(),
            nals: Vec::new(),
            parameters,
        })
    }

    pub(super) fn parameters(&self) -> Option<ParametersRef> {
        self.parameters
            .as_ref()
            .map(|p| ParametersRef::Video(&p.generic_parameters))
    }

    pub(super) fn push(&mut self, pkt: ReceivedPacket) -> Result<(), String> {
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<CodecItem> {
        self.pending.take().map(CodecItem::VideoFrame)
    }
}

/// `h264_reader::rbsp::BitRead` impl that *notes* extra trailing data rather than failing on it.
///
/// Some (Reolink) cameras appear to have a stray extra byte at the end. Follow the lead of most
/// other RTSP implementations in tolerating this.
#[derive(Debug)]
struct TolerantBitReader<'a, R> {
    inner: R,
    has_extra_trailing_data: &'a mut bool,
}

impl<'a, R: rbsp::BitRead> rbsp::BitRead for TolerantBitReader<'a, R> {
    fn read_ue(&mut self, name: &'static str) -> Result<u32, rbsp::BitReaderError> {
        self.inner.read_ue(name)
    }

    fn read_se(&mut self, name: &'static str) -> Result<i32, rbsp::BitReaderError> {
        self.inner.read_se(name)
    }

    fn read_bool(&mut self, name: &'static str) -> Result<bool, rbsp::BitReaderError> {
        self.inner.read_bool(name)
    }

    fn read_u8(&mut self, bit_count: u32, name: &'static str) -> Result<u8, rbsp::BitReaderError> {
        self.inner.read_u8(bit_count, name)
    }

    fn read_u16(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<u16, rbsp::BitReaderError> {
        self.inner.read_u16(bit_count, name)
    }

    fn read_u32(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<u32, rbsp::BitReaderError> {
        self.inner.read_u32(bit_count, name)
    }

    fn read_i32(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<i32, rbsp::BitReaderError> {
        self.inner.read_i32(bit_count, name)
    }

    fn has_more_rbsp_data(&mut self, name: &'static str) -> Result<bool, rbsp::BitReaderError> {
        self.inner.has_more_rbsp_data(name)
    }

    fn finish_rbsp(self) -> Result<(), rbsp::BitReaderError> {
        match self.inner.finish_rbsp() {
            Ok(()) => Ok(()),
            Err(rbsp::BitReaderError::RemainingData) => {
                *self.has_extra_trailing_data = true;
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    fn finish_sei_payload(self) -> Result<(), rbsp::BitReaderError> {
        self.inner.finish_sei_payload()
    }
}

/// Contextual data that needs to be tracked between evaluations of different portions of H264
/// syntax.
pub struct Context {
    seq_param_sets: Vec<Option<nal::sps::SeqParameterSet>>,
    pic_param_sets: Vec<Option<nal::pps::PicParameterSet>>,
}
impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}
impl Context {
    pub fn new() -> Self {
        let mut seq_param_sets = vec![];
        for _ in 0..32 {
            seq_param_sets.push(None);
        }
        let mut pic_param_sets = vec![];
        for _ in 0..32 {
            pic_param_sets.push(None);
        }
        Context {
            seq_param_sets,
            pic_param_sets,
        }
    }
}
impl Context {
    pub fn sps_by_id(&self, id: nal::pps::ParamSetId) -> Option<&nal::sps::SeqParameterSet> {
        if id.id() > 31 {
            None
        } else {
            self.seq_param_sets[id.id() as usize].as_ref()
        }
    }
    pub fn sps(&self) -> impl Iterator<Item = &nal::sps::SeqParameterSet> {
        self.seq_param_sets.iter().filter_map(Option::as_ref)
    }
    pub fn put_seq_param_set(&mut self, sps: nal::sps::SeqParameterSet) {
        let i = sps.seq_parameter_set_id.id() as usize;
        self.seq_param_sets[i] = Some(sps);
    }
    pub fn pps_by_id(&self, id: nal::pps::ParamSetId) -> Option<&nal::pps::PicParameterSet> {
        if id.id() > 31 {
            None
        } else {
            self.pic_param_sets[id.id() as usize].as_ref()
        }
    }
    pub fn pps(&self) -> impl Iterator<Item = &nal::pps::PicParameterSet> {
        self.pic_param_sets.iter().filter_map(Option::as_ref)
    }
    pub fn put_pic_param_set(&mut self, pps: nal::pps::PicParameterSet) {
        let i = pps.pic_parameter_set_id.id() as usize;
        self.pic_param_sets[i] = Some(pps);
    }
}
