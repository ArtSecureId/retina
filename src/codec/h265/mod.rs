////////////////////////////////////////////////////////////////////////////
// Reference to integrate with cros-codecs especially for h265
// https://github.com/chromeos/cros-codecs/blob/main/src/codec/h265/parser.rs
////////////////////////////////////////////////////////////////////////////

pub(crate) mod nal;
pub(crate) mod nalu;
pub(crate) mod nalu_reader;
pub(crate) mod parser;
pub(crate) mod rbsp;

use std::fmt::{self, Write};

use base64::Engine;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use log::{debug, log_enabled, trace};
use parser::NaluType;

use crate::codec::{CodecItem, ParametersRef, VideoFrame, VideoParameters};
use crate::rtp::ReceivedPacket;

use self::parser::{NaluHeader, Pps, Sps};

#[derive(Debug)]
pub enum UnitTypeError {
    /// if the value was outside the range `0` - `31`.
    ValueOutOfRange(u8),
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
    pub fn nal_unit_type(&self) -> NaluType {
        let nal_type = (self.0 >> 9) & 0b0000_0011_1111;
        match nal_type {
            1 => NaluType::TrailN,
            2 => NaluType::TrailR,
            32 => NaluType::VpsNut,
            33 => NaluType::SpsNut,
            34 => NaluType::PpsNut,
            19 => NaluType::IdrWRadl,
            20 => NaluType::IdrNLp,
            39 => NaluType::PrefixSeiNut,
            49 => NaluType::RsvNvcl49,
            _ => panic!("Unknown NAL unit type: {}", nal_type),
            // Add more cases as needed
        }
    }

    // Method to retrieve the value of the u16 inside the struct
    pub fn get_value(&self) -> u16 {
        self.0
    }

    pub fn nal_layer_id(&self) -> u16 {
        (self.0 >> 3) & 0b0000_0011_1111
    }

    // Extracts the Temporal ID, adding 1 because it is stored as `temporal_id_plus1`
    pub fn temporal_id(self) -> u8 {
        ((self.0 >> 7) & 0x07) as u8 // Assuming it follows right after the 6 bits of the unit type
    }

    // Example to demonstrate calling these methods
    pub fn display(self) {
        println!("NAL Unit Type: {}", self.nal_unit_type().value());
        println!("Temporal ID (0-based): {}", self.temporal_id() - 1);
    }

    pub fn bytes(&self) -> (u8, u8) {
        let high_byte = (self.0 >> 8) as u8; // Shift right to get the high byte
        let low_byte = (self.0 & 0xFF) as u8; // Mask to get the low byte
        (high_byte, low_byte)
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
                NaluType::SpsNut => {
                    if sps_nal.is_some() {
                        return Err("multiple SPSs".into());
                    }
                    //nal.drain(..2);
                    sps_nal = Some(nal);
                }
                NaluType::PpsNut => {
                    if pps_nal.is_some() {
                        return Err("multiple PPSs".into());
                    }
                    //nal.drain(..2);
                    pps_nal = Some(nal);
                }
                NaluType::VpsNut => {
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
        let sps_copy = sps.clone();

        pps_nal.insert(0, 1);
        pps_nal.insert(0, 0);
        pps_nal.insert(0, 0);
        let pps_nalu = Self::find_nalu_by_type(&pps_nal, parser::NaluType::PpsNut, 0).unwrap();
        let pps = parser.parse_pps(&pps_nalu).unwrap();
        let pps_copy = pps.clone();

        vps_nal.insert(0, 1);
        vps_nal.insert(0, 0);
        vps_nal.insert(0, 0);
        let vps_nalu = Self::find_nalu_by_type(&vps_nal, parser::NaluType::VpsNut, 0).unwrap();
        let vps = parser.parse_vps(&vps_nalu).unwrap();

        Self::parse_sps_and_pps(&sps_nal, &sps_copy, &pps_nal, &pps_copy)
    }

    pub fn find_nalu_by_type(
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
        sps_nalu: &[u8],
        sps_decoded: &Sps,
        pps_nalu: &[u8],
        pps_decoded: &Pps,
    ) -> Result<InternalParameters, String> {
        let rfc6381_codec = format!(
            "avc1.{:02X}{:02X}{:02X}",
            sps_nalu[0], sps_nalu[1], sps_nalu[2]
        );

        let sps_hex = crate::hex::LimitedHex::new(sps_nalu, 256);
        //debug!("SPS {sps_hex}: {:#?}", &sps_decoded);

        let pixel_dimensions: (u32, u32) = (
            sps_decoded.pic_width_in_luma_samples.into(),
            sps_decoded.pic_height_in_luma_samples.into(),
        );

        // Create the AVCDecoderConfiguration, ISO/IEC 14496-15 section 5.2.4.1.
        // The beginning of the AVCDecoderConfiguration takes a few values from
        // the SPS (ISO/IEC 14496-10 section 7.3.2.1.1).
        let mut avc_decoder_config = BytesMut::with_capacity(11 + sps_nalu.len() + pps_nalu.len());
        avc_decoder_config.put_u8(1); // configurationVersion
        avc_decoder_config.extend(&sps_nalu[0..=2]); // profile_idc . AVCProfileIndication
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
            &u16::try_from(sps_nalu.len())
                .map_err(|_| format!("SPS NAL is {} bytes long; must fit in u16", sps_nalu.len()))?
                .to_be_bytes()[..],
        );
        let sps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(sps_nalu);
        let sps_nal_end = avc_decoder_config.len();
        avc_decoder_config.put_u8(1); // # of PPSs.
        avc_decoder_config.extend(
            &u16::try_from(pps_nalu.len())
                .map_err(|_| format!("PPS NAL is {} bytes long; must fit in u16", pps_nalu.len()))?
                .to_be_bytes()[..],
        );
        let pps_nal_start = avc_decoder_config.len();
        avc_decoder_config.extend_from_slice(pps_nalu);
        let pps_nal_end = avc_decoder_config.len();
        assert_eq!(
            avc_decoder_config.len(),
            11 + sps_nalu.len() + pps_nalu.len()
        );

        let (pixel_aspect_ratio, frame_rate) = (None::<u32>, None::<u32>);

        let mut frame_rate = None;
        let mut pixel_aspect_ratio = None;

        if sps_decoded.vui_parameters_present_flag
            && sps_decoded.vui_parameters.timing_info_present_flag
        {
            frame_rate = Some((2, 25));
        }

        if sps_decoded.vui_parameters_present_flag
            && sps_decoded.vui_parameters.aspect_ratio_info_present_flag
        {
            pixel_aspect_ratio = Some((32, sps_decoded.vui_parameters.aspect_ratio_idc));
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
        })
    }
}

/// Returns true iff the bytes of `nal` equal the bytes of `[hdr, ..data]`.
fn nal_matches(nal: &[u8], hdr: NalHeader, pieces: &[Bytes]) -> bool {
    let nal_head = NalHeader::new([nal[0], nal[1]]);
    if nal.is_empty() || nal_head.unwrap().0 != u16::from(hdr.0) {
        return false;
    }
    let mut nal_pos = 1;
    for piece in pieces {
        let new_pos = nal_pos + piece.len();
        if nal.len() < new_pos {
            return false;
        }
        if piece[..] != nal[nal_pos..new_pos] {
            return false;
        }
        nal_pos = new_pos;
    }
    nal_pos == nal.len()
}

/// Saves the given NAL to a contiguous Bytes.
fn to_bytes(hdr: NalHeader, len: u32, pieces: &[Bytes]) -> Bytes {
    let len = usize::try_from(len).expect("u32 fits in usize");
    let mut out = Vec::with_capacity(len);
    let (high, low) = hdr.bytes();
    out.push(high);
    out.push(low);
    for piece in pieces {
        out.extend_from_slice(&piece[..]);
    }
    debug_assert_eq!(len, out.len());
    out.into()
}

/// Returns true if we allow the given NAL unit type to end an access unit.
///
/// We specifically prohibit this for the SPS and PPS. Reolink cameras sometimes
/// incorrectly set the RTP marker bit and/or change the timestamp after these.
fn can_end_au(nal_unit_type: NaluType) -> bool {
    // H.264 section 7.4.1.2.3 Order of NAL units and coded pictures and
    // association to access units says "Sequence parameter set NAL units or
    // picture parameter set NAL units may be present in an access unit, but
    // cannot follow the last VCL NAL unit of the primary coded picture within
    // the access unit, as this condition would specify the start of a new
    // access unit."
    nal_unit_type != NaluType::SpsNut && nal_unit_type != NaluType::PpsNut
}

/// An access unit that is currently being accumulated during `PreMark` state.
#[derive(Debug)]
struct AccessUnit {
    start_ctx: crate::PacketContext,
    end_ctx: crate::PacketContext,
    timestamp: crate::Timestamp,
    stream_id: usize,

    /// True iff currently processing a FU-A.
    in_fu_a: bool,

    /// RTP packets lost as this access unit was starting.
    loss: u16,

    same_ts_as_prev: bool,
}

impl AccessUnit {
    fn start(
        pkt: &crate::rtp::ReceivedPacket,
        additional_loss: u16,
        same_ts_as_prev: bool,
    ) -> Self {
        AccessUnit {
            start_ctx: *pkt.ctx(),
            end_ctx: *pkt.ctx(),
            timestamp: pkt.timestamp(),
            stream_id: pkt.stream_id(),
            in_fu_a: false,

            // TODO: overflow?
            loss: pkt.loss() + additional_loss,
            same_ts_as_prev,
        }
    }
}

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum DepacketizerInputState {
    /// Not yet processing an access unit.
    New,

    /// Ignoring the remainder of an access unit because of interior packet loss.
    Loss {
        timestamp: crate::Timestamp,
        pkts: u16,
    },

    /// Currently processing an access unit.
    /// This will be flushed after a marked packet or when receiving a later timestamp.
    PreMark(AccessUnit),

    /// Finished processing the given packet. It's an error to receive the same timestamp again.
    PostMark {
        timestamp: crate::Timestamp,
        loss: u16,
    },
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
    input_state: DepacketizerInputState,
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
            input_state: DepacketizerInputState::New,
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
        // Push shouldn't be called until pull is exhausted.
        if let Some(p) = self.pending.as_ref() {
            panic!("push with data already pending: {p:?}");
        }

        let mut access_unit =
            match std::mem::replace(&mut self.input_state, DepacketizerInputState::New) {
                DepacketizerInputState::New => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(&pkt, 0, false)
                }
                DepacketizerInputState::PreMark(mut access_unit) => {
                    let loss = pkt.loss();
                    if loss > 0 {
                        self.nals.clear();
                        self.pieces.clear();
                        if access_unit.timestamp.timestamp == pkt.timestamp().timestamp {
                            // Loss within this access unit. Ignore until mark or new timestamp.
                            self.input_state = if pkt.mark() {
                                DepacketizerInputState::PostMark {
                                    timestamp: pkt.timestamp(),
                                    loss,
                                }
                            } else {
                                self.pieces.clear();
                                self.nals.clear();
                                DepacketizerInputState::Loss {
                                    timestamp: pkt.timestamp(),
                                    pkts: loss,
                                }
                            };
                            return Ok(());
                        }
                        // A suffix of a previous access unit was lost; discard it.
                        // A prefix of the new one may have been lost; try parsing.
                        AccessUnit::start(&pkt, 0, false)
                    } else if access_unit.timestamp.timestamp != pkt.timestamp().timestamp {
                        if access_unit.in_fu_a {
                            return Err(format!(
                                "Timestamp changed from {} to {} in the middle of a fragmented NAL",
                                access_unit.timestamp,
                                pkt.timestamp()
                            ));
                        }
                        let last_nal_hdr = self.nals.last().unwrap().hdr;
                        if can_end_au(last_nal_hdr.nal_unit_type()) {
                            access_unit.end_ctx = *pkt.ctx();
                            self.pending =
                                Some(self.finalize_access_unit(access_unit, "ts change")?);
                            AccessUnit::start(&pkt, 0, false)
                        } else {
                            log::debug!(
                                "Bogus mid-access unit timestamp change after {:?}",
                                last_nal_hdr
                            );
                            access_unit.timestamp.timestamp = pkt.timestamp().timestamp;
                            access_unit
                        }
                    } else {
                        access_unit
                    }
                }
                DepacketizerInputState::PostMark {
                    timestamp: state_ts,
                    loss,
                } => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    AccessUnit::start(&pkt, loss, state_ts.timestamp == pkt.timestamp().timestamp)
                }
                DepacketizerInputState::Loss {
                    timestamp,
                    mut pkts,
                } => {
                    debug_assert!(self.nals.is_empty());
                    debug_assert!(self.pieces.is_empty());
                    if pkt.timestamp().timestamp == timestamp.timestamp {
                        pkts += pkt.loss();
                        self.input_state = DepacketizerInputState::Loss { timestamp, pkts };
                        return Ok(());
                    }
                    AccessUnit::start(&pkt, pkts, false)
                }
            };

        let ctx = *pkt.ctx();
        let mark = pkt.mark();
        let loss = pkt.loss();
        let timestamp = pkt.timestamp();
        let mut data = pkt.into_payload_bytes();
        if data.is_empty() {
            return Err("Empty NAL".into());
        }
        // https://tools.ietf.org/html/rfc6184#section-5.2
        let nal_header = NalHeader::new([data[0], data[1]]);
        if nal_header.is_err() {
            return Err(format!("NAL header has F bit set"));
        }
        let nal_header = nal_header.unwrap();
        data.advance(2); // skip the header byte.
        match nal_header.nal_unit_type().value() {
            1..=40 => {
                if access_unit.in_fu_a {
                    let value = nal_header.get_value();
                    return Err(format!(
                        "Non-fragmented NAL {value:02x} while fragment in progress"
                    ));
                }
                let len = u32::try_from(data.len()).expect("data len < u16::MAX") + 1;
                let next_piece_idx = self.add_piece(data)?;
                self.nals.push(Nal {
                    hdr: nal_header,
                    next_piece_idx,
                    len,
                });
            }
            24 => {
                // STAP-A. https://tools.ietf.org/html/rfc6184#section-5.7.1
                loop {
                    if data.remaining() < 3 {
                        return Err(format!(
                            "STAP-A has {} remaining bytes; expecting 2-byte length, non-empty NAL",
                            data.remaining()
                        ));
                    }
                    let len = data.get_u16();
                    if len == 0 {
                        return Err("zero length in STAP-A".into());
                    }
                    let hdr = NalHeader::new([data[0], data[1]])
                        .map_err(|_| format!("bad header {:02x} in STAP-A", data[0]))?;
                    match data.remaining().cmp(&usize::from(len)) {
                        std::cmp::Ordering::Less => {
                            return Err(format!(
                                "STAP-A too short: {} bytes remaining, expecting {}-byte NAL",
                                data.remaining(),
                                len
                            ))
                        }
                        std::cmp::Ordering::Equal => {
                            data.advance(2);
                            let next_piece_idx = self.add_piece(data)?;
                            self.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: u32::from(len),
                            });
                            break;
                        }
                        std::cmp::Ordering::Greater => {
                            let mut piece = data.split_to(usize::from(len));
                            piece.advance(1);
                            let next_piece_idx = self.add_piece(piece)?;
                            self.nals.push(Nal {
                                hdr,
                                next_piece_idx,
                                len: u32::from(len),
                            });
                        }
                    }
                }
            }
            25..=27 | 29 => {
                let value = nal_header.get_value();
                return Err(format!(
                    "unimplemented/unexpected interleaved mode NAL ({value:02x})",
                ));
            }
            49 => {
                // FU-A. https://tools.ietf.org/html/rfc6184#section-5.8
                if data.len() < 2 {
                    return Err(format!("FU-A len {} too short", data.len()));
                }
                let fu_header = data[0];
                let start = (fu_header & 0b10000000) != 0;
                let end = (fu_header & 0b01000000) != 0;
                let reserved = (fu_header & 0b00100000) != 0;
                data.advance(1);
                if (start && end) || reserved {
                    return Err(format!("Invalid FU-A header {fu_header:02x}"));
                }
                if !end && mark {
                    return Err("FU-A pkt with MARK && !END".into());
                }
                let u32_len = u32::try_from(data.len()).expect("RTP packet len must be < u16::MAX");
                match (start, access_unit.in_fu_a) {
                    (true, true) => return Err("FU-A with start bit while frag in progress".into()),
                    (true, false) => {
                        self.add_piece(data)?;
                        self.nals.push(Nal {
                            hdr: nal_header,
                            next_piece_idx: u32::MAX, // should be overwritten later.
                            len: 1 + u32_len,
                        });
                        access_unit.in_fu_a = true;
                    }
                    (false, true) => {
                        let pieces = self.add_piece(data)?;
                        let nal = self.nals.last_mut().expect("nals non-empty while in fu-a");
                        if u16::from(nal_header.0) != u16::from(nal.hdr.0) {
                            return Err(format!(
                                "FU-A has inconsistent NAL type: {:?} then {:?}",
                                nal.hdr, nal_header,
                            ));
                        }
                        nal.len += u32_len;
                        if end {
                            nal.next_piece_idx = pieces;
                            access_unit.in_fu_a = false;
                        } else if mark {
                            return Err("FU-A has MARK and no END".into());
                        }
                    }
                    (false, false) => {
                        if loss > 0 {
                            self.pieces.clear();
                            self.nals.clear();
                            self.input_state = DepacketizerInputState::Loss {
                                timestamp,
                                pkts: loss,
                            };
                            return Ok(());
                        }
                        return Err("FU-A has start bit unset while no frag in progress".into());
                    }
                }
            }
            _ => {
                let value = nal_header.get_value();
                return Err(format!("bad nal header {value:02x}"));
            }
        }
        self.input_state = if mark {
            let last_nal_hdr = self.nals.last().unwrap().hdr;
            if can_end_au(last_nal_hdr.nal_unit_type()) {
                access_unit.end_ctx = ctx;
                self.pending = Some(self.finalize_access_unit(access_unit, "mark")?);
                DepacketizerInputState::PostMark { timestamp, loss: 0 }
            } else {
                log::debug!(
                    "Bogus mid-access unit timestamp change after {:?}",
                    last_nal_hdr
                );
                access_unit.timestamp.timestamp = timestamp.timestamp;
                DepacketizerInputState::PreMark(access_unit)
            }
        } else {
            DepacketizerInputState::PreMark(access_unit)
        };
        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<CodecItem> {
        self.pending.take().map(CodecItem::VideoFrame)
    }

    /// Adds a piece to `self.pieces`, erroring if it becomes absurdly large.
    fn add_piece(&mut self, piece: Bytes) -> Result<u32, String> {
        self.pieces.push(piece);
        u32::try_from(self.pieces.len()).map_err(|_| "more than u32::MAX pieces!".to_string())
    }

    /// Checks NAL unit type ordering against rules of H.265.
    ///
    /// This doesn't precisely check every rule there but enough to diagnose some
    /// problems.
    fn validate_order(nals: &[Nal], errs: &mut String) {
        let mut seen_vcl = false;
        for (i, nal) in nals.iter().enumerate() {
            match nal.hdr.nal_unit_type() {
                // Assuming you have these H.265 unit types mapped
                NaluType::TrailN
                | NaluType::TrailR
                | NaluType::TsaN
                | NaluType::TsaR
                | NaluType::StsaN
                | NaluType::StsaR
                | NaluType::RadlN
                | NaluType::IdrWRadl
                | NaluType::IdrNLp => {
                    seen_vcl = true; // Marks VCL NAL units
                }
                NaluType::PrefixSeiNut | NaluType::SuffixSeiNut => {
                    if seen_vcl {
                        errs.push_str("\n* SEI after VCL");
                    }
                }
                NaluType::AudNut => {
                    // Access Unit Delimiter in H.265
                    if i != 0 {
                        let _ = write!(
                            errs,
                            "\n* Access unit delimiter must be first in AU; was preceded by {:?}",
                            nals[i - 1].hdr
                        );
                    }
                }
                NaluType::EosNut => {
                    if !seen_vcl {
                        errs.push_str("\n* End of sequence without VCL");
                    }
                }
                NaluType::EobNut => {
                    if i != nals.len() - 1 {
                        errs.push_str("\n* End of bitstream NAL isn't last");
                    }
                }
                _ => {}
            }
        }
        if !seen_vcl {
            errs.push_str("\n* Missing VCL");
        }
    }

    /// Logs information about each access unit.
    /// Currently, "bad" access units (violating certain specification rules)
    /// are logged at debug priority, and others are logged at trace priority.
    fn log_access_unit(&self, au: &AccessUnit, reason: &str) {
        let mut errs = String::new();
        if au.same_ts_as_prev {
            errs.push_str("\n* same timestamp as previous access unit");
        }
        Self::validate_order(&self.nals, &mut errs);
        if !errs.is_empty() {
            let mut nals = String::new();
            for (i, nal) in self.nals.iter().enumerate() {
                let _ = write!(&mut nals, "\n  {}: {:?}", i, nal.hdr);
            }
            debug!(
                "bad access unit (ended by {}) at ts {}\nerrors are:{}\nNALs are:{}",
                reason, au.timestamp, errs, nals
            );
        } else if log_enabled!(log::Level::Trace) {
            let mut nals = String::new();
            for (i, nal) in self.nals.iter().enumerate() {
                let _ = write!(&mut nals, "\n  {}: {:?}", i, nal.hdr);
            }
            trace!(
                "access unit (ended by {}) at ts {}; NALS are:{}",
                reason,
                au.timestamp,
                nals
            );
        }
    }

    fn finalize_access_unit(&mut self, au: AccessUnit, reason: &str) -> Result<VideoFrame, String> {
        let mut piece_idx = 0;
        let mut retained_len = 0usize;
        let mut is_random_access_point = false;
        let mut is_disposable = true;
        let mut new_sps = None;
        let mut new_pps = None;

        if log_enabled!(log::Level::Debug) {
            self.log_access_unit(&au, reason);
        }
        for nal in &self.nals {
            let next_piece_idx = usize::try_from(nal.next_piece_idx).expect("u32 fits in usize");
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            match nal.hdr.nal_unit_type() {
                NaluType::SpsNut => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.sps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_sps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                NaluType::PpsNut => {
                    if self
                        .parameters
                        .as_ref()
                        .map(|p| !nal_matches(&p.pps_nal[..], nal.hdr, nal_pieces))
                        .unwrap_or(true)
                    {
                        new_pps = Some(to_bytes(nal.hdr, nal.len, nal_pieces));
                    }
                }
                NaluType::IdrNLp => is_random_access_point = true,
                NaluType::IdrWRadl => is_random_access_point = true,
                _ => {}
            }
            if nal.hdr.temporal_id() != 0 {
                is_disposable = false;
            }
            // TODO: support optionally filtering non-VUI NALs.
            retained_len += 4usize + usize::try_from(nal.len).expect("u32 fits in usize");
            piece_idx = next_piece_idx;
        }
        let mut data = Vec::with_capacity(retained_len);
        piece_idx = 0;
        for nal in &self.nals {
            let next_piece_idx = usize::try_from(nal.next_piece_idx).expect("u32 fits in usize");
            let nal_pieces = &self.pieces[piece_idx..next_piece_idx];
            data.extend_from_slice(&nal.len.to_be_bytes()[..]);
            let (high, low) = nal.hdr.bytes();
            data.push(high);
            data.push(low);
            let mut actual_len = 1;
            for piece in nal_pieces {
                data.extend_from_slice(&piece[..]);
                actual_len += piece.len();
            }
            debug_assert_eq!(
                usize::try_from(nal.len).expect("u32 fits in usize"),
                actual_len
            );
            piece_idx = next_piece_idx;
        }
        debug_assert_eq!(retained_len, data.len());
        self.nals.clear();
        self.pieces.clear();

        let mut parser = parser::Parser::default();

        let has_new_parameters = match (
            new_sps.as_deref(),
            new_pps.as_deref(),
            self.parameters.as_ref(),
        ) {
            (Some(sps_nal), Some(pps_nal), old_ip) => {
                let pps_nalu =
                    InternalParameters::find_nalu_by_type(&pps_nal, parser::NaluType::PpsNut, 0)
                        .unwrap();
                let pps = parser.parse_pps(&pps_nalu).unwrap();
                let pps_copy = pps.clone();

                let sps_nalu =
                    InternalParameters::find_nalu_by_type(&sps_nal, parser::NaluType::SpsNut, 0)
                        .unwrap();
                let sps = parser.parse_sps(&sps_nalu).unwrap();
                let sps_copy = sps.clone();
                // TODO: could map this to a RtpPacketError more accurately.
                // let seen_extra_trailing_data =
                //     old_ip.map(|o| o.seen_extra_trailing_data).unwrap_or(false);
                self.parameters = Some(InternalParameters::parse_sps_and_pps(
                    sps_nal, &sps_copy, pps_nal, &pps_copy,
                )?);
                true
            }
            (Some(_), None, Some(old_ip)) | (None, Some(_), Some(old_ip)) => {
                let sps_nal = new_sps.as_deref().unwrap_or(&old_ip.sps_nal);
                let pps_nal = new_pps.as_deref().unwrap_or(&old_ip.pps_nal);

                let pps_nalu =
                    InternalParameters::find_nalu_by_type(&pps_nal, parser::NaluType::PpsNut, 0)
                        .unwrap();
                let pps = parser.parse_pps(&pps_nalu).unwrap();
                let pps_copy = pps.clone();

                let sps_nalu =
                    InternalParameters::find_nalu_by_type(&sps_nal, parser::NaluType::SpsNut, 0)
                        .unwrap();
                let sps = parser.parse_sps(&sps_nalu).unwrap();
                let sps_copy = sps.clone();

                // TODO: as above, could map this to a RtpPacketError more accurately.
                self.parameters = Some(InternalParameters::parse_sps_and_pps(
                    sps_nal, &sps_copy, pps_nal, &pps_copy,
                )?);
                true
            }
            _ => false,
        };
        Ok(VideoFrame {
            has_new_parameters,
            loss: au.loss,
            start_ctx: au.start_ctx,
            end_ctx: au.end_ctx,
            timestamp: au.timestamp,
            stream_id: au.stream_id,
            is_random_access_point,
            is_disposable,
            data,
        })
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
