use std::fmt::{self, Debug};

use crate::codec::h265::rbsp::{BitRead, BitReaderError};

#[derive(Debug)]
pub enum SpsError {
    /// Signals that bit_depth_luma_minus8 was greater than the max value, 6
    BitDepthOutOfRange(u32),
    RbspReaderError(BitReaderError),
    /// The `cpb_cnt_minus1` field must be between 0 and 31 inclusive.
    CpbCountOutOfRange(u32),
    /// The `sps_seq_parameter_set_id` field must be between 0 and 15 inclusive.
    BadSeqParamSetId(ParamSetIdError),
}

impl From<BitReaderError> for SpsError {
    fn from(e: BitReaderError) -> Self {
        SpsError::RbspReaderError(e)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct VideoParams(u8);
impl From<u8> for VideoParams {
    fn from(v: u8) -> Self {
        VideoParams(v)
    }
}
impl From<VideoParams> for u8 {
    fn from(v: VideoParams) -> Self {
        v.0
    }
}
impl VideoParams {
    pub fn vps_id(self) -> u8 {
        self.0 & 0b1111_0000 >> 4
    }
    /// Specifies the maximum number of temporal sub-layers that may be present in each CVS referring to the SPS.
    /// The value of sps_max_sub_layers_minus1 shall be in the range of 0 to 6, inclusive.
    /// The value of sps_max_sub_layers_minus1 shall be less than or equal to vps_max_sub_layers_minus1.
    pub fn max_nb_sub_layers(self) -> u8 {
        (self.0 & 0b0000_1110 >> 1) + 1
    }
    pub fn temporal_id_nesting_flag(self) -> bool {
        self.0 & 0b0000_0001 != 0
    }
}

impl Debug for VideoParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("VideoParams")
            .field("vps_id", &self.vps_id())
            .field("max_nb_sub_layers", &self.max_nb_sub_layers())
            .field("temporal_id_nesting_flag", &self.temporal_id_nesting_flag())
            .finish()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum AspectRatioInfo {
    #[default]
    Unspecified,
    Ratio1_1,
    Ratio12_11,
    Ratio10_11,
    Ratio16_11,
    Ratio40_33,
    Ratio24_11,
    Ratio20_11,
    Ratio32_11,
    Ratio80_33,
    Ratio18_11,
    Ratio15_11,
    Ratio64_33,
    Ratio160_99,
    Ratio4_3,
    Ratio3_2,
    Ratio2_1,
    Reserved(u8),
    Extended(u16, u16),
}
impl AspectRatioInfo {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<AspectRatioInfo>, BitReaderError> {
        let aspect_ratio_info_present_flag = r.read_bool("aspect_ratio_info_present_flag")?;
        Ok(if aspect_ratio_info_present_flag {
            let aspect_ratio_idc = r.read_u8(8, "aspect_ratio_idc")?;
            Some(match aspect_ratio_idc {
                0 => AspectRatioInfo::Unspecified,
                1 => AspectRatioInfo::Ratio1_1,
                2 => AspectRatioInfo::Ratio12_11,
                3 => AspectRatioInfo::Ratio10_11,
                4 => AspectRatioInfo::Ratio16_11,
                5 => AspectRatioInfo::Ratio40_33,
                6 => AspectRatioInfo::Ratio24_11,
                7 => AspectRatioInfo::Ratio20_11,
                8 => AspectRatioInfo::Ratio32_11,
                9 => AspectRatioInfo::Ratio80_33,
                10 => AspectRatioInfo::Ratio18_11,
                11 => AspectRatioInfo::Ratio15_11,
                12 => AspectRatioInfo::Ratio64_33,
                13 => AspectRatioInfo::Ratio160_99,
                14 => AspectRatioInfo::Ratio4_3,
                15 => AspectRatioInfo::Ratio3_2,
                16 => AspectRatioInfo::Ratio2_1,
                255 => AspectRatioInfo::Extended(
                    r.read_u16(16, "sar_width")?,
                    r.read_u16(16, "sar_height")?,
                ),
                _ => AspectRatioInfo::Reserved(aspect_ratio_idc),
            })
        } else {
            None
        })
    }

    /// Returns the aspect ratio as `(width, height)`, if specified.
    pub fn get(&self) -> Option<(u16, u16)> {
        match self {
            AspectRatioInfo::Unspecified => None,
            AspectRatioInfo::Ratio1_1 => Some((1, 1)),
            AspectRatioInfo::Ratio12_11 => Some((12, 11)),
            AspectRatioInfo::Ratio10_11 => Some((10, 11)),
            AspectRatioInfo::Ratio16_11 => Some((16, 11)),
            AspectRatioInfo::Ratio40_33 => Some((40, 33)),
            AspectRatioInfo::Ratio24_11 => Some((24, 11)),
            AspectRatioInfo::Ratio20_11 => Some((20, 11)),
            AspectRatioInfo::Ratio32_11 => Some((32, 11)),
            AspectRatioInfo::Ratio80_33 => Some((80, 33)),
            AspectRatioInfo::Ratio18_11 => Some((18, 11)),
            AspectRatioInfo::Ratio15_11 => Some((15, 11)),
            AspectRatioInfo::Ratio64_33 => Some((64, 33)),
            AspectRatioInfo::Ratio160_99 => Some((160, 99)),
            AspectRatioInfo::Ratio4_3 => Some((4, 3)),
            AspectRatioInfo::Ratio3_2 => Some((3, 2)),
            AspectRatioInfo::Ratio2_1 => Some((2, 1)),
            AspectRatioInfo::Reserved(_) => None,
            &AspectRatioInfo::Extended(width, height) => {
                // ISO/IEC 14496-10 section E.2.1: "When ... sar_width is equal to 0 or sar_height
                // is equal to 0, the sample aspect ratio shall be considered unspecified by this
                // Recommendation | International Standard."
                if width == 0 || height == 0 {
                    None
                } else {
                    Some((width, height))
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum OverscanAppropriate {
    #[default]
    Unspecified,
    Appropriate,
    Inappropriate,
}
impl OverscanAppropriate {
    fn read<R: BitRead>(r: &mut R) -> Result<OverscanAppropriate, BitReaderError> {
        let overscan_info_present_flag = r.read_bool("overscan_info_present_flag")?;
        Ok(if overscan_info_present_flag {
            let overscan_appropriate_flag = r.read_bool("overscan_appropriate_flag")?;
            if overscan_appropriate_flag {
                OverscanAppropriate::Appropriate
            } else {
                OverscanAppropriate::Inappropriate
            }
        } else {
            OverscanAppropriate::Unspecified
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum VideoFormat {
    #[default]
    Component,
    PAL,
    NTSC,
    SECAM,
    MAC,
    Unspecified,
    Reserved(u8),
}
impl VideoFormat {
    fn from(video_format: u8) -> VideoFormat {
        match video_format {
            0 => VideoFormat::Component,
            1 => VideoFormat::PAL,
            2 => VideoFormat::NTSC,
            3 => VideoFormat::SECAM,
            4 => VideoFormat::MAC,
            5 => VideoFormat::Unspecified,
            6 | 7 => VideoFormat::Reserved(video_format),
            _ => panic!("unsupported video_format value {}", video_format),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ColourDescription {
    pub colour_primaries: u8,
    pub transfer_characteristics: u8,
    pub matrix_coefficients: u8,
}
impl ColourDescription {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<ColourDescription>, BitReaderError> {
        let colour_description_present_flag = r.read_bool("colour_description_present_flag")?;
        Ok(if colour_description_present_flag {
            Some(ColourDescription {
                colour_primaries: r.read_u8(8, "colour_primaries")?,
                transfer_characteristics: r.read_u8(8, "transfer_characteristics")?,
                matrix_coefficients: r.read_u8(8, "matrix_coefficients")?,
            })
        } else {
            None
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VideoSignalType {
    pub video_format: VideoFormat,
    pub video_full_range_flag: bool,
    pub colour_description: Option<ColourDescription>,
}
impl VideoSignalType {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<VideoSignalType>, BitReaderError> {
        let video_signal_type_present_flag = r.read_bool("video_signal_type_present_flag")?;
        Ok(if video_signal_type_present_flag {
            Some(VideoSignalType {
                video_format: VideoFormat::from(r.read_u8(3, "video_format")?),
                video_full_range_flag: r.read_bool("video_full_range_flag")?,
                colour_description: ColourDescription::read(r)?,
            })
        } else {
            None
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ChromaLocInfo {
    pub chroma_sample_loc_type_top_field: u32,
    pub chroma_sample_loc_type_bottom_field: u32,
}
impl ChromaLocInfo {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<ChromaLocInfo>, BitReaderError> {
        let chroma_loc_info_present_flag = r.read_bool("chroma_loc_info_present_flag")?;
        Ok(if chroma_loc_info_present_flag {
            Some(ChromaLocInfo {
                chroma_sample_loc_type_top_field: r.read_ue("chroma_sample_loc_type_top_field")?,
                chroma_sample_loc_type_bottom_field: r
                    .read_ue("chroma_sample_loc_type_bottom_field")?,
            })
        } else {
            None
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TimingInfo {
    pub num_units_in_tick: u32,
    pub time_scale: u32,
    pub fixed_frame_rate_flag: bool,
}
impl TimingInfo {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<TimingInfo>, BitReaderError> {
        let timing_info_present_flag = r.read_bool("timing_info_present_flag")?;
        Ok(if timing_info_present_flag {
            Some(TimingInfo {
                num_units_in_tick: r.read_u32(32, "num_units_in_tick")?,
                time_scale: r.read_u32(32, "time_scale")?,
                fixed_frame_rate_flag: r.read_bool("fixed_frame_rate_flag")?,
            })
        } else {
            None
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CpbSpec {
    pub bit_rate_value_minus1: u32,
    pub cpb_size_value_minus1: u32,
    pub cbr_flag: bool,
}
impl CpbSpec {
    fn read<R: BitRead>(r: &mut R) -> Result<CpbSpec, BitReaderError> {
        Ok(CpbSpec {
            bit_rate_value_minus1: r.read_ue("bit_rate_value_minus1")?,
            cpb_size_value_minus1: r.read_ue("cpb_size_value_minus1")?,
            cbr_flag: r.read_bool("cbr_flag")?,
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HrdParameters {
    pub bit_rate_scale: u8,
    pub cpb_size_scale: u8,
    pub cpb_specs: Vec<CpbSpec>,
    pub initial_cpb_removal_delay_length_minus1: u8,
    pub cpb_removal_delay_length_minus1: u8,
    pub dpb_output_delay_length_minus1: u8,
    pub time_offset_length: u8,
}
impl HrdParameters {
    fn read<R: BitRead>(
        r: &mut R,
        hrd_parameters_present: &mut bool,
    ) -> Result<Option<HrdParameters>, SpsError> {
        let hrd_parameters_present_flag = r.read_bool("hrd_parameters_present_flag")?;
        *hrd_parameters_present |= hrd_parameters_present_flag;
        Ok(if hrd_parameters_present_flag {
            let cpb_cnt_minus1 = r.read_ue("cpb_cnt_minus1")?;
            if cpb_cnt_minus1 > 31 {
                return Err(SpsError::CpbCountOutOfRange(cpb_cnt_minus1));
            }
            let cpb_cnt = cpb_cnt_minus1 + 1;
            Some(HrdParameters {
                bit_rate_scale: r.read_u8(4, "bit_rate_scale")?,
                cpb_size_scale: r.read_u8(4, "cpb_size_scale")?,
                cpb_specs: Self::read_cpb_specs(r, cpb_cnt)?,
                initial_cpb_removal_delay_length_minus1: r
                    .read_u8(5, "initial_cpb_removal_delay_length_minus1")?,
                cpb_removal_delay_length_minus1: r.read_u8(5, "cpb_removal_delay_length_minus1")?,
                dpb_output_delay_length_minus1: r.read_u8(5, "dpb_output_delay_length_minus1")?,
                time_offset_length: r.read_u8(5, "time_offset_length")?,
            })
        } else {
            None
        })
    }
    fn read_cpb_specs<R: BitRead>(r: &mut R, cpb_cnt: u32) -> Result<Vec<CpbSpec>, BitReaderError> {
        let mut cpb_specs = Vec::with_capacity(cpb_cnt as usize);
        for _ in 0..cpb_cnt {
            cpb_specs.push(CpbSpec::read(r)?);
        }
        Ok(cpb_specs)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BitstreamRestrictions {
    pub motion_vectors_over_pic_boundaries_flag: bool,
    pub max_bytes_per_pic_denom: u32,
    pub max_bits_per_mb_denom: u32,
    pub log2_max_mv_length_horizontal: u32,
    pub log2_max_mv_length_vertical: u32,
    pub max_num_reorder_frames: u32,
    pub max_dec_frame_buffering: u32,
}
impl BitstreamRestrictions {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<BitstreamRestrictions>, BitReaderError> {
        let bitstream_restriction_flag = r.read_bool("bitstream_restriction_flag")?;
        Ok(if bitstream_restriction_flag {
            Some(BitstreamRestrictions {
                motion_vectors_over_pic_boundaries_flag: r
                    .read_bool("motion_vectors_over_pic_boundaries_flag")?,
                max_bytes_per_pic_denom: r.read_ue("max_bytes_per_pic_denom")?,
                max_bits_per_mb_denom: r.read_ue("max_bits_per_mb_denom")?,
                log2_max_mv_length_horizontal: r.read_ue("log2_max_mv_length_horizontal")?,
                log2_max_mv_length_vertical: r.read_ue("log2_max_mv_length_vertical")?,
                max_num_reorder_frames: r.read_ue("max_num_reorder_frames")?,
                max_dec_frame_buffering: r.read_ue("max_dec_frame_buffering")?,
            })
        } else {
            None
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VuiParameters {
    pub aspect_ratio_info: Option<AspectRatioInfo>,
    pub overscan_appropriate: OverscanAppropriate,
    pub video_signal_type: Option<VideoSignalType>,
    pub chroma_loc_info: Option<ChromaLocInfo>,
    pub timing_info: Option<TimingInfo>,
    pub nal_hrd_parameters: Option<HrdParameters>,
    pub vcl_hrd_parameters: Option<HrdParameters>,
    pub low_delay_hrd_flag: Option<bool>,
    pub pic_struct_present_flag: bool,
    pub bitstream_restrictions: Option<BitstreamRestrictions>,
}
impl VuiParameters {
    fn read<R: BitRead>(r: &mut R) -> Result<Option<VuiParameters>, SpsError> {
        let vui_parameters_present_flag = r.read_bool("vui_parameters_present_flag")?;
        Ok(if vui_parameters_present_flag {
            let mut hrd_parameters_present = false;
            Some(VuiParameters {
                aspect_ratio_info: AspectRatioInfo::read(r)?,
                overscan_appropriate: OverscanAppropriate::read(r)?,
                video_signal_type: VideoSignalType::read(r)?,
                chroma_loc_info: ChromaLocInfo::read(r)?,
                timing_info: TimingInfo::read(r)?,
                nal_hrd_parameters: HrdParameters::read(r, &mut hrd_parameters_present)?,
                vcl_hrd_parameters: HrdParameters::read(r, &mut hrd_parameters_present)?,
                low_delay_hrd_flag: if hrd_parameters_present {
                    Some(r.read_bool("low_delay_hrd_flag")?)
                } else {
                    None
                },
                pic_struct_present_flag: r.read_bool("pic_struct_present_flag")?,
                bitstream_restrictions: BitstreamRestrictions::read(r)?,
            })
        } else {
            None
        })
    }
}

#[derive(Debug, PartialEq)]
pub enum ParamSetIdError {
    IdTooLarge(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamSetId(u8);
impl ParamSetId {
    pub fn from_u32(id: u32) -> Result<ParamSetId, ParamSetIdError> {
        if id > 15 {
            Err(ParamSetIdError::IdTooLarge(id))
        } else {
            Ok(ParamSetId(id as u8))
        }
    }
    pub fn id(self) -> u8 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ChromaFormat {
    Monochrome,
    #[default]
    YUV420,
    YUV422,
    YUV444,
    Invalid(u32),
}
impl ChromaFormat {
    fn from_chroma_format_idc(chroma_format_idc: u32) -> ChromaFormat {
        match chroma_format_idc {
            0 => ChromaFormat::Monochrome,
            1 => ChromaFormat::YUV420,
            2 => ChromaFormat::YUV422,
            3 => ChromaFormat::YUV444,
            _ => ChromaFormat::Invalid(chroma_format_idc),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ChromaFormatInfo {
    pub format: ChromaFormat,
    pub separate_colour_plane_flag: bool,
}

impl ChromaFormatInfo {
    fn read<R: BitRead>(r: &mut R) -> Result<ChromaFormatInfo, BitReaderError> {
        let chroma_format_idc = r.read_ue("chroma_format_idc")?;
        Ok(ChromaFormatInfo {
            format: ChromaFormat::from_chroma_format_idc(chroma_format_idc),
            separate_colour_plane_flag: if chroma_format_idc == 3 {
                r.read_bool("separate_colour_plane_flag")?
            } else {
                false
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqParameterSet {
    pub video_params: VideoParams,
    pub profile_tier_level: u32,  //To be modified
    pub profile_tier_level1: u32, //To be modified
    pub profile_tier_level2: u32, //To be modified
    pub seq_parameter_set_id: ParamSetId,
    pub chroma_format: ChromaFormatInfo,
    pub pic_width_in_luma_samples: u32,
    pub pic_height_in_luma_samples: u32,
    pub vui_parameters: Option<VuiParameters>,
}

impl SeqParameterSet {
    pub fn from_bits<R: BitRead>(mut r: R) -> Result<SeqParameterSet, SpsError> {
        let sps = SeqParameterSet {
            video_params: r.read_u8(8, "video_params")?.into(),
            profile_tier_level: r.read_u32(32, "profile_tier_level")?,
            profile_tier_level1: r.read_u32(32, "profile_tier_level1")?,
            profile_tier_level2: r.read_u32(32, "profile_tier_level2")?,
            seq_parameter_set_id: ParamSetId::from_u32(r.read_ue("sps_seq_parameter_set_id")?)
                .map_err(SpsError::BadSeqParamSetId)?,
            chroma_format: ChromaFormatInfo::read(&mut r)?,
            pic_width_in_luma_samples: r.read_ue("pic_width_in_luma_samples")?,
            pic_height_in_luma_samples: r.read_ue("pic_height_in_luma_samples")?,
            vui_parameters: None,
        };
        Ok(sps)
    }

    pub fn pixel_dimensions(&self) -> Result<(u32, u32), SpsError> {
        Ok((0, 0))
    }
}
