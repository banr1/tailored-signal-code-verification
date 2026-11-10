// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Stratified AArch64 instruction, RISU pattern, and FP/integer edge-value generators (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted test input generator for differential validation of
//!   `Arm64/Trusted/ISA/`).
//! - **Purpose:** Provides stratified edge-value samplers for IEEE-754 `f32`/`f64` and 32/64-bit
//!   integers, a parser for Linaro RISU `aarch64.risu` instruction patterns, and a complete
//!   49-family instruction generator covering every instruction class decoded by `Arm64.decode`.
//!
//! # Key Types & Functions
//! - [`SplitMix64`]: Deterministic PRNG matching `DifferentialEval.lean` and `sail_wrapper.c`.
//! - [`sample_fp32_edge`], [`sample_fp64_edge`]: Stratified IEEE-754 edge/boundary samplers.
//! - [`sample_int64_edge`]: Stratified 32/64-bit integer boundary sampler.
//! - [`RisuPattern`], [`load_risu_patterns`]: Parses Linaro RISU `aarch64.risu` bit templates.
//! - [`FAMILY_NAMES`], [`gen_family_insn_record`]: Generates 128-byte batch records for all 49
//!   instruction families in `Arm64.decode`.
//!
//! # When to Read This File
//! - Read this file when adding new instruction families to `Arm64.decode` or tuning edge-value
//!   weights for differential fuzzing.

use std::fs;
use std::path::Path;

use isa_oracle::{CpuState, NO_EXIT_PC, TestInput};

/// Deterministic SplitMix64 PRNG matching `DifferentialEval.lean` and `sail_wrapper.c`.
#[derive(Clone, Copy, Debug)]
pub struct SplitMix64 {
    pub state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        let s = self.state.wrapping_add(0x9e3779b97f4a7c15);
        self.state = s;
        let mut z = (s ^ (s >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    #[inline]
    pub fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    pub fn choose<T: Copy>(&mut self, slice: &[T]) -> T {
        slice[(self.next_u64() as usize) % slice.len()]
    }
}

/// Curated 32-bit IEEE-754 edge values: ±0, ±Inf, sNaN/qNaN with distinct payloads, subnormals,
/// min/max normals, halfway rounding values, and exact integer conversion boundaries (`2^31`, `2^32`, `2^63`, `2^64` ± 1 ULP).
pub const FP32_EDGES: &[u32] = &[
    0x0000_0000, // +0.0
    0x8000_0000, // -0.0
    0x7f80_0000, // +Inf
    0xff80_0000, // -Inf
    0x7fc0_0000, // default qNaN
    0xffc0_0000, // -qNaN
    0x7fc0_0001, // +qNaN payload 1
    0xffc1_2345, // -qNaN payload 0x12345
    0x7f80_0001, // +sNaN payload 1
    0xff80_0001, // -sNaN payload 1
    0x7f9a_bcde, // +sNaN payload 0x1abcde
    0xffbf_ffff, // -sNaN max payload
    0x0000_0001, // +min subnormal (2^-149)
    0x8000_0001, // -min subnormal
    0x007f_ffff, // +max subnormal
    0x807f_ffff, // -max subnormal
    0x0080_0000, // +min normal (2^-126)
    0x8080_0000, // -min normal
    0x7f7f_ffff, // +max normal
    0xff7f_ffff, // -max normal
    0x3f80_0000, // +1.0
    0xbf80_0000, // -1.0
    0x3f00_0000, // +0.5 (halfway)
    0xbf00_0000, // -0.5 (halfway)
    0x3fc0_0000, // +1.5 (halfway odd)
    0xbfc0_0000, // -1.5 (halfway odd)
    0x4020_0000, // +2.5 (halfway even)
    0xc020_0000, // -2.5 (halfway even)
    0x4eff_ffff, // 2^31 - 128 (max f32 < 2^31)
    0x4f00_0000, // 2^31 (i32 overflow boundary)
    0xcf00_0000, // -2^31 (i32 min exact)
    0xcf00_0001, // -(2^31 + 128) (i32 underflow boundary)
    0x4f7f_ffff, // 2^32 - 256 (max f32 < 2^32)
    0x4f80_0000, // 2^32 (u32 overflow boundary)
    0x5eff_ffff, // 2^63 - 2^39 (max f32 < 2^63)
    0x5f00_0000, // 2^63 (i64 overflow boundary)
    0xdf00_0000, // -2^63 (i64 min exact)
    0xdf00_0001, // -(2^63 + 2^39) (i64 underflow boundary)
    0x5f7f_ffff, // 2^64 - 2^40 (max f32 < 2^64)
    0x5f80_0000, // 2^64 (u64 overflow boundary)
];

/// Curated 64-bit IEEE-754 edge values.
pub const FP64_EDGES: &[u64] = &[
    0x0000_0000_0000_0000, // +0.0
    0x8000_0000_0000_0000, // -0.0
    0x7ff0_0000_0000_0000, // +Inf
    0xfff0_0000_0000_0000, // -Inf
    0x7ff8_0000_0000_0000, // default qNaN
    0xfff8_0000_0000_0000, // -qNaN
    0x7ff8_0000_0000_0001, // +qNaN payload 1
    0xfff9_2345_6789_abcd, // -qNaN payload
    0x7ff0_0000_0000_0001, // +sNaN payload 1
    0xfff0_0000_0000_0001, // -sNaN payload 1
    0x7ff7_ffff_ffff_ffff, // +sNaN max payload
    0xfff7_ffff_ffff_ffff, // -sNaN max payload
    0x0000_0000_0000_0001, // +min subnormal (2^-1074)
    0x8000_0000_0000_0001, // -min subnormal
    0x000f_ffff_ffff_ffff, // +max subnormal
    0x800f_ffff_ffff_ffff, // -max subnormal
    0x0010_0000_0000_0000, // +min normal (2^-1022)
    0x8010_0000_0000_0000, // -min normal
    0x7fef_ffff_ffff_ffff, // +max normal
    0xffef_ffff_ffff_ffff, // -max normal
    0x3ff0_0000_0000_0000, // +1.0
    0xbff0_0000_0000_0000, // -1.0
    0x3fe0_0000_0000_0000, // +0.5 (halfway)
    0xbfe0_0000_0000_0000, // -0.5 (halfway)
    0x3ff8_0000_0000_0000, // +1.5 (halfway odd)
    0xbff8_0000_0000_0000, // -1.5 (halfway odd)
    0x4004_0000_0000_0000, // +2.5 (halfway even)
    0xc004_0000_0000_0000, // -2.5 (halfway even)
    0x41df_ffff_ffc0_0000, // 2^31 - 1
    0x41df_ffff_ffe0_0000, // 2^31 - 0.5
    0x41e0_0000_0000_0000, // 2^31
    0xc1e0_0000_0000_0000, // -2^31
    0xc1e0_0000_0010_0000, // -2^31 - 0.5
    0xc1e0_0000_0020_0000, // -2^31 - 1
    0x41ef_ffff_ffe0_0000, // 2^32 - 1
    0x41f0_0000_0000_0000, // 2^32
    0x43df_ffff_ffff_ffff, // max f64 < 2^63
    0x43e0_0000_0000_0000, // 2^63
    0xc3e0_0000_0000_0000, // -2^63
    0xc3e0_0000_0000_0001, // -(2^63 + 1024)
    0x43ef_ffff_ffff_ffff, // max f64 < 2^64
    0x43f0_0000_0000_0000, // 2^64
];

/// Curated 64-bit integer boundary values (covering 8/16/32/64-bit signed/unsigned limits and shift counts).
pub const INT64_EDGES: &[u64] = &[
    0,
    1,
    2,
    7,
    8,
    15,
    16,
    31,
    32,
    33,
    63,
    64,
    65,
    127,
    128,
    255,
    256,
    0x7fff,
    0x8000,
    0xffff,
    0x1_0000,
    0x7fff_ffff,
    0x8000_0000,
    0x8000_0001,
    0xffff_fffe,
    0xffff_ffff,
    0x1_0000_0000,
    0x7fff_ffff_ffff_fffe,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    0x8000_0000_0000_0001,
    0xffff_ffff_0000_0000,
    0xffff_ffff_7fff_ffff,
    0xffff_ffff_8000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0x0123_4567_89ab_cdef,
    0xfedc_ba98_7654_3210,
    0x5555_5555_5555_5555,
    0xaaaa_aaaa_aaaa_aaaa,
];

/// Stratified `f32` sampler (exponent class × significand pattern + edge table).
pub fn sample_fp32_edge(rng: &mut SplitMix64) -> u32 {
    let r = rng.next_u32();
    if (r & 3) != 0 {
        return rng.choose(FP32_EDGES);
    }
    let sign = (r >> 31) & 1;
    let exp_class = (r >> 24) & 7;
    let exp: u32 = match exp_class {
        0 => 0,
        1 => 1,
        2 => 126,
        3 => 127,
        4 => 128,
        5 => 127 + 31,
        6 => 254,
        _ => 255,
    };
    let frac_pat = (r >> 20) & 7;
    let frac: u32 = match frac_pat {
        0 => 0,
        1 => 1,
        2 => 0x0040_0000,
        3 => 0x003f_ffff,
        4 => 0x007f_fffe,
        5 => 0x007f_ffff,
        6 => 1 << ((r >> 8) % 23),
        _ => rng.next_u32() & 0x007f_ffff,
    };
    (sign << 31) | (exp << 23) | frac
}

/// Stratified `f64` sampler (exponent class × significand pattern + edge table).
pub fn sample_fp64_edge(rng: &mut SplitMix64) -> u64 {
    let r = rng.next_u64();
    if (r & 3) != 0 {
        return rng.choose(FP64_EDGES);
    }
    let sign = (r >> 63) & 1;
    let exp_class = (r >> 56) & 7;
    let exp: u64 = match exp_class {
        0 => 0,
        1 => 1,
        2 => 1022,
        3 => 1023,
        4 => 1024,
        5 => 1023 + 31,
        6 => 2046,
        _ => 2047,
    };
    let frac_pat = (r >> 52) & 7;
    let frac: u64 = match frac_pat {
        0 => 0,
        1 => 1,
        2 => 0x0008_0000_0000_0000,
        3 => 0x0007_ffff_ffff_ffff,
        4 => 0x000f_ffff_ffff_fffe,
        5 => 0x000f_ffff_ffff_ffff,
        6 => 1u64 << ((r >> 16) % 52),
        _ => rng.next_u64() & 0x000f_ffff_ffff_ffff,
    };
    (sign << 63) | (exp << 52) | frac
}

/// Stratified 64-bit integer sampler.
pub fn sample_int64_edge(rng: &mut SplitMix64) -> u64 {
    if (rng.next_u32() & 3) != 0 {
        rng.choose(INT64_EDGES)
    } else {
        rng.next_u64()
    }
}

/// Parsed Linaro RISU instruction pattern (`aarch64.risu`).
#[derive(Clone, Debug)]
pub struct RisuPattern {
    pub name: String,
    pub mask: u32,
    pub val: u32,
    pub rn_shift: Option<u32>,
}

/// Parse all 32-bit instruction patterns from Linaro RISU's `aarch64.risu`.
pub fn load_risu_patterns(path: &Path) -> Vec<RisuPattern> {
    let Ok(text) = fs::read_to_string(path) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for raw_line in text.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with('.') || line.starts_with('!') || line.starts_with('}') {
            continue;
        }
        let head = line.split('\\').next().unwrap_or(line).split('!').next().unwrap_or(line);
        let toks: Vec<&str> = head.split_whitespace().collect();
        if toks.len() < 3 || !toks[1].starts_with("A64") {
            continue;
        }
        let name = toks[0].to_string();
        let mut bit_pos: i32 = 32;
        let mut mask: u32 = 0;
        let mut val: u32 = 0;
        let mut rn_shift: Option<u32> = None;
        let mut ok = true;
        for &tok in &toks[2..] {
            if let Some((fname, w_str)) = tok.split_once(':') {
                let Ok(w) = w_str.parse::<i32>() else {
                    ok = false;
                    break;
                };
                bit_pos -= w;
                if bit_pos < 0 {
                    ok = false;
                    break;
                }
                if fname.eq_ignore_ascii_case("rn") && w == 5 {
                    rn_shift = Some(bit_pos as u32);
                }
            } else if tok.chars().all(|c| c == '0' || c == '1') {
                for ch in tok.chars() {
                    bit_pos -= 1;
                    if bit_pos < 0 {
                        ok = false;
                        break;
                    }
                    mask |= 1u32 << bit_pos;
                    if ch == '1' {
                        val |= 1u32 << bit_pos;
                    }
                }
            } else {
                ok = false;
                break;
            }
        }
        if ok && bit_pos == 0 {
            out.push(RisuPattern {
                name,
                mask,
                val,
                rn_shift,
            });
        }
    }
    out
}

/// Names of the 49 instruction families in `Arm64.decode` (`Decode.lean`).
pub const FAMILY_NAMES: [&str; 49] = [
    "01_nop_hint_dmb_clrex",
    "02_pc_rel_adr_adrp",
    "03_add_sub_imm",
    "04_logical_imm",
    "05_move_wide_imm",
    "06_bitfield_bfm_sbfm_ubfm",
    "07_extract_extr",
    "08_b_bl_uncond",
    "09_b_cond",
    "10_cbz_cbnz",
    "11_tbz_tbnz",
    "12_svc_brk_udf",
    "13_mrs_msr_dc_zva",
    "14_br_blr_ret",
    "15_data_proc_2src_div_shift_crc",
    "16_data_proc_1src_rbit_clz_rev",
    "17_logical_shifted_reg",
    "18_add_sub_shifted_reg",
    "19_add_sub_extended_reg",
    "20_add_sub_with_carry_adc_sbc",
    "21_cond_compare_ccmp_ccmn",
    "22_cond_select_csel_csinc_csinv_csneg",
    "23_data_proc_3src_madd_msub_mulh",
    "24_ldnp_stnp_gpr",
    "25_ldp_stp_gpr",
    "26_ldr_str_unsigned_imm",
    "27_ldur_stur_pre_post_regoff",
    "28_ldr_literal_gpr",
    "29_atomics_ldxr_stxr_cas_casp_rmw_rcpc",
    "30_ldr_literal_simd",
    "31_ldnp_stnp_simd",
    "32_ldp_stp_simd",
    "33_ldr_str_unsigned_imm_simd",
    "34_ldur_stur_pre_post_regoff_simd",
    "35_simd_ld1_st1_multi",
    "36_simd_ld1r",
    "37_simd_st1_single_post",
    "38_crypto_aes",
    "39_fmov_fcvt_scvtf_gpr_vec",
    "40_simd_imm_shift_movi_shl_ushll_sri_sli",
    "41_simd_tbl_tbx_addp_scalar",
    "42_simd_dup_ins_umov",
    "43_simd_three_same",
    "44_simd_two_reg_misc",
    "45_simd_across_lanes",
    "46_simd_permute_ext",
    "47_fp_dataproc_1_2_cmp_imm_ccmp_csel",
    "48_fp_dataproc_3_fmadd_fmsub_fnmadd_fnmsub",
    "49_fp_fixed_point_conv",
];

/// Generate one 16-word (128-byte) single-instruction batch record for family `fam_idx` (`0..49`).
pub fn gen_family_insn_record(fam_idx: usize, rng: &mut SplitMix64) -> [u64; 16] {
    let r = rng.next_u32();
    let rd = r & 0x1f;
    let rn = (r >> 5) & 0x1f;
    let rm = (r >> 10) & 0x1f;
    let ra = (r >> 15) & 0x1f;
    let sf = (r >> 31) & 1;

    let mut mem_base_reg: Option<u32> = if (23..=36).contains(&fam_idx) {
        Some(rn)
    } else {
        None
    };
    let mem_align_mask = !0xfu64;

    let insn: u32 = match fam_idx {
        0 => {
            match r & 3 {
                0 => 0xd503_201f, // NOP
                1 => {
                    let hint_imm = [0u32, 1, 4, 5, 16, 20, 22][(r as usize >> 8) % 7];
                    0xd503_201f | (hint_imm << 5) // HINT
                }
                2 => 0xd503_305f, // CLREX
                _ => 0xd503_309f | (((r >> 8) & 0xf) << 8) | (((r >> 12) & 1) << 5), // DMB/DSB
            }
        }
        1 => (r & 0xe0ff_ffff) | 0x1000_0000, // ADR / ADRP
        2 => (sf << 31) | ((r & 3) << 29) | 0x1100_0000 | (((r >> 2) & 1) << 22) | (((r >> 8) & 0xfff) << 10) | (rn << 5) | rd,
        3 => {
            let n_bit = if sf == 1 { (r >> 22) & 1 } else { 0 };
            let imms = (r >> 10) & 0x1e; // valid non-all-ones imms
            let immr = (r >> 16) & (if sf == 1 { 0x3f } else { 0x1f });
            (sf << 31) | ((r & 3) << 29) | 0x1200_0000 | (n_bit << 22) | (immr << 16) | (imms << 10) | (rn << 5) | rd
        }
        4 => {
            let hw = if sf == 1 { (r >> 21) & 3 } else { (r >> 21) & 1 };
            let opc = [0u32, 2, 3][(r as usize) % 3];
            (sf << 31) | (opc << 29) | 0x1280_0000 | (hw << 21) | (((r >> 5) & 0xffff) << 5) | rd
        }
        5 => {
            let opc = (r >> 29) & 2; // SBFM (0) or UBFM (2) or BFM (1)
            let opc3 = (r >> 29) % 3;
            let mask = if sf == 1 { 0x3f } else { 0x1f };
            let immr = (r >> 16) & mask;
            let imms = (r >> 10) & mask;
            let _ = opc;
            (sf << 31) | (opc3 << 29) | 0x1300_0000 | (sf << 22) | (immr << 16) | (imms << 10) | (rn << 5) | rd
        }
        6 => {
            let imms = (r >> 10) & (if sf == 1 { 0x3f } else { 0x1f });
            (sf << 31) | 0x1380_0000 | (sf << 22) | (rm << 16) | (imms << 10) | (rn << 5) | rd
        }
        7 => (((r >> 31) & 1) << 31) | 0x1400_0000 | (r & 0x03ff_ffff), // B / BL
        8 => 0x5400_0000 | (((r >> 5) & 0x7ffff) << 5) | (r & 0xf),     // B.cond
        9 => (sf << 31) | 0x3400_0000 | (((r >> 24) & 1) << 24) | (((r >> 5) & 0x7ffff) << 5) | rd, // CBZ/CBNZ
        10 => {
            let b5 = sf;
            let b40 = (r >> 19) & 0x1f;
            (b5 << 31) | 0x3600_0000 | (((r >> 24) & 1) << 24) | (b40 << 19) | (((r >> 5) & 0x3fff) << 5) | rd
        }
        11 => 0x0000_0000 | (r & 0xffff), // UDF (both Lean and Sail trap cleanly)
        12 => {
            // MRS/MSR TPIDR_EL0 or FPCR or FPSR, or DC ZVA
            match (r >> 5) % 6 {
                0 => 0xd53b_d040 | rd, // MRS Xd, TPIDR_EL0
                1 => 0xd53b_4400 | rd, // MRS Xd, FPCR
                2 => 0xd53b_4420 | rd, // MRS Xd, FPSR
                3 => 0xd51b_4420 | rd, // MSR FPSR, Xd
                4 => {
                    if (r >> 12) & 1 == 0 {
                        0xd51b_441f // MSR FPCR, XZR (succeeds as no-op)
                    } else {
                        0xd51b_4400 | rd // MSR FPCR, Xd (succeeds iff Xd == 0, else fails closed)
                    }
                }
                _ => {
                    mem_base_reg = Some(rd);
                    0xd50b_7420 | rd // DC ZVA, Xd
                }
            }
        }
        13 => {
            let opc = (r >> 21) % 3;
            0xd61f_0000 | (opc << 21) | (rn << 5) // BR / BLR / RET
        }
        14 => {
            let opc = [2u32, 3, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23][(r as usize) % 14];
            let sf_use = if opc >= 16 && opc <= 21 { 0 } else if opc >= 22 { 1 } else { sf };
            (sf_use << 31) | 0x1ac0_0000 | (rm << 16) | (opc << 10) | (rn << 5) | rd
        }
        15 => {
            let opc = if sf == 1 { (r >> 10) & 3 } else { [0u32, 1, 2, 4, 5][(r as usize) % 5] };
            (sf << 31) | 0x5ac0_0000 | (opc << 10) | (rn << 5) | rd
        }
        16 => {
            let shift = (r >> 22) & 3;
            let imm6 = (r >> 10) & (if sf == 1 { 0x3f } else { 0x1f });
            (sf << 31) | (((r >> 29) & 3) << 29) | 0x0a00_0000 | (shift << 22) | (((r >> 21) & 1) << 21) | (rm << 16) | (imm6 << 10) | (rn << 5) | rd
        }
        17 => {
            let shift = (r >> 22) % 3;
            let imm6 = (r >> 10) & (if sf == 1 { 0x3f } else { 0x1f });
            (sf << 31) | (((r >> 29) & 3) << 29) | 0x0b00_0000 | (shift << 22) | (rm << 16) | (imm6 << 10) | (rn << 5) | rd
        }
        18 => {
            let opt = (r >> 13) & 7;
            let imm3 = (r >> 10) & 3;
            (sf << 31) | (((r >> 29) & 3) << 29) | 0x0b20_0000 | (rm << 16) | (opt << 13) | (imm3 << 10) | (rn << 5) | rd
        }
        19 => (sf << 31) | (((r >> 29) & 3) << 29) | 0x1a00_0000 | (rm << 16) | (rn << 5) | rd, // ADC/ADCS/SBC/SBCS
        20 => {
            let cond = (r >> 12) & 0xf;
            let nzcv = r & 0xf;
            (sf << 31) | (((r >> 30) & 1) << 30) | 0x3a40_0000 | (rm << 16) | (cond << 12) | (((r >> 11) & 1) << 11) | (rn << 5) | nzcv
        }
        21 => {
            let cond = (r >> 12) & 0xf;
            let op = (r >> 30) & 1;
            let op2 = (r >> 10) & 1;
            (sf << 31) | (op << 30) | 0x1a80_0000 | (rm << 16) | (cond << 12) | (op2 << 10) | (rn << 5) | rd
        }
        22 => {
            // MADD, MSUB, SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH
            let kind = (r >> 21) % 6;
            let o0 = (r >> 15) & 1;
            match kind {
                0 | 1 => (sf << 31) | 0x1b00_0000 | (rm << 16) | (o0 << 15) | (ra << 10) | (rn << 5) | rd,
                2 => 0x9b20_0000 | (rm << 16) | (o0 << 15) | (ra << 10) | (rn << 5) | rd,
                3 => 0x9b40_7c00 | (rm << 16) | (rn << 5) | rd,
                4 => 0x9ba0_0000 | (rm << 16) | (o0 << 15) | (ra << 10) | (rn << 5) | rd,
                _ => 0x9bc0_7c00 | (rm << 16) | (rn << 5) | rd,
            }
        }
        23 => {
            let opc = if (r & 1) == 0 { 0u32 } else { 2u32 };
            let l_bit = (r >> 22) & 1;
            let rt2 = if l_bit == 1 && rd == ra { (rd + 1) & 0x1f } else { ra };
            let imm7 = ((r >> 15) & 3) << 0; // small offset 0..3 so ea stays in [0x20000, 0x20040)
            (opc << 30) | 0x2800_0000 | (l_bit << 22) | (imm7 << 15) | (rt2 << 10) | (rn << 5) | rd
        }
        24 => {
            let opc = (r >> 30) % 3;
            let l_bit = if opc == 1 { 1 } else { (r >> 22) & 1 };
            let mode = [1u32, 2, 3][(r as usize) % 3];
            let mut rt1 = rd;
            let mut rt2 = ra;
            if l_bit == 1 && rt1 == rt2 {
                rt2 = (rt1 + 1) & 0x1f;
            }
            if mode != 2 && rn != 31 {
                if rt1 == rn { rt1 = (rn + 1) % 30; }
                if rt2 == rn { rt2 = (rn + 2) % 30; }
            }
            let imm7 = (r >> 15) & 1;
            (opc << 30) | 0x2800_0000 | (mode << 23) | (l_bit << 22) | (imm7 << 15) | (rt2 << 10) | (rn << 5) | rt1
        }
        25 => {
            let sz = (r >> 30) & 3;
            let opc = match sz {
                0 | 1 => (r >> 22) & 3,
                2 => (r >> 22) % 3,
                _ => (r >> 22) & 1,
            };
            let imm12 = (r >> 10) & 1;
            (sz << 30) | 0x3900_0000 | (opc << 22) | (imm12 << 10) | (rn << 5) | rd
        }
        26 => {
            let sz = (r >> 30) & 3;
            let opc = match sz {
                0 | 1 => (r >> 22) & 3,
                2 => (r >> 22) % 3,
                _ => (r >> 22) & 1,
            };
            let mode = [0u32, 1, 3][(r as usize) % 3];
            let rt = if mode != 0 && rn != 31 && rd == rn { (rn + 1) % 30 } else { rd };
            let imm9 = (r >> 12) & 7;
            (sz << 30) | 0x3800_0000 | (opc << 22) | (imm9 << 12) | (mode << 10) | (rn << 5) | rt
        }
        27 => {
            // LDR literal (PC = 0x10000, imm19 = 0x4008 -> 0x20020 in scratch memory)
            let opc = (r >> 30) % 3;
            (opc << 30) | 0x1800_0000 | (0x4008 << 5) | rd
        }
        28 => {
            // Atomics: LDXR, STXR, CAS, CASP, LDADD, SWP, LDAPR
            let sub = r % 5;
            let sz = (r >> 30) & 3;
            match sub {
                0 => (sz << 30) | 0x085f_7c00 | (((r >> 15) & 1) << 15) | (rn << 5) | rd, // LDXR/LDAXR
                1 => {
                    let rs = if rm == rd || rm == rn { (rd + 2) % 30 } else { rm };
                    (sz << 30) | 0x0800_7c00 | (rs << 16) | (((r >> 15) & 1) << 15) | (rn << 5) | rd // STXR
                }
                2 => (sz << 30) | 0x08a0_7c00 | (((r >> 22) & 1) << 22) | (rm << 16) | (((r >> 15) & 1) << 15) | (rn << 5) | rd, // CAS
                3 => (sz << 30) | 0x38bfc000 | (rn << 5) | rd, // LDAPR
                _ => {
                    let opc = [0u32, 1, 2, 3, 4, 5, 6, 7, 8][(r as usize) % 9];
                    (sz << 30) | 0x3820_0000 | (((r >> 22) & 3) << 22) | (rm << 16) | (opc << 12) | (rn << 5) | rd // Atomic RMW / SWP
                }
            }
        }
        29 => {
            let opc = (r >> 30) % 3;
            (opc << 30) | 0x1c00_0000 | (0x4008 << 5) | rd // LDR Simd Lit (PC = 0x10000 -> 0x20020)
        }
        30 => {
            let opc = (r >> 30) % 3;
            let l_bit = (r >> 22) & 1;
            let vt2 = if l_bit == 1 && rd == ra { (rd + 1) & 0x1f } else { ra };
            (opc << 30) | 0x2c00_0000 | (l_bit << 22) | (vt2 << 10) | (rn << 5) | rd
        }
        31 => {
            let opc = (r >> 30) % 3;
            let l_bit = (r >> 22) & 1;
            let mode = [1u32, 2, 3][(r as usize) % 3];
            let vt2 = if l_bit == 1 && rd == ra { (rd + 1) & 0x1f } else { ra };
            (opc << 30) | 0x2c00_0000 | (mode << 23) | (l_bit << 22) | (vt2 << 10) | (rn << 5) | rd
        }
        32 => {
            let (sz, opc) = [(0u32, 0u32), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (0, 2), (0, 3)][(r as usize) % 10];
            (sz << 30) | 0x3d00_0000 | (opc << 22) | (rn << 5) | rd
        }
        33 => {
            let (sz, opc) = [(0u32, 0u32), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (0, 2), (0, 3)][(r as usize) % 10];
            let mode = [0u32, 1, 3][(r as usize) % 3];
            let imm9 = (r >> 12) & 7;
            (sz << 30) | 0x3c00_0000 | (opc << 22) | (imm9 << 12) | (mode << 10) | (rn << 5) | rd
        }
        34 => {
            // SIMD LD1/ST1 multiple (1..2 regs so total <= 32 bytes inside [0x20020, 0x20040))
            let q = (r >> 30) & 1;
            let l_bit = (r >> 22) & 1;
            let opcode = if (r & 1) == 0 { 7u32 } else { 10u32 };
            let sz = (r >> 10) & 3;
            let sz_use = if sz == 3 && q == 0 && opcode != 7 { 2 } else { sz };
            (q << 30) | 0x0c00_0000 | (l_bit << 22) | (opcode << 12) | (sz_use << 10) | (rn << 5) | rd
        }
        35 => {
            let q = (r >> 30) & 1;
            let sz = (r >> 10) & 3;
            (q << 30) | 0x0d40_c000 | (sz << 10) | (rn << 5) | rd // LD1R
        }
        36 => {
            let q = (r >> 30) & 1;
            let (opc, s_bit, sz) = [(0u32, 0u32, 0u32), (2, 0, 0), (4, 0, 0), (4, 0, 1)][(r as usize) % 4];
            (q << 30) | 0x0d9f_0000 | (opc << 13) | (s_bit << 12) | (sz << 10) | (rn << 5) | rd // ST1 single post #imm
        }
        37 => {
            // Crypto / Hash / Polynomial: AES, PMULL, SHA-1, SHA-256, SHA-512, SHA-3
            let sub = (r >> 20) % 8;
            match sub {
                0 => {
                    let op = (r >> 12) & 3;
                    0x4e28_4800 | (op << 12) | (rn << 5) | rd // AESE, AESD, AESMC, AESIMC
                }
                1 => {
                    let q = (r >> 30) & 1;
                    let sz = if ((r >> 22) & 1) == 0 { 0u32 } else { 3u32 };
                    (q << 30) | 0x0e20_e000 | (sz << 22) | (rm << 16) | (rn << 5) | rd // PMULL / PMULL2
                }
                2 => {
                    let opc = (r >> 12) % 3;
                    0x5e28_0800 | (opc << 12) | (rn << 5) | rd // SHA1H, SHA1SU1, SHA256SU0
                }
                3 => {
                    let opc = (r >> 12) % 7;
                    0x5e00_0000 | (rm << 16) | (opc << 12) | (rn << 5) | rd // SHA1C/P/M/SU0, SHA256H/H2/SU1
                }
                4 => 0xcec0_8000 | (rn << 5) | rd, // SHA512SU0
                5 => {
                    let opc = (r >> 10) & 3;
                    0xce60_8000 | (rm << 16) | (opc << 10) | (rn << 5) | rd // SHA512H, SHA512H2, SHA512SU1, RAX1
                }
                6 => {
                    let is_bcax = (r >> 21) & 1;
                    0xce00_0000 | (is_bcax << 21) | (rm << 16) | (ra << 10) | (rn << 5) | rd // EOR3, BCAX
                }
                _ => {
                    let imm6 = (r >> 10) & 0x3f;
                    0xce80_0000 | (rm << 16) | (imm6 << 10) | (rn << 5) | rd // XAR
                }
            }
        }
        38 => {
            // FMOV / FCVT* / SCVTF / UCVTF (GPR <-> SIMD/FP scalar)
            let ftype = (r >> 22) & 1;
            let sub = r % 6;
            match sub {
                0 => (ftype << 31) | 0x1e26_0000 | (ftype << 22) | (rn << 5) | rd, // FMOV Wd/Xd, Sn/Dn
                1 => (ftype << 31) | 0x1e27_0000 | (ftype << 22) | (rn << 5) | rd, // FMOV Sd/Dd, Wn/Xn
                2 | 3 => {
                    let rmode = (r >> 19) & 3;
                    let opc = (r >> 16) & 1;
                    (sf << 31) | 0x1e20_0000 | (ftype << 22) | (rmode << 19) | (opc << 16) | (rn << 5) | rd // FCVTNS/FCVTPS/FCVTMS/FCVTZS
                }
                4 => {
                    let opc = 4 | ((r >> 16) & 1);
                    (sf << 31) | 0x1e20_0000 | (ftype << 22) | (opc << 16) | (rn << 5) | rd // FCVTAS/FCVTAU
                }
                _ => {
                    let opc = 2 | ((r >> 16) & 1);
                    (sf << 31) | 0x1e20_0000 | (ftype << 22) | (opc << 16) | (rn << 5) | rd // SCVTF/UCVTF
                }
            }
        }
        39 => {
            // SIMD Modified Immediate & SIMD Shift by Immediate (§2.4 Family A)
            let q = (r >> 30) & 1;
            if (r & 3) == 0 {
                // Modified immediate (`immh == 0`, `o2 == 0`): MOVI, MVNI, ORR #imm, BIC #imm, MSL, FMOV #imm8
                let immb = (r >> 16) & 7;
                let (q_use, op, cmode) = [
                    (q, 0u32, 0b1110u32), // MOVI 8-bit
                    (1, 1, 0b1110),       // MOVI 64-bit
                    (q, 0, 0b0000),       // MOVI 32-bit LSL #0
                    (q, 0, 0b0010),       // MOVI 32-bit LSL #8
                    (q, 0, 0b0100),       // MOVI 32-bit LSL #16
                    (q, 0, 0b0110),       // MOVI 32-bit LSL #24
                    (q, 1, 0b0000),       // MVNI 32-bit LSL #0
                    (q, 1, 0b0100),       // MVNI 32-bit LSL #16
                    (q, 0, 0b0001),       // ORR 32-bit #imm LSL #0
                    (q, 0, 0b0111),       // ORR 32-bit #imm LSL #24
                    (q, 1, 0b0001),       // BIC 32-bit #imm LSL #0
                    (q, 1, 0b0101),       // BIC 32-bit #imm LSL #16
                    (q, 0, 0b1000),       // MOVI 16-bit LSL #0
                    (q, 0, 0b1010),       // MOVI 16-bit LSL #8
                    (q, 1, 0b1000),       // MVNI 16-bit LSL #0
                    (q, 1, 0b1010),       // MVNI 16-bit LSL #8
                    (q, 0, 0b1001),       // ORR 16-bit #imm LSL #0
                    (q, 1, 0b1011),       // BIC 16-bit #imm LSL #8
                    (q, 0, 0b1100),       // MOVI 32-bit MSL #8
                    (q, 0, 0b1101),       // MOVI 32-bit MSL #16
                    (q, 1, 0b1100),       // MVNI 32-bit MSL #8
                    (q, 1, 0b1101),       // MVNI 32-bit MSL #16
                    (q, 0, 0b1111),       // FMOV 2S/4S #imm8
                    (1, 1, 0b1111),       // FMOV 2D #imm8
                ][(r as usize >> 2) % 24];
                (q_use << 30) | (op << 29) | 0x0f00_0400 | (immb << 16) | (cmode << 12) | (rn << 5) | rd
            } else {
                // Shift by immediate (`immh != 0`): SSHR, USHR, SSRA, USRA, SRSHR, URSHR, SRSRA, URSRA,
                // SRI, SHL, SLI, SQSHLU, SQSHL, UQSHL, SHRN, RSHRN, SQSHRUN, SQRSHRUN, SQSHRN, UQSHRN,
                // SQRSHRN, UQRSHRN, SSHLL, USHLL.
                let (op, opc, allow_64) = [
                    (0u32, 0b00000u32, true),  // SSHR
                    (1, 0b00000, true),        // USHR
                    (0, 0b00010, true),        // SSRA
                    (1, 0b00010, true),        // USRA
                    (0, 0b00100, true),        // SRSHR
                    (1, 0b00100, true),        // URSHR
                    (0, 0b00110, true),        // SRSRA
                    (1, 0b00110, true),        // URSRA
                    (1, 0b01000, true),        // SRI
                    (0, 0b01010, true),        // SHL
                    (1, 0b01010, true),        // SLI
                    (1, 0b01100, true),        // SQSHLU
                    (0, 0b01110, true),        // SQSHL #imm
                    (1, 0b01110, true),        // UQSHL #imm
                    (0, 0b10000, false),       // SHRN / SHRN2
                    (0, 0b10001, false),       // RSHRN / RSHRN2
                    (1, 0b10000, false),       // SQSHRUN / SQSHRUN2
                    (1, 0b10001, false),       // SQRSHRUN / SQRSHRUN2
                    (0, 0b10010, false),       // SQSHRN / SQSHRN2
                    (1, 0b10010, false),       // UQSHRN / UQSHRN2
                    (0, 0b10011, false),       // SQRSHRN / SQRSHRN2
                    (1, 0b10011, false),       // UQRSHRN / UQRSHRN2
                    (0, 0b10100, false),       // SSHLL / SSHLL2
                    (1, 0b10100, false),       // USHLL / USHLL2
                ][(r as usize >> 2) % 24];
                let (q_use, immh) = if allow_64 && ((r >> 19) & 3) == 3 {
                    (1u32, 8u32 | ((r >> 21) & 7))
                } else {
                    let base = [1u32, 2, 4][(r as usize >> 19) % 3];
                    let extra = (r >> 21) & (base - 1);
                    (q, base | extra)
                };
                let immb = (r >> 16) & 7;
                (q_use << 30) | (op << 29) | 0x0f00_0400 | (immh << 19) | (immb << 16) | (opc << 11) | (rn << 5) | rd
            }
        }
        40 => {
            if (r & 1) == 0 {
                let q = (r >> 30) & 1;
                let len = (r >> 13) & 3;
                let op = (r >> 12) & 1;
                (q << 30) | 0x0e00_0000 | (rm << 16) | (len << 13) | (op << 12) | (rn << 5) | rd // TBL/TBX
            } else {
                0x5ef1_b800 | (rn << 5) | rd // ADDP Dd, Vn.2D
            }
        }
        41 => {
            // DUP / INS / UMOV / SMOV
            let sub = r % 8;
            match sub {
                0 => 0x4e01_0c00 | (rn << 5) | rd, // DUP Vd.16B, Wn
                1 => 0x4e04_0400 | (rn << 5) | rd, // DUP Vd.4S, Vn.S[0]
                2 => 0x0e04_3c00 | (rn << 5) | rd, // UMOV Wd, Vn.S[0]
                3 => 0x4e08_3c00 | (rn << 5) | rd, // UMOV Xd, Vn.D[0]
                4 => 0x0e01_2c00 | (((r >> 17) & 7) << 17) | (rn << 5) | rd, // SMOV Wd, Vn.B[i]
                5 => 0x0e02_2c00 | (((r >> 18) & 3) << 18) | (rn << 5) | rd, // SMOV Wd, Vn.H[i]
                6 => 0x4e04_2c00 | (((r >> 19) & 3) << 19) | (rn << 5) | rd, // SMOV Xd, Vn.S[i]
                _ => 0x6e08_0400 | (rn << 5) | rd, // INS Vd.D[0], Vn.D[0]
            }
        }
        42 => {
            // SIMD Three Same (§2.4 + §2.6 PMUL + Tier 1 integer AdvSIMD)
            let q = (r >> 30) & 1;
            let u = (r >> 29) & 1;
            let kind = (r as usize >> 2) % 24;
            match kind {
                0 => {
                    // Logical: AND, BIC, ORR, ORN, EOR, BSL, BIT, BIF (`opcode == 00011`)
                    let sz = (r >> 22) & 3;
                    (q << 30) | (u << 29) | 0x0e20_1c00 | (sz << 22) | (rm << 16) | (rn << 5) | rd
                }
                1 => {
                    // PMUL 8B/16B (`u = 1, size = 00, opcode = 10011`)
                    (q << 30) | 0x2e20_9c00 | (rm << 16) | (rn << 5) | rd
                }
                2 => {
                    // MUL 8B/16B/4H/8H/2S/4S (`u = 0, size in 0..3, opcode = 10011`)
                    let sz = (r >> 22) % 3;
                    (q << 30) | 0x0e20_9c00 | (sz << 22) | (rm << 16) | (rn << 5) | rd
                }
                3 => {
                    // SQDMULH / SQRDMULH (`size in {1, 2}, opcode = 10110`)
                    let sz = 1 + ((r >> 22) & 1);
                    (q << 30) | (u << 29) | 0x0e20_b400 | (sz << 22) | (rm << 16) | (rn << 5) | rd
                }
                4 => {
                    // ADDP vector (`u = 0, opcode = 10111`)
                    let sz = if q == 1 { (r >> 22) & 3 } else { (r >> 22) % 3 };
                    (q << 30) | 0x0e20_bc00 | (sz << 22) | (rm << 16) | (rn << 5) | rd
                }
                _ => {
                    let (opc, allow_d) = [
                        (0b00000u32, false), // SHADD / UHADD
                        (0b00001, true),     // SQADD / UQADD
                        (0b00010, false),    // SRHADD / URHADD
                        (0b00100, false),    // SHSUB / UHSUB
                        (0b00101, true),     // SQSUB / UQSUB
                        (0b00110, true),     // CMGT / CMHI
                        (0b00111, true),     // CMGE / CMHS
                        (0b01000, true),     // SSHL / USHL
                        (0b01001, true),     // SQSHL / UQSHL (reg)
                        (0b01010, true),     // SRSHL / URSHL
                        (0b01011, true),     // SQRSHL / UQRSHL
                        (0b01100, false),    // SMAX / UMAX
                        (0b01101, false),    // SMIN / UMIN
                        (0b01110, false),    // SABD / UABD
                        (0b01111, false),    // SABA / UABA
                        (0b10000, true),     // ADD / SUB
                        (0b10001, true),     // CMTST / CMEQ
                        (0b10010, false),    // MLA / MLS
                        (0b10100, false),    // SMAXP / UMAXP
                        (0b10101, false),    // SMINP / UMINP
                    ][(kind - 5) % 20];
                    let sz = if allow_d && q == 1 { (r >> 22) & 3 } else { (r >> 22) % 3 };
                    (q << 30) | (u << 29) | 0x0e20_0400 | (sz << 22) | (rm << 16) | (opc << 11) | (rn << 5) | rd
                }
            }
        }
        43 => {
            // SIMD Two-Reg Misc (§2.4 + Tier 1 integer AdvSIMD)
            let q = (r >> 30) & 1;
            let s012 = (r >> 22) % 3;
            let s0123 = if q == 1 { (r >> 22) & 3 } else { s012 };
            let (u, sz, opc) = [
                (0u32, s012, 0b00000u32),          // REV64
                (1, (r >> 22) & 1, 0b00000),       // REV32 (8B/16B/4H/8H)
                (0, 0, 0b00001),                   // REV16 (8B/16B)
                (0, s012, 0b00010),                // SADDLP
                (1, s012, 0b00010),                // UADDLP
                (0, s0123, 0b00011),               // SUQADD
                (1, s0123, 0b00011),               // USQADD
                (0, s012, 0b00100),                // CLS
                (1, s012, 0b00100),                // CLZ
                (0, 0, 0b00101),                   // CNT
                (1, 0, 0b00101),                   // NOT / MVN
                (1, 1, 0b00101),                   // RBIT (8B/16B)
                (0, s012, 0b00110),                // SADALP
                (1, s012, 0b00110),                // UADALP
                (0, s0123, 0b00111),               // SQABS
                (1, s0123, 0b00111),               // SQNEG
                (0, s0123, 0b01000),               // CMGT #0
                (1, s0123, 0b01000),               // CMGE #0
                (0, s0123, 0b01001),               // CMEQ #0
                (1, s0123, 0b01001),               // CMLE #0
                (0, s0123, 0b01010),               // CMLT #0
                (0, s0123, 0b01011),               // ABS
                (1, s0123, 0b01011),               // NEG
                (0, s012, 0b10010),                // XTN / XTN2
                (1, s012, 0b10010),                // SQXTUN / SQXTUN2
                (1, s012, 0b10011),                // SHLL / SHLL2
                (0, s012, 0b10100),                // SQXTN / SQXTN2
                (1, s012, 0b10100),                // UQXTN / UQXTN2
            ][(r as usize >> 2) % 28];
            (q << 30) | (u << 29) | 0x0e20_0800 | (sz << 22) | (opc << 12) | (rn << 5) | rd
        }
        44 => {
            // SIMD Across Lanes
            let q = 1u32;
            let sz = (r >> 22) % 3;
            let (u, opc) = [(1u32, 0b01010u32), (0, 0b01010), (1, 0b11010), (0, 0b11010), (0, 0b11011), (1, 0b00011), (0, 0b00011)][(r as usize) % 7];
            (q << 30) | (u << 29) | 0x0e30_0800 | (sz << 22) | (opc << 12) | (rn << 5) | rd
        }
        45 => {
            if (r & 1) == 0 {
                let q = 1u32;
                let sz = (r >> 22) & 3;
                let opc = [1u32, 2, 3, 5, 6, 7][(r as usize) % 6];
                (q << 30) | 0x0e00_0800 | (sz << 22) | (rm << 16) | (opc << 12) | (rn << 5) | rd // UZP/ZIP/TRN
            } else {
                let q = (r >> 30) & 1;
                let imm4 = (r >> 11) & (if q == 1 { 0xf } else { 0x7 });
                (q << 30) | 0x2e00_0000 | (rm << 16) | (imm4 << 11) | (rn << 5) | rd // EXT
            }
        }
        46 => {
            // Scalar FP 1-src, 2-src, FCMP, FMOV #imm, FCCMP, FCSEL
            let ftype = (r >> 22) & 1;
            let sub = r % 6;
            match sub {
                0 => {
                    let opc = [0u32, 1, 2, 3, 8, 9, 10, 11, 12, 14, 15][(r as usize) % 11];
                    0x1e20_4000 | (ftype << 22) | (opc << 15) | (rn << 5) | rd
                }
                1 => {
                    let opc = (r >> 12) % 9;
                    0x1e20_0800 | (ftype << 22) | (rm << 16) | (opc << 12) | (rn << 5) | rd
                }
                2 => {
                    let opc2 = [0u32, 8, 16, 24][(r as usize) % 4];
                    0x1e20_2000 | (ftype << 22) | (rm << 16) | (rn << 5) | opc2 // FCMP/FCMPE
                }
                3 => {
                    let imm8 = (r >> 13) & 0xff;
                    0x1e20_1000 | (ftype << 22) | (imm8 << 13) | rd // FMOV #imm8
                }
                4 => {
                    let cond = (r >> 12) & 0xf;
                    let op = (r >> 4) & 1;
                    let nzcv = r & 0xf;
                    0x1e20_0400 | (ftype << 22) | (rm << 16) | (cond << 12) | (rn << 5) | (op << 4) | nzcv // FCCMP
                }
                _ => {
                    let cond = (r >> 12) & 0xf;
                    0x1e20_0c00 | (ftype << 22) | (rm << 16) | (cond << 12) | (rn << 5) | rd // FCSEL
                }
            }
        }
        47 => {
            // Scalar FP 3-src: FMADD, FMSUB, FNMADD, FNMSUB
            let ftype = (r >> 22) & 1;
            let o1 = (r >> 21) & 1;
            let o0 = (r >> 15) & 1;
            0x1f00_0000 | (ftype << 22) | (o1 << 21) | (rm << 16) | (o0 << 15) | (ra << 10) | (rn << 5) | rd
        }
        _ => {
            // Scalar FP fixed-point conversion: SCVTF, UCVTF, FCVTZS, FCVTZU
            let ftype = (r >> 22) & 1;
            let fbits = if sf == 1 { ((r >> 10) % 64) + 1 } else { ((r >> 10) % 32) + 1 };
            let scale = 64 - fbits;
            let (rmode, opc) = [(3u32, 0u32), (3, 1), (0, 2), (0, 3)][(r as usize) % 4];
            (sf << 31) | 0x1e00_0000 | (ftype << 22) | (rmode << 19) | (opc << 16) | (scale << 10) | (rn << 5) | rd
        }
    };

    build_record_with_edges(insn, mem_base_reg, mem_align_mask, rng)
}

/// Build a 128-byte batch record for `insn` with edge-weighted GPRs, VRegs, and aligned base pointer.
pub fn build_record_with_edges(
    insn: u32,
    mem_base_reg: Option<u32>,
    mem_align_mask: u64,
    rng: &mut SplitMix64,
) -> [u64; 16] {
    let init_nzcv = (rng.next_u32() & 0xf) as u64;
    let init_fpsr = (rng.next_u32() as u64) & isa_oracle::FPSR_MASK;
    let seed = rng.next_u64();
    let sp = 0x20020u64;
    let pc = 0x10000u64;

    let rn = (insn >> 5) & 0x1f;
    let rm = (insn >> 16) & 0x1f;
    let ra = (insn >> 10) & 0x1f;
    let rd = insn & 0x1f;

    let r0_idx = rn;
    let r1_idx = rm;
    let r2_idx = ra;
    let r3_idx = mem_base_reg.map(|b| b & 0x1f).unwrap_or(0xff);
    let v0_idx = rn;
    let v1_idx = rm;
    let uses_va = (insn & 0xff00_0000) == 0x1f00_0000 || (insn & 0xffc0_8000) == 0xce00_0000;
    let v2_cand = if uses_va { ra } else { rd };
    let v2_idx = if v2_cand != rn && v2_cand != rm {
        v2_cand
    } else {
        (rd + 1) & 0x1f
    };

    let w4: u64 = (r0_idx as u64)
        | ((r1_idx as u64) << 8)
        | ((r2_idx as u64) << 16)
        | ((r3_idx as u64) << 24)
        | ((v0_idx as u64) << 32)
        | ((v1_idx as u64) << 40)
        | ((v2_idx as u64) << 48)
        | (0xffu64 << 56);

    let r0_val = sample_int64_edge(rng);
    let r1_val = sample_int64_edge(rng);
    let r2_val = sample_int64_edge(rng);
    let r3_val = 0x20020u64 & mem_align_mask;

    let sample_v128 = |rng: &mut SplitMix64| -> (u64, u64) {
        match rng.next_u32() & 3 {
            0 => {
                let lo = (sample_fp32_edge(rng) as u64) | ((sample_fp32_edge(rng) as u64) << 32);
                let hi = (sample_fp32_edge(rng) as u64) | ((sample_fp32_edge(rng) as u64) << 32);
                (lo, hi)
            }
            1 => (sample_fp64_edge(rng), sample_fp64_edge(rng)),
            _ => (sample_int64_edge(rng), sample_int64_edge(rng)),
        }
    };
    let (v0_lo, v0_hi) = sample_v128(rng);
    let (v1_lo, v1_hi) = sample_v128(rng);
    let (v2_lo, v2_hi) = sample_v128(rng);
    let mem_w4 = sample_int64_edge(rng);

    [
        (insn as u64) | (init_nzcv << 32) | (init_fpsr << 36),
        seed,
        sp,
        pc,
        w4,
        r0_val,
        r1_val,
        r2_val,
        r3_val,
        v0_lo,
        v0_hi,
        v1_lo,
        v1_hi,
        v2_lo,
        v2_hi,
        mem_w4,
    ]
}

/// Expand a single 16-word single-instruction record into a canonical [`TestInput`].
///
/// This is the single place in the repository that expands the `SplitMix64` seed and register/memory
/// edge overrides of a 16-word record into a full initial [`CpuState`] and 64-byte `[0x20000, 0x20040)`
/// scratch region.
///
/// `mapped` covers the code word (`[pc, pc + 4)`) and the 64-byte scratch region
/// (`[0x20000, 0x20040)`), which `UnicornOracle` page-aligns to `[0x10000, 0x11000)` and
/// `[0x20000, 0x21000)` (`8 KiB` total) and zeroes before each record so no dirty memory leaks
/// across records. Instructions whose random immediate offset (`LDR/STR` unsigned 12-bit scaled
/// immediate or `LDR` 19-bit PC-relative literal) lands outside those two 4 KiB pages fault with
/// `FaultKind::Unmapped` in Unicorn while executing against total zero-initialized memory in Lean
/// and Sail (`UnicornQuirkAdjudicatedBySail` when `Lean == Sail`).
pub fn expand_record_to_test_input(rec: &[u64]) -> TestInput {
    debug_assert_eq!(rec.len(), 16);
    let w0 = rec[0];
    let mut rng = SplitMix64::new(rec[1]);
    let sp = rec[2];
    let pc = rec[3];
    let w4 = rec[4];
    let w15 = rec[15];

    let mut gprs = [0u64; 31];
    for r in &mut gprs {
        *r = rng.next_u64();
    }
    let mut vregs = [0u128; 32];
    for v in &mut vregs {
        let lo = rng.next_u64() as u128;
        let hi = rng.next_u64() as u128;
        *v = (hi << 64) | lo;
    }
    let mut mem_bytes = vec![0u8; 64];
    for i in 0..8 {
        let m = rng.next_u64();
        let mw = if i == 4 { w15 } else { m };
        mem_bytes[i * 8..(i + 1) * 8].copy_from_slice(&mw.to_le_bytes());
    }
    for k in 0..4 {
        let r_idx = ((w4 >> (k * 8)) & 0xff) as usize;
        if r_idx < 31 {
            gprs[r_idx] = rec[5 + k];
        }
    }
    for k in 0..3 {
        let v_idx = ((w4 >> ((k + 4) * 8)) & 0xff) as usize;
        if v_idx < 32 {
            let lo = rec[9 + k * 2] as u128;
            let hi = rec[10 + k * 2] as u128;
            vregs[v_idx] = (hi << 64) | lo;
        }
    }

    let insn = (w0 & 0xffff_ffff) as u32;
    let nzcv = ((w0 >> 32) & 0xf) as u8;
    let fpcr = 0;
    let fpsr = (w0 >> 36) & isa_oracle::FPSR_MASK;

    TestInput {
        state: CpuState {
            gprs,
            vregs,
            sp,
            pc,
            nzcv,
            fpcr,
            fpsr,
            tpidr_el0: 0,
        },
        code: vec![(pc, vec![insn])],
        mem: vec![(0x0002_0000, mem_bytes)],
        mapped: vec![pc..pc.wrapping_add(4), 0x0002_0000..0x0002_0040],
        watch: vec![0x0002_0000..0x0002_0040],
        exit_pc: NO_EXIT_PC,
        max_steps: 1,
    }
}

/// Expand a packed slice of `16 * count` `u64` words into `count` [`TestInput`] records.
pub fn expand_records_to_test_inputs(records: &[u64]) -> Vec<TestInput> {
    assert_eq!(records.len() % 16, 0);
    records
        .chunks_exact(16)
        .map(expand_record_to_test_input)
        .collect()
}
