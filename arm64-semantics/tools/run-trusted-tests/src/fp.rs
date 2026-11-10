// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Standalone IEEE-754 floating-point differential testing harness (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (auditable IEEE-754 floating-point oracle harness comparing
//!   `Arm64/Trusted/ISA/Float.lean` via `Arm64/Testing/Harness/FpEval.lean` against Berkeley
//!   SoftFloat 3e `ARM-VFPv2`, Berkeley TestFloat 3e, and IBM FPgen).
//! - **Purpose:** Separates pure IEEE-754 floating-point evaluation from the general A64
//!   instruction-stepping harness (`unicorn.rs`, `sail.rs`, `fuzz.rs`) so that `Float.lean` can be
//!   audited and tested independently via `run-trusted-tests --fp-only [--print-vectors N]`:
//!   1. **Berkeley SoftFloat 3e (`csrc/softfloat_ffi.c`)**: `run_softfloat_batch` evaluates 32-byte
//!      `FpBatchRecord` tuples `(meta, a, b, c)` in SoftFloat 3e compiled with `SPECIALIZE_TYPE=ARM-VFPv2`.
//!   2. **Lean `FpEval.lean` (`diff_eval --batch-fp`)**: `eval_lean_fp_batch` evaluates the exact
//!      same 32-byte records in `Arm64.Testing.Harness.evalFpBatchRecord`.
//!   3. **IBM FPgen (`*.fptest`, 144,635 vectors)**, **Berkeley TestFloat 3e (`testfloat_gen -level 1`,
//!      324,300 vectors)**, and **Stratified FP edge vectors (`run_stratified_fp_batch`, 10,500 vectors)**.
//!
//! # Key Types & Functions
//! - [`run_softfloat_batch`]: FFI bridge to `softfloat_eval_batch` in `csrc/softfloat_ffi.c`.
//! - [`eval_lean_fp_batch`]: Binary batch bridge to `diff_eval --batch-fp` (`FpEval.lean`).
//! - [`run_fp_validation`]: Standalone entry point for `--fp-only` (479,435 IEEE-754 vectors).
//! - [`print_curated_fp_vectors`]: Side-by-side display of concrete FP vectors across Lean
//!   `Float.lean` and Berkeley SoftFloat 3e (`ARM-VFPv2`).

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::time::Instant;

use anyhow::{Context, Result, anyhow, bail};

use crate::compare::{
    compare_fpgen_result, compare_softfloat_batch, is_fpgen_trapped_underflow_or_overflow,
};
use crate::fuzz::{FuzzConfig, FuzzReport};
use crate::fuzz_gen::{SplitMix64, sample_fp32_edge, sample_fp64_edge, sample_int64_edge};

static SOFTFLOAT_LOCK: Mutex<()> = Mutex::new(());

unsafe extern "C" {
    fn softfloat_eval_batch(in_words: *const u64, count: usize, out_words: *mut u64);
}

pub(crate) fn upstream_cache_dir() -> PathBuf {
    if let Some(dir) = env::var_os("ARM64_UPSTREAM_CACHE") {
        return PathBuf::from(dir);
    }
    if let Some(xdg) = env::var_os("XDG_CACHE_HOME") {
        return PathBuf::from(xdg).join("arm64-verification-engine");
    }
    let home = env::var_os("HOME").expect("HOME must be set");
    PathBuf::from(home)
        .join(".cache")
        .join("arm64-verification-engine")
}

/// Execute a batch of `count` 4-word (32-byte) FP records in Berkeley SoftFloat 3e (`ARM-VFPv2`),
/// returning `2 * count` words (`[val_0, flags_0, val_1, flags_1, ...]`).
pub fn run_softfloat_batch(in_words: &[u64]) -> Result<Vec<u64>> {
    assert_eq!(in_words.len() % 4, 0);
    let count = in_words.len() / 4;
    let mut out_words = vec![0u64; count * 2];
    let _guard = SOFTFLOAT_LOCK
        .lock()
        .map_err(|_| anyhow!("SOFTFLOAT_LOCK mutex poisoned"))?;
    unsafe {
        softfloat_eval_batch(in_words.as_ptr(), count, out_words.as_mut_ptr());
    }
    Ok(out_words)
}

/// Evaluate a batch of 4-word (32-byte) `FpBatchRecord`s in Lean (`diff_eval --batch-fp`).
pub fn eval_lean_fp_batch(diff_eval_bin: &Path, records: &[u64]) -> Result<Vec<u64>> {
    assert_eq!(records.len() % 4, 0);
    let tmp_dir = env::temp_dir();
    let pid = std::process::id();
    let in_path = tmp_dir.join(format!("arm64_fp_in_{pid}.bin"));
    let out_path = tmp_dir.join(format!("arm64_fp_out_{pid}.bin"));

    let mut in_bytes = Vec::with_capacity(records.len() * 8);
    for &w in records {
        in_bytes.extend_from_slice(&w.to_le_bytes());
    }
    fs::write(&in_path, &in_bytes)?;

    let status = Command::new(diff_eval_bin)
        .arg("--batch-fp")
        .arg(&in_path)
        .arg(&out_path)
        .status()
        .with_context(|| format!("failed to invoke `{}` --batch-fp", diff_eval_bin.display()))?;
    let _ = fs::remove_file(&in_path);
    if !status.success() {
        let _ = fs::remove_file(&out_path);
        bail!("diff_eval --batch-fp exited with {status}");
    }
    let out_bytes = fs::read(&out_path)?;
    let _ = fs::remove_file(&out_path);
    let mut out = Vec::with_capacity(out_bytes.len() / 8);
    for chunk in out_bytes.chunks_exact(8) {
        let mut b = [0u8; 8];
        b.copy_from_slice(chunk);
        out.push(u64::from_le_bytes(b));
    }
    Ok(out)
}

/// Parse one IBM FPgen `b32` token (`+Zero`, `-Zero`, `+Inf`, `-Inf`, `Q`, `S`, `[+-][01].XXXXXXP<exp>`).
///
/// Note on IBM FPgen's hex significand convention: unlike C99 `%a` hex floats, IBM FPgen writes
/// the raw 23-bit IEEE-754 `binary32` trailing significand field right-aligned in 6 hex digits
/// (`000000`..`7FFFFF`), so bit 22 (`0x40_0000`) is $2^{-1}$ and bit 0 (`0x00_0001`) is $2^{-23}$.
pub fn parse_fpgen_b32(tok: &str) -> Option<u32> {
    match tok {
        "+Zero" => return Some(0x0000_0000),
        "-Zero" => return Some(0x8000_0000),
        "+Inf" => return Some(0x7f80_0000),
        "-Inf" => return Some(0xff80_0000),
        "Q" => return Some(0x7fc0_0000),
        "S" => return Some(0x7fa0_0000),
        _ => {}
    }
    let (sign, rest) = if let Some(r) = tok.strip_prefix('+') {
        (0u32, r)
    } else if let Some(r) = tok.strip_prefix('-') {
        (1u32, r)
    } else {
        return None;
    };
    let (mant_str, exp_str) = rest.split_once('P')?;
    let exp: i32 = exp_str.parse().ok()?;
    let (lead_str, frac_str) = mant_str.split_once('.')?;
    if frac_str.len() != 6 {
        return None;
    }
    let frac = u32::from_str_radix(frac_str, 16).ok()?;
    if frac > 0x7f_ffff {
        return None;
    }
    let biased_exp: u32 = if lead_str == "0" {
        if exp != -126 {
            return None;
        }
        0
    } else if lead_str == "1" {
        let biased = exp + 127;
        if !(1..=254).contains(&biased) {
            return None;
        }
        biased as u32
    } else {
        return None;
    };
    Some((sign << 31) | (biased_exp << 23) | frac)
}

/// Parse and evaluate all IBM FPgen `*.fptest` files in `fpgen_dir`.
pub fn run_fpgen_corpus(
    fpgen_dir: &Path,
    diff_eval_bin: &Path,
    report: &mut FuzzReport,
) -> Result<()> {
    let Ok(entries) = fs::read_dir(fpgen_dir) else {
        return Ok(());
    };
    let mut records = Vec::new();
    let mut expected = Vec::new();

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("fptest") {
            continue;
        }
        let Ok(content) = fs::read_to_string(&path) else {
            continue;
        };
        for line in content.lines() {
            let line = line.trim();
            if !line.starts_with("b32") {
                continue;
            }
            let Some((lhs, rhs)) = line.split_once("->") else {
                continue;
            };
            let lhs_toks: Vec<&str> = lhs.split_whitespace().collect();
            let rhs_toks: Vec<&str> = rhs.split_whitespace().collect();
            if lhs_toks.len() < 3 || rhs_toks.is_empty() {
                continue;
            }
            let op_code: u64 = match lhs_toks[0] {
                "b32+" => 0,
                "b32-" => 1,
                "b32*" => 2,
                "b32/" => 3,
                "b32V" => 4,
                "b32*+" => 5,
                _ => continue,
            };
            let rm_code: u64 = match lhs_toks[1] {
                "=0" => 0,
                ">" => 1,
                "<" => 2,
                "0" => 3,
                "=^" => 4,
                _ => continue,
            };
            let lhs_traps = if !lhs_toks[2].starts_with(['+', '-', 'Q', 'S']) {
                lhs_toks[2]
            } else {
                ""
            };
            let rhs_excs = rhs_toks.get(1).copied().unwrap_or("");
            if is_fpgen_trapped_underflow_or_overflow(lhs_traps, rhs_excs) {
                report.outcome_counts.fpgen_trapped_exception_skipped += 1;
                continue;
            }
            let Some(out_b32) = parse_fpgen_b32(rhs_toks[0]) else {
                continue;
            };
            let mut args = Vec::new();
            for &t in &lhs_toks[2..] {
                if let Some(v) = parse_fpgen_b32(t) {
                    args.push(v);
                }
            }
            let (a, b, c) = match (op_code, args.as_slice()) {
                (4, &[a]) => (a as u64, 0, 0),
                (0..=3, &[a, b]) => (a as u64, b as u64, 0),
                (5, &[a, b, c]) => (a as u64, b as u64, c as u64),
                _ => continue,
            };
            let meta = op_code | (rm_code << 8);
            records.extend_from_slice(&[meta, a, b, c]);
            expected.push((line.to_string(), out_b32 as u64));
        }
    }

    if records.is_empty() {
        return Ok(());
    }
    let lean_out = eval_lean_fp_batch(diff_eval_bin, &records)?;
    let sf_out = run_softfloat_batch(&records)?;
    report.fpgen_cases += expected.len() as u64;
    report.total_cases += expected.len() as u64;
    *report
        .fp_op_cases
        .entry("ibm_fpgen_b32".to_string())
        .or_insert(0) += expected.len() as u64;

    for (i, (line_str, exp_val)) in expected.iter().enumerate() {
        let l_val = lean_out[i * 2];
        let l_flags = lean_out[i * 2 + 1];
        let s_val = sf_out[i * 2];
        let s_flags = sf_out[i * 2 + 1];
        let rm_code = (records[i * 4] >> 8) & 0xff;
        if let Err(msg) = compare_fpgen_result(
            line_str,
            l_val,
            s_val,
            *exp_val,
            &mut report.outcome_counts,
        ) {
            report.lean_vs_sail_mismatches.push(msg);
        } else if rm_code == 0 && l_flags != s_flags {
            report.lean_vs_sail_mismatches.push(format!(
                "FPgen FPSR flag mismatch on `{line_str}`: Lean flags=0x{l_flags:02x} vs SoftFloat flags=0x{s_flags:02x}"
            ));
        }
    }
    Ok(())
}

struct TestFloatSpec {
    tf_name: &'static str,
    op_code: u64,
    arity: usize,
    all_rm: bool,
}

const TESTFLOAT_SPECS: &[TestFloatSpec] = &[
    TestFloatSpec { tf_name: "f32_add", op_code: 0, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f32_sub", op_code: 1, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f32_mul", op_code: 2, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f32_div", op_code: 3, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f32_sqrt", op_code: 4, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f32_mulAdd", op_code: 5, arity: 3, all_rm: true },
    TestFloatSpec { tf_name: "f32_roundToInt", op_code: 6, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f32_to_f64", op_code: 7, arity: 1, all_rm: false },
    TestFloatSpec { tf_name: "f32_to_i32", op_code: 8, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f32_to_ui32", op_code: 9, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f32_to_i64", op_code: 10, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f32_to_ui64", op_code: 11, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "i32_to_f32", op_code: 12, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "ui32_to_f32", op_code: 13, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "i64_to_f32", op_code: 14, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "ui64_to_f32", op_code: 15, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f64_add", op_code: 32, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f64_sub", op_code: 33, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f64_mul", op_code: 34, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f64_div", op_code: 35, arity: 2, all_rm: true },
    TestFloatSpec { tf_name: "f64_sqrt", op_code: 36, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f64_mulAdd", op_code: 37, arity: 3, all_rm: true },
    TestFloatSpec { tf_name: "f64_roundToInt", op_code: 38, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f64_to_f32", op_code: 39, arity: 1, all_rm: false },
    TestFloatSpec { tf_name: "f64_to_i32", op_code: 40, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f64_to_ui32", op_code: 41, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f64_to_i64", op_code: 42, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "f64_to_ui64", op_code: 43, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "i32_to_f64", op_code: 44, arity: 1, all_rm: false },
    TestFloatSpec { tf_name: "ui32_to_f64", op_code: 45, arity: 1, all_rm: false },
    TestFloatSpec { tf_name: "i64_to_f64", op_code: 46, arity: 1, all_rm: true },
    TestFloatSpec { tf_name: "ui64_to_f64", op_code: 47, arity: 1, all_rm: true },
];

const RM_FLAGS: &[(u64, &str)] = &[
    (0, "-rnear_even"),
    (1, "-rmax"),
    (2, "-rmin"),
    (3, "-rminMag"),
    (4, "-rnear_maxMag"),
];

/// Run `testfloat_gen -level 1` across `TESTFLOAT_SPECS` and compare `diff_eval --batch-fp` against SoftFloat.
pub fn run_testfloat_pass(
    tf_bin: &Path,
    diff_eval_bin: &Path,
    seed: u64,
    all_rounding_modes: bool,
    report: &mut FuzzReport,
) -> Result<()> {
    if !tf_bin.is_file() {
        return Ok(());
    }
    for spec in TESTFLOAT_SPECS {
        let rms: &[(u64, &str)] = if spec.all_rm && all_rounding_modes {
            RM_FLAGS
        } else {
            &RM_FLAGS[..1]
        };
        for &(rm_code, rm_flag) in rms {
            let mut cmd = Command::new(tf_bin);
            cmd.arg("-level")
                .arg("1")
                .arg("-seed")
                .arg(format!("{}", (seed % 1_000_000) + 1));
            if spec.arity == 3 {
                cmd.arg("-n")
                    .arg(if all_rounding_modes { "100000" } else { "50000" });
            }
            let output = cmd
                .arg(rm_flag)
                .arg(spec.tf_name)
                .output()
                .with_context(|| format!("failed to run testfloat_gen {}", spec.tf_name))?;
            if !output.status.success() {
                continue;
            }
            let text = String::from_utf8_lossy(&output.stdout);
            let mut records = Vec::new();
            for line in text.lines() {
                let toks: Vec<&str> = line.split_whitespace().collect();
                if toks.len() < spec.arity + 2 {
                    continue;
                }
                let a = u64::from_str_radix(toks[0], 16).unwrap_or(0);
                let b = if spec.arity >= 2 {
                    u64::from_str_radix(toks[1], 16).unwrap_or(0)
                } else {
                    0
                };
                let c = if spec.arity >= 3 {
                    u64::from_str_radix(toks[2], 16).unwrap_or(0)
                } else {
                    0
                };
                let meta = spec.op_code | (rm_code << 8);
                records.extend_from_slice(&[meta, a, b, c]);
            }
            if records.is_empty() {
                continue;
            }
            let count = (records.len() / 4) as u64;
            let lean_out = eval_lean_fp_batch(diff_eval_bin, &records)?;
            let sf_out = run_softfloat_batch(&records)?;
            report.testfloat_cases += count;
            report.total_cases += count;
            *report
                .fp_op_cases
                .entry(spec.tf_name.to_string())
                .or_insert(0) += count;

            let label = format!("TestFloat {} (rm={rm_flag})", spec.tf_name);
            compare_softfloat_batch(
                &records,
                &lean_out,
                &sf_out,
                &label,
                &mut report.outcome_counts,
                &mut report.lean_vs_sail_mismatches,
            );
        }
    }
    Ok(())
}

/// Run stratified FP edge-case batches (including `FMIN*`, `FMAX*`, `FCMP`) against SoftFloat.
pub fn run_stratified_fp_batch(
    diff_eval_bin: &Path,
    rng: &mut SplitMix64,
    batch_per_op: usize,
    report: &mut FuzzReport,
) -> Result<()> {
    let ops: &[(u64, &str)] = &[
        (0, "f32_add"),
        (1, "f32_sub"),
        (2, "f32_mul"),
        (3, "f32_div"),
        (4, "f32_sqrt"),
        (5, "f32_mulAdd"),
        (6, "f32_roundToInt"),
        (7, "f32_to_f64"),
        (8, "f32_to_i32"),
        (9, "f32_to_ui32"),
        (10, "f32_to_i64"),
        (11, "f32_to_ui64"),
        (12, "i32_to_f32"),
        (13, "ui32_to_f32"),
        (14, "i64_to_f32"),
        (15, "ui64_to_f32"),
        (16, "f32_min"),
        (17, "f32_max"),
        (18, "f32_minnm"),
        (19, "f32_maxnm"),
        (20, "f32_cmp"),
        (21, "f32_roundToInt_exact"),
        (22, "f32_cmpe"),
        (32, "f64_add"),
        (33, "f64_sub"),
        (34, "f64_mul"),
        (35, "f64_div"),
        (36, "f64_sqrt"),
        (37, "f64_mulAdd"),
        (38, "f64_roundToInt"),
        (39, "f64_to_f32"),
        (40, "f64_to_i32"),
        (41, "f64_to_ui32"),
        (42, "f64_to_i64"),
        (43, "f64_to_ui64"),
        (44, "i32_to_f64"),
        (45, "ui32_to_f64"),
        (46, "i64_to_f64"),
        (47, "ui64_to_f64"),
        (48, "f64_min"),
        (49, "f64_max"),
        (50, "f64_minnm"),
        (51, "f64_maxnm"),
        (52, "f64_cmp"),
        (53, "f64_roundToInt_exact"),
        (54, "f64_cmpe"),
    ];
    let mut records = Vec::with_capacity(ops.len() * batch_per_op * 4);
    for &(op, name) in ops {
        let is_f32 = op < 32;
        let is_int_in = matches!(op, 12..=15 | 44..=47);
        for batch_idx in 0..batch_per_op {
            let rm_code = if batch_idx < batch_per_op / 2
                || matches!(op, 7 | 20..=22 | 39 | 44 | 45 | 52..=54)
            {
                0
            } else {
                (rng.next_u32() % 5) as u64
            };
            let meta = op | (rm_code << 8);
            let (a, b, c) = if is_int_in {
                (sample_int64_edge(rng), 0, 0)
            } else if is_f32 {
                (
                    sample_fp32_edge(rng) as u64,
                    sample_fp32_edge(rng) as u64,
                    sample_fp32_edge(rng) as u64,
                )
            } else {
                (
                    sample_fp64_edge(rng),
                    sample_fp64_edge(rng),
                    sample_fp64_edge(rng),
                )
            };
            records.extend_from_slice(&[meta, a, b, c]);
        }
        *report.fp_op_cases.entry(name.to_string()).or_insert(0) += batch_per_op as u64;
    }
    let count = (records.len() / 4) as u64;
    let lean_out = eval_lean_fp_batch(diff_eval_bin, &records)?;
    let sf_out = run_softfloat_batch(&records)?;
    report.stratified_fp_cases += count;
    report.total_cases += count;

    compare_softfloat_batch(
        &records,
        &lean_out,
        &sf_out,
        "Stratified FP",
        &mut report.outcome_counts,
        &mut report.lean_vs_sail_mismatches,
    );
    Ok(())
}

struct CuratedFpVector {
    desc: &'static str,
    op_name: &'static str,
    rm_name: &'static str,
    op: u64,
    rm: u64,
    a: u64,
    b: u64,
    c: u64,
    is_f32: bool,
}

const CURATED_FP_VECTORS: &[CuratedFpVector] = &[
    CuratedFpVector {
        desc: "Halfway tie-to-even (even LSB=0: 1.0 + 2^-53 -> 1.0)",
        op_name: "FADD.D",
        rm_name: "RNE",
        op: 32,
        rm: 0,
        a: 0x3ff0_0000_0000_0000,
        b: 0x3ca0_0000_0000_0000,
        c: 0,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "Halfway tie-to-even (odd LSB=1: (1.0+2^-52) + 2^-53 -> 1.0+2^-51)",
        op_name: "FADD.D",
        rm_name: "RNE",
        op: 32,
        rm: 0,
        a: 0x3ff0_0000_0000_0001,
        b: 0x3ca0_0000_0000_0000,
        c: 0,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "Exact cancellation sign in RNE (+1.5 + -1.5 -> +0.0)",
        op_name: "FADD.D",
        rm_name: "RNE",
        op: 32,
        rm: 0,
        a: 0x3ff8_0000_0000_0000,
        b: 0xbff8_0000_0000_0000,
        c: 0,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "Exact cancellation sign in RTN (+1.5 + -1.5 -> -0.0)",
        op_name: "FADD.D",
        rm_name: "RTN",
        op: 32,
        rm: 2,
        a: 0x3ff8_0000_0000_0000,
        b: 0xbff8_0000_0000_0000,
        c: 0,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "Subnormal-to-normal carry (max_subnormal + min_subnormal -> min_normal)",
        op_name: "FADD.D",
        rm_name: "RNE",
        op: 32,
        rm: 0,
        a: 0x000f_ffff_ffff_ffff,
        b: 0x0000_0000_0000_0001,
        c: 0,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "FMADD single rounding ((1+2^-52)*(1-2^-53) + (-1.0) -> -2^-105 + 2^-53)",
        op_name: "FMADD.D",
        rm_name: "RNE",
        op: 37,
        rm: 0,
        a: 0x3ff0_0000_0000_0001,
        b: 0x3fef_ffff_ffff_ffff,
        c: 0xbff0_0000_0000_0000,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "FMADD sNaN in Rn overrides qNaN in Ra (FPProcessNaNs3)",
        op_name: "FMADD.D",
        rm_name: "RNE",
        op: 37,
        rm: 0,
        a: 0x7ff0_0000_0000_0033,
        b: 0x3ff0_0000_0000_0000,
        c: 0x7ff8_0000_0000_0011,
        is_f32: false,
    },
    CuratedFpVector {
        desc: "Signed-zero minimum FMIN(+0.0, -0.0) -> -0.0",
        op_name: "FMIN.D",
        rm_name: "RNE",
        op: 48,
        rm: 0,
        a: 0x0000_0000_0000_0000,
        b: 0x8000_0000_0000_0000,
        c: 0,
        is_f32: false,
    },
];

/// Evaluate and print up to `limit` curated IEEE-754 floating-point vectors side by side
/// (`Lean Float.lean` vs `Berkeley SoftFloat 3e ARM-VFPv2`). Returns any mismatches found.
pub fn print_curated_fp_vectors(diff_eval_bin: &Path, limit: usize) -> Result<Vec<String>> {
    let n = limit.min(CURATED_FP_VECTORS.len());
    if n == 0 {
        return Ok(Vec::new());
    }
    let mut records = Vec::with_capacity(n * 4);
    for v in &CURATED_FP_VECTORS[..n] {
        let meta = v.op | (v.rm << 8);
        records.extend_from_slice(&[meta, v.a, v.b, v.c]);
    }
    let lean_out = eval_lean_fp_batch(diff_eval_bin, &records)?;
    let sf_out = run_softfloat_batch(&records)?;
    let mut mismatches = Vec::new();

    println!(
        "\n=== Curated IEEE-754 Floating-Point Vectors (Lean `Float.lean` vs Berkeley SoftFloat 3e `ARM-VFPv2`) ==="
    );
    for (idx, v) in CURATED_FP_VECTORS[..n].iter().enumerate() {
        let l = lean_out[idx * 2];
        let l_flags = lean_out[idx * 2 + 1];
        let s = sf_out[idx * 2];
        let s_flags = sf_out[idx * 2 + 1];
        let matched = l == s && l_flags == s_flags;
        let status = if matched { "MATCH" } else { "MISMATCH" };
        if v.is_f32 {
            println!(
                "  [{idx}] {} ({}, rm={})\n      Inputs : a=0x{:08x}, b=0x{:08x}, c=0x{:08x}\n      Lean   : 0x{:08x} (fpsr=0x{:02x}) | SoftFloat 3e: 0x{:08x} (fpsr=0x{:02x}) -> [{status}]",
                v.desc,
                v.op_name,
                v.rm_name,
                v.a as u32,
                v.b as u32,
                v.c as u32,
                l as u32,
                l_flags,
                s as u32,
                s_flags
            );
        } else {
            println!(
                "  [{idx}] {} ({}, rm={})\n      Inputs : a=0x{:016x}, b=0x{:016x}, c=0x{:016x}\n      Lean   : 0x{:016x} (fpsr=0x{:02x}) | SoftFloat 3e: 0x{:016x} (fpsr=0x{:02x}) -> [{status}]",
                v.desc, v.op_name, v.rm_name, v.a, v.b, v.c, l, l_flags, s, s_flags
            );
        }
        if !matched {
            mismatches.push(format!(
                "CuratedFP[{}] ({}): Lean=0x{l:016x} (fpsr=0x{l_flags:02x}) vs SoftFloat=0x{s:016x} (fpsr=0x{s_flags:02x})",
                idx, v.desc
            ));
        }
    }
    Ok(mismatches)
}

/// Run the standalone IEEE-754 floating-point differential validation campaign (`--fp-only`):
/// 1. Curated FP vectors (when `print_vectors > 0`)
/// 2. IBM FPgen (`*.fptest`, 144,635 vectors)
/// 3. Berkeley TestFloat 3e (`testfloat_gen -level 1`, 324,300 vectors)
/// 4. Stratified FP edge-value batches (`run_stratified_fp_batch`, 10,500 vectors)
pub fn run_fp_validation(cfg: &FuzzConfig, print_vectors: usize) -> Result<FuzzReport> {
    let start = Instant::now();
    let cache = upstream_cache_dir();
    let fp_dir = cache.join("fp-tools");
    let fpgen_dir = fp_dir.join("fpgen");
    let tf_bin = fp_dir
        .join("testfloat3")
        .join("build")
        .join("Linux-x86_64-GCC")
        .join("testfloat_gen");

    let mut report = FuzzReport {
        seed: format!("0x{:016x}", cfg.seed),
        ..Default::default()
    };
    let mut rng = SplitMix64::new(cfg.seed);

    if print_vectors > 0 {
        let curated_errs = print_curated_fp_vectors(&cfg.diff_eval_bin, print_vectors)?;
        report.lean_vs_sail_mismatches.extend(curated_errs);
    }

    let long_run = cfg.duration_secs >= 60;
    run_fpgen_corpus(&fpgen_dir, &cfg.diff_eval_bin, &mut report)?;
    run_testfloat_pass(&tf_bin, &cfg.diff_eval_bin, cfg.seed, long_run, &mut report)?;
    run_stratified_fp_batch(
        &cfg.diff_eval_bin,
        &mut rng,
        if long_run { 2000 } else { 250 },
        &mut report,
    )?;

    report.elapsed_secs = start.elapsed().as_secs_f64();
    if let Some(ref rpath) = cfg.report_path {
        fs::write(rpath, serde_json::to_string_pretty(&report)?)?;
    }
    println!(
        "FP Differential Summary (seed={}, {:.1}s): total_fp_cases={} (ibm_fpgen={}, berkeley_testfloat={}, stratified_fp={}), mismatches={}",
        report.seed,
        report.elapsed_secs,
        report.total_cases,
        report.fpgen_cases,
        report.testfloat_cases,
        report.stratified_fp_cases,
        report.lean_vs_sail_mismatches.len()
    );
    println!(
        "  FP outcome classification: executed_compared={}, fpgen_trapped_skipped={}, fpgen_nan_canonicalized={}",
        report.outcome_counts.executed_compared,
        report.outcome_counts.fpgen_trapped_exception_skipped,
        report.outcome_counts.fpgen_nan_canonicalized,
    );
    for m in report.lean_vs_sail_mismatches.iter().take(20) {
        eprintln!("  MISMATCH: {m}");
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_fpgen_b32_special_and_vectors() {
        assert_eq!(parse_fpgen_b32("+Zero"), Some(0x0000_0000));
        assert_eq!(parse_fpgen_b32("-Zero"), Some(0x8000_0000));
        assert_eq!(parse_fpgen_b32("+Inf"), Some(0x7f80_0000));
        assert_eq!(parse_fpgen_b32("-Inf"), Some(0xff80_0000));
        assert_eq!(parse_fpgen_b32("Q"), Some(0x7fc0_0000));
        assert_eq!(parse_fpgen_b32("S"), Some(0x7fa0_0000));

        // +1.0 = +1.000000P0 -> 0x3f80_0000
        assert_eq!(parse_fpgen_b32("+1.000000P0"), Some(0x3f80_0000));
        // +1.5 in IBM FPgen format (23-bit mantissa right-aligned in 6 hex digits: 0x40_0000)
        assert_eq!(parse_fpgen_b32("+1.400000P0"), Some(0x3fc0_0000));
        assert_eq!(f32::from_bits(0x3fc0_0000), 1.5f32);

        // Vector from IBM FPgen `Add-Cancellation.fptest`:
        // `b32+ =0 x -1.7FFFFDP-6 +1.000000P-5 -> +1.400000P-28`
        let a = parse_fpgen_b32("-1.7FFFFDP-6").unwrap();
        let b = parse_fpgen_b32("+1.000000P-5").unwrap();
        let exp = parse_fpgen_b32("+1.400000P-28").unwrap();
        assert_eq!((f32::from_bits(a) + f32::from_bits(b)).to_bits(), exp);

        // Subnormal vector from IBM FPgen `Add-Cancellation-And-Subnorm-Result.fptest`:
        // `b32+ =0 x +1.7FFFFFP-123 -1.000000P-122 -> -0.000008P-126`
        let s_a = parse_fpgen_b32("+1.7FFFFFP-123").unwrap();
        let s_b = parse_fpgen_b32("-1.000000P-122").unwrap();
        let s_exp = parse_fpgen_b32("-0.000008P-126").unwrap();
        assert_eq!((f32::from_bits(s_a) + f32::from_bits(s_b)).to_bits(), s_exp);

        // Validation of malformed or out-of-range tokens
        assert_eq!(parse_fpgen_b32("+1.800000P0"), None);
        assert_eq!(parse_fpgen_b32("+1.4000P0"), None);
        assert_eq!(parse_fpgen_b32("+1.0000000000000P0"), None);
        assert_eq!(parse_fpgen_b32("+1.000000P128"), None);
        assert_eq!(parse_fpgen_b32("+1.000000P-127"), None);
        assert_eq!(parse_fpgen_b32("+0.000001P-125"), None);
    }
}
