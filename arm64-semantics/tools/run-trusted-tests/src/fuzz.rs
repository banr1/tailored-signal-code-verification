// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! High-throughput differential fuzzing orchestrator (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted differential fuzzer comparing Lean 4 `Arm64` ISA and
//!   FP semantics against Berkeley SoftFloat 3e `ARM-VFPv2`, Berkeley TestFloat 3e, IBM FPgen,
//!   Linaro RISU, Sail Armv9.4-A, and Unicorn/QEMU).
//! - **Purpose:** Runs:
//!   1. **IBM FPgen IEEE-754 corpus (`*.fptest`)** against `diff_eval --batch-fp` and SoftFloat.
//!   2. **Berkeley TestFloat 3 (`testfloat_gen -level 1`) + stratified FP/fixed-point** across all
//!      operations and all 5 rounding modes (`RNE`, `RTP`, `RTN`, `RTZ`, `RNA`) against
//!      `diff_eval --batch-fp`, SoftFloat `ARM-VFPv2`, and Sail Armv9.4-A.
//!   3. **Linaro RISU (`aarch64.risu`) + 49-family `Arm64.decode` instruction fuzzing** against
//!      `LeanOracle` (`diff_eval --serve`), `SailOracle` (authoritative), and `UnicornOracle`
//!      via `Arm64Oracle::run_batch` and `isa_oracle::diff`.
//!
//! # Key Types & Functions
//! - [`FuzzConfig`], [`FuzzReport`]: Configuration and per-family/per-suite result summary.
//! - [`run_fuzz_campaign`]: Executes either the fast CI seeded batch or a timed local campaign.
//! - [`run_insn_fuzz_only`]: Executes only the 49-family + RISU single-instruction fuzzing pass
//!   (without the standalone IEEE-754 FP corpora in `src/fp.rs`).
//!
//! # When to Read This File
//! - Read this file when modifying the single-instruction differential fuzzing pipeline, oracle
//!   adjudication, or fuzz report output.
//! - For standalone IEEE-754 floating-point differential testing (`--fp-only`), read `src/fp.rs`.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{Result, anyhow, bail};
use isa_oracle::{Arm64Oracle, Outcome, Policy};
use sail_aarch64::SailOracle;
use serde::Serialize;
use unicorn_aarch64::UnicornOracle;

use crate::compare::{
    OutcomeCounts, compare_oracle_batch_outcomes, prepare_and_classify_test_inputs,
};
use crate::fp::{
    run_fpgen_corpus, run_stratified_fp_batch, run_testfloat_pass, upstream_cache_dir,
};
use crate::fuzz_gen::{
    FAMILY_NAMES, SplitMix64, build_record_with_edges, expand_records_to_test_inputs,
    gen_family_insn_record, load_risu_patterns,
};
use crate::lean_oracle::LeanOracle;

#[derive(Clone, Debug)]
pub struct FuzzConfig {
    pub repo_root: PathBuf,
    pub diff_eval_bin: PathBuf,
    pub seed: u64,
    pub duration_secs: u64,
    pub cases_per_family: usize,
    pub report_path: Option<PathBuf>,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct FuzzReport {
    pub seed: String,
    pub elapsed_secs: f64,
    pub total_cases: u64,
    pub fpgen_cases: u64,
    pub testfloat_cases: u64,
    pub stratified_fp_cases: u64,
    pub risu_cases: u64,
    pub family_cases: BTreeMap<String, u64>,
    pub fp_op_cases: BTreeMap<String, u64>,
    pub outcome_counts: OutcomeCounts,
    pub unicorn_fp_quirks_adjudicated_by_sail: u64,
    pub lean_vs_sail_mismatches: Vec<String>,
}

/// Expand a batch of 16-word instruction records into [`isa_oracle::TestInput`]s once and evaluate
/// them across `LeanOracle`, `SailOracle`, and `UnicornOracle` via [`Arm64Oracle::run_batch`].
fn check_insn_records(
    lean_oracle: &mut LeanOracle,
    sail_oracle: &mut SailOracle,
    unicorn_oracle: &mut UnicornOracle,
    policy: &Policy,
    records: &[u64],
    tag: &str,
    check_unicorn: bool,
    report: &mut FuzzReport,
) -> Result<()> {
    if records.is_empty() {
        return Ok(());
    }
    let inputs = expand_records_to_test_inputs(records);
    let lean_out = lean_oracle.run_batch(&inputs);
    let before_compared = report.outcome_counts.executed_compared;
    let active_inputs =
        prepare_and_classify_test_inputs(&inputs, &lean_out, policy, &mut report.outcome_counts)
            .map_err(|e| anyhow!("[{tag}] {e}"))?;
    let batch_compared = report
        .outcome_counts
        .executed_compared
        .saturating_sub(before_compared);
    let min_pct: u64 = match tag {
        "simd_crypto_campaign" => 99,
        "insn_family_batch" | "insn_family_unicorn_sample" => 95,
        _ => 0,
    };
    if min_pct > 0 && batch_compared * 100 < (inputs.len() as u64) * min_pct {
        bail!(
            "[{tag}] executed_compared ({batch_compared}/{}) fell below required {min_pct}% floor",
            inputs.len()
        );
    }
    let sail_out = sail_oracle.run_batch(&active_inputs);
    for (idx, s_out) in sail_out.iter().enumerate() {
        if let Outcome::OracleError(msg) = s_out {
            bail!("[{tag}] SailOracle error at record {idx}: {msg}");
        }
    }
    let uc_out = if check_unicorn {
        let uo = unicorn_oracle.run_batch(&active_inputs);
        for (idx, u_out) in uo.iter().enumerate() {
            if let Outcome::OracleError(msg) = u_out {
                bail!("[{tag}] UnicornOracle error at record {idx}: {msg}");
            }
        }
        Some(uo)
    } else {
        None
    };

    compare_oracle_batch_outcomes(
        &inputs,
        &lean_out,
        &sail_out,
        uc_out.as_deref(),
        policy,
        tag,
        &mut report.outcome_counts,
        &mut report.lean_vs_sail_mismatches,
    );
    report.unicorn_fp_quirks_adjudicated_by_sail =
        report.outcome_counts.unicorn_fp_quirks_adjudicated_by_sail;
    Ok(())
}

/// Run the full differential fuzzing campaign (fast CI mode when `duration_secs == 0`, or timed local campaign).
pub fn run_fuzz_campaign(cfg: &FuzzConfig) -> Result<FuzzReport> {
    run_fuzz_campaign_with_options(cfg, true)
}

/// Run only the 49-family + Linaro RISU single-instruction fuzzing pass (`--insn-fuzz-only`),
/// without running the standalone IEEE-754 floating-point corpora (`--fp-only` in `src/fp.rs`).
pub fn run_insn_fuzz_only(cfg: &FuzzConfig) -> Result<FuzzReport> {
    run_fuzz_campaign_with_options(cfg, false)
}

fn run_fuzz_campaign_with_options(cfg: &FuzzConfig, include_fp: bool) -> Result<FuzzReport> {
    let start = Instant::now();
    let cache = upstream_cache_dir();
    let fp_dir = cache.join("fp-tools");
    let fpgen_dir = fp_dir.join("fpgen");
    let tf_bin = fp_dir
        .join("testfloat3")
        .join("build")
        .join("Linux-x86_64-GCC")
        .join("testfloat_gen");
    let risu_path = fp_dir.join("risu").join("aarch64.risu");

    let mut report = FuzzReport {
        seed: format!("0x{:016x}", cfg.seed),
        ..Default::default()
    };
    let mut rng = SplitMix64::new(cfg.seed);
    let long_run = cfg.duration_secs >= 60;

    if include_fp {
        // 1. IBM FPgen fixed IEEE-754 corpus
        run_fpgen_corpus(&fpgen_dir, &cfg.diff_eval_bin, &mut report)?;

        // 2. Berkeley TestFloat 3 (`testfloat_gen -level 1`)
        run_testfloat_pass(&tf_bin, &cfg.diff_eval_bin, cfg.seed, long_run, &mut report)?;

        // 3. Stratified FP edge batch
        run_stratified_fp_batch(
            &cfg.diff_eval_bin,
            &mut rng,
            if long_run { 2000 } else { 250 },
            &mut report,
        )?;
    }

    // 4. Linaro RISU patterns + 49 instruction families
    let mut lean_oracle =
        LeanOracle::new(&cfg.diff_eval_bin).map_err(|e| anyhow!("{e}"))?;
    let mut sail_oracle = SailOracle::new()?;
    let mut unicorn_oracle = UnicornOracle::new().map_err(|e| anyhow!("{e}"))?;
    let policy = Policy::default();

    let risu_patterns = load_risu_patterns(&risu_path);
    let deadline = if cfg.duration_secs > 0 {
        Some(Instant::now() + Duration::from_secs(cfg.duration_secs))
    } else {
        None
    };

    let chunk_per_fam = if long_run {
        5000
    } else {
        cfg.cases_per_family.clamp(100, 5000)
    };
    let target_per_fam = if long_run {
        cfg.cases_per_family.max(100_000)
    } else {
        cfg.cases_per_family.max(100)
    };
    let mut pass_idx = 0u64;

    loop {
        pass_idx += 1;
        // Generate `chunk_per_fam` cases for each of the 49 families in a single batch
        let total_fam_insns = FAMILY_NAMES.len() * chunk_per_fam;
        let mut all_records = Vec::with_capacity(total_fam_insns * 16);
        for fam_idx in 0..FAMILY_NAMES.len() {
            for _ in 0..chunk_per_fam {
                let rec = gen_family_insn_record(fam_idx, &mut rng);
                all_records.extend_from_slice(&rec);
            }
            *report
                .family_cases
                .entry(FAMILY_NAMES[fam_idx].to_string())
                .or_insert(0) += chunk_per_fam as u64;
        }
        report.total_cases += total_fam_insns as u64;
        check_insn_records(
            &mut lean_oracle,
            &mut sail_oracle,
            &mut unicorn_oracle,
            &policy,
            &all_records,
            "insn_family_batch",
            pass_idx == 1 && !long_run,
            &mut report,
        )?;
        if pass_idx == 1 && long_run {
            // Also run Unicorn on a 500-case/family sample on pass 1 of a long run
            let mut uc_records = Vec::with_capacity(FAMILY_NAMES.len() * 500 * 16);
            for fam_idx in 0..FAMILY_NAMES.len() {
                let base = fam_idx * chunk_per_fam * 16;
                uc_records.extend_from_slice(&all_records[base..base + 500 * 16]);
            }
            check_insn_records(
                &mut lean_oracle,
                &mut sail_oracle,
                &mut unicorn_oracle,
                &policy,
                &uc_records,
                "insn_family_unicorn_sample",
                true,
                &mut report,
            )?;
        }

        // Generate RISU pattern batch
        if !risu_patterns.is_empty() {
            let risu_batch_len = if long_run { 2000 } else { 500 };
            let mut risu_records = Vec::with_capacity(risu_batch_len * 16);
            for _ in 0..risu_batch_len {
                let pat = &risu_patterns[(rng.next_u64() as usize) % risu_patterns.len()];
                let raw = rng.next_u32();
                let insn = (raw & !pat.mask) | pat.val;
                let mem_base = pat.rn_shift.map(|sh| (insn >> sh) & 0x1f);
                let rec = build_record_with_edges(insn, mem_base, !0xfu64, &mut rng);
                risu_records.extend_from_slice(&rec);
            }
            check_insn_records(
                &mut lean_oracle,
                &mut sail_oracle,
                &mut unicorn_oracle,
                &policy,
                &risu_records,
                "risu",
                pass_idx == 1,
                &mut report,
            )?;
            report.risu_cases += risu_batch_len as u64;
            report.total_cases += risu_batch_len as u64;
        }

        if long_run && include_fp {
            run_stratified_fp_batch(&cfg.diff_eval_bin, &mut rng, 1000, &mut report)?;
        }

        report.elapsed_secs = start.elapsed().as_secs_f64();
        if let Some(ref rpath) = cfg.report_path {
            let _ = fs::write(rpath, serde_json::to_string_pretty(&report)?);
        }

        let have_per_fam = (pass_idx as usize) * chunk_per_fam;
        match deadline {
            Some(dl)
                if (Instant::now() < dl || have_per_fam < target_per_fam)
                    && report.lean_vs_sail_mismatches.is_empty() =>
            {
                continue
            }
            None if have_per_fam < target_per_fam && report.lean_vs_sail_mismatches.is_empty() => {
                continue
            }
            _ => break,
        }
    }

    report.elapsed_secs = start.elapsed().as_secs_f64();
    if let Some(ref rpath) = cfg.report_path {
        fs::write(rpath, serde_json::to_string_pretty(&report)?)?;
    }
    println!(
        "Fuzz summary (seed={}, {:.1}s): total_cases={} (fpgen={}, testfloat={}, stratified_fp={}, risu={}), unicorn_quirks={}, mismatches={}",
        report.seed,
        report.elapsed_secs,
        report.total_cases,
        report.fpgen_cases,
        report.testfloat_cases,
        report.stratified_fp_cases,
        report.risu_cases,
        report.unicorn_fp_quirks_adjudicated_by_sail,
        report.lean_vs_sail_mismatches.len()
    );
    println!(
        "  Outcome classification: executed_compared={}, unmodeled_decode={}, exec_exception={}, non_nop_hint_neutralized={}, fpgen_trapped_skipped={}, fpgen_nan_canonicalized={}, unicorn_quirks_adjudicated={}",
        report.outcome_counts.executed_compared,
        report.outcome_counts.unmodeled_decode,
        report.outcome_counts.exec_exception,
        report.outcome_counts.non_nop_hint_neutralized,
        report.outcome_counts.fpgen_trapped_exception_skipped,
        report.outcome_counts.fpgen_nan_canonicalized,
        report.outcome_counts.unicorn_fp_quirks_adjudicated_by_sail
    );
    for m in report.lean_vs_sail_mismatches.iter().take(20) {
        eprintln!("  MISMATCH: {m}");
    }
    let min_campaign_pct: u64 = if include_fp { 99 } else { 90 };
    if report.lean_vs_sail_mismatches.is_empty()
        && report.outcome_counts.executed_compared * 100 < report.total_cases * min_campaign_pct
    {
        bail!(
            "Fuzz campaign executed_compared ({}/{}) fell below required {min_campaign_pct}% floor",
            report.outcome_counts.executed_compared,
            report.total_cases
        );
    }
    Ok(report)
}

/// Run a targeted high-throughput differential fuzzing campaign over the 5 AdvSIMD & Crypto
/// instruction families (`38_crypto_aes`, `40_simd_imm_shift_movi_shl_ushll_sri_sli`,
/// `42_simd_dup_ins_umov`, `43_simd_three_same`, `44_simd_two_reg_misc`) against both
/// Sail Armv9.4-A and Unicorn `UC_CPU_ARM64_MAX`.
pub fn run_simd_crypto_fuzz_campaign(
    diff_eval_bin: &Path,
    seed: u64,
    cases_per_family: usize,
) -> Result<FuzzReport> {
    let start = Instant::now();
    let mut report = FuzzReport {
        seed: format!("0x{seed:016x}"),
        ..Default::default()
    };
    let mut rng = SplitMix64::new(seed);
    let mut lean_oracle =
        LeanOracle::new(diff_eval_bin).map_err(|e| anyhow!("{e}"))?;
    let mut sail_oracle = SailOracle::new()?;
    let mut unicorn_oracle = UnicornOracle::new().map_err(|e| anyhow!("{e}"))?;
    let policy = Policy::default();

    let simd_families: [usize; 5] = [37, 39, 41, 42, 43];
    let chunk = 20_000usize.min(cases_per_family.max(1));
    let passes = (cases_per_family + chunk - 1) / chunk;

    for pass in 0..passes {
        let cur_chunk = if pass + 1 == passes {
            cases_per_family - pass * chunk
        } else {
            chunk
        };
        let mut batch_records = Vec::with_capacity(simd_families.len() * cur_chunk * 16);
        for &fam_idx in &simd_families {
            for _ in 0..cur_chunk {
                let rec = gen_family_insn_record(fam_idx, &mut rng);
                batch_records.extend_from_slice(&rec);
            }
            *report
                .family_cases
                .entry(FAMILY_NAMES[fam_idx].to_string())
                .or_insert(0) += cur_chunk as u64;
        }
        report.total_cases += (simd_families.len() * cur_chunk) as u64;
        check_insn_records(
            &mut lean_oracle,
            &mut sail_oracle,
            &mut unicorn_oracle,
            &policy,
            &batch_records,
            "simd_crypto_campaign",
            pass < 5,
            &mut report,
        )?;
        if !report.lean_vs_sail_mismatches.is_empty() {
            break;
        }
    }

    let uc_per_fam = cases_per_family.min(5 * chunk);
    report.elapsed_secs = start.elapsed().as_secs_f64();
    println!(
        "SIMD/Crypto Fuzz Campaign (seed={}, {:.1}s): total_cases={}, unicorn_cases_per_family={}, unicorn_quirks={}, mismatches={}",
        report.seed,
        report.elapsed_secs,
        report.total_cases,
        uc_per_fam,
        report.unicorn_fp_quirks_adjudicated_by_sail,
        report.lean_vs_sail_mismatches.len()
    );
    for (fam, count) in &report.family_cases {
        println!(
            "  {fam}: sail_cases={count}, unicorn_cases={uc_per_fam}, oracle=Sail Armv9.4-A + Unicorn UC_CPU_ARM64_MAX, mismatches={}",
            report.lean_vs_sail_mismatches.len()
        );
    }
    for m in report.lean_vs_sail_mismatches.iter().take(20) {
        eprintln!("  MISMATCH: {m}");
    }
    if report.lean_vs_sail_mismatches.is_empty()
        && report.outcome_counts.executed_compared * 100 < report.total_cases * 99
    {
        bail!(
            "SIMD/Crypto campaign executed_compared ({}/{}) fell below required 99% floor",
            report.outcome_counts.executed_compared,
            report.total_cases
        );
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    #[test]
    fn test_broken_serve_early_eof_fails_check_insn_records() {
        let mut cmd = Command::new("/bin/sh");
        cmd.arg("-c").arg("exit 0");
        let mut lean_oracle = LeanOracle::spawn_with_command(&mut cmd, PathBuf::from("/bin/sh"))
            .expect("spawn broken EOF serve");
        let mut sail_oracle = SailOracle::new().expect("SailOracle::new");
        let mut uc_oracle = UnicornOracle::new().expect("UnicornOracle::new");
        let policy = Policy::default();
        let mut rng = SplitMix64::new(0x1234_5678);
        let rec = gen_family_insn_record(2, &mut rng);
        let mut report = FuzzReport::default();

        let res = check_insn_records(
            &mut lean_oracle,
            &mut sail_oracle,
            &mut uc_oracle,
            &policy,
            &rec,
            "broken_eof",
            false,
            &mut report,
        );
        assert!(
            res.is_err(),
            "expected broken serve (early EOF) to fail check_insn_records"
        );
        assert_eq!(report.outcome_counts.executed_compared, 0);
        assert_eq!(report.outcome_counts.exec_exception, 0);
    }

    #[test]
    fn test_broken_serve_wrong_count_fails_check_insn_records() {
        let mut cmd = Command::new("/bin/sh");
        // Drain request header and reply with a 4-byte frame containing count = 0 for a 2-record batch.
        cmd.arg("-c")
            .arg("head -c 4 >/dev/null; printf '\\004\\000\\000\\000\\000\\000\\000\\000'");
        let mut lean_oracle = LeanOracle::spawn_with_command(&mut cmd, PathBuf::from("/bin/sh"))
            .expect("spawn broken wrong-count serve");
        let mut sail_oracle = SailOracle::new().expect("SailOracle::new");
        let mut uc_oracle = UnicornOracle::new().expect("UnicornOracle::new");
        let policy = Policy::default();
        let mut rng = SplitMix64::new(0x8765_4321);
        let mut records = Vec::new();
        records.extend_from_slice(&gen_family_insn_record(2, &mut rng));
        records.extend_from_slice(&gen_family_insn_record(2, &mut rng));
        let mut report = FuzzReport::default();

        let err = check_insn_records(
            &mut lean_oracle,
            &mut sail_oracle,
            &mut uc_oracle,
            &policy,
            &records,
            "broken_wrong_count",
            false,
            &mut report,
        )
        .expect_err("expected wrong RUN_BATCH count from serve to fail check_insn_records");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("RUN_BATCH returned 0 outcomes for 2 inputs"),
            "unexpected error message: {msg}"
        );
        assert_eq!(report.outcome_counts.executed_compared, 0);
        assert_eq!(report.outcome_counts.exec_exception, 0);
    }
}
