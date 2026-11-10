// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for `run-trusted-tests` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (empirical differential test runner comparing Lean 4 ARM64
//!   semantics against LLVM assembly, Unicorn/QEMU AArch64, and Sail Armv9.4-A execution).
//! - **Purpose:** Parses CLI flags (`--repo-root`, `--diff-eval-bin`, `--input`, `--filter`,
//!   `--oracle`) and invokes [`run_trusted_tests::run_differential_validation_with_oracle`],
//!   exiting `0` when all test cases in `Arm64.Testing.TrustedSuite` match the selected oracle(s), or `1`
//!   on any mismatch.
//!
//! # Key Types & Functions
//! - `Cli`: `clap` argument parser for `run-trusted-tests`.
//! - `run_trusted_tests::default_repo_root`: Resolves the default `--repo-root`.
//! - `main`: Entry point driving [`run_differential_validation_with_oracle`].
//!
//! # When to Read This File
//! - The header suffices unless you are changing CLI flags. For differential validation logic,
//!   read [`lib.rs`](lib.rs), [`assembler.rs`](assembler.rs), [`unicorn.rs`](unicorn.rs),
//!   [`sail.rs`](sail.rs), and [`fp.rs`](fp.rs).

use std::path::PathBuf;
use std::process::ExitCode;

use clap::Parser;
use run_trusted_tests::fp::run_fp_validation;
use run_trusted_tests::fuzz::{
    FuzzConfig, run_fuzz_campaign, run_insn_fuzz_only, run_simd_crypto_fuzz_campaign,
};
use run_trusted_tests::model::OracleSelection;
use run_trusted_tests::{
    ensure_diff_eval_bin, resolve_head_sha_seed, run_differential_validation_ext,
    run_random_suite_validation,
};

#[derive(Parser, Debug)]
#[command(
    name = "run-trusted-tests",
    about = "Differential validator comparing Lean 4 ARM64 semantics (`diff_eval`) against Unicorn Engine (`UC_ARCH_ARM64`), Sail Armv9.4-A (`rems-project/sail-arm`), SoftFloat (`ARM-VFPv2`), and LLVM (`llvm-mc`).",
    after_help = "Examples:\n  tools/target/release/run-trusted-tests --oracle unicorn\n  tools/target/release/run-trusted-tests --oracle all --filter ldp\n  tools/target/release/run-trusted-tests --fp-only --print-vectors 8\n  tools/target/release/run-trusted-tests --seed 0x20261016 --random-cases 4 --print-vectors 2"
)]
struct Cli {
    /// Repository root directory (defaults to the parent of `run-trusted-tests`).
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// Path to `diff_eval` binary (defaults to `<repo_root>/Arm64/Testing/.lake/build/bin/diff_eval`).
    #[arg(long)]
    diff_eval_bin: Option<PathBuf>,

    /// Optional JSON test suite file (defaults to `diff_eval --dump-suite` from Lean's `Arm64.Testing.TrustedSuite`).
    #[arg(long)]
    input: Option<PathBuf>,

    /// Only run test cases whose name contains `FILTER`.
    #[arg(long)]
    filter: Option<String>,

    /// Reference ISA oracle(s) to execute and compare against (`all`, `unicorn`, or `sail`).
    #[arg(long, value_enum, default_value_t = OracleSelection::All)]
    oracle: OracleSelection,

    /// Print up to `PRINT_VECTORS` populated test vectors (inputs and Lean/Unicorn/Sail or SoftFloat post-states).
    #[arg(long, default_value_t = 0)]
    print_vectors: usize,

    /// Run only the standalone IEEE-754 floating-point differential suite (IBM FPgen + TestFloat 3e + Stratified FP vs SoftFloat 3e `ARM-VFPv2`).
    #[arg(long, default_value_t = false)]
    fp_only: bool,

    /// Run only the multi-instruction `IsaTestCase` JSON suite (`diff_eval --dump-suite`), skipping the 504k fuzz pass.
    #[arg(long, default_value_t = false)]
    suite_only: bool,

    /// Run only the 49-family + Linaro RISU single-instruction fuzzing pass, skipping the JSON suite and standalone FP corpora.
    #[arg(long, default_value_t = false)]
    insn_fuzz_only: bool,

    /// Generate and run `RANDOM_CASES` freshly seeded random `IsaTestCase` blocks via `diff_eval --dump-random`.
    #[arg(long)]
    random_cases: Option<usize>,

    /// Number of instructions per block when `--random-cases` is used.
    #[arg(long, default_value_t = 8)]
    random_insns: usize,

    /// Run a timed differential fuzzing campaign for `FUZZ_SECS` seconds (e.g. `3600` for 60 minutes).
    #[arg(long)]
    fuzz_secs: Option<u64>,

    /// Explicit 64-bit RNG seed (hex with `0x` or decimal; defaults to first 16 hex chars of `HEAD` SHA).
    #[arg(long)]
    seed: Option<String>,

    /// Number of cases per instruction family per fuzzing pass in CI mode.
    #[arg(long, default_value_t = 500)]
    cases_per_family: usize,

    /// Optional output path for a JSON fuzz report.
    #[arg(long)]
    fuzz_report: Option<PathBuf>,

    /// Run a targeted AdvSIMD + Crypto differential fuzzing campaign with `SIMD_FUZZ_CASES` per family against Sail and Unicorn.
    #[arg(long)]
    simd_fuzz_cases: Option<usize>,
}

fn parse_seed(raw: Option<&str>, repo_root: & std::path::Path) -> u64 {
    if let Some(s) = raw {
        let s = s.trim();
        if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
            && let Ok(v) = u64::from_str_radix(hex, 16)
        {
            return v;
        }
        if let Ok(v) = s.parse::<u64>() {
            return v;
        }
        if let Ok(v) = u64::from_str_radix(s, 16) {
            return v;
        }
    }
    resolve_head_sha_seed(repo_root)
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let repo_root = cli
        .repo_root
        .unwrap_or_else(run_trusted_tests::default_repo_root);

    if cli.fp_only {
        let diff_eval_bin = match ensure_diff_eval_bin(&repo_root, cli.diff_eval_bin.as_deref()) {
            Ok(b) => b,
            Err(err) => {
                eprintln!("error: {err:#}");
                return ExitCode::from(2);
            }
        };
        let seed = parse_seed(cli.seed.as_deref(), &repo_root);
        let cfg = FuzzConfig {
            repo_root,
            diff_eval_bin,
            seed,
            duration_secs: cli.fuzz_secs.unwrap_or(0),
            cases_per_family: cli.cases_per_family,
            report_path: cli.fuzz_report,
        };
        return match run_fp_validation(&cfg, cli.print_vectors) {
            Ok(report) if report.lean_vs_sail_mismatches.is_empty() => ExitCode::SUCCESS,
            Ok(_) => ExitCode::from(1),
            Err(err) => {
                eprintln!("error: {err:#}");
                ExitCode::from(2)
            }
        };
    }

    if let Some(random_count) = cli.random_cases {
        let seed = parse_seed(cli.seed.as_deref(), &repo_root);
        return match run_random_suite_validation(
            &repo_root,
            cli.diff_eval_bin.as_deref(),
            seed,
            random_count,
            cli.random_insns,
            cli.oracle,
            cli.print_vectors,
        ) {
            Ok(true) => ExitCode::SUCCESS,
            Ok(false) => ExitCode::from(1),
            Err(err) => {
                eprintln!("error: {err:#}");
                ExitCode::from(2)
            }
        };
    }

    if cli.insn_fuzz_only {
        let diff_eval_bin = match ensure_diff_eval_bin(&repo_root, cli.diff_eval_bin.as_deref()) {
            Ok(b) => b,
            Err(err) => {
                eprintln!("error: {err:#}");
                return ExitCode::from(2);
            }
        };
        let seed = parse_seed(cli.seed.as_deref(), &repo_root);
        let cfg = FuzzConfig {
            repo_root,
            diff_eval_bin,
            seed,
            duration_secs: cli.fuzz_secs.unwrap_or(0),
            cases_per_family: cli.cases_per_family,
            report_path: cli.fuzz_report,
        };
        return match run_insn_fuzz_only(&cfg) {
            Ok(report) if report.lean_vs_sail_mismatches.is_empty() => ExitCode::SUCCESS,
            Ok(_) => ExitCode::from(1),
            Err(err) => {
                eprintln!("error: {err:#}");
                ExitCode::from(2)
            }
        };
    }

    if let Some(cases_per_fam) = cli.simd_fuzz_cases {
        let diff_eval_bin = match ensure_diff_eval_bin(&repo_root, cli.diff_eval_bin.as_deref()) {
            Ok(b) => b,
            Err(err) => {
                eprintln!("error: {err:#}");
                return ExitCode::from(2);
            }
        };
        let seed = parse_seed(cli.seed.as_deref(), &repo_root);
        return match run_simd_crypto_fuzz_campaign(&diff_eval_bin, seed, cases_per_fam) {
            Ok(report) if report.lean_vs_sail_mismatches.is_empty() => ExitCode::SUCCESS,
            Ok(_) => ExitCode::from(1),
            Err(err) => {
                eprintln!("error: {err:#}");
                ExitCode::from(2)
            }
        };
    }

    if let Some(duration_secs) = cli.fuzz_secs {
        let diff_eval_bin = match ensure_diff_eval_bin(&repo_root, cli.diff_eval_bin.as_deref()) {
            Ok(b) => b,
            Err(err) => {
                eprintln!("error: {err:#}");
                return ExitCode::from(2);
            }
        };
        let seed = parse_seed(cli.seed.as_deref(), &repo_root);
        let cfg = FuzzConfig {
            repo_root,
            diff_eval_bin,
            seed,
            duration_secs,
            cases_per_family: cli.cases_per_family,
            report_path: cli.fuzz_report,
        };
        return match run_fuzz_campaign(&cfg) {
            Ok(report) if report.lean_vs_sail_mismatches.is_empty() => ExitCode::SUCCESS,
            Ok(_) => ExitCode::from(1),
            Err(err) => {
                eprintln!("error: {err:#}");
                ExitCode::from(2)
            }
        };
    }

    match run_differential_validation_ext(
        &repo_root,
        cli.diff_eval_bin.as_deref(),
        cli.input.as_deref(),
        cli.filter.as_deref(),
        cli.oracle,
        cli.print_vectors,
        cli.suite_only,
    ) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(err) => {
            eprintln!("error: {err:#}");
            ExitCode::from(2)
        }
    }
}
