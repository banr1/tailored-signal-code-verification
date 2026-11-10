// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Differential test runner bridging Lean 4 (`diff_eval --serve`), LLVM (`rustc` + `ld.lld`),
//! Unicorn Engine (`UC_ARCH_ARM64` / QEMU AArch64), and the official Sail Armv9.4-A
//! (`rems-project/sail-arm`) formal ISA semantics (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (validates the trusted Lean ISA semantics in `Arm64/` against
//!   independent external oracles: LLVM's AArch64 assembler, Unicorn's AArch64 CPU model, and
//!   Arm's ASL-derived Sail Armv9.4-A specification).
//! - **Purpose:** Loads test cases from `diff_eval --dump-suite` (`Arm64/Testing/Generators/TrustedSuite.lean`),
//!   batch-assembles any assembly snippets into 32-bit machine words via [`assembler::LlvmAssembler`],
//!   converts each case to [`isa_oracle::TestInput`], steps [`lean_oracle::LeanOracle`],
//!   [`unicorn_aarch64::UnicornOracle`], and [`sail_aarch64::SailOracle`] in lockstep instruction by
//!   instruction, and diffs full [`isa_oracle::Outcome`] states after every instruction via
//!   [`isa_oracle::diff`].
//!
//! # Key Types & Functions
//! - [`ensure_diff_eval_bin`]: Locates or builds `Arm64/Testing/.lake/build/bin/diff_eval`.
//! - [`load_lean_suite`]: Dumps JSON [`model::DiffTestCase`] vectors from `diff_eval --dump-suite`.
//! - [`populate_words`]: Batch-assembles `asm` strings into `words` via [`assembler::LlvmAssembler`].
//! - [`run_suite_lockstep`]: Steps all active [`isa_oracle::Arm64Oracle`] backends in lockstep and
//!   reports the first divergent instruction on mismatch.
//! - [`run_differential_validation_with_oracle`]: Orchestrates suite loading, assembly, lockstep
//!   differential execution, and the 504k single-instruction + IEEE-754 fuzz pass.
//!
//! # When to Read This File
//! - Read this file when modifying the lockstep multi-instruction runner or state-comparison report.
//! - For standalone IEEE-754 floating-point differential testing (`--fp-only`), read [`fp`].

pub mod assembler;
pub mod compare;
pub mod elf_loader_diff;
pub mod fp;
pub mod fuzz;
pub mod fuzz_gen;
pub mod lean_oracle;
pub mod model;
pub mod process_e2e;
pub mod sail;
pub mod std_syscall_inventory;
pub mod unicorn;

#[cfg(all(test, target_os = "linux"))]
mod fs_linux_diff_tests;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use anyhow::{Context, Result, anyhow, bail};
use isa_oracle::{Arm64Oracle, NO_EXIT_PC, Outcome, Policy, TestInput, diff};
use sail_aarch64::SailOracle;
use unicorn_aarch64::UnicornOracle;

use crate::assembler::LlvmAssembler;
use crate::lean_oracle::LeanOracle;
use crate::model::{DiffTestCase, OracleSelection, OracleState};

static DIFF_EVAL_BUILD_LOCK: Mutex<()> = Mutex::new(());

const DIFF_EVAL_CONFIG_FILES: &[&str] = &[
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
    "Arm64.lean",
    "Arm64/lakefile.toml",
    "Arm64/lake-manifest.json",
    "ProofLib.lean",
    "ProofLib/lakefile.toml",
    "ProofLib/lake-manifest.json",
    "Arm64/Testing/lakefile.lean",
    "Arm64/Testing/lake-manifest.json",
    "Arm64/Testing/Generators/CompiledBinaryFixture.lean",
    "Arm64/Testing/Generators/CompiledBinaryFixture.bin",
];

fn diff_eval_input_hash(repo_root: &Path) -> Option<String> {
    let mut rel_paths: Vec<PathBuf> = DIFF_EVAL_CONFIG_FILES
        .iter()
        .map(PathBuf::from)
        .filter(|rel| repo_root.join(rel).is_file())
        .collect();

    for subdir in ["Arm64", "ProofLib"] {
        let dir = repo_root.join(subdir);
        if !dir.is_dir() {
            continue;
        }
        for entry in walkdir::WalkDir::new(&dir)
            .into_iter()
            .filter_entry(|e| e.file_name() != ".lake" && e.file_name() != "target")
            .filter_map(|e| e.ok())
        {
            if entry.file_type().is_file()
                && entry.path().extension().is_some_and(|ext| ext == "lean")
                && let Ok(rel) = entry.path().strip_prefix(repo_root)
            {
                rel_paths.push(rel.to_path_buf());
            }
        }
    }

    rel_paths.sort();
    rel_paths.dedup();

    let mut payload = Vec::new();
    for rel in &rel_paths {
        let bytes = fs::read(repo_root.join(rel)).ok()?;
        let rel_str = rel.to_string_lossy();
        payload.extend_from_slice(&(rel_str.len() as u64).to_le_bytes());
        payload.extend_from_slice(rel_str.as_bytes());
        payload.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        payload.extend_from_slice(&bytes);
    }

    Some(crate::process_e2e::sha256_hex(&payload))
}

/// Ensure `<repo_root>/Arm64/Testing/.lake/build/bin/diff_eval` exists and matches the SHA-256
/// `.srchash` digest of the current Lean toolchain, `lakefile*`, `Arm64/`, and `ProofLib/` inputs,
/// building it serially via `lake -d Arm64/Testing build --no-ansi diff_eval` if missing or stale.
pub fn ensure_diff_eval_bin(repo_root: &Path, explicit_bin: Option<&Path>) -> Result<PathBuf> {
    if let Some(bin) = explicit_bin {
        if bin.is_file() {
            return Ok(bin.to_path_buf());
        }
        bail!(
            "specified `--diff-eval-bin` does not exist: {}",
            bin.display()
        );
    }

    let _guard = DIFF_EVAL_BUILD_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());

    let diff_eval_bin = repo_root
        .join("Arm64")
        .join("Testing")
        .join(".lake")
        .join("build")
        .join("bin")
        .join("diff_eval");
    let srchash_path = repo_root
        .join("Arm64")
        .join("Testing")
        .join(".lake")
        .join("build")
        .join("bin")
        .join("diff_eval.srchash");

    if diff_eval_bin.is_file()
        && let Some(ref cur_hash) = diff_eval_input_hash(repo_root)
        && let Ok(saved_hash) = fs::read_to_string(&srchash_path)
        && saved_hash.trim() == cur_hash
    {
        return Ok(diff_eval_bin);
    }

    let lake_bin = which::which("lake")
        .ok()
        .or_else(|| {
            std::env::var_os("HOME")
                .map(|h| PathBuf::from(h).join(".elan").join("bin").join("lake"))
                .filter(|p| p.is_file())
        })
        .ok_or_else(|| {
            anyhow!(
                "{} is missing and `lake` was not found on PATH; run `lake -d Arm64/Testing build --no-ansi diff_eval` first",
                diff_eval_bin.display()
            )
        })?;

    println!("Building {}...", diff_eval_bin.display());
    let status = Command::new(lake_bin)
        .args(["-d", "Arm64/Testing", "build", "--no-ansi", "diff_eval"])
        .current_dir(repo_root)
        .status()
        .context("failed to invoke `lake -d Arm64/Testing build --no-ansi diff_eval`")?;
    if !status.success() {
        bail!("`lake -d Arm64/Testing build --no-ansi diff_eval` exited with status {status}");
    }
    if !diff_eval_bin.is_file() {
        bail!(
            "`lake -d Arm64/Testing build --no-ansi diff_eval` succeeded without producing {}",
            diff_eval_bin.display()
        );
    }
    if let Some(cur_hash) = diff_eval_input_hash(repo_root) {
        let _ = fs::write(&srchash_path, format!("{cur_hash}\n"));
    }
    Ok(diff_eval_bin)
}

/// Export the test suite defined in Lean (`Arm64.Testing.TrustedSuite`) via `diff_eval --dump-suite`.
pub fn load_lean_suite(diff_eval_bin: &Path, repo_root: &Path) -> Result<Vec<DiffTestCase>> {
    let out = Command::new(diff_eval_bin)
        .arg("--dump-suite")
        .current_dir(repo_root)
        .output()
        .with_context(|| {
            format!(
                "failed to execute `{} --dump-suite`",
                diff_eval_bin.display()
            )
        })?;
    if !out.status.success() {
        bail!(
            "`diff_eval --dump-suite` failed ({}):\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let suite: Vec<DiffTestCase> = serde_json::from_slice(&out.stdout)
        .context("failed to parse JSON suite from `diff_eval --dump-suite`")?;
    Ok(suite)
}

/// Export `count` freshly generated seeded random `IsaTestCase` blocks from Lean via
/// `diff_eval --dump-random <seed> <count> <insns_per_block>`.
pub fn load_random_suite(
    diff_eval_bin: &Path,
    repo_root: &Path,
    seed: u64,
    count: usize,
    insns_per_block: usize,
) -> Result<Vec<DiffTestCase>> {
    let seed_arg = format!("0x{seed:016x}");
    let out = Command::new(diff_eval_bin)
        .args([
            "--dump-random",
            &seed_arg,
            &count.to_string(),
            &insns_per_block.to_string(),
        ])
        .current_dir(repo_root)
        .output()
        .with_context(|| {
            format!(
                "failed to execute `{} --dump-random {seed_arg} {count} {insns_per_block}`",
                diff_eval_bin.display()
            )
        })?;
    if !out.status.success() {
        bail!(
            "`diff_eval --dump-random` failed ({}):\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let suite: Vec<DiffTestCase> = serde_json::from_slice(&out.stdout)
        .context("failed to parse JSON suite from `diff_eval --dump-random`")?;
    Ok(suite)
}

/// Populate `words` for any test case in `suite` that specifies assembly source (`asm`).
pub fn populate_words(suite: &mut [DiffTestCase]) -> Result<()> {
    let mut to_assemble_indices = Vec::new();
    let mut to_assemble_items = Vec::new();

    for (idx, tc) in suite.iter().enumerate() {
        if tc.words.is_empty() {
            let asm_text = tc.asm.as_deref().ok_or_else(|| {
                anyhow!(
                    "test case `{}` has neither `words` nor `asm` source",
                    tc.name
                )
            })?;
            let base_pc = tc.base_pc_u64()?;
            to_assemble_indices.push(idx);
            to_assemble_items.push((base_pc, asm_text));
        }
    }

    if !to_assemble_items.is_empty() {
        let assembler = LlvmAssembler::discover()?;
        let batch_words = assembler.assemble_batch(&to_assemble_items)?;
        for (suite_idx, words) in to_assemble_indices.into_iter().zip(batch_words) {
            suite[suite_idx].words = words.into_iter().map(|w| format!("0x{w:08x}")).collect();
        }
    }

    Ok(())
}

/// Observed post-states for a single test case across Lean, Unicorn, and Sail.
#[derive(Debug, Clone)]
pub struct CaseLockedStates {
    pub lean: Option<OracleState>,
    pub unicorn: Option<OracleState>,
    pub sail: Option<OracleState>,
}

/// Print up to `limit` populated test vectors showing inputs (`asm`, `words`, initial registers/memory)
/// and the side-by-side post-states produced by Lean `Arm64.Step` (`LeanOracle`), Unicorn, and Sail.
pub fn print_test_vectors(suite: &[DiffTestCase], states: &[CaseLockedStates], limit: usize) {
    let count = limit.min(suite.len()).min(states.len());
    if count == 0 {
        return;
    }
    println!(
        "\n--- Test Vectors (showing {count} of {} case(s)) ---",
        suite.len()
    );
    for idx in 0..count {
        let tc = &suite[idx];
        let st_bundle = &states[idx];
        println!("\nVector [{}/{}]: {}", idx + 1, suite.len(), tc.name);
        if let Some(asm) = &tc.asm {
            let compact = asm
                .lines()
                .map(str::trim)
                .filter(|l| !l.is_empty())
                .collect::<Vec<_>>()
                .join(" ; ");
            println!("  input.asm       : {compact}");
        }
        if tc.words.len() <= 8 {
            println!("  input.words     : [{}]", tc.words.join(", "));
        } else {
            let base = tc.base_pc_u64().unwrap_or(0);
            let start = tc.start_pc_u64().unwrap_or(base);
            let word_off = ((start.saturating_sub(base)) / 4) as usize;
            let slice_end = (word_off + 6).min(tc.words.len());
            let slice = &tc.words[word_off.min(tc.words.len())..slice_end];
            println!(
                "  input.words     : [{}, ...] (entry at word +{word_off}, {} words in image)",
                slice.join(", "),
                tc.words.len()
            );
        }
        let start_pc = tc.start_pc.as_deref().unwrap_or(&tc.base_pc);
        println!(
            "  input.pc/sp/nzcv: pc={start_pc} -> exit_pc={}, sp={}, nzcv=0x{:x}",
            tc.exit_pc, tc.sp, tc.nzcv
        );
        if let Ok(init_regs) = tc.initial_regs_u64() {
            let non_zero: Vec<String> = init_regs
                .iter()
                .enumerate()
                .filter(|&(_, &v)| v != 0)
                .map(|(r, &v)| format!("x{r}=0x{v:x}"))
                .collect();
            if non_zero.is_empty() {
                println!("  input.regs      : (all x0..x30 = 0)");
            } else {
                println!("  input.regs      : {}", non_zero.join(", "));
            }
        }
        if let Ok(init_vregs) = tc.initial_vregs_u128() {
            let non_zero: Vec<String> = init_vregs
                .iter()
                .enumerate()
                .filter(|&(_, &v)| v != 0)
                .map(|(r, &v)| format!("v{r}=0x{v:032x}"))
                .collect();
            if !non_zero.is_empty() {
                println!("  input.vregs     : {}", non_zero.join(", "));
            }
        }
        if let Ok(mem_init) = tc.initial_mem_writes()
            && !mem_init.is_empty()
        {
            let formatted: Vec<String> = mem_init
                .iter()
                .map(|(addr, val, sz)| format!("[0x{addr:x}; {sz}B]=0x{val:x}"))
                .collect();
            println!("  input.mem_init  : {}", formatted.join(", "));
        }
        for (label, state_opt) in [
            ("eval.lean_step", st_bundle.lean.as_ref()),
            ("oracle.unicorn", st_bundle.unicorn.as_ref()),
            ("oracle.sail   ", st_bundle.sail.as_ref()),
        ] {
            if let Some(st) = state_opt {
                if let Some(err) = &st.error {
                    println!("  {label}  : ERROR({err})");
                    continue;
                }
                let nz_regs: Vec<String> = st
                    .regs
                    .iter()
                    .enumerate()
                    .filter_map(|(r, s)| {
                        let v = crate::model::parse_u64_str(s).ok()?;
                        (v != 0).then(|| format!("x{r}=0x{v:x}"))
                    })
                    .collect();
                let nz_vregs: Vec<String> = st
                    .vregs
                    .iter()
                    .enumerate()
                    .filter_map(|(r, s)| {
                        let v = crate::model::parse_u128_str(s).ok()?;
                        (v != 0).then(|| format!("v{r}=0x{v:032x}"))
                    })
                    .collect();
                let mem_out: Vec<String> = st
                    .mem_out
                    .iter()
                    .map(|m| format!("[{}; {}B]={}", m.addr, m.size, m.val))
                    .collect();
                println!(
                    "  {label}  : pc={}, sp={}, nzcv=0x{:x}, regs=[{}]{}{}",
                    st.pc,
                    st.sp,
                    st.nzcv,
                    nz_regs.join(", "),
                    if nz_vregs.is_empty() {
                        String::new()
                    } else {
                        format!(", vregs=[{}]", nz_vregs.join(", "))
                    },
                    if mem_out.is_empty() {
                        String::new()
                    } else {
                        format!(", mem_out=[{}]", mem_out.join(", "))
                    }
                );
            }
        }
    }
    println!("----------------------------------------------------\n");
}

fn lookup_code_word(input: &TestInput, pc: u64) -> Option<u32> {
    for (base, words) in &input.code {
        if pc >= *base {
            let off = pc - *base;
            if off % 4 == 0 {
                let idx = (off / 4) as usize;
                if idx < words.len() {
                    return Some(words[idx]);
                }
            }
        }
    }
    None
}

/// Step [`LeanOracle`], [`UnicornOracle`], and [`SailOracle`] in lockstep across `suite`, diffing
/// full [`Outcome`] states after every instruction and reporting the first divergent instruction.
pub fn run_suite_lockstep(
    diff_eval_bin: &Path,
    suite: &[DiffTestCase],
    oracle_sel: OracleSelection,
    print_vectors: usize,
) -> Result<bool> {
    let mut lean_oracle = LeanOracle::new(diff_eval_bin).map_err(|e| anyhow!("{e}"))?;
    let mut uc_oracle = if oracle_sel.includes_unicorn() {
        Some(UnicornOracle::new().map_err(|e| anyhow!("{e}"))?)
    } else {
        None
    };
    let mut sail_oracle = if oracle_sel.includes_sail() {
        Some(SailOracle::new()?)
    } else {
        None
    };

    let policy = Policy {
        neutralize_unmodeled_to_nop: false,
        neutralize_non_nop_hints: false,
        sail_adjudicates_unicorn_fp_quirks: false,
        compare_fpsr: true,
        compare_fpcr: false,
        compare_tpidr_el0: false,
    };

    let mut passed = 0usize;
    let mut failed = 0usize;
    let mut total_words = 0usize;
    let mut executed_all = 0usize;
    let mut skipped_sail = 0usize;
    let mut unmodeled_decode = 0usize;
    let mut exec_exception = 0usize;
    let mut locked_states = Vec::with_capacity(suite.len().min(print_vectors));
    let mut failure_reports: Vec<(String, Vec<String>)> = Vec::new();

    for (case_idx, tc) in suite.iter().enumerate() {
        let input = tc.to_test_input()?;
        let case_word_count: usize = input.code.iter().map(|(_, w)| w.len()).sum();
        total_words += case_word_count;

        let use_unicorn = uc_oracle.is_some();
        let use_sail = sail_oracle.is_some() && tc.skip_sail.is_none();
        let has_exclusive_ls = input
            .code
            .iter()
            .any(|(_, words)| words.iter().any(|&w| (w & 0x3f00_0000) == 0x0800_0000));

        lean_oracle
            .load(&input)
            .map_err(|e| anyhow!("LeanOracle::load failed on `{}`: {e}", tc.name))?;
        if let Some(uc) = uc_oracle.as_mut() {
            uc.load(&input)
                .map_err(|e| anyhow!("UnicornOracle::load failed on `{}`: {e}", tc.name))?;
        }
        if use_sail && let Some(sail) = sail_oracle.as_mut() {
            sail.load(&input)
                .map_err(|e| anyhow!("SailOracle::load failed on `{}`: {e}", tc.name))?;
        }

        let mut cur_pc = input.state.pc;
        let mut case_mismatches: Vec<String> = Vec::new();
        let mut last_lean: Option<Outcome> = None;
        let mut last_uc: Option<Outcome> = None;
        let mut last_sail: Option<Outcome> = None;
        let mut case_unmodeled = false;
        let mut case_exception = false;

        for step_idx in 1..=input.max_steps {
            if cur_pc == input.exit_pc {
                break;
            }
            let insn_word = lookup_code_word(&input, cur_pc).unwrap_or(0);

            let l_out = lean_oracle.step();
            let u_out = if use_unicorn {
                let uc = uc_oracle.as_mut().unwrap();
                Some(if has_exclusive_ls {
                    let mut prefix = input.clone();
                    prefix.exit_pc = NO_EXIT_PC;
                    prefix.max_steps = step_idx;
                    uc.run(&prefix)
                } else {
                    uc.step()
                })
            } else {
                None
            };
            let s_out = if use_sail {
                Some(sail_oracle.as_mut().unwrap().step())
            } else {
                None
            };

            match &l_out {
                Outcome::Unmodeled { pc, word } => {
                    case_unmodeled = true;
                    case_mismatches.push(format!(
                        "step {step_idx} (pc=0x{pc:016x}, insn=0x{word:08x}): decode_error (unmodeled instruction)"
                    ));
                    last_lean = Some(l_out);
                    last_uc = u_out;
                    last_sail = s_out;
                    break;
                }
                Outcome::Fault { .. } | Outcome::StepLimit { .. } | Outcome::OracleError(_) => {
                    case_exception = true;
                    case_mismatches.push(format!(
                        "step {step_idx} (pc=0x{cur_pc:016x}, insn=0x{insn_word:08x}): Lean terminated with {}",
                        l_out.summary()
                    ));
                    last_lean = Some(l_out);
                    last_uc = u_out;
                    last_sail = s_out;
                    break;
                }
                Outcome::Ok { .. } => {}
            }

            if let Some(ref uo) = u_out {
                let u_diffs = diff(&l_out, uo, &policy);
                for d in u_diffs {
                    case_mismatches.push(format!(
                        "step {step_idx} (pc=0x{cur_pc:016x}, insn=0x{insn_word:08x}): {}",
                        d.format_with_names("Lean", "Unicorn")
                    ));
                }
            }

            if let Some(ref so) = s_out {
                let s_diffs = diff(&l_out, so, &policy);
                for d in s_diffs {
                    case_mismatches.push(format!(
                        "step {step_idx} (pc=0x{cur_pc:016x}, insn=0x{insn_word:08x}): {}",
                        d.format_with_names("Lean", "Sail")
                    ));
                }
            }

            let next_pc = match &l_out {
                Outcome::Ok { state, .. } => state.pc,
                _ => cur_pc,
            };
            last_lean = Some(l_out);
            last_uc = u_out;
            last_sail = s_out;

            if !case_mismatches.is_empty() {
                break;
            }
            cur_pc = next_pc;
            if cur_pc == input.exit_pc {
                break;
            }
        }

        if case_mismatches.is_empty() && input.exit_pc != NO_EXIT_PC && cur_pc != input.exit_pc {
            case_exception = true;
            case_mismatches.push(format!(
                "step {} (pc=0x{cur_pc:016x}): StepLimitReached before reaching exit_pc=0x{:016x}",
                input.max_steps, input.exit_pc
            ));
        }

        if case_idx < print_vectors {
            locked_states.push(CaseLockedStates {
                lean: last_lean.as_ref().map(OracleState::from_outcome),
                unicorn: last_uc.as_ref().map(OracleState::from_outcome),
                sail: last_sail.as_ref().map(OracleState::from_outcome),
            });
        }

        if case_unmodeled {
            unmodeled_decode += 1;
        } else if case_exception {
            exec_exception += 1;
        } else if tc.skip_sail.is_some() {
            skipped_sail += 1;
        } else {
            executed_all += 1;
        }

        if case_mismatches.is_empty() {
            passed += 1;
        } else {
            failed += 1;
            failure_reports.push((tc.name.clone(), case_mismatches));
        }
    }

    if print_vectors > 0 {
        print_test_vectors(suite, &locked_states, print_vectors);
    }

    for (name, errs) in &failure_reports {
        println!("[FAIL] {name}:");
        for m in errs.iter().take(8) {
            println!("    {m}");
        }
    }

    println!(
        "\nDifferential Validation Summary (Rust lockstep `Arm64Oracle`: Lean `diff_eval --serve` vs Unicorn `UC_ARCH_ARM64` + Sail `armv9.4-a`, mode={}):",
        oracle_sel.as_cli_str()
    );
    println!("  Total test cases        : {}", suite.len());
    println!("  Total instruction words : {total_words}");
    println!(
        "  Outcome classification  : executed_all_oracles={executed_all}, skipped_sail={skipped_sail}, unmodeled_decode={unmodeled_decode}, exec_exception={exec_exception}"
    );
    println!("  Passed                  : {passed}");
    println!("  Failed                  : {failed}");

    Ok(failed == 0)
}

/// Run the full differential test suite against both Unicorn and Sail in lockstep.
pub fn run_differential_validation(
    repo_root: &Path,
    explicit_diff_eval_bin: Option<&Path>,
    input_json_path: Option<&Path>,
    filter: Option<&str>,
) -> Result<bool> {
    run_differential_validation_with_oracle(
        repo_root,
        explicit_diff_eval_bin,
        input_json_path,
        filter,
        OracleSelection::All,
    )
}

/// Run the differential test suite against `oracle_sel` (`All`, `Unicorn`, or `Sail`) in lockstep.
pub fn run_differential_validation_with_oracle(
    repo_root: &Path,
    explicit_diff_eval_bin: Option<&Path>,
    input_json_path: Option<&Path>,
    filter: Option<&str>,
    oracle_sel: OracleSelection,
) -> Result<bool> {
    run_differential_validation_with_options(
        repo_root,
        explicit_diff_eval_bin,
        input_json_path,
        filter,
        oracle_sel,
        0,
    )
}

/// Run the differential test suite against `oracle_sel` (`All`, `Unicorn`, or `Sail`), optionally
/// printing up to `print_vectors` populated test vectors.
pub fn run_differential_validation_with_options(
    repo_root: &Path,
    explicit_diff_eval_bin: Option<&Path>,
    input_json_path: Option<&Path>,
    filter: Option<&str>,
    oracle_sel: OracleSelection,
    print_vectors: usize,
) -> Result<bool> {
    run_differential_validation_ext(
        repo_root,
        explicit_diff_eval_bin,
        input_json_path,
        filter,
        oracle_sel,
        print_vectors,
        false,
    )
}

/// Run the differential test suite against `oracle_sel` (`All`, `Unicorn`, or `Sail`), optionally
/// printing up to `print_vectors` populated test vectors and optionally skipping the 504k fuzz
/// pass when `suite_only` is true.
pub fn run_differential_validation_ext(
    repo_root: &Path,
    explicit_diff_eval_bin: Option<&Path>,
    input_json_path: Option<&Path>,
    filter: Option<&str>,
    oracle_sel: OracleSelection,
    print_vectors: usize,
    suite_only: bool,
) -> Result<bool> {
    let diff_eval_bin = ensure_diff_eval_bin(repo_root, explicit_diff_eval_bin)?;

    let mut suite = match input_json_path {
        Some(path) => {
            let bytes =
                fs::read(path).with_context(|| format!("failed to read `{}`", path.display()))?;
            serde_json::from_slice::<Vec<DiffTestCase>>(&bytes)
                .with_context(|| format!("failed to parse JSON from `{}`", path.display()))?
        }
        None => load_lean_suite(&diff_eval_bin, repo_root)?,
    };

    if let Some(pat) = filter {
        suite.retain(|tc| tc.name.contains(pat));
    }

    println!(
        "Running {} test cases in lockstep against oracle={} (VIXL + Unicorn test_arm64 + C/Rust Subroutines + 100 Random Fuzz Blocks + Scalar FP)...",
        suite.len(),
        oracle_sel.as_cli_str()
    );

    populate_words(&mut suite)?;
    let suite_ok = run_suite_lockstep(&diff_eval_bin, &suite, oracle_sel, print_vectors)?;
    if !suite_ok {
        return Ok(false);
    }

    if !suite_only
        && filter.is_none()
        && input_json_path.is_none()
        && oracle_sel == OracleSelection::All
    {
        let seed = resolve_head_sha_seed(repo_root);
        let cfg = fuzz::FuzzConfig {
            repo_root: repo_root.to_path_buf(),
            diff_eval_bin,
            seed,
            duration_secs: 0,
            cases_per_family: 500,
            report_path: None,
        };
        let report = fuzz::run_fuzz_campaign(&cfg)?;
        if !report.lean_vs_sail_mismatches.is_empty() {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Generate `count` freshly seeded random `IsaTestCase` blocks via `diff_eval --dump-random <seed> <count> <insns_per_block>`
/// and run them end-to-end through LLVM assembly and Rust lockstep comparison across Lean, Unicorn, and Sail.
pub fn run_random_suite_validation(
    repo_root: &Path,
    explicit_diff_eval_bin: Option<&Path>,
    seed: u64,
    count: usize,
    insns_per_block: usize,
    oracle_sel: OracleSelection,
    print_vectors: usize,
) -> Result<bool> {
    let diff_eval_bin = ensure_diff_eval_bin(repo_root, explicit_diff_eval_bin)?;
    println!(
        "Generating {count} freshly seeded random IsaTestCase block(s) (seed=0x{seed:016x}, insns_per_block={insns_per_block}) via `diff_eval --dump-random`..."
    );
    let mut suite = load_random_suite(&diff_eval_bin, repo_root, seed, count, insns_per_block)?;
    populate_words(&mut suite)?;
    run_suite_lockstep(&diff_eval_bin, &suite, oracle_sel, print_vectors)
}

/// Derive a deterministic 64-bit RNG seed from `git rev-parse HEAD` (first 16 hex digits).
pub fn resolve_head_sha_seed(repo_root: &Path) -> u64 {
    if let Ok(out) = Command::new("git")
        .arg("rev-parse")
        .arg("HEAD")
        .current_dir(repo_root)
        .output()
        && out.status.success()
    {
        let s = String::from_utf8_lossy(&out.stdout);
        let hex = s.trim();
        if hex.len() >= 16
            && let Ok(val) = u64::from_str_radix(&hex[..16], 16)
        {
            return val;
        }
    }
    0x2026_1014_dead_beef
}

/// Resolve the repository root (`../..` from `tools/run-trusted-tests`, else nearest ancestor
/// containing `lakefile.lean` and `Arm64/`, else current directory).
pub fn default_repo_root() -> PathBuf {
    let is_root = |d: &Path| d.join("lakefile.lean").is_file() && d.join("Arm64").is_dir();
    let from_manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    if is_root(&from_manifest) {
        return from_manifest.canonicalize().unwrap_or(from_manifest);
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    cwd.ancestors()
        .find(|d| is_root(d))
        .map(Path::to_path_buf)
        .unwrap_or(cwd)
}

#[cfg(test)]
mod staleness_tests {
    use super::*;

    #[test]
    fn diff_eval_input_hash_tracks_root_configs_and_sources() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        fs::create_dir_all(root.join("Arm64/Testing")).unwrap();
        fs::create_dir_all(root.join("ProofLib")).unwrap();
        fs::write(root.join("lakefile.lean"), "-- v1\n").unwrap();
        fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.34.0\n").unwrap();
        fs::write(root.join("lake-manifest.json"), "{}\n").unwrap();
        fs::write(root.join("Arm64/Testing/lakefile.lean"), "name = \"arm64-testing\"\n").unwrap();
        fs::write(root.join("Arm64.lean"), "import Arm64.Trusted\n").unwrap();
        fs::write(root.join("Arm64/Testing/A.lean"), "def a := 1\n").unwrap();
        fs::write(root.join("ProofLib/B.lean"), "def b := 1\n").unwrap();

        let mut prev = diff_eval_input_hash(root).unwrap();
        for (rel, updated) in [
            ("lakefile.lean", "-- v2\n"),
            ("lean-toolchain", "leanprover/lean4:v4.35.0\n"),
            ("lake-manifest.json", "{\"version\": 7}\n"),
            ("Arm64/Testing/lakefile.lean", "name = \"arm64-testing\" -- v2\n"),
            ("Arm64.lean", "import Arm64.Trusted -- v2\n"),
            ("Arm64/Testing/A.lean", "def a := 2\n"),
            ("ProofLib/B.lean", "def b := 2\n"),
        ] {
            fs::write(root.join(rel), updated).unwrap();
            let next = diff_eval_input_hash(root).unwrap();
            assert_ne!(
                prev, next,
                "{rel} modification must update diff_eval fingerprint"
            );
            prev = next;
        }
    }
}
