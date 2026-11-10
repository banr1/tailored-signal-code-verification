// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Canonical oracle comparison, masking rules, and outcome classification (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (Rust-side counterpart to `Arm64/Testing/Harness/Compare.lean`).
//! - **Purpose:** Defines in one place how outputs from the Lean 4 ISA evaluator (`diff_eval`),
//!   official ARM Sail (`armv9.4-a`), Unicorn Engine (`UC_ARCH_ARM64` / `UC_CPU_ARM64_MAX`),
//!   Berkeley SoftFloat 3e (`ARM-VFPv2`), IBM FPgen, and the Linux kernel (`binfmt_elf` + VFS)
//!   are compared, what state fields are masked or canonicalized, and how unmodeled,
//!   `.Exception`, and oracle-quirk outcomes are classified and counted.
//!
//! # Oracle × Compared-Fields Matrix
//!
//! | Mode / Harness | Oracles Compared | `X0..X30` | `V0..V31` (128b) | `SP` | `PC` | `NZCV` (4b) | `FPSR` (32b) | Memory | Status / Outcome |
//! |---|---|---|---|---|---|---|---|---|---|
//! | Multi-step lockstep (`Arm64Oracle::step`) | `LeanOracle` (`diff_eval --serve`) vs `UnicornOracle` + `SailOracle` (`skip_sail` on 2 cases) | All 31 64-bit GP regs (per step) | All 32 128-bit SIMD/FP regs (per step) | 64-bit `SP` (per step) | 64-bit `PC` (per step) | 4-bit `(N,Z,C,V)` (per step) | Masked `0x0800_009f` (per step) | Explicit `watch` ranges `(addr, bytes)` (per step) | [`isa_oracle::Outcome::Ok`] at every step until `exit_pc` |
//! | Single-insn batch (`Arm64Oracle::run_batch`) | `LeanOracle` (`diff_eval --serve`) vs `SailOracle` (authoritative) + `UnicornOracle` | All 31 64-bit GP regs (`isa_oracle::diff`) | All 32 128-bit SIMD/FP regs (`isa_oracle::diff`) | 64-bit `SP` (`isa_oracle::diff`) | 64-bit `PC` (`isa_oracle::diff`) | 4-bit `NZCV` (`isa_oracle::diff`) | Masked `0x0800_009f` (`isa_oracle::diff`) | 64-byte scratch `[0x20000, 0x20040)` (`isa_oracle::diff`) | Typed [`isa_oracle::Outcome`] (`Ok`, `Unmodeled`, `Fault`) |
//! | Pure IEEE-754 batch (`diff_eval --batch-fp`) | Lean FP ops vs SoftFloat 3e (`ARM-VFPv2`) + IBM FPgen | — | 32/64-bit IEEE-754 result bit-for-bit | — | — | 4-bit `NZCV` for `FCMP`/`FCMPE` (`op = 20, 22, 52, 54`) | 5-bit IEEE-754 flags (`0x1f`) | — | Trapped IEEE-754-1985 `u`/`o` lines counted & skipped; symbolic `Q` NaN canonicalized |
//! | Linux VFS & ELF (`fs_linux_diff_tests`, `lld_diff`) | Lean `FsState` / `LinkedImage.load` vs host Linux kernel | Syscall return `x0` (27 trace outputs) | — | — | Entry/exit `PC` | — | — | File contents, fd offsets, `PT_LOAD` page perms & bytes | Exact `errno` / byte / permission equality |
//!
//! # Masking, Canonicalization & Adjudication Rules
//! 1. **Unmodeled decode ([`Outcome::Unmodeled`], `Arm64.decode w = none`)**:
//!    Counted in [`OutcomeCounts::unmodeled_decode`]. Neutralized to `NOP` (`0xd503_201f`) via
//!    [`Policy::should_neutralize_for_reference`] before reference-oracle batch execution; never
//!    silently dropped.
//! 2. **Execution exception ([`Outcome::Fault`], `sf.status != .Running`)**:
//!    Counted in [`OutcomeCounts::exec_exception`] (e.g., misaligned `SP` or unmapped memory
//!    outside `[0x20000, 0x20040)`).
//! 3. **Non-NOP `HINT` encodings (`0xd503_201f` family outside `CRm:op2 ∈ {0,1,4,5,16,20,22}`)**:
//!    Armv8.3+ PAC (`PACIA1716`, `AUTIA1716`, `XPACLRI`) and Armv8.5+ BTI hints in the `HINT`
//!    encoding space mutate `X16`/`X17`/`X30` or `PSTATE.BTYPE` in Sail Armv9.4-A, whereas Lean
//!    models the `HINT` space as architectural `NOP`. Counted in
//!    [`OutcomeCounts::non_nop_hint_neutralized`] and rewritten to `NOP` (`0xd503_201f`) before
//!    invoking Sail/Unicorn.
//! 4. **Unicorn QEMU 5.0 TCG FP/SIMD quirks (`unicorn_fp_quirks_adjudicated_by_sail`)**:
//!    When Lean and official ARM Sail (`armv9.4-a`) agree bit-for-bit across all [`CpuState`] and
//!    watched memory fields ([`isa_oracle::diff`]) but Unicorn disagrees, Sail is authoritative and
//!    the divergence is counted in [`OutcomeCounts::unicorn_fp_quirks_adjudicated_by_sail`].
//! 5. **IBM FPgen IEEE 754-1985 trapped underflow/overflow (`fpgen_trapped_exception_skipped`)**:
//!    FPgen lines where `u` (underflow) or `o` (overflow) is both trap-enabled on the LHS and
//!    raised on the RHS specify the IEEE 754-1985 §7.3/§7.4 trap-handler exponent-wrapped
//!    (`E ± 192`) result rather than the untrapped IEEE-754 value produced by ARM64 instructions
//!    (`FPCR.UFE=0, OFE=0`). Counted in [`OutcomeCounts::fpgen_trapped_exception_skipped`].
//! 6. **IBM FPgen symbolic `Q` quiet-NaN results (`fpgen_nan_canonicalized`)**:
//!    FPgen writes symbolic `Q` (`0x7fc0_0000`) for any quiet NaN without fixing an architecture
//!    payload; when `exp_val`, `lean_val`, and `softfloat_val` are all `binary32` NaNs, the case is
//!    counted in [`OutcomeCounts::fpgen_nan_canonicalized`] (while `TestFloat` and `stratified_fp`
//!    still check Lean's exact ARM64 Default NaN `0x7fc0_0000` bit-for-bit against SoftFloat).

pub use isa_oracle::{AARCH64_NOP_WORD, Outcome, Policy, TestInput, ThreeWayVerdict, is_non_nop_hint_encoding};
use serde::{Deserialize, Serialize};

/// Explicit classification counts across single-instruction and FP differential batches.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OutcomeCounts {
    /// Cases where Lean executed to completion and was compared against the authoritative oracle.
    pub executed_compared: u64,
    /// Single-instruction records where `Arm64.decode w = none` (`l_status == 1`).
    pub unmodeled_decode: u64,
    /// Single-instruction records where `execInst` raised `.Exception` / `.Fault` (`l_status == 2`).
    pub exec_exception: u64,
    /// Single-instruction records in the `HINT` space outside `{0,1,4,5,16,20,22}` rewritten to `NOP`.
    pub non_nop_hint_neutralized: u64,
    /// Cases where Lean matched Sail Armv9.4-A bit-for-bit but Unicorn (QEMU 5.0 TCG) diverged.
    pub unicorn_fp_quirks_adjudicated_by_sail: u64,
    /// IBM FPgen lines with IEEE 754-1985 trapped overflow/underflow (`E ± 192` exponent wrapping).
    pub fpgen_trapped_exception_skipped: u64,
    /// IBM FPgen lines with symbolic `Q` NaN where both Lean and SoftFloat produced quiet NaNs.
    pub fpgen_nan_canonicalized: u64,
}

/// Returns `true` if an IBM FPgen test vector has trap-enabled underflow (`u`) or overflow (`o`)
/// on the LHS that is also raised on the RHS (IEEE 754-1985 §7.3/§7.4 `E ± 192` trap-handler result).
#[inline]
pub fn is_fpgen_trapped_underflow_or_overflow(lhs_traps: &str, rhs_excs: &str) -> bool {
    (lhs_traps.contains('u') && rhs_excs.contains('u'))
        || (lhs_traps.contains('o') && rhs_excs.contains('o'))
}

/// Returns `true` if the low 32 bits of `v` represent an IEEE-754 `binary32` NaN.
#[inline]
pub fn is_f32_nan_bits(v: u64) -> bool {
    ((v as u32) & 0x7fff_ffff) > 0x7f80_0000
}

/// Compare a single IBM FPgen `binary32` result across Lean, SoftFloat, and the FPgen expected word,
/// updating `counts` and returning `Ok(())` on match or `Err(mismatch_description)` on mismatch.
pub fn compare_fpgen_result(
    line_str: &str,
    lean_val: u64,
    sf_val: u64,
    exp_val: u64,
    counts: &mut OutcomeCounts,
) -> Result<(), String> {
    counts.executed_compared += 1;
    if is_f32_nan_bits(lean_val) && is_f32_nan_bits(sf_val) && is_f32_nan_bits(exp_val) {
        counts.fpgen_nan_canonicalized += 1;
        return Ok(());
    }
    if lean_val == exp_val && sf_val == exp_val {
        return Ok(());
    }
    Err(format!(
        "FPgen mismatch on `{line_str}`: Lean=0x{lean_val:08x}, SoftFloat=0x{sf_val:08x}, FPgen=0x{exp_val:08x}"
    ))
}

/// Compare a batch of 4-word `FpBatchRecord` outputs (`(val, flags)` pairs per record) between
/// Lean (`diff_eval --batch-fp`) and Berkeley SoftFloat 3e (`ARM-VFPv2`), updating `counts` and
/// appending any mismatches.
///
/// Value outputs (`out[2 * i]`) and 5-bit `FPSR` exception flags (`out[2 * i + 1]`) are
/// compared across all records and all five IEEE-754 rounding modes (`RNE`, `RTP`, `RTN`, `RTZ`,
/// `RNA`).
pub fn compare_softfloat_batch(
    records: &[u64],
    lean_out: &[u64],
    sf_out: &[u64],
    suite_label: &str,
    counts: &mut OutcomeCounts,
    mismatches: &mut Vec<String>,
) {
    let count = records.len() / 4;
    assert_eq!(lean_out.len(), count * 2);
    assert_eq!(sf_out.len(), count * 2);
    counts.executed_compared += count as u64;
    for i in 0..count {
        let meta = records[i * 4];
        let op = meta & 0xff;
        let rm = (meta >> 8) & 0xff;
        let a = records[i * 4 + 1];
        let b = records[i * 4 + 2];
        let c = records[i * 4 + 3];
        let l_val = lean_out[i * 2];
        let l_flags = lean_out[i * 2 + 1];
        let s_val = sf_out[i * 2];
        let s_flags = sf_out[i * 2 + 1];
        if l_val != s_val {
            mismatches.push(format!(
                "{suite_label} value mismatch op={op} rm={rm}: a=0x{a:x} b=0x{b:x} c=0x{c:x} -> Lean=0x{l_val:x} vs SoftFloat=0x{s_val:x}"
            ));
        }
        if l_flags != s_flags {
            mismatches.push(format!(
                "{suite_label} FPSR flag mismatch op={op} rm={rm}: a=0x{a:x} b=0x{b:x} c=0x{c:x} -> Lean flags=0x{l_flags:02x} vs SoftFloat flags=0x{s_flags:02x} (Lean val=0x{l_val:x}, SF val=0x{s_val:x})"
            ));
        }
    }
}

/// Classify Lean's single-instruction [`Outcome`]s and prepare reference-oracle [`TestInput`]s
/// according to `policy` (rewriting unmodeled, faulting, and non-NOP `HINT` records to `NOP`
/// while updating exact [`OutcomeCounts`]).
///
/// Any [`Outcome::OracleError`] from Lean (such as a `diff_eval --serve` crash, EOF, protocol
/// error, or batch count mismatch) is treated as a hard harness error (`Err`) rather than an
/// `exec_exception`, preventing fail-open skips.
pub fn prepare_and_classify_test_inputs(
    inputs: &[TestInput],
    lean_out: &[Outcome],
    policy: &Policy,
    counts: &mut OutcomeCounts,
) -> Result<Vec<TestInput>, String> {
    if inputs.len() != lean_out.len() {
        return Err(format!(
            "LeanOracle batch outcome count mismatch: expected {}, got {}",
            inputs.len(),
            lean_out.len()
        ));
    }
    let mut active = Vec::with_capacity(inputs.len());
    for (idx, (inp, l_out)) in inputs.iter().zip(lean_out.iter()).enumerate() {
        let non_nop_hint = policy.neutralize_non_nop_hints
            && inp.entry_word().is_some_and(is_non_nop_hint_encoding);
        match l_out {
            Outcome::Ok { .. } => {
                if non_nop_hint {
                    counts.non_nop_hint_neutralized += 1;
                } else {
                    counts.executed_compared += 1;
                }
            }
            Outcome::Unmodeled { .. } => counts.unmodeled_decode += 1,
            Outcome::Fault { .. } | Outcome::StepLimit { .. } => {
                counts.exec_exception += 1;
            }
            Outcome::OracleError(msg) => {
                return Err(format!("LeanOracle error at record {idx}: {msg}"));
            }
        }
        let neutralize = match l_out {
            Outcome::Ok { .. } => non_nop_hint && policy.neutralize_non_nop_hints,
            Outcome::Unmodeled { .. } | Outcome::Fault { .. } | Outcome::StepLimit { .. } => {
                policy.neutralize_unmodeled_to_nop
            }
            Outcome::OracleError(_) => unreachable!("OracleError returned above"),
        };
        if neutralize {
            active.push(inp.neutralized_to_nop());
        } else {
            active.push(inp.clone());
        }
    }
    Ok(active)
}

/// Compare full-state [`Outcome`]s across Lean, authoritative Sail Armv9.4-A, and optional Unicorn
/// using [`isa_oracle::diff`] and [`Policy::adjudicate_three_way`].
pub fn compare_oracle_batch_outcomes(
    inputs: &[TestInput],
    lean_out: &[Outcome],
    sail_out: &[Outcome],
    uc_out: Option<&[Outcome]>,
    policy: &Policy,
    tag: &str,
    counts: &mut OutcomeCounts,
    mismatches: &mut Vec<String>,
) {
    assert_eq!(inputs.len(), lean_out.len());
    assert_eq!(inputs.len(), sail_out.len());
    if let Some(uo) = uc_out {
        assert_eq!(inputs.len(), uo.len());
    }
    for idx in 0..inputs.len() {
        let inp = &inputs[idx];
        let l_out = &lean_out[idx];
        let non_nop_hint = policy.neutralize_non_nop_hints
            && inp.entry_word().is_some_and(is_non_nop_hint_encoding);
        if matches!(l_out, Outcome::Ok { .. }) && !non_nop_hint {
            let s_out = &sail_out[idx];
            let u_out = uc_out.map(|u| &u[idx]);
            match policy.adjudicate_three_way(l_out, s_out, u_out) {
                ThreeWayVerdict::Match => {}
                ThreeWayVerdict::UnicornQuirkAdjudicatedBySail { .. } => {
                    counts.unicorn_fp_quirks_adjudicated_by_sail += 1;
                }
                ThreeWayVerdict::Mismatch {
                    oracle_name,
                    mismatches: fields,
                } => {
                    let insn = inp.entry_word().unwrap_or(0);
                    let summary: Vec<String> = fields
                        .iter()
                        .take(6)
                        .map(|m| m.format_with_names("Lean", oracle_name))
                        .collect();
                    mismatches.push(format!(
                        "[{tag}] insn=0x{insn:08x} (pc=0x{:016x}, nzcv=0x{:x}): {}",
                        inp.state.pc,
                        inp.state.nzcv,
                        summary.join("; ")
                    ));
                }
            }
        }
    }
}
