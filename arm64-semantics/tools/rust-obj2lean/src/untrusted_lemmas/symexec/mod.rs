// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Fast Untrusted ARM64 Symbolic Execution Advisor (`symexec`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (pure read-only advisor reading `*Index.json` and
//!   `*Obj.code.bin` or `--hex` words to emit human/JSON proof advice for `rust-obj2lean symexec`
//!   and `lean-sig symexec`; never modifies trusted `Obj` definitions).
//! - **Purpose:** Provides sub-5ms multi-path symbolic execution, stack-slot & memory footprint
//!   tracking, and Lean 4 `BitVec` expression synthesis for AArch64 functions.
//!
//! # Key Types & Functions
//! - Submodules & re-exports:
//!   - [`insn_semantics`]: [`StepOutcome`], [`step_instruction`], [`eval_shifted_reg`],
//!     [`eval_extended_reg`].
//!   - [`expr`]: [`SymExpr`], [`FlagState`], [`SymCond`], [`Nzcv`], [`ConcreteContext`].
//!   - [`state`]: [`SymState`], [`MemAccessRecord`], [`CallSiteRecord`], [`BranchRecord`].
//!   - [`driver`]: [`analyze_and_execute`], [`run_symexec`], [`run_symexec_cli`].
//!   - [`emit`]: [`SymexecArgs`], [`SymexecReport`], [`format_report_text`].
//!   - [`hints`]: per-path block-hint certificates (`--block-hints`, `--block-hints-json`):
//!     [`BlockHintsReport`], [`HintStep`], [`format_block_hints_text`].
//!   - [`source`]: DWARF `file:line`, live-variable and `param->field` annotations.
//!
//! # When to Read This File
//! - Read this file only for the re-export surface or in-module unit tests; read the specific
//!   submodule (`insn_semantics.rs`, `expr.rs`, `state.rs`, `driver.rs`, `emit.rs`) for logic.

pub mod atomics;
pub mod driver;
pub mod emit;
pub mod expr;
pub mod hints;
pub mod insn_semantics;
pub mod source;
pub mod state;

pub use driver::{
    analyze_and_execute, analyze_and_execute_with_limits, block_hints_report, run_symexec,
    run_symexec_cli,
};
pub use emit::{
    DisasmLine, PathSnapshot, StackSlotSummary, SymexecArgs, SymexecReport, format_report_text,
};
pub use expr::{
    BinOpKind, BitfieldOp, ConcreteContext, FlagState, Nzcv, SymCond, SymExpr, SymMemWrite,
    UnaryOpKind, add_with_carry_32, add_with_carry_64, condition_holds, eval_add_sub_with_carry,
    eval_binop, eval_bitfield, eval_extr, eval_unary, fmt_operand_for_width, format_bv64,
    negate_cond_str, reg_name, render_cond,
};
pub use hints::{
    BlockHintsReport, HintAddr, HintLine, HintStep, PathHints, format_block_hints_text,
};
pub use insn_semantics::{StepOutcome, eval_extended_reg, eval_shifted_reg, step_instruction};
pub use state::{
    BranchRecord, CallSiteRecord, ConcreteMachineState, DEFAULT_MAX_EXPR_NODES,
    LET_BINDING_NODE_THRESHOLD, MemAccessRecord, SymState,
};

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use clap::Parser;

    use super::*;

    fn words_to_bytes(ws: &[u32]) -> Vec<u8> {
        ws.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    #[test]
    fn symexec_stack_frame_and_arithmetic_folding() {
        // Prologue + spill + reload + epilogue:
        // 0x00: sub sp, sp, #0x20         (0xd10083ff)
        // 0x04: stp x29, x30, [sp, #0x10] (0xa9017bfd)
        // 0x08: add x0, x0, #0x5          (0x91001400)
        // 0x0c: str x0, [sp, #0x8]        (0xf90007e0)
        // 0x10: ldr x1, [sp, #0x8]        (0xf94007e1)
        // 0x14: add x0, x1, #0x3          (0x91000c20)
        // 0x18: ldp x29, x30, [sp, #0x10] (0xa9417bfd)
        // 0x1c: add sp, sp, #0x20         (0x910083ff)
        // 0x20: ret                       (0xd65f03c0)
        let code = words_to_bytes(&[
            0xd100_83ff,
            0xa901_7bfd,
            0x9100_1400,
            0xf900_07e0,
            0xf940_07e1,
            0x9100_0c20,
            0xa941_7bfd,
            0x9100_83ff,
            0xd65f_03c0,
        ]);
        let report = analyze_and_execute(
            "demo_stack_fold",
            0,
            &code,
            None,
            0,
            &BTreeSet::new(),
            &BTreeMap::new(),
            &[],
            64,
            8,
        )
        .unwrap();

        assert_eq!(report.prologue_frame_bytes, Some(32));
        assert_eq!(report.stack_slots.len(), 3);
        assert_eq!(report.stack_slots[0].sp_offset, -24);
        assert_eq!(report.stack_slots[0].addr_lean, "(sp - 0x18#64)");
        assert_eq!(report.stack_slots[1].sp_offset, -16);
        assert_eq!(report.stack_slots[1].addr_lean, "(sp - 0x10#64)");
        assert_eq!(report.stack_slots[2].sp_offset, -8);
        assert_eq!(report.stack_slots[2].addr_lean, "(sp - 0x8#64)");

        assert_eq!(report.snapshots.len(), 1);
        let snap = &report.snapshots[0];
        // `(x0 + 5) + 3` folds to `(x0 + 0x8#64)`, and `sp`, `x29`, `x30` are restored to entry values!
        assert_eq!(
            snap.modified_regs.get("x0").map(String::as_str),
            Some("(x0 + 0x8#64)")
        );
        assert!(!snap.modified_regs.contains_key("sp"));
        assert!(!snap.modified_regs.contains_key("x29"));
        assert!(!snap.modified_regs.contains_key("x30"));
    }

    #[test]
    fn symexec_branches_and_cuts() {
        // 0x00: cmp x0, #0xa     (subs xzr, x0, #0xa -> 0xf100281f)
        // 0x04: b.hi +0xc (0x10) (0x54000068)
        // 0x08: add x0, x0, #1   (0x91000400)
        // 0x0c: ret              (0xd65f03c0)
        // 0x10: movz x0, #0xff   (0xd2801fe0)
        // 0x14: ret              (0xd65f03c0)
        let code = words_to_bytes(&[
            0xf100_281f,
            0x5400_0068,
            0x9100_0400,
            0xd65f_03c0,
            0xd280_1fe0,
            0xd65f_03c0,
        ]);
        let report = analyze_and_execute(
            "branch_demo",
            0,
            &code,
            None,
            0,
            &BTreeSet::new(),
            &BTreeMap::new(),
            &[],
            64,
            8,
        )
        .unwrap();
        assert_eq!(report.branches.len(), 1);
        assert_eq!(report.branches[0].cond_lean, "(0xa#64 <ᵤ x0)");
        assert_eq!(report.branches[0].taken_offset, 0x10);
        assert_eq!(report.branches[0].fallthrough_offset, 0x8);
        assert_eq!(report.snapshots.len(), 2);
        assert_eq!(
            report.snapshots[0].modified_regs.get("x0").map(String::as_str),
            Some("(x0 + 0x1#64)")
        );
        assert_eq!(
            report.snapshots[1].modified_regs.get("x0").map(String::as_str),
            Some("0xff#64")
        );
    }

    #[test]
    fn symexec_lsl_imm_blr_and_unsupported_sysreg() {
        let callees = BTreeMap::new();
        let mut accesses = Vec::new();
        let mut calls = Vec::new();

        // 1. `lsl x4, x0, #7` (`ubfm x4, x0, #57, #56` -> 0xd379_e004) must simplify to `BinOpKind::Lsl`,
        //    not `SymExpr::Bitfield`.
        let mut state = SymState::new(0);
        let out = step_instruction(
            0xd379_e004,
            &mut state,
            &callees,
            16,
            &mut accesses,
            &mut calls,
        );
        assert!(matches!(out, StepOutcome::Next));
        assert!(
            matches!(
                &state.regs[4],
                SymExpr::BinOp {
                    op_kind: Some(BinOpKind::Lsl),
                    width: 64,
                    ..
                }
            ),
            "expected BinOpKind::Lsl for lsl x4, x0, #7, got {:?}",
            state.regs[4]
        );
        assert_eq!(state.regs[4].to_lean(), "(x0 <<< 0x7#64)");

        // 2. `blr x8` (`0xd63f_0100`) after flag-setting `cmp x0, #1` must update `x30` and clobber `flags`.
        let _ = step_instruction(
            0xf100_041f, // cmp x0, #1
            &mut state,
            &callees,
            16,
            &mut accesses,
            &mut calls,
        );
        assert!(!matches!(state.flags, FlagState::Unknown));
        let out_blr = step_instruction(
            0xd63f_0100, // blr x8 at pc = 0x8 -> next_pc = 0xc
            &mut state,
            &callees,
            16,
            &mut accesses,
            &mut calls,
        );
        assert!(matches!(out_blr, StepOutcome::Next));
        assert_eq!(state.regs[30].to_lean(), "(fn_entry + 0xc#64)");
        assert!(matches!(state.flags, FlagState::Unknown));

        // 3. Unsupported system register (`mrs x0, nzcv` -> 0xd53b_4200) must halt.
        let out_sys = step_instruction(
            0xd53b_4200,
            &mut state,
            &callees,
            16,
            &mut accesses,
            &mut calls,
        );
        assert!(
            matches!(out_sys, StepOutcome::Halted { ref reason, .. } if reason.contains("unsupported sysreg")),
            "expected Halted on unsupported sysreg, got {:?}",
            out_sys
        );
    }

    #[test]
    fn symexec_multi_round_arx_sipround_let_bindings_fast_and_compact() {
        // 12-instruction SipRound on x0 (v0), x1 (v1), x2 (v2), x3 (v3):
        //   add x0, x0, x1        (0x8b010000)
        //   add x2, x2, x3        (0x8b030042)
        //   ror x1, x1, #51       (extr x1, x1, x1, #51 -> 0x93c1cc21)
        //   ror x3, x3, #48       (extr x3, x3, x3, #48 -> 0x93c3c063)
        //   eor x1, x1, x0        (0xca000021)
        //   eor x3, x3, x2        (0xca020063)
        //   ror x0, x0, #32       (extr x0, x0, x0, #32 -> 0x93c08000)
        //   add x2, x2, x1        (0x8b010042)
        //   add x0, x0, x3        (0x8b030000)
        //   ror x1, x1, #47       (extr x1, x1, x1, #47 -> 0x93c1bc21)
        //   ror x3, x3, #43       (extr x3, x3, x3, #43 -> 0x93c3ac63)
        //   eor x1, x1, x2        (0xca020021)
        //   eor x3, x3, x0        (0xca000063)
        //   ror x2, x2, #32       (extr x2, x2, x2, #32 -> 0x93c28042)
        let sip_round: [u32; 14] = [
            0x8b01_0000,
            0x8b03_0042,
            0x93c1_cc21,
            0x93c3_c063,
            0xca00_0021,
            0xca02_0063,
            0x93c0_8000,
            0x8b01_0042,
            0x8b03_0000,
            0x93c1_bc21,
            0x93c3_ac63,
            0xca02_0021,
            0xca00_0063,
            0x93c2_8042,
        ];
        let mut words = Vec::with_capacity(14 * 6 + 4);
        for _ in 0..6 {
            words.extend_from_slice(&sip_round);
        }
        // Final XOR fold: x0 = (x0 ^ x1) ^ (x2 ^ x3); ret
        words.push(0xca01_0000); // eor x0, x0, x1
        words.push(0xca03_0042); // eor x2, x2, x3
        words.push(0xca02_0000); // eor x0, x0, x2
        words.push(0xd65f_03c0); // ret

        let code = words_to_bytes(&words);
        let start = std::time::Instant::now();
        let report = analyze_and_execute(
            "sipround_arx_6rounds",
            0,
            &code,
            None,
            0,
            &BTreeSet::new(),
            &BTreeMap::new(),
            &[],
            256,
            8,
        )
        .unwrap();
        let text = format_report_text(&report);
        let elapsed = start.elapsed();

        assert!(
            elapsed.as_millis() < 500,
            "expected 6-round ARX symexec to finish in < 500ms, took {:?}",
            elapsed
        );
        assert!(
            text.len() < 10_000,
            "expected compact output (< 10 KB) with let-bindings, got {} bytes",
            text.len()
        );
        assert_eq!(report.snapshots.len(), 1);
        let snap = &report.snapshots[0];
        assert!(
            !snap.let_bindings.is_empty(),
            "expected intermediate let bindings to be emitted on 6-round ARX loop"
        );
        assert!(
            text.contains("let r"),
            "expected formatted report to render intermediate `let r... := ...` bindings:\n{text}"
        );
    }

    #[test]
    fn symexec_let_binding_feeds_cmp_csel_and_branch_eval() {
        // Build a >32-node chain in x0 via 2 rounds of SipRound (28 instructions), then:
        //   mov x4, x0          (0xaa0003e4)
        //   cmp x0, x4          (0xeb04001f -> Z=1, C=1)
        //   csel x5, x1, x2, eq (0x9a820025 -> should pick x1, not x2, even when x0 is a let-bound Var)
        let sip_round: [u32; 14] = [
            0x8b01_0000,
            0x8b03_0042,
            0x93c1_cc21,
            0x93c3_c063,
            0xca00_0021,
            0xca02_0063,
            0x93c0_8000,
            0x8b01_0042,
            0x8b03_0000,
            0x93c1_bc21,
            0x93c3_ac63,
            0xca02_0021,
            0xca00_0063,
            0x93c2_8042,
        ];
        let mut state = SymState::new(0);
        let callees = BTreeMap::new();
        let mut accesses = Vec::new();
        let mut calls = Vec::new();
        for _ in 0..2 {
            for &w in &sip_round {
                state.steps += 1;
                let _ = step_instruction(w, &mut state, &callees, 256, &mut accesses, &mut calls);
            }
        }
        assert!(
            !state.bindings.is_empty(),
            "expected let-bindings after 2 SipRounds"
        );
        // Add x4 = x0 + 7; cmp x4, x0 (so x4 != x0 and Z == 0 unless Var is wrongly treated as 0)
        // Actually test exact equality against expected concrete value:
        // Compare x0 against x1 after setting x1 := x0 ^ 0 (or compare x0 with a distinct register).
        // Let's compute concrete state on non-zero inputs and verify Cmp & Csel & CondBranch!
        let mut ctx = ConcreteContext::default();
        ctx.regs[0] = 0x736f_6d65_7073_6575;
        ctx.regs[1] = 0x646f_7261_6e64_6f6d;
        ctx.regs[2] = 0x6c79_6765_6e65_7261;
        ctx.regs[3] = 0x7465_6462_7974_6573;

        // Expected concrete x0 after 2 SipRounds:
        let pre_eval = state.eval_concrete(&ctx);
        let expected_x0 = pre_eval.regs[0];
        assert_ne!(expected_x0, 0);

        // Seed x4 with the exact concrete value `expected_x0` via `SymExpr::Const(expected_x0)`,
        // then run `cmp x0, x4` (`0xeb04_001f`) and `csel x5, x1, x2, eq` (`0x9a82_0025`).
        // If `FlagState::eval_nzcv_with_vars` or `SymCond::eval_with_vars` failed to thread
        // `let_bindings`, `x0` (`SymExpr::Var(...)`) would evaluate to `0 != expected_x0`!
        state.regs[4] = SymExpr::Const(expected_x0);
        state.steps += 1;
        let _ = step_instruction(
            0xeb04_001f, // cmp x0, x4
            &mut state,
            &callees,
            256,
            &mut accesses,
            &mut calls,
        );
        state.steps += 1;
        let _ = step_instruction(
            0x9a82_0025, // csel x5, x1, x2, eq
            &mut state,
            &callees,
            256,
            &mut accesses,
            &mut calls,
        );
        let post_eval = state.eval_concrete(&ctx);
        assert!(
            post_eval.nzcv.z,
            "expected Z=1 when comparing let-bound x0 against its exact concrete value"
        );
        assert_eq!(
            post_eval.regs[5], post_eval.regs[1],
            "expected csel eq to select x1 when let-bound x0 == x4"
        );
    }

    // Frame prologue/epilogue with a spill, a byte load through `x0`, and a `cbz`:
    // 0x00: stp x29, x30, [sp, #-0x20]!  (0xa9be7bfd)
    // 0x04: mov x29, sp                  (0x910003fd)
    // 0x08: str x0, [sp, #0x10]          (0xf9000be0)
    // 0x0c: ldrb w1, [x0, #3]            (0x39400c01)
    // 0x10: cbz w1, 0x1c                 (0x34000061)
    // 0x14: ldr x0, [sp, #0x10]          (0xf9400be0)
    // 0x18: add x0, x0, #1               (0x91000400)
    // 0x1c: ldp x29, x30, [sp], #0x20    (0xa8c27bfd)
    // 0x20: ret                          (0xd65f03c0)
    const HINT_DEMO_HEX: &str = "0xa9be7bfd 0x910003fd 0xf9000be0 0x39400c01 0x34000061 \
                                 0xf9400be0 0x91000400 0xa8c27bfd 0xd65f03c0";

    fn run_hint_cli(extra: &[&str]) -> String {
        let mut argv = vec!["rust-obj2lean symexec", "--hex", HINT_DEMO_HEX];
        argv.extend_from_slice(extra);
        let args = SymexecArgs::try_parse_from(argv).unwrap();
        run_symexec(&args).unwrap()
    }

    /// Lines of path `idx` (without the `path` header) in a version-1 text certificate.
    fn hint_path_lines(text: &str, idx: usize) -> Vec<String> {
        let header = format!("path {idx} ");
        text.lines()
            .skip_while(|l| !l.starts_with(&header))
            .skip(1)
            .take_while(|l| !l.starts_with("path "))
            .map(str::to_string)
            .collect()
    }

    #[test]
    fn symexec_block_hints_forced_fallthrough() {
        let text = run_hint_cli(&["--branches", "0x10=F", "--block-hints"]);
        assert!(text.starts_with("# symexec-block-hints v1\npath 0 fn 0x0 entry 0x0\n"));
        assert!(
            !text.contains("path 1 "),
            "forced branch must yield one path:\n{text}"
        );
        let lines = hint_path_lines(&text, 0);
        assert_eq!(lines[0], "0x0 store2 sp0-0x20:8 sp0-0x18:8");
        assert_eq!(lines[1], "0x4 auto");
        assert_eq!(lines[2], "0x8 store sp0-0x10:8");
        assert_eq!(lines[3], "0xc load x0+0x3:1");
        assert!(
            lines[4].starts_with("0x10 br fallthrough cond "),
            "unexpected branch hint `{}`",
            lines[4]
        );
        assert_eq!(lines[5], "0x14 load sp0-0x10:8");
        assert_eq!(lines[6], "0x18 auto");
        assert_eq!(lines[7], "0x1c load2 sp0-0x20:8 sp0-0x18:8");
        assert_eq!(lines[8], "0x20 end ret");
        assert_eq!(lines.len(), 9);
    }

    #[test]
    fn symexec_block_hints_forced_taken_and_both_paths() {
        let text = run_hint_cli(&["--branches", "0x10=taken", "--block-hints"]);
        let lines = hint_path_lines(&text, 0);
        assert!(lines[4].starts_with("0x10 br taken cond "), "{}", lines[4]);
        assert_eq!(lines[5], "0x1c load2 sp0-0x20:8 sp0-0x18:8");
        assert_eq!(lines[6], "0x20 end ret");
        assert_eq!(lines.len(), 7);

        // Unforced: fallthrough path first, then the taken path, each with its own prefix.
        let both = run_hint_cli(&["--block-hints"]);
        let p0 = hint_path_lines(&both, 0);
        let p1 = hint_path_lines(&both, 1);
        assert!(p0[4].starts_with("0x10 br fallthrough cond "));
        assert!(p1[4].starts_with("0x10 br taken cond "));
        assert_eq!(p0[..4], p1[..4]);
        assert_eq!(p0.last().map(String::as_str), Some("0x20 end ret"));
        assert_eq!(p1.last().map(String::as_str), Some("0x20 end ret"));
        // The two branch conditions are complementary.
        let c0 = p0[4].trim_start_matches("0x10 br fallthrough cond ");
        let c1 = p1[4].trim_start_matches("0x10 br taken cond ");
        assert_eq!(c0, negate_cond_str(c1));
    }

    #[test]
    fn symexec_block_hints_json_and_calls() {
        let json = run_hint_cli(&["--branches", "0x10=F", "--block-hints-json"]);
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["version"], 1);
        let lines = v["paths"][0]["lines"].as_array().unwrap();
        assert_eq!(lines[0]["kind"], "store2");
        assert_eq!(lines[0]["addr1"]["root"], "sp0");
        assert_eq!(lines[0]["addr1"]["offset"], -32);
        assert_eq!(lines[3]["kind"], "load");
        assert_eq!(lines[3]["addr"]["root"], "x0");
        assert_eq!(lines[3]["addr"]["bytes"], 1);
        assert_eq!(lines[4]["kind"], "br");
        assert_eq!(lines[4]["taken"], false);
        assert_eq!(lines[8]["kind"], "ret");

        // `bl` ends a block (path continues); `adrp`+`ldr` resolves to `g:base`; a load through
        // a non-root address is `?`.
        // 0x00: bl 0x40                (0x94000010)
        // 0x04: adrp x8, 0x1000        (0xb0000008)
        // 0x08: ldr x9, [x8, #0x10]    (0xf9400909)
        // 0x0c: ldr x10, [x0, x1]      (0xf861680a)
        // 0x10: ret                    (0xd65f03c0)
        let args = SymexecArgs::try_parse_from([
            "rust-obj2lean symexec",
            "--hex",
            "0x94000010 0xb0000008 0xf9400909 0xf861680a 0xd65f03c0",
            "--block-hints",
        ])
        .unwrap();
        let text = run_symexec(&args).unwrap();
        let lines = hint_path_lines(&text, 0);
        assert_eq!(lines[0], "0x0 end call 0x40");
        assert_eq!(lines[1], "0x4 auto");
        assert_eq!(lines[2], "0x8 load g:base+0x1010:8");
        assert_eq!(lines[3], "0xc load ?:8");
        assert_eq!(lines[4], "0x10 end ret");
    }
}
