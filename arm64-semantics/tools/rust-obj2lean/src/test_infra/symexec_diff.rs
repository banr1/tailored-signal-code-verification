// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Differential tests of the untrusted symbolic executor (`symexec::insn_semantics`) against
//! Unicorn (`UC_ARCH_ARM64`) (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (`#[cfg(test)]` differential test suite checking that
//!   `untrusted_lemmas::symexec` agrees bit-for-bit with Unicorn on all modeled instructions).
//! - **Purpose:** For every supported AArch64 instruction class and multi-instruction sequence,
//!   compares three executions across concrete initial states `(regs, sp, pc, nzcv, tpidr_el0, mem)`:
//!   1. **Symbolic Execution + Concrete Evaluation**: Steps on a symbolic [`SymState::new`] and
//!      evaluates the resulting [`SymExpr`]s and [`FlagState`] on [`ConcreteContext`].
//!   2. **Constant-Folded Symbolic Execution**: Steps on a [`SymState`] seeded with
//!      `SymExpr::Const` and `FlagState::Literal` to exercise all constant-folding rules.
//!   3. **Ground-Truth Unicorn (`UC_ARCH_ARM64`)**: Runs the same machine code in Unicorn and
//!      compares `X0..X30`, `SP`, `PC`, `NZCV`, `TPIDR_EL0`, and memory bytes bit-for-bit.
//!
//! # Key Types & Functions
//! - `run_unicorn_seq`: Executes an instruction sequence in Unicorn from a [`ConcreteContext`].
//! - `assert_symexec_matches_unicorn`: Verifies both symbolic and constant-folded paths match Unicorn.
//!
//! # When to Read This File
//! - Read this file when adding differential test cases for new instruction semantics in
//!   [`insn_semantics.rs`](../untrusted_lemmas/symexec/insn_semantics.rs) or expression folding in
//!   [`expr.rs`](../untrusted_lemmas/symexec/expr.rs).

use std::collections::BTreeMap;
use std::path::Path;

use unicorn_engine::unicorn_const::{Arch, Mode, Permission};
use unicorn_engine::{RegisterARM64, Unicorn};

use crate::test_infra::{Tool, mc_only};
use crate::untrusted_lemmas::symexec::{
    ConcreteContext, ConcreteMachineState, FlagState, Nzcv, StepOutcome, SymExpr, SymState,
    step_instruction,
};
use crate::untrusted_lemmas::{extract, sign_extend};

const CODE_BASE: u64 = 0x0040_0000;
const CODE_PAGE_SIZE: usize = 0x10000;
const DATA_BASE: u64 = 0x0080_0000;
const DATA_PAGE_SIZE: usize = 0x10000;
const STACK_BASE: u64 = 0x7fff_0000;
const STACK_PAGE_SIZE: usize = 0x10000;
const DEFAULT_SP: u64 = STACK_BASE + 0x8000;

const GPR_REGS: [RegisterARM64; 31] = [
    RegisterARM64::X0,
    RegisterARM64::X1,
    RegisterARM64::X2,
    RegisterARM64::X3,
    RegisterARM64::X4,
    RegisterARM64::X5,
    RegisterARM64::X6,
    RegisterARM64::X7,
    RegisterARM64::X8,
    RegisterARM64::X9,
    RegisterARM64::X10,
    RegisterARM64::X11,
    RegisterARM64::X12,
    RegisterARM64::X13,
    RegisterARM64::X14,
    RegisterARM64::X15,
    RegisterARM64::X16,
    RegisterARM64::X17,
    RegisterARM64::X18,
    RegisterARM64::X19,
    RegisterARM64::X20,
    RegisterARM64::X21,
    RegisterARM64::X22,
    RegisterARM64::X23,
    RegisterARM64::X24,
    RegisterARM64::X25,
    RegisterARM64::X26,
    RegisterARM64::X27,
    RegisterARM64::X28,
    RegisterARM64::X29,
    RegisterARM64::X30,
];

/// Assemble newline-separated AArch64 assembly lines into 32-bit instruction words using `llvm-mc`.
pub fn assemble_words(mc: &Tool, asm: &str, tmp_dir: &Path) -> Vec<u32> {
    let obj_path = tmp_dir.join("snippet.o");
    let mut child = mc
        .cmd()
        .args([
            "-triple=aarch64-linux-gnu",
            "-mattr=+lse,+rcpc,+rcpc-immo,+crc",
            "-filetype=obj",
            "-o",
            obj_path.to_str().unwrap(),
        ])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("failed to spawn llvm-mc");
    {
        use std::io::Write as _;
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(asm.as_bytes())
            .unwrap();
    }
    let out = child.wait_with_output().unwrap();
    assert!(
        out.status.success(),
        "llvm-mc failed on:\n{asm}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&obj_path).unwrap();
    let elf = object::File::parse(&*bytes).unwrap();
    use object::{Object as _, ObjectSection as _};
    let text = elf.section_by_name(".text").unwrap();
    let data = text.data().unwrap();
    assert_eq!(data.len() % 4, 0);
    data.chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
        .collect()
}

/// Shared execution loop stepping `words` from `state` and evaluating against `ctx`.
///
/// For `BL` / `BLR` instructions, architectural link-register semantics (`X30 := PC + 4`,
/// `PC := target`) is used so single-instruction and multi-instruction differential tests match
/// Unicorn bit-for-bit.
fn step_words_with_state(
    words: &[u32],
    mut state: SymState,
    ctx: &ConcreteContext,
    max_steps: usize,
) -> ConcreteMachineState {
    let mut accesses = Vec::new();
    let mut calls = Vec::new();
    let empty_callees = BTreeMap::new();
    let fn_size = (words.len() * 4) as u64;
    let mut explicit_pc: Option<u64> = None;

    for _ in 0..max_steps {
        let pc = state.pc_off;
        if pc >= fn_size || pc % 4 != 0 {
            break;
        }
        let w = words[(pc / 4) as usize];
        // Architectural `BL` / `BLR`: write `X30 = PC + 4` and branch to target.
        if (w & 0xfc00_0000) == 0x9400_0000 {
            let imm26 = extract(w, 0, 26);
            let disp = (sign_extend(imm26, 26) << 2) as i64;
            let target_pc = (pc as i64).wrapping_add(disp) as u64;
            state.write_gpr_zr(
                30,
                true,
                SymExpr::PcRel {
                    pc_off: pc + 4,
                    offset: 0,
                    is_page: false,
                },
            );
            state.pc_off = target_pc;
            continue;
        }
        if (w & 0xffff_fc1f) == 0xd63f_0000 {
            let rn_bits = extract(w, 5, 5);
            let target_expr = state.read_gpr_zr(rn_bits, true);
            let vars = state.eval_vars(ctx);
            let target_addr = target_expr.eval_with_vars(ctx, &vars);
            state.write_gpr_zr(
                30,
                true,
                SymExpr::PcRel {
                    pc_off: pc + 4,
                    offset: 0,
                    is_page: false,
                },
            );
            let rel = target_addr.wrapping_sub(ctx.base_pc);
            if rel < fn_size && rel % 4 == 0 {
                state.pc_off = rel;
                continue;
            }
            explicit_pc = Some(target_addr);
            break;
        }
        let outcome = step_instruction(
            w,
            &mut state,
            &empty_callees,
            fn_size,
            &mut accesses,
            &mut calls,
        );
        match outcome {
            StepOutcome::Next => continue,
            StepOutcome::CondBranch {
                cond,
                taken_pc,
                fallthrough_pc,
                ..
            } => {
                let vars = state.eval_vars(ctx);
                if cond.eval_with_vars(ctx, &vars) {
                    state.pc_off = taken_pc;
                } else {
                    state.pc_off = fallthrough_pc;
                }
            }
            StepOutcome::Return { target, .. } | StepOutcome::Halted { target, .. } => {
                if let Some(t) = target {
                    let vars = state.eval_vars(ctx);
                    let target_addr = t.eval_with_vars(ctx, &vars);
                    let rel = target_addr.wrapping_sub(ctx.base_pc);
                    if rel < fn_size && rel % 4 == 0 {
                        state.pc_off = rel;
                        continue;
                    }
                    explicit_pc = Some(target_addr);
                }
                break;
            }
        }
    }

    let mut out = state.eval_concrete(ctx);
    if let Some(pc_val) = explicit_pc {
        out.pc = pc_val;
    }
    out
}

/// Step `words` starting from a fresh symbolic `SymState::new(0)` and evaluate against `ctx`.
pub fn step_words_and_eval_concrete(
    words: &[u32],
    ctx: &ConcreteContext,
    max_steps: usize,
) -> ConcreteMachineState {
    step_words_with_state(words, SymState::new(0), ctx, max_steps)
}

/// Step `words` with `SymState` initialized to concrete `SymExpr::Const` values (testing all
/// constant-folding paths in `SymExpr` and `FlagState`).
pub fn step_words_const_folded(
    words: &[u32],
    ctx: &ConcreteContext,
    max_steps: usize,
) -> ConcreteMachineState {
    let mut state = SymState::new(0);
    for i in 0..32 {
        state.regs[i] = SymExpr::Const(ctx.regs[i]);
    }
    state.flags = FlagState::Literal(ctx.nzcv);
    state.tpidr_el0 = SymExpr::Const(ctx.tpidr_el0);
    step_words_with_state(words, state, ctx, max_steps)
}

/// Run `words` in Unicorn (`UC_ARCH_ARM64`) from `ctx` and return the resulting
/// [`ConcreteMachineState`], reading back `watched_addrs` from Unicorn memory.
pub fn run_unicorn(
    words: &[u32],
    ctx: &ConcreteContext,
    max_steps: usize,
    watched_addrs: &[u64],
) -> ConcreteMachineState {
    let mut uc = Unicorn::new(Arch::ARM64, Mode::LITTLE_ENDIAN).expect("Unicorn::new failed");
    // `max` CPU so Armv8.1+ encodings (LSE atomics, RCpc `LDAPR`/`LDAPUR`, CRC32) execute.
    uc.ctl_set_cpu_model(unicorn_engine::Arm64CpuModel::UC_CPU_ARM64_MAX.into())
        .expect("ctl_set_cpu_model failed");

    // Enable FP/SIMD in CPACR_EL1 (bits 20..21 = 0b11)
    let cpacr = uc.reg_read(RegisterARM64::CPACR_EL1).unwrap_or(0);
    uc.reg_write(RegisterARM64::CPACR_EL1, cpacr | (3 << 20))
        .unwrap();

    let code_page = ctx.base_pc & !0xffff;
    uc.mem_map(code_page, CODE_PAGE_SIZE, Permission::ALL)
        .unwrap();
    if DATA_BASE != code_page {
        uc.mem_map(DATA_BASE, DATA_PAGE_SIZE, Permission::ALL)
            .unwrap();
    }
    if STACK_BASE != code_page && STACK_BASE != DATA_BASE {
        uc.mem_map(STACK_BASE, STACK_PAGE_SIZE, Permission::ALL)
            .unwrap();
    }

    let code_bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    uc.mem_write(ctx.base_pc, &code_bytes).unwrap();

    for (&addr, &byte) in &ctx.mem {
        uc.mem_write(addr, &[byte]).unwrap();
    }

    for (i, &reg) in GPR_REGS.iter().enumerate() {
        uc.reg_write(reg, ctx.regs[i]).unwrap();
    }
    uc.reg_write(RegisterARM64::SP, ctx.regs[31]).unwrap();
    uc.reg_write(RegisterARM64::NZCV, ctx.nzcv.to_pstate_u64())
        .unwrap();
    uc.reg_write(RegisterARM64::TPIDR_EL0, ctx.tpidr_el0)
        .unwrap();

    let end_pc = ctx.base_pc + (words.len() as u64) * 4;
    // Note: if `BR` / `BLR` / `RET` jumps to an unmapped exit address (e.g. `LR`), Unicorn stops
    // with `FETCH_UNMAPPED` at that target PC, which is the exact architectural post-branch PC.
    let _ = uc.emu_start(ctx.base_pc, end_pc, 0, max_steps);

    let mut regs = [0u64; 32];
    for (i, &reg) in GPR_REGS.iter().enumerate() {
        regs[i] = uc.reg_read(reg).unwrap();
    }
    regs[31] = uc.reg_read(RegisterARM64::SP).unwrap();
    let pc = uc.reg_read(RegisterARM64::PC).unwrap();
    let nzcv = Nzcv::from_pstate_u64(uc.reg_read(RegisterARM64::NZCV).unwrap());
    let tpidr_el0 = uc.reg_read(RegisterARM64::TPIDR_EL0).unwrap();

    let mut mem = BTreeMap::new();
    for &addr in ctx.mem.keys().chain(watched_addrs.iter()) {
        let mut b = [0u8; 1];
        if uc.mem_read(addr, &mut b).is_ok() {
            mem.insert(addr, b[0]);
        }
    }

    ConcreteMachineState {
        regs,
        pc,
        nzcv,
        tpidr_el0,
        mem,
    }
}

/// Assert that BOTH symbolic execution (`SymState::new(0)` + `SymExpr::eval(&ctx)`) AND
/// constant-folded symbolic execution (`SymExpr::Const` inputs) match Unicorn bit-for-bit on
/// all 31 GPRs (`X0..X30`), `SP`, `PC`, `NZCV` (`N, Z, C, V`), `TPIDR_EL0`, and watched memory!
pub fn assert_symexec_matches_unicorn(
    label: &str,
    words: &[u32],
    ctx: &ConcreteContext,
    max_steps: usize,
    watched_addrs: &[u64],
) {
    let mut ctx_with_code = ctx.clone();
    for (idx, w) in words.iter().enumerate() {
        let base = ctx.base_pc.wrapping_add((idx as u64) * 4);
        for (b_idx, b) in w.to_le_bytes().into_iter().enumerate() {
            ctx_with_code
                .mem
                .entry(base.wrapping_add(b_idx as u64))
                .or_insert(b);
        }
    }
    let ctx = &ctx_with_code;
    let sym_eval = step_words_and_eval_concrete(words, ctx, max_steps);
    let const_eval = step_words_const_folded(words, ctx, max_steps);
    let uc_state = run_unicorn(words, ctx, max_steps, watched_addrs);

    for r in 0..32 {
        let rname = if r == 31 {
            "SP".to_string()
        } else {
            format!("X{r}")
        };
        assert_eq!(
            sym_eval.regs[r], uc_state.regs[r],
            "[{label}] symbolic eval mismatch on {rname}: sym={:#018x}, unicorn={:#018x}",
            sym_eval.regs[r], uc_state.regs[r]
        );
        assert_eq!(
            const_eval.regs[r], uc_state.regs[r],
            "[{label}] const-folded mismatch on {rname}: const={:#018x}, unicorn={:#018x}",
            const_eval.regs[r], uc_state.regs[r]
        );
    }

    assert_eq!(
        sym_eval.pc, uc_state.pc,
        "[{label}] symbolic eval mismatch on PC: sym={:#018x}, unicorn={:#018x}",
        sym_eval.pc, uc_state.pc
    );
    assert_eq!(
        const_eval.pc, uc_state.pc,
        "[{label}] const-folded mismatch on PC: const={:#018x}, unicorn={:#018x}",
        const_eval.pc, uc_state.pc
    );

    assert_eq!(
        sym_eval.nzcv, uc_state.nzcv,
        "[{label}] symbolic eval mismatch on NZCV: sym={:?}, unicorn={:?}",
        sym_eval.nzcv, uc_state.nzcv
    );
    assert_eq!(
        const_eval.nzcv, uc_state.nzcv,
        "[{label}] const-folded mismatch on NZCV: const={:?}, unicorn={:?}",
        const_eval.nzcv, uc_state.nzcv
    );

    assert_eq!(
        sym_eval.tpidr_el0, uc_state.tpidr_el0,
        "[{label}] symbolic eval mismatch on TPIDR_EL0: sym={:#018x}, unicorn={:#018x}",
        sym_eval.tpidr_el0, uc_state.tpidr_el0
    );

    for &addr in ctx.mem.keys().chain(watched_addrs.iter()) {
        let sym_b = sym_eval.mem.get(&addr).copied().unwrap_or(0);
        let const_b = const_eval.mem.get(&addr).copied().unwrap_or(0);
        let uc_b = uc_state.mem.get(&addr).copied().unwrap_or(0);
        assert_eq!(
            sym_b, uc_b,
            "[{label}] symbolic eval mem mismatch at {addr:#x}: sym={sym_b:#04x}, unicorn={uc_b:#04x}"
        );
        assert_eq!(
            const_b, uc_b,
            "[{label}] const-folded mem mismatch at {addr:#x}: const={const_b:#04x}, unicorn={uc_b:#04x}"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_ctx(x0: u64, x1: u64, x2: u64, x3: u64) -> ConcreteContext {
        let mut regs = [0u64; 32];
        regs[0] = x0;
        regs[1] = x1;
        regs[2] = x2;
        regs[3] = x3;
        regs[4] = DATA_BASE + 0x100;
        regs[29] = DEFAULT_SP;
        regs[30] = CODE_BASE + 0x4000;
        regs[31] = DEFAULT_SP;
        ConcreteContext {
            regs,
            base_pc: CODE_BASE,
            nzcv: Nzcv::default(),
            tpidr_el0: 0x1122_3344_5566_7788,
            mem: BTreeMap::new(),
        }
    }

    const BOUNDARY_VALS: &[u64] = &[
        0,
        1,
        2,
        7,
        0x7f,
        0x80,
        0xff,
        0x7fff,
        0x8000,
        0xffff,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_fffe,
        0xffff_ffff,
        0x0000_0001_0000_0000,
        0xdead_beef_0000_0000,
        0xdead_beef_8000_0000,
        0xdead_beef_ffff_ffff,
        0x0123_4567_89ab_cdef,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        0xffff_ffff_ffff_fffe,
        0xffff_ffff_ffff_ffff,
    ];

    #[test]
    fn diff_arithmetic_and_carry_flags_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            "add x4, x0, #0\nadd x5, x0, #0xfff\nadd x6, x0, #0x123, lsl #12",
            "adds x4, x0, x1\nsub x5, x0, x1\nsubs x6, x0, x1",
            "add w4, w0, #0xfff\nadds w5, w0, w1\nsub w6, w0, w1\nsubs w7, w0, w1",
            "add x4, x0, x1, lsl #3\nsub x5, x0, x1, lsr #7\nadds x6, x0, x1, asr #15\nsubs x7, x0, x1, asr #63",
            "add w4, w0, w1, lsl #3\nsub w5, w0, w1, lsr #7\nadds w6, w0, w1, asr #15\nsubs w7, w0, w1, asr #31",
            "add x4, sp, w1, uxtw #2\nsub x5, sp, w1, sxtw #3\nadds x6, x0, w1, sxtb #1\nsubs x7, x0, w1, sxth #2",
            "add w4, wsp, w1, uxtb #1\nsub w5, wsp, w1, uxth #2\nadds w6, w0, w1, sxtb #3\nsubs w7, w0, w1, sxth #1",
            "adc x4, x0, x1\nadcs x5, x0, x1\nsbc x6, x0, x1\nsbcs x7, x0, x1",
            "adc w4, w0, w1\nadcs w5, w0, w1\nsbc w6, w0, w1\nsbcs w7, w0, w1",
        ];

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &a in BOUNDARY_VALS {
                for &b in &[
                    0u64,
                    1,
                    0x7fff_ffff,
                    0x8000_0000,
                    0xffff_ffff,
                    0x7fff_ffff_ffff_ffff,
                    0x8000_0000_0000_0000,
                    0xffff_ffff_ffff_ffff,
                ] {
                    for c_in in [false, true] {
                        let mut ctx = default_ctx(a, b, 0, 0);
                        ctx.nzcv.c = c_in;
                        assert_symexec_matches_unicorn(
                            &format!("arith_{s_idx}_a={a:#x}_b={b:#x}_c={c_in}"),
                            &words,
                            &ctx,
                            words.len(),
                            &[],
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn diff_logical_and_move_wide_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            "and x4, x0, #0xff\nand x5, x0, #0xffff\nand x6, x0, #0xffffffff\nands x7, x0, #0x5555555555555555",
            "orr x4, x0, #0xf0f0f0f0f0f0f0f0\neor x5, x0, #0xaaaaaaaaaaaaaaaa\nands w6, w0, #0x00ff00ff\norr w7, w0, #0xff00ff00",
            "and x4, x0, x1, lsl #4\nbic x5, x0, x1, lsr #5\norr x6, x0, x1, asr #9\norn x7, x0, x1, ror #13",
            "eor x4, x0, x1, ror #7\neon x5, x0, x1, lsl #11\nands x6, x0, x1\nbics x7, x0, x1, asr #3",
            "and w4, w0, w1, lsl #4\nbic w5, w0, w1, lsr #5\norr w6, w0, w1, asr #9\norn w7, w0, w1, ror #13\neor w8, w0, w1\neon w9, w0, w1\nands w10, w0, w1\nbics w11, w0, w1",
            "mov x4, x0\nmvn x5, x1\nmov w6, w0\nmvn w7, w1",
            "movz x4, #0x1234\nmovk x4, #0x5678, lsl #16\nmovk x4, #0x9abc, lsl #32\nmovk x4, #0xdef0, lsl #48\nmovn x5, #0x1234, lsl #32\nmovn w6, #0x1234, lsl #16\nmovk w0, #0xabcd, lsl #16",
        ];

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &a in BOUNDARY_VALS {
                for &b in &[
                    0u64,
                    1,
                    0x1234_5678_9abc_def0,
                    0x8000_0000_0000_0001,
                    0xffff_ffff_ffff_ffff,
                ] {
                    let ctx = default_ctx(a, b, 0, 0);
                    assert_symexec_matches_unicorn(
                        &format!("logical_{s_idx}_a={a:#x}_b={b:#x}"),
                        &words,
                        &ctx,
                        words.len(),
                        &[],
                    );
                }
            }
        }
    }

    #[test]
    fn diff_bitfield_and_extr_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            // Canonical extensions and shifts
            "uxtb x4, w0\nuxth x5, w0\nuxtw x6, w0\nsxtb x7, w0\nsxth x8, w0\nsxtw x9, w0\nsxtb w10, w0\nsxth w11, w0",
            "lsl x4, x0, #7\nlsr x5, x0, #7\nasr x6, x0, #7\nlsl w7, w0, #7\nlsr w8, w0, #7\nasr w9, w0, #7",
            // Non-wrapping bitfield extracts (`imms >= immr`: UBFX, SBFX, BFXIL)
            "ubfx x4, x0, #4, #12\nsbfx x5, x0, #4, #12\nubfx w6, w0, #5, #11\nsbfx w7, w0, #5, #11",
            "mov x4, x1\nbfxil x4, x0, #8, #16\nmov w5, w1\nbfxil w5, w0, #4, #10",
            // Wrapping bitfield inserts (`imms < immr`: UBFIZ, SBFIZ, BFI)
            "ubfiz x4, x0, #12, #8\nsbfiz x5, x0, #12, #8\nubfiz w6, w0, #9, #7\nsbfiz w7, w0, #9, #7",
            "mov x4, x1\nbfi x4, x0, #12, #8\nmov w5, w1\nbfi w5, w0, #9, #7",
            // EXTR & ROR immediate
            "extr x4, x0, x1, #0\nextr x5, x0, x1, #13\nextr x6, x0, x1, #63\nror x7, x0, #19",
            "extr w4, w0, w1, #0\nextr w5, w0, w1, #13\nextr w6, w0, w1, #31\nror w7, w0, #19",
        ];

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &a in BOUNDARY_VALS {
                for &b in &[
                    0u64,
                    0xffff_ffff_ffff_ffff,
                    0xaaaa_5555_aaaa_5555,
                    0x1234_5678_9abc_def0,
                ] {
                    let ctx = default_ctx(a, b, 0, 0);
                    assert_symexec_matches_unicorn(
                        &format!("bitfield_{s_idx}_a={a:#x}_b={b:#x}"),
                        &words,
                        &ctx,
                        words.len(),
                        &[],
                    );
                }
            }
        }
    }

    #[test]
    fn diff_cond_select_and_ccmp_all_16_conds_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        // Test allcondition codes on CSEL, CSINC, CSINV, CSNEG, CCMP, CCMN
        let snippets = [
            "csel x4, x0, x1, eq\ncsinc x5, x0, x1, ne\ncsinv x6, x0, x1, cs\ncsneg x7, x0, x1, cc\ncsel x8, x0, x1, mi\ncsinc x9, x0, x1, pl\ncsinv x10, x0, x1, vs\ncsneg x11, x0, x1, vc",
            "csel x4, x0, x1, hi\ncsinc x5, x0, x1, ls\ncsinv x6, x0, x1, ge\ncsneg x7, x0, x1, lt\ncsel x8, x0, x1, gt\ncsinc x9, x0, x1, le\ncsinv x10, x0, x1, al\ncsneg w11, w0, w1, lt",
            "cmp x0, x1\ncsel x4, x2, x3, eq\ncsinc x5, x2, x3, hi\ncsinv x6, x2, x3, lt\ncsneg x7, x2, x3, le",
            "cmp w0, w1\ncsel w4, w2, w3, ge\ncsinc w5, w2, w3, ls\ncsinv w6, w2, w3, gt\ncsneg w7, w2, w3, cc",
            "cmp x0, x1\nccmp x2, x3, #0b1010, ne\ncsel x4, x0, x1, eq\nccmn x2, #7, #0b0101, gt\ncsinc x5, x0, x1, lt",
            "cmp w0, w1\nccmp w2, #15, #0b0100, ge\ncsel w4, w0, w1, eq\nccmn w2, w3, #0b1001, ne\ncsinv w5, w0, w1, hi",
        ];

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            // Test all 16 initial NZCV combinations (`0..16`) plus boundary operand pairs
            for nzcv_bits in 0..16u8 {
                let mut ctx = default_ctx(
                    0x8000_0000_0000_0005,
                    0x7fff_ffff_ffff_fffa,
                    0x1111_2222_3333_4444,
                    0x5555_6666_7777_8888,
                );
                ctx.nzcv = Nzcv::from_u8(nzcv_bits);
                assert_symexec_matches_unicorn(
                    &format!("csel_nzcv_{s_idx}_{nzcv_bits:#x}"),
                    &words,
                    &ctx,
                    words.len(),
                    &[],
                );
            }
            for &(a, b) in &[
                (0u64, 0u64),
                (5, 5),
                (5, 10),
                (10, 5),
                (0x8000_0000, 0x7fff_ffff),
                (0xffff_ffff, 1),
                (0x8000_0000_0000_0000, 1),
                (0xffff_ffff_ffff_ffff, 0),
            ] {
                let ctx = default_ctx(a, b, a.wrapping_add(1), b.wrapping_sub(1));
                assert_symexec_matches_unicorn(
                    &format!("csel_cmp_{s_idx}_{a:#x}_{b:#x}"),
                    &words,
                    &ctx,
                    words.len(),
                    &[],
                );
            }
        }
    }

    #[test]
    fn diff_dataproc_1src_2src_3src_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            // 1-source (64-bit & 32-bit)
            "rbit x4, x0\nrev16 x5, x0\nrev32 x6, x0\nrev x7, x0\nclz x8, x0\ncls x9, x0",
            "rbit w4, w0\nrev16 w5, w0\nrev w6, w0\nclz w7, w0\ncls w8, w0",
            // 2-source (64-bit & 32-bit)
            "udiv x4, x0, x1\nsdiv x5, x0, x1\nlslv x6, x0, x1\nlsrv x7, x0, x1\nasrv x8, x0, x1\nrorv x9, x0, x1",
            "udiv w4, w0, w1\nsdiv w5, w0, w1\nlslv w6, w0, w1\nlsrv w7, w0, w1\nasrv w8, w0, w1\nrorv w9, w0, w1",
            // 3-source (MADD, MSUB, SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH)
            "madd x4, x0, x1, x2\nmsub x5, x0, x1, x2\nmadd w6, w0, w1, w2\nmsub w7, w0, w1, w2",
            "smaddl x4, w0, w1, x2\nsmsubl x5, w0, w1, x2\nsmulh x6, x0, x1\numaddl x7, w0, w1, x2\numsubl x8, w0, w1, x2\numulh x9, x0, x1",
        ];

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &a in BOUNDARY_VALS {
                for &b in &[
                    0u64, // tests div-by-zero -> 0 and shift by 0
                    1,
                    7,
                    31,
                    32,
                    63,
                    64,
                    99,
                    0xffff_ffff,          // -1 in W32 (tests INT32_MIN / -1 overflow in sdiv w)
                    0xffff_ffff_ffff_ffff, // -1 in X64 (tests INT64_MIN / -1 overflow in sdiv x)
                    0x8000_0000_0000_0000,
                    0x1234_5678_9abc_def0,
                ] {
                    let ctx = default_ctx(a, b, 0x1000_0000_2000_0000, 0);
                    assert_symexec_matches_unicorn(
                        &format!("dp123_{s_idx}_a={a:#x}_b={b:#x}"),
                        &words,
                        &ctx,
                        words.len(),
                        &[],
                    );
                }
            }
        }
    }

    #[test]
    fn diff_loads_stores_all_widths_and_modes_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            // Stack frame STP/LDP (64-bit & 32-bit, pre-index, signed offset, post-index) + LDPSW
            "stp x0, x1, [sp, #-32]!\nstp w2, w3, [sp, #16]\nldp x5, x6, [sp]\nldpsw x7, x8, [sp, #16]\nldp w9, w10, [sp, #16]\nldp x11, x12, [sp], #32",
            // All single-register widths (8/16/32/64, unsigned & signed to W/X)
            "str x0, [x4]\nstr x1, [x4, #8]\nldrb w5, [x4, #0]\nldrsb x6, [x4, #0]\nldrsb w7, [x4, #0]\nldrh w8, [x4, #2]\nldrsh x9, [x4, #2]\nldrsh w10, [x4, #2]\nldr w11, [x4, #4]\nldrsw x12, [x4, #4]\nldr x13, [x4, #8]",
            // Unscaled immediate (LDUR / STUR negative & positive offsets)
            "stur x0, [x4, #-16]\nsturb w1, [x4, #-5]\nsturh w2, [x4, #-4]\nstur w3, [x4, #4]\nldur x5, [x4, #-16]\nldursb x6, [x4, #-5]\nldursb w7, [x4, #-5]\nldursh x8, [x4, #-4]\nldursh w9, [x4, #-4]\nldursw x10, [x4, #4]",
            // Pre-index & post-index single register loads/stores
            "str x0, [x4, #16]!\nldr x5, [x4], #-8\nstrb w1, [x4, #-1]!\nldrsb x6, [x4], #9",
            // Register-offset addressing (`uxtw`, `sxtw`, `lsl`, `sxtx`)
            "mov w2, #3\nstr x0, [x4, w2, uxtw #3]\nldr x5, [x4, w2, uxtw #3]\nmov x3, #-2\nstr w1, [x4, x3, sxtx #2]\nldrsw x6, [x4, x3, sxtx #2]",
            // Load-Acquire / Store-Release (`stlr*`, `ldar*`)
            "stlr x0, [x4]\nldar x5, [x4]\nstlr w1, [x4, #0]\nldar w6, [x4]\nstlrh w2, [x4]\nldarh w7, [x4]\nstlrb w3, [x4]\nldarb w8, [x4]",
            // Load/Store-Exclusive pairs (`ldxr*`/`ldaxr*` then `stxr*`/`stlxr*` succeed: `Ws := 0`)
            "mov w9, #7\nmov w10, #7\nldxr x5, [x4]\nstxr w9, x0, [x4]\nldaxr w6, [x4]\nstlxr w10, w1, [x4]\nldxrh w7, [x4]\nstxrh w11, w2, [x4]\nldaxrb w8, [x4]\nstlxrb w12, w3, [x4]",
            // Sub-word store/load overlap & forwarding on stack
            "stp x0, x1, [sp, #-16]!\nstrb w2, [sp, #3]\nstrh w3, [sp, #4]\nldr x5, [sp]\nldr w6, [sp, #4]\nldrsb x7, [sp, #3]\nadd sp, sp, #16",
        ];

        let mut watched = Vec::new();
        for off in -32i64..64 {
            watched.push((DEFAULT_SP as i64 + off) as u64);
            watched.push(((DATA_BASE + 0x100) as i64 + off) as u64);
        }

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &(x0, x1) in &[
                (0x89ab_cdef_0123_4567u64, 0xfedc_ba98_7654_3210u64),
                (0xffff_ffff_ffff_ffffu64, 0x8000_0000_8000_0000u64),
                (0x0000_0000_0000_0000u64, 0x7f7f_7f7f_7f7f_7f7fu64),
            ] {
                let ctx = default_ctx(x0, x1, 0x0000_0000_dead_beef, 0x0000_0000_cafe_babe);
                assert_symexec_matches_unicorn(
                    &format!("mem_{s_idx}_{x0:#x}"),
                    &words,
                    &ctx,
                    words.len() + 4,
                    &watched,
                );
            }
        }
    }

    #[test]
    fn diff_atomics_rcpc_hints_and_misc_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            // LSE atomic RMW, 64-bit, all eight ops + SWP + ST<op> alias (Rt = XZR)
            "str x0, [x4]\nldadd x1, x5, [x4]\nldclr x2, x6, [x4]\nldeor x3, x7, [x4]\nldset x1, x8, [x4]\nldsmax x2, x9, [x4]\nldsmin x3, x10, [x4]\nldumax x1, x11, [x4]\nldumin x2, x12, [x4]\nswp x3, x13, [x4]\nstadd x1, [x4]\nldr x14, [x4]",
            // LSE atomic RMW at sub-word widths with acquire/release variants
            "str x0, [x4]\nldaddalb w1, w5, [x4]\nldumaxah w1, w8, [x4]\nlduminb w2, w9, [x4]\nldeoral w3, w10, [x4]\nswpalh w1, w11, [x4]\nldr x13, [x4]",
            // Sub-word / 32-bit LDSMAX/LDSMIN on non-negative operands only: Unicorn 2.1.3
            // (QEMU 5 TCG) zero-extends the memory operand, so it compares unsigned and
            // disagrees with the ARM ASL (and our model) whenever the loaded value is negative.
            "and x15, x0, #0x3f3f3f3f3f3f3f3f\nand x16, x2, #0x3f3f3f3f3f3f3f3f\nand x17, x3, #0x3f3f3f3f3f3f3f3f\nstr x15, [x4]\nldsmaxh w16, w6, [x4]\nldsminlb w17, w7, [x4]\nldsmax w16, w12, [x4]\nldsminal w17, w14, [x4]\nldr x13, [x4]",
            // CAS: one succeeding and one failing compare-and-swap
            "str x0, [x4]\nmov x5, x0\ncas x5, x1, [x4]\nmov x6, x2\ncasal x6, x3, [x4]\nldr x7, [x4]\nstr w2, [x4, #8]\nmov w8, w2\ncasb w8, w3, [x4]\nldr x9, [x4, #8]",
            // CASP (even register pairs), success then failure
            "stp x0, x1, [x4]\nmov x6, x0\nmov x7, x1\nmov x8, x2\nmov x9, x3\ncasp x6, x7, x8, x9, [x4]\nldp x10, x11, [x4]\ncaspal x6, x7, x8, x9, [x4]\nldp x12, x13, [x4]\nmov w14, w2\nmov w15, w3\ncasp w14, w15, w0, w1, [x4]\nldp w16, w17, [x4]",
            // Exclusive pairs: LDXP/STXP (Ws := 0), LDAXP/STLXP at W width
            "stp x0, x1, [x4]\nmov w9, #7\nldxp x5, x6, [x4]\nstxp w9, x2, x3, [x4]\nldaxp w7, w8, [x4]\nmov w10, #7\nstlxp w10, w0, w1, [x4]\nldp x11, x12, [x4]",
            // RCpc: LDAPR, STLUR/LDAPUR (+ sign-extending variants)
            "str x0, [x4]\nldapr x5, [x4]\nldaprb w6, [x4]\nldaprh w7, [x4]\nldapr w8, [x4]\nstlur x1, [x4, #-16]\nstlurb w2, [x4, #-3]\nstlurh w3, [x4, #6]\nldapur x9, [x4, #-16]\nldapursb x10, [x4, #-3]\nldapursh w11, [x4, #6]\nldapursw x12, [x4, #-16]\nstlur w0, [x4, #12]\nldapur w13, [x4, #12]",
            // Non-temporal pairs (X and W forms, negative offsets)
            "stnp x0, x1, [x4, #-16]\nstnp w2, w3, [x4, #8]\nldnp x5, x6, [x4, #-16]\nldnp w7, w8, [x4, #8]\nldnp x9, x10, [x4, #-8]",
            // DC ZVA zeroes the 64-byte block containing x5 (DCZID = 4)
            "stp x0, x1, [x4]\nstp x2, x3, [x4, #48]\nstr x0, [x4, #64]\nadd x5, x4, #17\ndc zva, x5\nldp x6, x7, [x4]\nldr x8, [x4, #56]\nldr x9, [x4, #64]",
            // Hints and prefetches are architectural no-ops
            "yield\nprfm pldl1keep, [x4]\nprfm pstl2strm, [x4, #64]\nprfum pldl1keep, [x4, #-3]\nprfm pldl1keep, [x4, x0]\nsevl\nadd x5, x0, x1",
            // NZCV MSR from a constant, MRS NZCV / DCZID_EL0, then flag consumers
            "mov x9, #0x60000000\nmsr nzcv, x9\nmrs x5, nzcv\ncset x6, eq\ncset x7, cs\nmrs x8, dczid_el0",
            // SIMD LD1 multi / LD1R: only the GPR post-index writeback is modeled
            "mov x5, #16\nld1 {v0.16b, v1.16b}, [x4], #32\nld1r {v2.4s}, [x4], x5\nld1 {v3.2d}, [x4]\nld1r {v4.8b}, [x4], #1\nmov x6, x4",
        ];

        let mut watched = Vec::new();
        for off in -32i64..96 {
            watched.push((DEFAULT_SP as i64 + off) as u64);
            watched.push(((DATA_BASE + 0x100) as i64 + off) as u64);
        }

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &(x0, x1, x2, x3) in &[
                (
                    0x89ab_cdef_0123_4567u64,
                    0xfedc_ba98_7654_3210u64,
                    0x0000_0000_dead_beefu64,
                    0x0000_0000_cafe_babeu64,
                ),
                (
                    0xffff_ffff_ffff_ff80u64,
                    0x8000_0000_8000_0000u64,
                    0x7fff_ffff_ffff_ff7fu64,
                    0x0000_0000_0000_0001u64,
                ),
                (0, 0x7f7f_7f7f_7f7f_7f7fu64, 0, 0x8080_8080_8080_8080u64),
            ] {
                let ctx = default_ctx(x0, x1, x2, x3);
                assert_symexec_matches_unicorn(
                    &format!("atomic_{s_idx}_{x0:#x}"),
                    &words,
                    &ctx,
                    words.len() + 4,
                    &watched,
                );
            }
        }
    }

    #[test]
    fn diff_branches_pc_rel_and_sysreg_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        let snippets = [
            // ADR, ADRP, and PC-relative literal loads
            "adr x4, label_pool\nadrp x5, label_pool\nldr x6, label_pool\nldr w7, label_pool\nldrsw x8, label_pool\nb done\n.p2align 3\nlabel_pool:\n.xword 0xfedcba9889abcdef\ndone:\nnop",
            // CBZ / CBNZ (32-bit vs 64-bit when upper 32 bits are non-zero!)
            "cbz w0, w_zero\nmov x4, #1\nb check_x\nw_zero:\nmov x4, #2\ncheck_x:\ncbnz x0, x_nz\nmov x5, #10\nb done\nx_nz:\nmov x5, #20\ndone:\nnop",
            // TBZ / TBNZ on low and high bits
            "tbz w0, #31, bit31_clr\nmov x4, #100\nb next\nbit31_clr:\nmov x4, #200\nnext:\ntbnz x0, #63, bit63_set\nmov x5, #300\nb done\nbit63_set:\nmov x5, #400\ndone:\nnop",
            // B.cond diamond + MRS/MSR TPIDR_EL0 + BL + RET
            "mrs x4, tpidr_el0\nadd x4, x4, x0\nmsr tpidr_el0, x4\ncmp x0, x1\nb.ge ge_branch\nsub x2, x1, x0\nb after_cmp\nge_branch:\nsub x2, x0, x1\nafter_cmp:\nbl helper\nadd x0, x0, x2\nb exit\nhelper:\nlsl x0, x0, #1\nret\nexit:\nnop",
        ];

        for (s_idx, asm) in snippets.iter().enumerate() {
            let words = assemble_words(&mc, asm, dir.path());
            for &(x0, x1) in &[
                (0u64, 10u64),
                (0xdead_beef_0000_0000u64, 10u64), // W0 == 0, X0 != 0!
                (0x0000_0000_8000_0000u64, 5u64),  // bit 31 = 1, bit 63 = 0
                (0x8000_0000_0000_0000u64, 5u64),  // bit 31 = 0, bit 63 = 1
                (25u64, 10u64),
            ] {
                let ctx = default_ctx(x0, x1, 0, 0);
                assert_symexec_matches_unicorn(
                    &format!("ctrl_{s_idx}_{x0:#x}_{x1:#x}"),
                    &words,
                    &ctx,
                    64,
                    &[],
                );
            }
        }
    }

    #[test]
    fn diff_trusted_suite_random_fuzz_blocks_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();

        // Deterministic SplitMix64 matching `Arm64/Testing/TrustedSuite.lean` (`buildRandomFuzzSuite`)
        struct SplitMix64(u64);
        impl SplitMix64 {
            fn next_u64(&mut self) -> u64 {
                self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = self.0;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            }
            fn next_usize(&mut self, bound: usize) -> usize {
                (self.next_u64() as usize) % bound
            }
        }

        let mut rng = SplitMix64(20260918);
        for block_idx in 0..100 {
            let mut lines = Vec::with_capacity(10);
            for _ in 0..8 {
                let kind = rng.next_usize(36);
                let d = rng.next_usize(8);
                let n = rng.next_usize(8);
                let m = rng.next_usize(8);
                let a = rng.next_usize(8);
                let insn = match kind {
                    0 => format!("add x{d}, x{n}, x{m}"),
                    1 => format!("adds x{d}, x{n}, x{m}"),
                    2 => format!("sub x{d}, x{n}, x{m}"),
                    3 => format!("subs x{d}, x{n}, x{m}"),
                    4 => format!("add w{d}, w{n}, w{m}"),
                    5 => format!("adds w{d}, w{n}, w{m}"),
                    6 => format!("sub w{d}, w{n}, w{m}"),
                    7 => format!("subs w{d}, w{n}, w{m}"),
                    8 => format!("and x{d}, x{n}, x{m}"),
                    9 => format!("orr x{d}, x{n}, x{m}"),
                    10 => format!("eor x{d}, x{n}, x{m}"),
                    11 => format!("bic x{d}, x{n}, x{m}"),
                    12 => format!("orn x{d}, x{n}, x{m}"),
                    13 => format!("eon x{d}, x{n}, x{m}"),
                    14 => format!("ands w{d}, w{n}, w{m}"),
                    15 => format!("bics w{d}, w{n}, w{m}"),
                    16 => format!("csel x{d}, x{n}, x{m}, eq"),
                    17 => format!("csinc x{d}, x{n}, x{m}, cs"),
                    18 => format!("csinv x{d}, x{n}, x{m}, lt"),
                    19 => format!("csneg w{d}, w{n}, w{m}, ge"),
                    20 => format!("rbit x{d}, x{n}"),
                    21 => format!("rev x{d}, x{n}"),
                    22 => format!("rev w{d}, w{n}"),
                    23 => format!("rev32 x{d}, x{n}"),
                    24 => format!("rev16 x{d}, x{n}"),
                    25 => format!("clz x{d}, x{n}"),
                    26 => format!("cls w{d}, w{n}"),
                    27 => format!("lslv x{d}, x{n}, x{m}"),
                    28 => format!("lsrv w{d}, w{n}, w{m}"),
                    29 => format!("asrv w{d}, w{n}, w{m}"),
                    30 => format!("rorv w{d}, w{n}, w{m}"),
                    31 => format!("madd x{d}, x{n}, x{m}, x{a}"),
                    32 => format!("msub w{d}, w{n}, w{m}, w{a}"),
                    33 => format!("smaddl x{d}, w{n}, w{m}, x{a}"),
                    34 => format!("umaddl x{d}, w{n}, w{m}, x{a}"),
                    _ => format!("umulh x{d}, x{n}, x{m}"),
                };
                lines.push(insn);
            }
            lines.push("ret".to_string());
            let asm = lines.join("\n");
            let words = assemble_words(&mc, &asm, dir.path());

            let mut ctx = default_ctx(0, 0, 0, 0);
            for r in 0..8 {
                ctx.regs[r] = rng.next_u64();
            }
            ctx.nzcv = Nzcv::from_u8(rng.next_usize(16) as u8);
            assert_symexec_matches_unicorn(
                &format!("random_fuzz_block_{block_idx:03}"),
                &words,
                &ctx,
                16,
                &[],
            );
        }
    }

    #[test]
    fn diff_arx_let_bindings_cmp_csel_and_branch_vs_unicorn() {
        let Some(mc) = mc_only() else { return };
        let dir = tempfile::tempdir().unwrap();
        // Two SipRound-like ARX rounds exceed LET_BINDING_NODE_THRESHOLD (32 nodes),
        // checkpointing x0..x3 into `SymExpr::Var("r{i}_step{k}")`, then feeding
        // `cmp`, `csel`, `b.eq`, and `cbnz`.
        let mut lines = Vec::new();
        for _ in 0..2 {
            lines.extend_from_slice(&[
                "add x0, x0, x1",
                "ror x1, x1, #51",
                "eor x1, x1, x0",
                "ror x0, x0, #32",
                "add x2, x2, x3",
                "ror x3, x3, #48",
                "eor x3, x3, x2",
                "add x0, x0, x3",
                "ror x3, x3, #43",
                "eor x3, x3, x0",
                "add x2, x2, x1",
                "ror x1, x1, #47",
                "eor x1, x1, x2",
                "ror x2, x2, #32",
            ]);
        }
        lines.extend_from_slice(&[
            "cmp x0, x1",
            "csel x5, x2, x3, hi",
            "b.eq eq_lbl",
            "cbnz x5, nz_lbl",
            "mov x6, #11",
            "b done_lbl",
            "eq_lbl:",
            "mov x6, #22",
            "b done_lbl",
            "nz_lbl:",
            "add x6, x5, x0",
            "done_lbl:",
            "eor x0, x0, x6",
            "ret",
        ]);
        let asm = lines.join("\n");
        let words = assemble_words(&mc, &asm, dir.path());
        for &(x0, x1, x2, x3) in &[
            (
                0x736f_6d65_7073_6575u64,
                0x646f_7261_6e64_6f6du64,
                0x6c79_6765_6e65_7261u64,
                0x7465_6462_7974_6573u64,
            ),
            (0u64, 0u64, 0u64, 0u64),
            (1u64, 2u64, 3u64, 4u64),
        ] {
            let ctx = default_ctx(x0, x1, x2, x3);
            assert_symexec_matches_unicorn(
                &format!("arx_let_cmp_branch_{x0:#x}"),
                &words,
                &ctx,
                64,
                &[],
            );
        }
    }
}

