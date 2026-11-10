// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 Per-Instruction Symbolic Semantics (`insn_semantics.rs`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (symbolic transfer functions for the `symexec` proof advisor,
//!   differentially tested against Unicorn and `Arm64.execInst` in `test_infra/symexec_diff.rs`).
//! - **Purpose:** Isolates the symbolic transfer function of every modeled AArch64 instruction
//!   mirroring `Arm64/Trusted/ISA/Eval.lean` (`execInst`, `shiftVal`, `extendVal`, `evalAddSub`, `evalLogical`,
//!   `evalBitfield`, `evalAddrMode`), free of ELF, CLI, or report-formatting logic.
//!
//! # Key Types & Functions
//! - [`StepOutcome`]: Result of stepping one instruction (`Fallthrough`, `BranchCond`, `Jump`,
//!   `Call`, `Return`, `Terminated`).
//! - [`step_instruction`]: Top-level 32-bit A64 opcode dispatcher over [`SymState`]:
//!   - **Imm**: `step_adr_adrp`, `step_add_sub_imm`, `step_logical_imm`, `step_move_wide`,
//!     `step_bitfield`, `step_extr`.
//!   - **Reg**: `step_logical_shifted`, `step_add_sub_shifted`, `step_add_sub_extended`,
//!     `step_add_sub_carry`, `step_cond_compare`, `step_cond_select`, `step_dataproc_{1,2,3}src`.
//!   - **Mem & Branch**: `step_load_store_{pair,unsigned_imm,unscaled_or_reg}`, `step_load_literal`,
//!     `step_ldar_stlr`, `step_ldxr_stxr`, `step_branch_imm`, `step_cbz_cbnz`, `step_tbz_tbnz`,
//!     `step_b_cond`, `step_branch_reg`, `step_sysreg`.
//!   - **Atomics/hints**: sequential atomics, RCpc, HINT, PRFM, LDNP/STNP, DC ZVA, UDF, CRC32
//!     are delegated to `atomics::step_atomic_or_hint`.
//! - [`eval_shifted_reg`], [`eval_extended_reg`]: Operand shift and sign/zero-extension helpers.
//!
//! # When to Read This File
//! - Read this file when adding or debugging the symbolic transfer function for an AArch64
//!   instruction in `symexec`.

use std::collections::BTreeMap;

use crate::untrusted_lemmas::index::CalleeInfo;
use crate::untrusted_lemmas::{bit, decode_bit_masks, extract, sign_extend};

use super::expr::{
    BinOpKind, BitfieldOp, FlagState, SymCond, SymExpr, UnaryOpKind, eval_bitfield, eval_extr,
    reg_name,
};
use super::state::{CallSiteRecord, MemAccessRecord, SymState};

/// Outcome of stepping a single 32-bit AArch64 instruction word.
#[derive(Clone, Debug)]
pub enum StepOutcome {
    /// Straight-line step (`state.pc_off` has been updated to the next instruction offset).
    Next,
    /// Conditional branch (`CBZ`, `CBNZ`, `TBZ`, `TBNZ`, `B.<cond>`).
    CondBranch {
        mnemonic: String,
        cond_lean: String,
        cond: SymCond,
        taken_pc: u64,
        fallthrough_pc: u64,
    },
    /// Function return (`RET`) or tail call (`B <callee>`).
    Return {
        reason: String,
        target: Option<SymExpr>,
    },
    /// Unmodeled or indirect jump (`BR`).
    Halted {
        reason: String,
        target: Option<SymExpr>,
    },
}

// ---------------------------------------------------------------------------
// 1. Operand Shift & Extend Helpers (mirroring `Arm64.shiftVal` / `Arm64.extendVal`)
// ---------------------------------------------------------------------------

/// Evaluate a shifted register operand (`LSL`, `LSR`, `ASR`, `ROR`) at `width` (32 or 64),
/// mirroring `Arm64.shiftVal` in `Arm64/Trusted/ISA/Eval.lean`.
pub fn eval_shifted_reg(
    state: &SymState,
    rm_bits: u64,
    shift_type: u64,
    amount: u64,
    is_64: bool,
) -> SymExpr {
    let rm = state.read_gpr_zr(rm_bits, is_64);
    if amount == 0 {
        return rm;
    }
    let width = if is_64 { 64 } else { 32 };
    let kind = match shift_type {
        0 => BinOpKind::Lsl,
        1 => BinOpKind::Lsr,
        2 => BinOpKind::Asr,
        _ => BinOpKind::Ror,
    };
    SymExpr::binop(kind, width, rm, SymExpr::Const(amount))
}

/// Evaluate a sign- or zero-extended register operand (`UXTB..SXTX`) shifted left by `shift`,
/// mirroring `Arm64.extendVal` in `Arm64/Trusted/ISA/Eval.lean`.
pub fn eval_extended_reg(
    state: &SymState,
    rm_bits: u64,
    option: u64,
    shift: u64,
    is_64: bool,
) -> SymExpr {
    let rm = state.read_gpr_zr(rm_bits, is_64);
    let extended = match option {
        0 => rm.zero_ext(8),
        1 => rm.zero_ext(16),
        2 => rm.zero_ext(32),
        3 => rm,
        4 => rm.sign_ext(8),
        5 => rm.sign_ext(16),
        6 => rm.sign_ext(32),
        _ => rm,
    };
    let width = if is_64 { 64 } else { 32 };
    let shifted = if shift == 0 {
        extended
    } else {
        SymExpr::binop(BinOpKind::Lsl, width, extended, SymExpr::Const(shift))
    };
    if is_64 {
        shifted
    } else {
        shifted.zero_ext(32)
    }
}

// ---------------------------------------------------------------------------
// 2. Data Processing — Immediate
// ---------------------------------------------------------------------------

/// `ADR` / `ADRP`: PC-relative address calculation (`(w & 0x1f00_0000) == 0x1000_0000`).
fn step_adr_adrp(w: u32, state: &mut SymState, pc: u64, next_pc: u64) -> StepOutcome {
    let page = bit(w, 31);
    let immlo = extract(w, 29, 2);
    let immhi = extract(w, 5, 19);
    let imm21 = (immhi << 2) | immlo;
    let sext = sign_extend(imm21, 21);
    let offset = if page { sext << 12 } else { sext };
    let rd = extract(w, 0, 5);
    state.write_gpr_zr(
        rd,
        true,
        SymExpr::PcRel {
            pc_off: pc,
            offset: offset as i64,
            is_page: page,
        },
    );
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `ADD` / `ADDS` / `SUB` / `SUBS` (immediate) (`(w & 0x1f80_0000) == 0x1100_0000`).
fn step_add_sub_imm(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    next_pc: u64,
) -> StepOutcome {
    let is_sub = bit(w, 30);
    let set_flags = bit(w, 29);
    let sh = bit(w, 22);
    let imm12 = extract(w, 10, 12);
    let imm = if sh { imm12 << 12 } else { imm12 };
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let lhs = state.read_gpr_sp(rn_bits, is_64);
    let rhs = SymExpr::Const(imm);
    let res = if is_sub {
        SymExpr::sub(lhs.clone(), rhs.clone(), is_64)
    } else {
        SymExpr::add(lhs.clone(), rhs.clone(), is_64)
    };
    if set_flags {
        state.flags = if is_sub {
            FlagState::Cmp { width, lhs, rhs }
        } else {
            FlagState::Cmn { width, lhs, rhs }
        };
        state.write_gpr_zr(rd_bits, is_64, res);
    } else {
        state.write_gpr_sp(rd_bits, is_64, res);
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `AND` / `ORR` / `EOR` / `ANDS` (bitmask immediate) (`(w & 0x1f80_0000) == 0x1200_0000`).
fn step_logical_imm(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let opc = extract(w, 29, 2);
    let imm_n = bit(w, 22);
    if !is_64 && imm_n {
        return StepOutcome::Halted {
            reason: format!("invalid W32 logical immediate N=1 at +0x{pc:x}"),
            target: None,
        };
    }
    let immr = extract(w, 16, 6);
    let imms = extract(w, 10, 6);
    let Some(mask_raw) = decode_bit_masks(imm_n, imms, immr) else {
        return StepOutcome::Halted {
            reason: format!("invalid logical immediate at +0x{pc:x}"),
            target: None,
        };
    };
    let mask = if is_64 {
        mask_raw
    } else {
        mask_raw & 0xffff_ffff
    };
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let lhs = state.read_gpr_zr(rn_bits, is_64);
    let res = match (&lhs, opc) {
        (SymExpr::Const(a), 0 | 3) => SymExpr::Const(a & mask),
        (SymExpr::Const(a), 1) => SymExpr::Const(a | mask),
        (SymExpr::Const(a), _) => SymExpr::Const(a ^ mask),
        (_, 0 | 3) if mask == 0xff => lhs.zero_ext(8),
        (_, 0 | 3) if mask == 0xffff => lhs.zero_ext(16),
        (_, 0 | 3) if mask == 0xffff_ffff => lhs.zero_ext(32),
        (_, 1) if rn_bits == 31 => SymExpr::Const(mask),
        _ => {
            let kind = match opc {
                0 | 3 => BinOpKind::And,
                1 => BinOpKind::Or,
                _ => BinOpKind::Xor,
            };
            SymExpr::binop(kind, width, lhs, SymExpr::Const(mask))
        }
    };
    if opc == 3 {
        state.flags = FlagState::Tst {
            width,
            res: res.clone(),
        };
        state.write_gpr_zr(rd_bits, is_64, res);
    } else {
        state.write_gpr_sp(rd_bits, is_64, res);
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `MOVN` / `MOVZ` / `MOVK` (move wide immediate) (`(w & 0x1f80_0000) == 0x1280_0000`).
fn step_move_wide(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let opc = extract(w, 29, 2);
    let hw_idx = extract(w, 21, 2);
    if !is_64 && hw_idx >= 2 {
        return StepOutcome::Halted {
            reason: format!("invalid W32 move wide hw={hw_idx} at +0x{pc:x}"),
            target: None,
        };
    }
    let hw = hw_idx * 16;
    let imm16 = extract(w, 5, 16);
    let rd_bits = extract(w, 0, 5);
    let shifted = imm16 << hw;
    let val = match opc {
        0 => {
            // MOVN
            let inv = !shifted;
            SymExpr::Const(if is_64 { inv } else { inv & 0xffff_ffff })
        }
        2 => {
            // MOVZ
            SymExpr::Const(if is_64 {
                shifted
            } else {
                shifted & 0xffff_ffff
            })
        }
        3 => {
            // MOVK
            let old = state.read_gpr_zr(rd_bits, is_64);
            let clear_mask = if is_64 {
                !(0xffffu64 << hw)
            } else {
                (!(0xffffu64 << hw)) & 0xffff_ffff
            };
            let masked = SymExpr::binop(BinOpKind::And, width, old, SymExpr::Const(clear_mask));
            SymExpr::binop(BinOpKind::Or, width, masked, SymExpr::Const(shifted))
        }
        _ => {
            return StepOutcome::Halted {
                reason: format!("unknown move wide opc={opc} at +0x{pc:x}"),
                target: None,
            };
        }
    };
    state.write_gpr_zr(rd_bits, is_64, val);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `SBFM` / `BFM` / `UBFM` (bitfield move) (`(w & 0x1f80_0000) == 0x1300_0000`),
/// mirroring `Arm64.evalBitfield` in `Arm64/Trusted/ISA/Eval.lean`.
fn step_bitfield(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let opc = extract(w, 29, 2);
    let Some(bf_op) = BitfieldOp::from_opc(opc) else {
        return StepOutcome::Halted {
            reason: format!("invalid bitfield opc={opc} at +0x{pc:x}"),
            target: None,
        };
    };
    let imm_n = bit(w, 22);
    let immr = extract(w, 16, 6);
    let imms = extract(w, 10, 6);
    if imm_n != is_64 || (!is_64 && (immr >= 32 || imms >= 32)) {
        return StepOutcome::Halted {
            reason: format!("invalid bitfield immN/immr/imms at +0x{pc:x}"),
            target: None,
        };
    }
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let src = state.read_gpr_zr(rn_bits, is_64);
    let dst = state.read_gpr_zr(rd_bits, is_64);
    let max_bit = if is_64 { 63 } else { 31 };

    let val = match (&dst, &src, bf_op) {
        (_, SymExpr::Const(sc), BitfieldOp::Sbfm | BitfieldOp::Ubfm) => SymExpr::Const(
            eval_bitfield(width, bf_op, 0, *sc, immr as u32, imms as u32),
        ),
        (SymExpr::Const(dc), SymExpr::Const(sc), BitfieldOp::Bfm) => SymExpr::Const(eval_bitfield(
            width,
            bf_op,
            *dc,
            *sc,
            immr as u32,
            imms as u32,
        )),
        _ => match (bf_op, immr, imms) {
            // UXTB / UXTH / UXTW
            (BitfieldOp::Ubfm, 0, 7) => src.zero_ext(8),
            (BitfieldOp::Ubfm, 0, 15) => src.zero_ext(16),
            (BitfieldOp::Ubfm, 0, 31) => src.zero_ext(32),
            // SXTB / SXTH / SXTW
            (BitfieldOp::Sbfm, 0, 7) => src.sign_ext(8),
            (BitfieldOp::Sbfm, 0, 15) => src.sign_ext(16),
            (BitfieldOp::Sbfm, 0, 31) => src.sign_ext(32),
            // LSR immediate: imms == max_bit
            (BitfieldOp::Ubfm, r, s) if s == max_bit => {
                eval_shifted_reg(state, rn_bits, 1, r, is_64)
            }
            // ASR immediate: imms == max_bit
            (BitfieldOp::Sbfm, r, s) if s == max_bit => {
                eval_shifted_reg(state, rn_bits, 2, r, is_64)
            }
            // LSL immediate: imms + 1 == immr
            (BitfieldOp::Ubfm, r, s) if r > 0 && s + 1 == r => {
                let shl = (max_bit + 1) - r;
                eval_shifted_reg(state, rn_bits, 0, shl, is_64)
            }
            _ => SymExpr::Bitfield {
                op: bf_op,
                width,
                dst: Box::new(dst),
                src: Box::new(src),
                immr: immr as u32,
                imms: imms as u32,
            },
        },
    };
    state.write_gpr_zr(rd_bits, is_64, val);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `EXTR` / `ROR` immediate (`(w & 0x7f80_0000) == 0x1380_0000`).
fn step_extr(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let imm_n = bit(w, 22);
    let o0 = bit(w, 21);
    let rm_bits = extract(w, 16, 5);
    let lsb = extract(w, 10, 6);
    if imm_n != is_64 || o0 || (!is_64 && lsb >= 32) {
        return StepOutcome::Halted {
            reason: format!("invalid EXTR encoding at +0x{pc:x}"),
            target: None,
        };
    }
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let val = if rm_bits == rn_bits {
        eval_shifted_reg(state, rn_bits, 3, lsb, is_64)
    } else {
        let rn = state.read_gpr_zr(rn_bits, is_64);
        let rm = state.read_gpr_zr(rm_bits, is_64);
        if lsb == 0 {
            rm
        } else if let (SymExpr::Const(nc), SymExpr::Const(mc)) = (&rn, &rm) {
            SymExpr::Const(eval_extr(width, *nc, *mc, lsb as u32))
        } else {
            SymExpr::Extr {
                width,
                rn: Box::new(rn),
                rm: Box::new(rm),
                lsb: lsb as u32,
            }
        }
    };
    state.write_gpr_zr(rd_bits, is_64, val);
    state.pc_off = next_pc;
    StepOutcome::Next
}

// ---------------------------------------------------------------------------
// 3. Data Processing — Register
// ---------------------------------------------------------------------------

/// `AND` / `BIC` / `ORR` / `ORN` / `EOR` / `EON` / `ANDS` / `BICS` (shifted register)
/// (`(w & 0x1f00_0000) == 0x0a00_0000`), mirroring `Arm64.evalLogical` in `Arm64/Trusted/ISA/Eval.lean`.
fn step_logical_shifted(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let opc = extract(w, 29, 2);
    let n_bit = bit(w, 21);
    let shift_type = extract(w, 22, 2);
    let rm_bits = extract(w, 16, 5);
    let imm6 = extract(w, 10, 6);
    if !is_64 && imm6 >= 32 {
        return StepOutcome::Halted {
            reason: format!("invalid W32 logical shifted imm6={imm6} at +0x{pc:x}"),
            target: None,
        };
    }
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);

    let lhs = state.read_gpr_zr(rn_bits, is_64);
    let rhs_shifted = eval_shifted_reg(state, rm_bits, shift_type, imm6, is_64);
    // Handle `mov rd, rm` (`orr rd, xzr, rm, shift #imm`) and `mvn rd, rm` (`orn rd, xzr, rm, shift #imm`)
    let res = if opc == 1 && rn_bits == 31 {
        if n_bit {
            SymExpr::bit_not(rhs_shifted, width)
        } else {
            rhs_shifted
        }
    } else {
        let rhs = if n_bit {
            SymExpr::bit_not(rhs_shifted, width)
        } else {
            rhs_shifted
        };
        let kind = match opc {
            0 | 3 => BinOpKind::And,
            1 => BinOpKind::Or,
            _ => BinOpKind::Xor,
        };
        SymExpr::binop(kind, width, lhs, rhs)
    };
    if opc == 3 {
        state.flags = FlagState::Tst {
            width,
            res: res.clone(),
        };
    }
    state.write_gpr_zr(rd_bits, is_64, res);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `ADD` / `ADDS` / `SUB` / `SUBS` (shifted register) (`(w & 0x1f20_0000) == 0x0b00_0000`).
fn step_add_sub_shifted(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let is_sub = bit(w, 30);
    let set_flags = bit(w, 29);
    let shift_type = extract(w, 22, 2);
    let rm_bits = extract(w, 16, 5);
    let imm6 = extract(w, 10, 6);
    if shift_type == 3 || (!is_64 && imm6 >= 32) {
        return StepOutcome::Halted {
            reason: format!("invalid add/sub shifted encoding at +0x{pc:x}"),
            target: None,
        };
    }
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);

    let lhs = state.read_gpr_zr(rn_bits, is_64);
    let rhs = eval_shifted_reg(state, rm_bits, shift_type, imm6, is_64);
    let res = if is_sub {
        SymExpr::sub(lhs.clone(), rhs.clone(), is_64)
    } else {
        SymExpr::add(lhs.clone(), rhs.clone(), is_64)
    };
    if set_flags {
        state.flags = if is_sub {
            FlagState::Cmp { width, lhs, rhs }
        } else {
            FlagState::Cmn { width, lhs, rhs }
        };
    }
    state.write_gpr_zr(rd_bits, is_64, res);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `ADD` / `ADDS` / `SUB` / `SUBS` (extended register) (`(w & 0x1fe0_0000) == 0x0b20_0000`).
fn step_add_sub_extended(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let is_sub = bit(w, 30);
    let set_flags = bit(w, 29);
    let rm_bits = extract(w, 16, 5);
    let option = extract(w, 13, 3);
    let imm3 = extract(w, 10, 3);
    if imm3 > 4 {
        return StepOutcome::Halted {
            reason: format!("invalid add/sub extended imm3={imm3} at +0x{pc:x}"),
            target: None,
        };
    }
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);

    let lhs = state.read_gpr_sp(rn_bits, is_64);
    let rhs = eval_extended_reg(state, rm_bits, option, imm3, is_64);
    let res = if is_sub {
        SymExpr::sub(lhs.clone(), rhs.clone(), is_64)
    } else {
        SymExpr::add(lhs.clone(), rhs.clone(), is_64)
    };
    if set_flags {
        state.flags = if is_sub {
            FlagState::Cmp { width, lhs, rhs }
        } else {
            FlagState::Cmn { width, lhs, rhs }
        };
        state.write_gpr_zr(rd_bits, is_64, res);
    } else {
        state.write_gpr_sp(rd_bits, is_64, res);
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `ADC` / `ADCS` / `SBC` / `SBCS` (`(w & 0x1fe0_fc00) == 0x1a00_0000`).
fn step_add_sub_carry(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    next_pc: u64,
) -> StepOutcome {
    let is_sub = bit(w, 30);
    let set_flags = bit(w, 29);
    let rm_bits = extract(w, 16, 5);
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let lhs = state.read_gpr_zr(rn_bits, is_64);
    let rhs = state.read_gpr_zr(rm_bits, is_64);
    let carry_flags = state.flags.clone();
    let res = SymExpr::AdcSbc {
        is_sub,
        width,
        lhs: Box::new(lhs.clone()),
        rhs: Box::new(rhs.clone()),
        flags: Box::new(carry_flags.clone()),
    };
    if set_flags {
        state.flags = FlagState::AdcSbc {
            is_sub,
            width,
            lhs,
            rhs,
            carry_in: Box::new(carry_flags),
        };
    }
    state.write_gpr_zr(rd_bits, is_64, res);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `CCMN` / `CCMP` (register and 5-bit immediate) (`(w & 0x3fe0_0410) == 0x3a40_0000`).
fn step_cond_compare(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    next_pc: u64,
) -> StepOutcome {
    let is_sub = bit(w, 30);
    let is_imm = bit(w, 11);
    let rm_or_imm = extract(w, 16, 5);
    let cond_bits = extract(w, 12, 4) as u8;
    let rn_bits = extract(w, 5, 5);
    let nzcv_imm = extract(w, 0, 4) as u8;
    let lhs = state.read_gpr_zr(rn_bits, is_64);
    let rhs = if is_imm {
        SymExpr::Const(rm_or_imm)
    } else {
        state.read_gpr_zr(rm_or_imm, is_64)
    };
    let prev = state.flags.clone();
    state.flags = FlagState::Ccmp {
        is_sub,
        width,
        lhs,
        rhs,
        cond_bits,
        nzcv_imm,
        prev_flags: Box::new(prev),
    };
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `CSEL` / `CSINC` / `CSINV` / `CSNEG` (`(w & 0x3fe0_0800) == 0x1a80_0000`).
fn step_cond_select(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    next_pc: u64,
) -> StepOutcome {
    let is_inv = bit(w, 30);
    let is_inc = bit(w, 10);
    let rm_bits = extract(w, 16, 5);
    let cond_bits = extract(w, 12, 4) as u8;
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);

    let then_val = state.read_gpr_zr(rn_bits, is_64);
    let rm = state.read_gpr_zr(rm_bits, is_64);
    let else_val = match (is_inv, is_inc) {
        (false, false) => rm,
        (false, true) => SymExpr::add(rm, SymExpr::Const(1), is_64),
        (true, false) => SymExpr::bit_not(rm, width),
        (true, true) => SymExpr::sub(SymExpr::Const(0), rm, is_64),
    };
    let cond = SymCond::FlagCond {
        cond_bits,
        flags: state.flags.clone(),
    };
    let val = SymExpr::ite(cond, then_val, else_val);
    state.write_gpr_zr(rd_bits, is_64, val);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `RBIT` / `REV16` / `REV32` / `REV` / `CLZ` / `CLS` (`(w & 0x7fff_0000) == 0x5ac0_0000`).
fn step_dataproc_1src(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let opcode = extract(w, 10, 6);
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let rn = state.read_gpr_zr(rn_bits, is_64);
    let op = match (is_64, opcode) {
        (_, 0) => UnaryOpKind::Rbit,
        (_, 1) => UnaryOpKind::Rev16,
        (false, 2) => UnaryOpKind::Rev32,
        (true, 2) => UnaryOpKind::Rev32,
        (true, 3) => UnaryOpKind::Rev64,
        (_, 4) => UnaryOpKind::Clz,
        (_, 5) => UnaryOpKind::Cls,
        _ => {
            return StepOutcome::Halted {
                reason: format!("unknown 1-source opcode={opcode} (is_64={is_64}) at +0x{pc:x}"),
                target: None,
            };
        }
    };
    let val = SymExpr::unary_op(op, width, rn);
    state.write_gpr_zr(rd_bits, is_64, val);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `UDIV` / `SDIV` / `LSLV` / `LSRV` / `ASRV` / `RORV` (`(w & 0x7fe0_0000) == 0x1ac0_0000`).
fn step_dataproc_2src(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let opcode = extract(w, 10, 6);
    let rm_bits = extract(w, 16, 5);
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);
    let lhs = state.read_gpr_zr(rn_bits, is_64);
    let rhs = state.read_gpr_zr(rm_bits, is_64);
    let kind = match opcode {
        2 => BinOpKind::UDiv,
        3 => BinOpKind::SDiv,
        8 => BinOpKind::Lsl,
        9 => BinOpKind::Lsr,
        10 => BinOpKind::Asr,
        11 => BinOpKind::Ror,
        _ => {
            return StepOutcome::Halted {
                reason: format!("unknown 2-source opcode={opcode} at +0x{pc:x}"),
                target: None,
            };
        }
    };
    let val = SymExpr::binop(kind, width, lhs, rhs);
    state.write_gpr_zr(rd_bits, is_64, val);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `MADD` / `MSUB` / `SMADDL` / `SMSUBL` / `SMULH` / `UMADDL` / `UMSUBL` / `UMULH`
/// (`(w & 0x7f00_0000) == 0x1b00_0000`).
fn step_dataproc_3src(
    w: u32,
    state: &mut SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let op31 = extract(w, 21, 3);
    let is_sub = bit(w, 15);
    let rm_bits = extract(w, 16, 5);
    let ra_bits = extract(w, 10, 5);
    let rn_bits = extract(w, 5, 5);
    let rd_bits = extract(w, 0, 5);

    match (is_64, op31, is_sub) {
        // MADD / MSUB (32-bit or 64-bit)
        (_, 0, _) => {
            let rn = state.read_gpr_zr(rn_bits, is_64);
            let rm = state.read_gpr_zr(rm_bits, is_64);
            let prod = SymExpr::binop(BinOpKind::Mul, width, rn, rm);
            let res = if ra_bits == 31 && !is_sub {
                prod
            } else {
                let ra = state.read_gpr_zr(ra_bits, is_64);
                if is_sub {
                    SymExpr::sub(ra, prod, is_64)
                } else {
                    SymExpr::add(ra, prod, is_64)
                }
            };
            state.write_gpr_zr(rd_bits, is_64, res);
        }
        // SMADDL / SMSUBL: signed 32x32 -> 64 multiply-accumulate
        (true, 1, _) => {
            let rn = state.read_gpr_zr(rn_bits, false).sign_ext(32);
            let rm = state.read_gpr_zr(rm_bits, false).sign_ext(32);
            let prod = SymExpr::binop(BinOpKind::Mul, 64, rn, rm);
            let res = if ra_bits == 31 && !is_sub {
                prod
            } else {
                let ra = state.read_gpr_zr(ra_bits, true);
                if is_sub {
                    SymExpr::sub(ra, prod, true)
                } else {
                    SymExpr::add(ra, prod, true)
                }
            };
            state.write_gpr_zr(rd_bits, true, res);
        }
        // SMULH: signed 64x64 high-half multiply
        (true, 2, false) if ra_bits == 31 => {
            let rn = state.read_gpr_zr(rn_bits, true);
            let rm = state.read_gpr_zr(rm_bits, true);
            let res = SymExpr::binop(BinOpKind::Smulh, 64, rn, rm);
            state.write_gpr_zr(rd_bits, true, res);
        }
        // UMADDL / UMSUBL: unsigned 32x32 -> 64 multiply-accumulate
        (true, 5, _) => {
            let rn = state.read_gpr_zr(rn_bits, false);
            let rm = state.read_gpr_zr(rm_bits, false);
            let prod = SymExpr::binop(BinOpKind::Mul, 64, rn, rm);
            let res = if ra_bits == 31 && !is_sub {
                prod
            } else {
                let ra = state.read_gpr_zr(ra_bits, true);
                if is_sub {
                    SymExpr::sub(ra, prod, true)
                } else {
                    SymExpr::add(ra, prod, true)
                }
            };
            state.write_gpr_zr(rd_bits, true, res);
        }
        // UMULH: unsigned 64x64 high-half multiply
        (true, 6, false) if ra_bits == 31 => {
            let rn = state.read_gpr_zr(rn_bits, true);
            let rm = state.read_gpr_zr(rm_bits, true);
            let res = SymExpr::binop(BinOpKind::Umulh, 64, rn, rm);
            state.write_gpr_zr(rd_bits, true, res);
        }
        _ => {
            return StepOutcome::Halted {
                reason: format!("unknown 3-source op31={op31} o0={is_sub} at +0x{pc:x}"),
                target: None,
            };
        }
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

// ---------------------------------------------------------------------------
// 4. Loads and Stores
// ---------------------------------------------------------------------------

/// Execute a single-register load or store at `addr`, applying optional base writeback `wb`
/// in architectural order (writeback before destination register update on loads).
pub(super) fn exec_single_load_store(
    state: &mut SymState,
    pc: u64,
    size_bits: u64,
    opc: u64,
    rt_bits: u64,
    addr: &SymExpr,
    wb: Option<(u64, SymExpr)>,
    width_bits: u32,
    accesses: &mut Vec<MemAccessRecord>,
) -> bool {
    match (size_bits, opc) {
        (0..=3, 0) => {
            // STRB / STRH / STR (32/64)
            let is_64 = size_bits == 3;
            let val = state.read_gpr_zr(rt_bits, is_64);
            state.store_mem(pc, addr, width_bits, val, accesses);
            if let Some((rn_bits, wb_val)) = wb {
                state.write_gpr_sp(rn_bits, true, wb_val);
            }
            true
        }
        (0..=3, 1) => {
            // LDRB / LDRH / LDR (32/64)
            let is_64 = size_bits == 3;
            let val = state.load_mem(pc, addr, width_bits, None, accesses);
            if let Some((rn_bits, wb_val)) = wb {
                state.write_gpr_sp(rn_bits, true, wb_val);
            }
            state.write_gpr_zr(rt_bits, is_64, val);
            true
        }
        (0..=2, 2) => {
            // LDRSB / LDRSH / LDRSW (sign-extend to 64-bit)
            let val = state.load_mem(pc, addr, width_bits, Some(64), accesses);
            if let Some((rn_bits, wb_val)) = wb {
                state.write_gpr_sp(rn_bits, true, wb_val);
            }
            state.write_gpr_zr(rt_bits, true, val);
            true
        }
        (0..=1, 3) => {
            // LDRSB / LDRSH (sign-extend to 32-bit, zero-extend to 64-bit)
            let val = state.load_mem(pc, addr, width_bits, Some(32), accesses);
            if let Some((rn_bits, wb_val)) = wb {
                state.write_gpr_sp(rn_bits, true, wb_val);
            }
            state.write_gpr_zr(rt_bits, false, val);
            true
        }
        _ => false,
    }
}

/// `LDP` / `STP` / `LDPSW` (load/store pair) (`(w & 0x3e00_0000) == 0x2800_0000`).
pub(super) fn step_load_store_pair(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let opc = extract(w, 30, 2);
    let mode_bits = extract(w, 23, 2);
    let is_load = bit(w, 22);
    if opc == 3 || (!is_load && opc == 1) {
        return StepOutcome::Halted {
            reason: format!("invalid ldp/stp opc={opc} is_load={is_load} at +0x{pc:x}"),
            target: None,
        };
    }
    let imm7 = extract(w, 15, 7);
    let scale = if opc == 2 { 3 } else { 2 };
    let offset = sign_extend(imm7, 7) << scale;
    let step_bytes = if opc == 2 { 8u64 } else { 4u64 };
    let width_bits = (step_bytes * 8) as u32;
    let rt2_bits = extract(w, 10, 5);
    let rn_bits = extract(w, 5, 5);
    let rt1_bits = extract(w, 0, 5);

    let base = state.read_gpr_sp(rn_bits, true);
    let addr1 = match mode_bits {
        1 => base.clone(),                       // Post-index
        2 | 3 => base.clone().add_const(offset), // Signed offset or Pre-index
        _ => {
            return StepOutcome::Halted {
                reason: format!("unsupported ldp/stp mode={mode_bits} at +0x{pc:x}"),
                target: None,
            };
        }
    };
    let addr2 = addr1.clone().add_const(step_bytes);
    let wb = (mode_bits == 1 || mode_bits == 3).then(|| base.add_const(offset));

    if is_load {
        let signed_to = (opc == 1).then_some(64);
        let is_64_pair = opc >= 1;
        let v1 = state.load_mem(pc, &addr1, width_bits, signed_to, accesses);
        let v2 = state.load_mem(pc, &addr2, width_bits, signed_to, accesses);
        if let Some(wb_val) = wb {
            state.write_gpr_sp(rn_bits, true, wb_val);
        }
        state.write_gpr_zr(rt1_bits, is_64_pair, v1);
        state.write_gpr_zr(rt2_bits, is_64_pair, v2);
    } else {
        let is_64_pair = opc == 2;
        let v1 = state.read_gpr_zr(rt1_bits, is_64_pair);
        let v2 = state.read_gpr_zr(rt2_bits, is_64_pair);
        state.store_mem(pc, &addr1, width_bits, v1, accesses);
        state.store_mem(pc, &addr2, width_bits, v2, accesses);
        if let Some(wb_val) = wb {
            state.write_gpr_sp(rn_bits, true, wb_val);
        }
    }

    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `LDR*` / `STR*` (unsigned scaled 12-bit immediate) (`(w & 0x3f00_0000) == 0x3900_0000`).
fn step_load_store_unsigned_imm(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let size_bits = extract(w, 30, 2);
    let opc = extract(w, 22, 2);
    let imm12 = extract(w, 10, 12);
    let offset = imm12 << size_bits;
    let rn_bits = extract(w, 5, 5);
    let rt_bits = extract(w, 0, 5);
    let width_bits = 8u32 << size_bits;
    let base = state.read_gpr_sp(rn_bits, true);
    let addr = base.add_const(offset);
    if !exec_single_load_store(
        state, pc, size_bits, opc, rt_bits, &addr, None, width_bits, accesses,
    ) {
        return StepOutcome::Halted {
            reason: format!("unsupported ldr/str size={size_bits} opc={opc} at +0x{pc:x}"),
            target: None,
        };
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `LDUR*` / `STUR*` (unscaled immediate), pre/post-indexed `LDR*`/`STR*`, and register-offset
/// `LDR*`/`STR*` (`(w & 0x3f00_0000) == 0x3800_0000`).
fn step_load_store_unscaled_or_reg(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> Option<StepOutcome> {
    let size_bits = extract(w, 30, 2);
    let opc = extract(w, 22, 2);
    let rn_bits = extract(w, 5, 5);
    let rt_bits = extract(w, 0, 5);
    let width_bits = 8u32 << size_bits;
    let base = state.read_gpr_sp(rn_bits, true);

    if !bit(w, 21) {
        let imm9 = extract(w, 12, 9);
        let offset = sign_extend(imm9, 9);
        let mode = extract(w, 10, 2);
        if mode != 0 && mode != 1 && mode != 3 {
            return None;
        }
        let addr = match mode {
            1 => base.clone(),
            _ => base.clone().add_const(offset),
        };
        let wb = (mode == 1 || mode == 3).then(|| (rn_bits, base.add_const(offset)));
        if !exec_single_load_store(
            state, pc, size_bits, opc, rt_bits, &addr, wb, width_bits, accesses,
        ) {
            return None;
        }
        state.pc_off = next_pc;
        Some(StepOutcome::Next)
    } else if extract(w, 10, 2) == 2 {
        let rm_bits = extract(w, 16, 5);
        let option = extract(w, 13, 3);
        let s_bit = bit(w, 12);
        let shift = if s_bit { size_bits } else { 0 };
        let off_expr = eval_extended_reg(state, rm_bits, option, shift, true);
        let addr = SymExpr::add(base, off_expr, true);
        if !exec_single_load_store(
            state, pc, size_bits, opc, rt_bits, &addr, None, width_bits, accesses,
        ) {
            return None;
        }
        state.pc_off = next_pc;
        Some(StepOutcome::Next)
    } else {
        None
    }
}

/// `LDR` (32/64) / `LDRSW` (PC-relative literal) (`(w & 0x3f00_0000) == 0x1800_0000`).
fn step_load_literal(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let opc = extract(w, 30, 2);
    let imm19 = extract(w, 5, 19);
    let offset = sign_extend(imm19, 19) << 2;
    let rt_bits = extract(w, 0, 5);
    let addr = SymExpr::PcRel {
        pc_off: pc,
        offset: offset as i64,
        is_page: false,
    };
    match opc {
        0 => {
            let val = state.load_mem(pc, &addr, 32, None, accesses);
            state.write_gpr_zr(rt_bits, false, val);
        }
        1 => {
            let val = state.load_mem(pc, &addr, 64, None, accesses);
            state.write_gpr_zr(rt_bits, true, val);
        }
        2 => {
            let val = state.load_mem(pc, &addr, 32, Some(64), accesses);
            state.write_gpr_zr(rt_bits, true, val);
        }
        _ => {
            return StepOutcome::Halted {
                reason: format!("unsupported literal load opc={opc} at +0x{pc:x}"),
                target: None,
            };
        }
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `LDARB` / `LDARH` / `LDAR` / `STLRB` / `STLRH` / `STLR` (`(w & 0x3fbf_fc00) == 0x089f_fc00`).
fn step_ldar_stlr(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let size_bits = extract(w, 30, 2);
    let is_load = bit(w, 22);
    let rn_bits = extract(w, 5, 5);
    let rt_bits = extract(w, 0, 5);
    let width_bits = 8u32 << size_bits;
    let is_64 = size_bits == 3;
    let addr = state.read_gpr_sp(rn_bits, true);
    if is_load {
        let val = state.load_mem(pc, &addr, width_bits, None, accesses);
        state.write_gpr_zr(rt_bits, is_64, val);
    } else {
        let val = state.read_gpr_zr(rt_bits, is_64);
        state.store_mem(pc, &addr, width_bits, val, accesses);
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `LDXR*` / `LDAXR*` (`(w & 0x3fff_7c00) == 0x085f_7c00`) and `STXR*` / `STLXR*`
/// (`(w & 0x3fe0_7c00) == 0x0800_7c00`). The trusted model is single-threaded, so the
/// exclusive monitor always succeeds: loads are plain loads and stores write `Ws := 0`.
fn step_ldxr_stxr(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let size_bits = extract(w, 30, 2);
    let is_load = bit(w, 22);
    let rs_bits = extract(w, 16, 5);
    let rn_bits = extract(w, 5, 5);
    let rt_bits = extract(w, 0, 5);
    let width_bits = 8u32 << size_bits;
    let is_64 = size_bits == 3;
    let addr = state.read_gpr_sp(rn_bits, true);
    if is_load {
        let val = state.load_mem(pc, &addr, width_bits, None, accesses);
        state.write_gpr_zr(rt_bits, is_64, val);
    } else {
        let val = state.read_gpr_zr(rt_bits, is_64);
        state.store_mem(pc, &addr, width_bits, val, accesses);
        state.write_gpr_zr(rs_bits, false, SymExpr::Const(0));
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

// ---------------------------------------------------------------------------
// 5. Branches & System Instructions
// ---------------------------------------------------------------------------

fn sanitize_ident(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

/// `B` / `BL` (unconditional branch immediate) (`(w & 0x7c00_0000) == 0x1400_0000`).
fn step_branch_imm(
    w: u32,
    state: &mut SymState,
    callees_by_off: &BTreeMap<u64, &CalleeInfo>,
    fn_size: u64,
    pc: u64,
    next_pc: u64,
    calls: &mut Vec<CallSiteRecord>,
) -> StepOutcome {
    let is_bl = bit(w, 31);
    let imm26 = extract(w, 0, 26);
    let disp = (sign_extend(imm26, 26) << 2) as i64;
    let target_pc = (pc as i64).wrapping_add(disp) as u64;

    if let Some(callee_info) = callees_by_off.get(&pc) {
        let mut args = BTreeMap::new();
        for r in 0..=8u8 {
            let v = &state.regs[r as usize];
            if *v != SymExpr::InitReg(r) || r <= 3 {
                args.insert(reg_name(r).to_string(), v.to_lean());
            }
        }
        calls.push(CallSiteRecord {
            call_offset: pc,
            call_offset_hex: format!("0x{pc:x}"),
            callee: callee_info.callee.clone(),
            is_tail_call: callee_info.is_tail_call,
            is_extern: callee_info.is_extern,
            args,
            sp_lean: state.regs[31].to_lean(),
        });
        if !is_bl && callee_info.is_tail_call {
            return StepOutcome::Return {
                reason: format!("tail_call {}", callee_info.callee),
                target: Some(SymExpr::PcRel {
                    pc_off: target_pc,
                    offset: 0,
                    is_page: false,
                }),
            };
        }
        if is_bl {
            state.regs[0] = SymExpr::CallRet {
                callee: sanitize_ident(&callee_info.callee),
                call_offset: pc,
            };
            state.regs[30] = SymExpr::Unary {
                desc: format!("(fn_entry + 0x{next_pc:x}#64)"),
            };
            state.flags = FlagState::Unknown;
            state.pc_off = next_pc;
            return StepOutcome::Next;
        }
    }

    if is_bl {
        let callee_name = format!("sub_0x{target_pc:x}");
        let mut args = BTreeMap::new();
        for r in 0..=3u8 {
            args.insert(reg_name(r).to_string(), state.regs[r as usize].to_lean());
        }
        calls.push(CallSiteRecord {
            call_offset: pc,
            call_offset_hex: format!("0x{pc:x}"),
            callee: callee_name.clone(),
            is_tail_call: false,
            is_extern: false,
            args,
            sp_lean: state.regs[31].to_lean(),
        });
        state.regs[0] = SymExpr::CallRet {
            callee: callee_name,
            call_offset: pc,
        };
        state.regs[30] = SymExpr::Unary {
            desc: format!("(fn_entry + 0x{next_pc:x}#64)"),
        };
        state.flags = FlagState::Unknown;
        state.pc_off = next_pc;
        return StepOutcome::Next;
    }

    // Intra-function unconditional branch `b target_pc`
    if target_pc < fn_size {
        state.pc_off = target_pc;
        StepOutcome::Next
    } else {
        StepOutcome::Return {
            reason: format!("tail_branch 0x{target_pc:x}"),
            target: Some(SymExpr::PcRel {
                pc_off: target_pc,
                offset: 0,
                is_page: false,
            }),
        }
    }
}

/// `CBZ` / `CBNZ` (compare and branch on zero / non-zero) (`(w & 0x7e00_0000) == 0x3400_0000`).
fn step_cbz_cbnz(
    w: u32,
    state: &SymState,
    is_64: bool,
    width: u32,
    pc: u64,
    next_pc: u64,
) -> StepOutcome {
    let is_nz = bit(w, 24);
    let imm19 = extract(w, 5, 19);
    let disp = (sign_extend(imm19, 19) << 2) as i64;
    let target_pc = (pc as i64).wrapping_add(disp) as u64;
    let rt_bits = extract(w, 0, 5);
    let rt_val = state.read_gpr_zr(rt_bits, is_64);
    let cond = SymCond::Cbz {
        is_nz,
        width,
        val: rt_val,
    };
    let cond_lean = cond.to_lean();
    let mnemonic = if is_nz { "cbnz" } else { "cbz" }.to_string();
    StepOutcome::CondBranch {
        mnemonic,
        cond_lean,
        cond,
        taken_pc: target_pc,
        fallthrough_pc: next_pc,
    }
}

/// `TBZ` / `TBNZ` (test bit and branch) (`(w & 0x7e00_0000) == 0x3600_0000`).
fn step_tbz_tbnz(w: u32, state: &SymState, pc: u64, next_pc: u64) -> StepOutcome {
    let is_nz = bit(w, 24);
    let b5 = if bit(w, 31) { 32 } else { 0 };
    let b40 = extract(w, 19, 5);
    let bit_pos = (b5 + b40) as u32;
    let imm14 = extract(w, 5, 14);
    let disp = (sign_extend(imm14, 14) << 2) as i64;
    let target_pc = (pc as i64).wrapping_add(disp) as u64;
    let rt_bits = extract(w, 0, 5);
    let rt_val = state.read_gpr_zr(rt_bits, true);
    let cond = SymCond::Tbz {
        is_nz,
        bit_pos,
        val: rt_val,
    };
    let cond_lean = cond.to_lean();
    let mnemonic = if is_nz { "tbnz" } else { "tbz" }.to_string();
    StepOutcome::CondBranch {
        mnemonic,
        cond_lean,
        cond,
        taken_pc: target_pc,
        fallthrough_pc: next_pc,
    }
}

/// `B.<cond>` (conditional branch) (`(w & 0xff00_0010) == 0x5400_0000`).
fn step_b_cond(w: u32, state: &mut SymState, pc: u64, next_pc: u64) -> StepOutcome {
    let imm19 = extract(w, 5, 19);
    let disp = (sign_extend(imm19, 19) << 2) as i64;
    let target_pc = (pc as i64).wrapping_add(disp) as u64;
    let cond_bits = extract(w, 0, 4) as u8;
    if cond_bits == 14 || cond_bits == 15 {
        state.pc_off = target_pc;
        return StepOutcome::Next;
    }
    let cond = SymCond::FlagCond {
        cond_bits,
        flags: state.flags.clone(),
    };
    let cond_lean = cond.to_lean();
    StepOutcome::CondBranch {
        mnemonic: format!("b.cond({cond_bits})"),
        cond_lean,
        cond,
        taken_pc: target_pc,
        fallthrough_pc: next_pc,
    }
}

/// `BR` / `BLR` / `RET` (unconditional branch to register) (`(w & 0xff9f_fc1f) == 0xd61f_0000`).
fn step_branch_reg(w: u32, state: &mut SymState, pc: u64, next_pc: u64) -> StepOutcome {
    let opc = extract(w, 21, 2);
    let rn_bits = extract(w, 5, 5);
    let target_expr = state.read_gpr_zr(rn_bits, true);
    match opc {
        2 => StepOutcome::Return {
            reason: "ret".into(),
            target: Some(target_expr),
        },
        1 => {
            // BLR
            let target = target_expr.to_lean();
            state.regs[0] = SymExpr::CallRet {
                callee: format!("blr_{target}"),
                call_offset: pc,
            };
            state.regs[30] = SymExpr::Unary {
                desc: format!("(fn_entry + 0x{next_pc:x}#64)"),
            };
            state.flags = FlagState::Unknown;
            state.pc_off = next_pc;
            StepOutcome::Next
        }
        _ => StepOutcome::Halted {
            reason: format!("indirect branch br x{rn_bits} at +0x{pc:x}"),
            target: Some(target_expr),
        },
    }
}

/// `MRS` / `MSR` (`TPIDR_EL0`, `NZCV`, read-only `DCZID_EL0`) (`(w & 0xffd0_0000) == 0xd510_0000`).
fn step_sysreg(w: u32, state: &mut SymState, next_pc: u64) -> StepOutcome {
    let is_read = bit(w, 21);
    let sysreg = extract(w, 5, 15);
    let rt_bits = extract(w, 0, 5);
    let unsupported = |why: &str| StepOutcome::Halted {
        reason: format!("unsupported sysreg 0x{sysreg:x}{why}"),
        target: None,
    };
    // TPIDR_EL0 encoding is op0=3, op1=3, CRn=13, CRm=0, op2=2 (`0x5e82`).
    if sysreg == 0x5e82 {
        if is_read {
            let val = state.tpidr_el0.clone();
            state.write_gpr_zr(rt_bits, true, val);
        } else {
            state.tpidr_el0 = state.read_gpr_zr(rt_bits, true);
        }
    } else if sysreg == 0x5807 && is_read {
        // DCZID_EL0: DZP = 0, BS = 4 (64-byte DC ZVA block), as in `Eval.lean`.
        state.write_gpr_zr(rt_bits, true, SymExpr::Const(4));
    } else if sysreg == 0x5a10 {
        // NZCV (bits 31..28). Only concrete flag values are representable here.
        if is_read {
            let FlagState::Literal(nzcv) = state.flags else {
                return unsupported(" (MRS of symbolic NZCV)");
            };
            state.write_gpr_zr(rt_bits, true, SymExpr::Const(nzcv.to_pstate_u64()));
        } else {
            let SymExpr::Const(v) = state.read_gpr_zr(rt_bits, true) else {
                return unsupported(" (MSR of symbolic value to NZCV)");
            };
            state.flags = FlagState::Literal(super::expr::Nzcv::from_pstate_u64(v));
        }
    } else {
        return unsupported("");
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

// ---------------------------------------------------------------------------
// 6. Top-Level Instruction Dispatcher (`step_instruction`)
// ---------------------------------------------------------------------------

/// Step a single 32-bit AArch64 instruction word `w` on `state`.
pub fn step_instruction(
    w: u32,
    state: &mut SymState,
    callees_by_off: &BTreeMap<u64, &CalleeInfo>,
    fn_size: u64,
    accesses: &mut Vec<MemAccessRecord>,
    calls: &mut Vec<CallSiteRecord>,
) -> StepOutcome {
    let pc = state.pc_off;
    let next_pc = pc + 4;
    let is_64 = bit(w, 31);
    let width = if is_64 { 64 } else { 32 };

    // 1. NOP / Barriers (DMB, DSB, ISB, CLREX)
    if w == 0xd503_201f || (w & 0xffff_f01f) == 0xd503_301f {
        state.pc_off = next_pc;
        return StepOutcome::Next;
    }

    // 1b. Constructors for sequential atomics / C++ & Go idioms (`atomics.rs`): HINT, UDF,
    // DC ZVA, CRC32, LDNP/STNP, PRFM*, LSE, LDAPR, LDAPUR/STLUR, LDXP/STXP, CAS, CASP, LD1/ST1
    // (multiple) and LD1R writeback. Keyed on `decode_word_to_lean` so the matched encodings
    // follow `Decode.lean` priority (several overlap the legacy groups below).
    if let Some(outcome) = super::atomics::step_atomic_or_hint(w, state, pc, next_pc, accesses) {
        return outcome;
    }

    // 2. ADR / ADRP
    if (w & 0x1f00_0000) == 0x1000_0000 {
        return step_adr_adrp(w, state, pc, next_pc);
    }

    // 3. Add/Subtract (immediate)
    if (w & 0x1f80_0000) == 0x1100_0000 {
        return step_add_sub_imm(w, state, is_64, width, next_pc);
    }

    // 4. Logical (immediate)
    if (w & 0x1f80_0000) == 0x1200_0000 {
        return step_logical_imm(w, state, is_64, width, pc, next_pc);
    }

    // 5. Move Wide (MOVN, MOVZ, MOVK)
    if (w & 0x1f80_0000) == 0x1280_0000 {
        return step_move_wide(w, state, is_64, width, pc, next_pc);
    }

    // 6. Bitfield (SBFM, BFM, UBFM)
    if (w & 0x1f80_0000) == 0x1300_0000 {
        return step_bitfield(w, state, is_64, width, pc, next_pc);
    }

    // 7. Extract (EXTR / ROR immediate)
    if (w & 0x7f80_0000) == 0x1380_0000 {
        return step_extr(w, state, is_64, width, pc, next_pc);
    }

    // 8. Unconditional branch (B / BL)
    if (w & 0x7c00_0000) == 0x1400_0000 {
        return step_branch_imm(w, state, callees_by_off, fn_size, pc, next_pc, calls);
    }

    // 9. Compare and branch (CBZ, CBNZ)
    if (w & 0x7e00_0000) == 0x3400_0000 {
        return step_cbz_cbnz(w, state, is_64, width, pc, next_pc);
    }

    // 10. Test bit and branch (TBZ, TBNZ)
    if (w & 0x7e00_0000) == 0x3600_0000 {
        return step_tbz_tbnz(w, state, pc, next_pc);
    }

    // 11. Conditional branch (B.<cond>)
    if (w & 0xff00_0010) == 0x5400_0000 {
        return step_b_cond(w, state, pc, next_pc);
    }

    // 12. Unconditional branch to register (BR, BLR, RET)
    if (w & 0xff9f_fc1f) == 0xd61f_0000 {
        return step_branch_reg(w, state, pc, next_pc);
    }

    // 13. Logical (shifted register)
    if (w & 0x1f00_0000) == 0x0a00_0000 {
        return step_logical_shifted(w, state, is_64, width, pc, next_pc);
    }

    // 14. Add/Subtract (shifted register)
    if (w & 0x1f20_0000) == 0x0b00_0000 {
        return step_add_sub_shifted(w, state, is_64, width, pc, next_pc);
    }

    // 15. Add/Subtract (extended register)
    if (w & 0x1fe0_0000) == 0x0b20_0000 {
        return step_add_sub_extended(w, state, is_64, width, pc, next_pc);
    }

    // 16. Add/Subtract with carry (ADC, ADCS, SBC, SBCS)
    if (w & 0x1fe0_fc00) == 0x1a00_0000 {
        return step_add_sub_carry(w, state, is_64, width, next_pc);
    }

    // 17. Conditional compare (CCMN, CCMP)
    if (w & 0x3fe0_0410) == 0x3a40_0000 {
        return step_cond_compare(w, state, is_64, width, next_pc);
    }

    // 18. Conditional select (CSEL, CSINC, CSINV, CSNEG)
    if (w & 0x3fe0_0800) == 0x1a80_0000 {
        return step_cond_select(w, state, is_64, width, next_pc);
    }

    // 19. Data Processing (1 source: RBIT, REV16, REV32, REV, CLZ, CLS)
    if (w & 0x7fff_0000) == 0x5ac0_0000 {
        return step_dataproc_1src(w, state, is_64, width, pc, next_pc);
    }

    // 20. Data Processing (2 source: UDIV, SDIV, LSLV, LSRV, ASRV, RORV)
    if (w & 0x7fe0_0000) == 0x1ac0_0000 {
        return step_dataproc_2src(w, state, is_64, width, pc, next_pc);
    }

    // 21. Data Processing (3 source: MADD, MSUB, SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH)
    if (w & 0x7f00_0000) == 0x1b00_0000 {
        return step_dataproc_3src(w, state, is_64, width, pc, next_pc);
    }

    // 22. Load/Store Pair (LDP, STP, LDPSW)
    if (w & 0x3e00_0000) == 0x2800_0000 {
        return step_load_store_pair(w, state, pc, next_pc, accesses);
    }

    // 23. Load/Store Register (Unsigned Immediate)
    if (w & 0x3f00_0000) == 0x3900_0000 {
        return step_load_store_unsigned_imm(w, state, pc, next_pc, accesses);
    }

    // 24. Load/Store Register (Unscaled Immediate, Pre/Post-Index, Register Offset)
    if (w & 0x3f00_0000) == 0x3800_0000 {
        if let Some(outcome) = step_load_store_unscaled_or_reg(w, state, pc, next_pc, accesses) {
            return outcome;
        }
    }

    // 25. Load Register (Literal)
    if (w & 0x3f00_0000) == 0x1800_0000 {
        return step_load_literal(w, state, pc, next_pc, accesses);
    }

    // 26. Load-Acquire / Store-Release (LDARB, LDARH, LDAR, STLRB, STLRH, STLR)
    if (w & 0x3fbf_fc00) == 0x089f_fc00 {
        return step_ldar_stlr(w, state, pc, next_pc, accesses);
    }

    // 26b/26c. Load/Store-Exclusive register (LDXR*, LDAXR*, STXR*, STLXR*)
    if (w & 0x3fff_7c00) == 0x085f_7c00 {
        return step_ldxr_stxr(w, state, pc, next_pc, accesses);
    }
    if (w & 0x3fe0_7c00) == 0x0800_7c00 {
        let (s_bits, n_bits, t_bits) = (extract(w, 16, 5), extract(w, 5, 5), extract(w, 0, 5));
        if !(s_bits == t_bits || (s_bits == n_bits && n_bits != 31)) {
            return step_ldxr_stxr(w, state, pc, next_pc, accesses);
        }
    }

    // 27. System Register Move (MRS / MSR TPIDR_EL0)
    if (w & 0xffd0_0000) == 0xd510_0000 {
        return step_sysreg(w, state, next_pc);
    }

    // Fallback: if decoded as a modeled SIMD/FP/AES/barrier instruction, step past it.
    if is_modeled_simd_or_barrier(w) {
        state.pc_off = next_pc;
        return StepOutcome::Next;
    }

    StepOutcome::Halted {
        reason: describe_unmodeled_word(w, pc),
        target: None,
    }
}

fn describe_unmodeled_word(w: u32, pc: u64) -> String {
    let detail = if (w & 0x9F20_0C00) == 0x0E20_0000 {
        format!(
            "unsupported AdvSIMD encoding class three-different (q={} u={} size={} opcode={}) — not modeled in Arm64/Trusted/ISA",
            bit(w, 30) as u8,
            bit(w, 29) as u8,
            extract(w, 22, 2),
            extract(w, 12, 4)
        )
    } else if (w & 0x9F00_0400) == 0x0F00_0000 {
        format!(
            "unsupported AdvSIMD encoding class vector-by-element (q={} u={} size={} opcode={}) — not modeled in Arm64/Trusted/ISA",
            bit(w, 30) as u8,
            bit(w, 29) as u8,
            extract(w, 22, 2),
            extract(w, 12, 4)
        )
    } else if (w & 0xDF20_0400) == 0x5E20_0400 {
        format!(
            "unsupported AdvSIMD encoding class scalar-three-same (u={} size={} opcode={}) — scalar SIMD not modeled in Arm64/Trusted/ISA",
            bit(w, 29) as u8,
            extract(w, 22, 2),
            extract(w, 11, 5)
        )
    } else if (w & 0xDF3E_0C00) == 0x5E20_0800 {
        format!(
            "unsupported AdvSIMD encoding class scalar-two-reg-misc (u={} size={} opcode={}) — scalar SIMD not modeled in Arm64/Trusted/ISA",
            bit(w, 29) as u8,
            extract(w, 22, 2),
            extract(w, 12, 5)
        )
    } else if (w & 0xDF3E_0C00) == 0x5E30_0800 {
        format!(
            "unsupported AdvSIMD encoding class scalar-pairwise (u={} size={} opcode={}) — scalar SIMD not modeled in Arm64/Trusted/ISA",
            bit(w, 29) as u8,
            extract(w, 22, 2),
            extract(w, 12, 5)
        )
    } else if (w & 0xDF80_0400) == 0x5F00_0400 {
        format!(
            "unsupported AdvSIMD encoding class scalar-shift-imm (u={} immh={} immb={} opcode={}) — scalar SIMD not modeled in Arm64/Trusted/ISA",
            bit(w, 29) as u8,
            extract(w, 19, 4),
            extract(w, 16, 3),
            extract(w, 11, 5)
        )
    } else if (w & 0xBFBF_0000) == 0x0C00_0000 || (w & 0xBFA0_0000) == 0x0C80_0000 {
        format!(
            "unsupported AdvSIMD encoding class multi-structure LD2-LD4/ST2-ST4 (q={} L={} opcode={} size={}) — not modeled in Arm64/Trusted/ISA",
            bit(w, 30) as u8,
            bit(w, 22) as u8,
            extract(w, 12, 4),
            extract(w, 10, 2)
        )
    } else if (w & 0xBF80_0000) == 0x0D00_0000 {
        format!(
            "unsupported AdvSIMD encoding class single-structure LD1-LD4/ST1-ST4 (q={} L={} R={} opcode={} size={}) — not modeled in Arm64/Trusted/ISA",
            bit(w, 30) as u8,
            bit(w, 22) as u8,
            bit(w, 21) as u8,
            extract(w, 13, 3),
            extract(w, 10, 2)
        )
    } else if (w & 0x1E00_0000) == 0x0400_0000 {
        "unsupported SVE instruction — SVE not modeled in Arm64/Trusted/ISA".to_string()
    } else {
        "not modeled in Arm64/Trusted/ISA".to_string()
    };
    format!("unmodeled instruction word 0x{w:08x} at +0x{pc:x} ({detail})")
}

fn simd_load_store_scale(size_bits: u64, opc: u64) -> Option<u32> {
    match (size_bits, opc) {
        (0, 0 | 1) => Some(0),
        (0, 2 | 3) => Some(4),
        (1, 0 | 1) => Some(1),
        (2, 0 | 1) => Some(2),
        (3, 0 | 1) => Some(3),
        _ => None,
    }
}

fn is_modeled_simd_or_barrier(w: u32) -> bool {
    // 25b. SIMD/FP Load Register (Literal)
    if (w & 0x3F00_0000) == 0x1C00_0000 {
        return extract(w, 30, 2) <= 2;
    }
    // 28. Memory Barrier (CLREX, DSB, DMB, ISB)
    if (w & 0xFFFF_F01F) == 0xD503_301F {
        return matches!(extract(w, 5, 3), 2 | 4 | 5 | 6);
    }
    // 28b. SIMD/FP Load/Store No-Allocate Pair
    if (w & 0x3F80_0000) == 0x2C00_0000 {
        return extract(w, 30, 2) <= 2 && !(bit(w, 22) && extract(w, 0, 5) == extract(w, 10, 5));
    }
    // 29. SIMD/FP Load/Store Pair
    if (w & 0x3E00_0000) == 0x2C00_0000 {
        return extract(w, 30, 2) <= 2
            && matches!(extract(w, 23, 2), 1..=3)
            && !(bit(w, 22) && extract(w, 0, 5) == extract(w, 10, 5));
    }
    // 30. SIMD/FP Load/Store Register (Unsigned Immediate)
    if (w & 0x3F00_0000) == 0x3D00_0000 {
        return simd_load_store_scale(extract(w, 30, 2), extract(w, 22, 2)).is_some();
    }
    // 31. SIMD/FP Load/Store Register (Unscaled, Pre/Post-Index, RegOffset)
    if (w & 0x3F00_0000) == 0x3C00_0000 {
        let Some(scale) = simd_load_store_scale(extract(w, 30, 2), extract(w, 22, 2)) else {
            return false;
        };
        if !bit(w, 21) {
            return matches!(extract(w, 10, 2), 0 | 1 | 3);
        } else if extract(w, 10, 2) == 2 {
            let option = extract(w, 13, 3);
            let s_bit = bit(w, 12);
            return (option & 0b010) != 0 && !(scale == 0 && s_bit);
        }
        return false;
    }
    // 32–49. SIMD/FP/AES/SHA data-processing and single-structure post-index
    (w & 0xBFE0_0000) == 0x0D80_0000
        || (w & 0xFFFF_CC00) == 0x4E28_4800
        || (w & 0x7F20_FC00) == 0x1E20_0000
        || (w & 0x9F80_0400) == 0x0F00_0400
        || (w & 0xBFE0_8C00) == 0x0E00_0000
        || (w & 0xFFFF_FC00) == 0x5EF1_B800
        || (w & 0x9FE0_8400) == 0x0E00_0400
        || (w & 0x9F20_0400) == 0x0E20_0400
        || (w & 0x9F3E_0C00) == 0x0E20_0800
        || (w & 0x9F3E_0C00) == 0x0E30_0800
        || (w & 0xBF20_8C00) == 0x0E00_0800
        || (w & 0xBFE0_8400) == 0x2E00_0000
        || ((w & 0xBF20_FC00) == 0x0E20_E000 && matches!(extract(w, 22, 2), 0 | 3))
        || ((w & 0xFFFE_0C00) == 0x5E28_0800 && extract(w, 12, 5) <= 2)
        || ((w & 0xFFE0_8C00) == 0x5E00_0000 && extract(w, 12, 3) != 7)
        || (w & 0xFFFF_FC00) == 0xCEC0_8000
        || (w & 0xFFE0_F000) == 0xCE60_8000
        || (w & 0xFFC0_8000) == 0xCE00_0000
        || (w & 0xFFE0_0000) == 0xCE80_0000
        || (w & 0xFF20_7C00) == 0x1E20_4000
        || (w & 0xFF20_0C00) == 0x1E20_0800
        || (w & 0xFF20_3C00) == 0x1E20_2000
        || (w & 0xFF20_1FE0) == 0x1E20_1000
        || (w & 0xFF20_0C00) == 0x1E20_0400
        || (w & 0xFF20_0C00) == 0x1E20_0C00
        || (w & 0xFF00_0000) == 0x1F00_0000
        || (w & 0x7F20_0000) == 0x1E00_0000
}
