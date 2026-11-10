// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Symbolic semantics for sequential atomics, RCpc, hints, prefetch, non-temporal pairs and
//! `DC ZVA` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (symbolic transfer functions for the `symexec` proof advisor,
//!   differentially tested against Unicorn in `test_infra/symexec_diff.rs`).
//! - **Purpose:** Mirrors the single-threaded `Arm64/Trusted/ISA/Eval.lean` arms appended for
//!   C++/Go runtime idioms: `ldxp`/`stxp` (exclusive monitor always succeeds, `Ws := 0`), `cas`
//!   (`Rs := old`), `casp`, `atomicRmw` (`Rt := old`, `mem := op(old, Rs)`), `ldapr`,
//!   `ldapurStlur`, `ldnp`/`stnp`, `dcZva`, and the no-op `hint`/`prfm`/`prfmLit`. SIMD-only
//!   forms are left to the generic decoded-instruction fallback except for the GPR post-index
//!   writeback of `LD1`/`ST1` (multiple) and `LD1R`; `crc32` and `udf` halt.
//!
//! # Key Types & Functions
//! # Key Types & Functions
//! - [`step_atomic_or_hint`]: Dispatches on the instruction encoding matching `Arm64/Trusted/ISA/Decode.lean`.
//!
//! # When to Read This File
//! - Read this file when adding/debugging symbolic semantics for one of the constructors above.

use super::expr::{SymCond, SymExpr};
use super::insn_semantics::{StepOutcome, exec_single_load_store, step_load_store_pair};
use super::state::{MemAccessRecord, SymState};
use crate::untrusted_lemmas::{bit, extract, sign_extend};

// Condition codes used with `FlagState::Cmp` (`lhs - rhs`).
const COND_EQ: u8 = 0;
const COND_CC: u8 = 3; // unsigned <
const COND_HI: u8 = 8; // unsigned >
const COND_LT: u8 = 11; // signed <
const COND_GT: u8 = 12; // signed >

fn cmp_cond(cond_bits: u8, lhs: SymExpr, rhs: SymExpr) -> SymCond {
    SymCond::FlagCond {
        cond_bits,
        flags: super::expr::FlagState::Cmp {
            width: 64,
            lhs,
            rhs,
        },
    }
}

fn halted(reason: String) -> StepOutcome {
    StepOutcome::Halted {
        reason,
        target: None,
    }
}

fn classify_atomic_or_hint(w: u32) -> Option<&'static str> {
    if w != 0xD503_201F && (w & 0xFFFF_F01F) == 0xD503_201F {
        return Some("hint");
    }
    if (w & 0xFFFF_0000) == 0x0000_0000 && w != 0 {
        return Some("udf");
    }
    if (w & 0xFFFF_FFE0) == 0xD50B_7420 {
        return Some("dcZva");
    }
    if (w & 0x7FE0_E000) == 0x1AC0_4000 && bit(w, 31) == (extract(w, 10, 2) == 3) {
        return Some("crc32");
    }
    if (w & 0x7F80_0000) == 0x2800_0000 {
        if bit(w, 22) && extract(w, 0, 5) == extract(w, 10, 5) {
            return None;
        }
        return Some(if bit(w, 22) { "ldnp" } else { "stnp" });
    }
    if (w & 0xFFC0_0000) == 0xF980_0000
        || (w & 0xFFE0_0C00) == 0xF880_0000
        || ((w & 0xFFE0_0C00) == 0xF8A0_0800 && (extract(w, 13, 3) & 0b010) != 0)
    {
        return Some("prfm");
    }
    if (w & 0x3F20_0C00) == 0x3820_0000 {
        let o3 = bit(w, 15);
        let opc = extract(w, 12, 3);
        if !o3 || opc == 0 {
            return Some("atomicRmw");
        } else if opc == 4 && bit(w, 23) && !bit(w, 22) && extract(w, 16, 5) == 31 {
            return Some("ldapr");
        }
        return None;
    }
    if (w & 0x3F20_0C00) == 0x1900_0000 {
        let size_bits = extract(w, 30, 2);
        let opc = extract(w, 22, 2);
        if (size_bits == 3 && (opc & 0b10) != 0) || (size_bits == 2 && opc == 3) {
            return None;
        }
        return Some("ldapurStlur");
    }
    if (w & 0xFF00_0000) == 0xD800_0000 {
        return Some("prfmLit");
    }
    if (w & 0xBFFF_0000) == 0x887F_0000 {
        if extract(w, 0, 5) == extract(w, 10, 5) {
            return None;
        }
        return Some("ldxp");
    }
    if (w & 0xBFE0_0000) == 0x8820_0000 {
        let s_bits = extract(w, 16, 5);
        let t2_bits = extract(w, 10, 5);
        let n_bits = extract(w, 5, 5);
        let t_bits = extract(w, 0, 5);
        if s_bits == t_bits || s_bits == t2_bits || (s_bits == n_bits && n_bits != 31) {
            return None;
        }
        return Some("stxp");
    }
    if (w & 0x3FA0_7C00) == 0x08A0_7C00 {
        return Some("cas");
    }
    if (w & 0xBFA0_7C00) == 0x0820_7C00 {
        if (extract(w, 16, 5) & 1) != 0 || (extract(w, 0, 5) & 1) != 0 {
            return None;
        }
        return Some("casp");
    }
    if ((w & 0xBFBF_0000) == 0x0C00_0000 || (w & 0xBFA0_0000) == 0x0C80_0000)
        && matches!(extract(w, 12, 4), 2 | 6 | 7 | 10)
    {
        return Some("simdLdSt1Multi");
    }
    if (w & 0xBFFF_F000) == 0x0D40_C000 || (w & 0xBFE0_F000) == 0x0DC0_C000 {
        return Some("simdLd1r");
    }
    None
}

/// Step `w` if it decodes to one of the constructors handled here; otherwise return `None` so
/// the caller's existing dispatcher runs.
pub(super) fn step_atomic_or_hint(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> Option<StepOutcome> {
    let ctor = classify_atomic_or_hint(w)?;
    let outcome = match ctor {
        "hint" | "prfm" | "prfmLit" => {
            state.pc_off = next_pc;
            StepOutcome::Next
        }
        "udf" => halted(format!("udf at +0x{pc:x}")),
        "crc32" => halted(format!("unmodeled crc32 at +0x{pc:x}")),
        "dcZva" => step_dc_zva(w, state, pc, next_pc, accesses),
        "ldxp" | "stxp" => step_ldxp_stxp(w, state, pc, next_pc, accesses),
        "cas" => step_cas(w, state, pc, next_pc, accesses),
        "casp" => step_casp(w, state, pc, next_pc, accesses),
        "atomicRmw" => step_atomic_rmw(w, state, pc, next_pc, accesses),
        "ldapr" => {
            let size_bits = extract(w, 30, 2);
            let addr = state.read_gpr_sp(extract(w, 5, 5), true);
            let val = state.load_mem(pc, &addr, 8u32 << size_bits, None, accesses);
            state.write_gpr_zr(extract(w, 0, 5), size_bits == 3, val);
            state.pc_off = next_pc;
            StepOutcome::Next
        }
        "ldapurStlur" => step_ldapur_stlur(w, state, pc, next_pc, accesses),
        // `LDNP`/`STNP` are sequentially signed-offset `LDP`/`STP`: rewrite the mode bits
        // (24:23) from `00` to `10` and reuse the pair stepper.
        "ldnp" | "stnp" => step_load_store_pair(w | (1 << 24), state, pc, next_pc, accesses),
        "simdLdSt1Multi" | "simdLd1r" => {
            step_simd_post_index(w, ctor == "simdLd1r", state);
            state.pc_off = next_pc;
            StepOutcome::Next
        }
        _ => return None,
    };
    Some(outcome)
}

/// `DC ZVA, Xt`: zero the 64-byte block containing `Xt` (eight 64-bit stores).
fn step_dc_zva(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let xt = state.read_gpr_zr(extract(w, 0, 5), true);
    let base = SymExpr::binop(super::expr::BinOpKind::And, 64, xt, SymExpr::Const(!63u64));
    for i in 0..8u64 {
        state.store_mem(
            pc,
            &base.clone().add_const(8 * i),
            64,
            SymExpr::Const(0),
            accesses,
        );
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `LDXP`/`LDAXP` and `STXP`/`STLXP` (`STXP` always succeeds: `Ws := 0`).
fn step_ldxp_stxp(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let is_64 = bit(w, 30);
    let width_bits = if is_64 { 64 } else { 32 };
    let step = (width_bits / 8) as u64;
    let rs_bits = extract(w, 16, 5);
    let rt2_bits = extract(w, 10, 5);
    let rt_bits = extract(w, 0, 5);
    let addr = state.read_gpr_sp(extract(w, 5, 5), true);
    if bit(w, 22) {
        let v1 = state.load_mem(pc, &addr, width_bits, None, accesses);
        let v2 = state.load_mem(
            pc,
            &addr.clone().add_const(step),
            width_bits,
            None,
            accesses,
        );
        state.write_gpr_zr(rt_bits, is_64, v1);
        state.write_gpr_zr(rt2_bits, is_64, v2);
    } else {
        let v1 = state.read_gpr_zr(rt_bits, is_64);
        let v2 = state.read_gpr_zr(rt2_bits, is_64);
        state.store_mem(pc, &addr, width_bits, v1, accesses);
        state.store_mem(pc, &addr.clone().add_const(step), width_bits, v2, accesses);
        state.write_gpr_zr(rs_bits, false, SymExpr::Const(0));
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `CAS{A}{L}{B,H}`: `old := mem[Xn]`; `mem[Xn] := (old == Rs<size>) ? Rt : old`; `Rs := old`.
fn step_cas(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let size_bits = extract(w, 30, 2);
    let width_bits = 8u32 << size_bits;
    let is_64 = size_bits == 3;
    let rs_bits = extract(w, 16, 5);
    let addr = state.read_gpr_sp(extract(w, 5, 5), true);
    let old = state.load_mem(pc, &addr, width_bits, None, accesses);
    let expected = state.read_gpr_zr(rs_bits, true).zero_ext(width_bits);
    let new = state.read_gpr_zr(extract(w, 0, 5), true);
    let stored = SymExpr::ite(cmp_cond(COND_EQ, old.clone(), expected), new, old.clone());
    state.store_mem(pc, &addr, width_bits, stored, accesses);
    state.write_gpr_zr(rs_bits, is_64, old);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// `CASP{A}{L}`: compare both halves; store both `Rt`/`Rt2` iff both match; `Rs, Rs2 := old`.
fn step_casp(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let is_64 = bit(w, 30);
    let width_bits = if is_64 { 64 } else { 32 };
    let step = (width_bits / 8) as u64;
    let rs_bits = extract(w, 16, 5);
    let rs2_bits = (rs_bits + 1) & 31;
    let rt_bits = extract(w, 0, 5);
    let rt2_bits = (rt_bits + 1) & 31;
    let addr1 = state.read_gpr_sp(extract(w, 5, 5), true);
    let addr2 = addr1.clone().add_const(step);
    let old1 = state.load_mem(pc, &addr1, width_bits, None, accesses);
    let old2 = state.load_mem(pc, &addr2, width_bits, None, accesses);
    let exp1 = state.read_gpr_zr(rs_bits, is_64);
    let exp2 = state.read_gpr_zr(rs2_bits, is_64);
    let new1 = state.read_gpr_zr(rt_bits, true);
    let new2 = state.read_gpr_zr(rt2_bits, true);
    let both = |state_new: SymExpr, old: &SymExpr| {
        SymExpr::ite(
            cmp_cond(COND_EQ, old1.clone(), exp1.clone()),
            SymExpr::ite(
                cmp_cond(COND_EQ, old2.clone(), exp2.clone()),
                state_new,
                old.clone(),
            ),
            old.clone(),
        )
    };
    let s1 = both(new1, &old1);
    let s2 = both(new2, &old2);
    state.store_mem(pc, &addr1, width_bits, s1, accesses);
    state.store_mem(pc, &addr2, width_bits, s2, accesses);
    state.write_gpr_zr(rs_bits, is_64, old1);
    state.write_gpr_zr(rs2_bits, is_64, old2);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// LSE `LD<OP>{A}{L}{B,H}` / `SWP{A}{L}{B,H}` (`Eval.lean` `evalAtomicOp`).
fn step_atomic_rmw(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    use super::expr::BinOpKind;
    let size_bits = extract(w, 30, 2);
    let width_bits = 8u32 << size_bits;
    let is_64 = size_bits == 3;
    let o3 = bit(w, 15);
    let opc = extract(w, 12, 3);
    let addr = state.read_gpr_sp(extract(w, 5, 5), true);
    let old = state.load_mem(pc, &addr, width_bits, None, accesses);
    let b = state
        .read_gpr_zr(extract(w, 16, 5), true)
        .zero_ext(width_bits);
    let signed = |x: &SymExpr| x.clone().sign_ext(width_bits);
    let sel = |cond: SymCond| SymExpr::ite(cond, b.clone(), old.clone());
    let new = match (o3, opc) {
        (true, _) => b.clone(), // SWP
        (false, 0) => SymExpr::binop(BinOpKind::Add, 64, old.clone(), b.clone()),
        (false, 1) => SymExpr::binop(
            BinOpKind::And,
            64,
            old.clone(),
            SymExpr::bit_not(b.clone(), 64),
        ),
        (false, 2) => SymExpr::binop(BinOpKind::Xor, 64, old.clone(), b.clone()),
        (false, 3) => SymExpr::binop(BinOpKind::Or, 64, old.clone(), b.clone()),
        (false, 4) => sel(cmp_cond(COND_GT, signed(&b), signed(&old))), // SMAX
        (false, 5) => sel(cmp_cond(COND_LT, signed(&b), signed(&old))), // SMIN
        (false, 6) => sel(cmp_cond(COND_HI, b.clone(), old.clone())),   // UMAX
        (false, _) => sel(cmp_cond(COND_CC, b.clone(), old.clone())),   // UMIN
    };
    // `store_mem` truncates to `width_bits` (`evalAtomicOp` masks `res`).
    state.store_mem(pc, &addr, width_bits, new, accesses);
    state.write_gpr_zr(extract(w, 0, 5), is_64, old);
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// RCpc unscaled `STLUR*` (`opc = 00`), `LDAPUR*` (`01`), `LDAPURS* Xt` (`10`), `LDAPURS* Wt` (`11`).
fn step_ldapur_stlur(
    w: u32,
    state: &mut SymState,
    pc: u64,
    next_pc: u64,
    accesses: &mut Vec<MemAccessRecord>,
) -> StepOutcome {
    let size_bits = extract(w, 30, 2);
    let opc = extract(w, 22, 2);
    let offset = sign_extend(extract(w, 12, 9), 9);
    let addr = state.read_gpr_sp(extract(w, 5, 5), true).add_const(offset);
    // Same `(size, opc)` table as `LDUR*`/`STUR*`, which `exec_single_load_store` implements.
    if !exec_single_load_store(
        state,
        pc,
        size_bits,
        opc,
        extract(w, 0, 5),
        &addr,
        None,
        8u32 << size_bits,
        accesses,
    ) {
        return halted(format!(
            "invalid ldapur/stlur size={size_bits} opc={opc} at +0x{pc:x}"
        ));
    }
    state.pc_off = next_pc;
    StepOutcome::Next
}

/// GPR effect of SIMD `LD1`/`ST1` (multiple) and `LD1R` with post-index (bit 23): `Xn += inc`,
/// where `inc` is `Xm` or (for `Rm = 31`) the transfer size. Vector-register and memory effects of
/// SIMD loads/stores are not tracked by `symexec` (same as `ldrSimd`/`strSimd`).
fn step_simd_post_index(w: u32, is_ld1r: bool, state: &mut SymState) {
    if !bit(w, 23) {
        return;
    }
    let rn_bits = extract(w, 5, 5);
    let rm_bits = extract(w, 16, 5);
    let inc = if rm_bits == 31 {
        let bytes = if is_ld1r {
            1u64 << extract(w, 10, 2)
        } else {
            let nregs = match extract(w, 12, 4) {
                7 => 1,
                10 => 2,
                6 => 3,
                _ => 4,
            };
            nregs * if bit(w, 30) { 16 } else { 8 }
        };
        SymExpr::Const(bytes)
    } else {
        state.read_gpr_zr(rm_bits, true)
    };
    let base = state.read_gpr_sp(rn_bits, true);
    state.write_gpr_sp(rn_bits, true, SymExpr::add(base, inc, true));
}
