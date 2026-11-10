// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Static ELF64 (`ET_EXEC`) AArch64 `svc #0` syscall scanner with intra-procedural CFG constant
//! propagation and transitive `arg0 -> x8` wrapper resolution (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted host audit infrastructure under
//!   `tools/run-trusted-tests`).
//! - **Purpose:** Parse static AArch64 ELF executables (`SHF_EXECINSTR` sections + `.symtab`),
//!   locate every 4-byte-aligned `svc #0` (`0xd4000001`) instruction, recover constant `x8` values
//!   across straight-line and intra-function branch paths (`MOVZ`, `MOVN`, `MOVK`, `MOV`/`ORR`,
//!   `ADD`/`SUB`, `UXTW`/`SXTW`), and resolve generic syscall wrappers where `x8` is copied from
//!   `x0`/`w0` by scanning all `BL` and tail-call `B` call sites across the binary.
//!
//! # Key Types & Functions
//! - [`StaticBinaryScan`]: Complete deterministic static `svc #0` inventory for one ELF binary.
//! - [`StaticSvcSite`] / [`StaticX8Value`]: Per-site address, enclosing symbol, and resolved `x8`.
//! - [`scan_elf_bytes`]: Parse an ELF64 `ET_EXEC` AArch64 image and resolve all `svc #0` sites.
//! - [`analyze_functions`]: Pure instruction-level analyzer exercised directly by unit tests.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use anyhow::{Context, Result, anyhow, bail};
use object::elf::{ET_EXEC, SHF_EXECINSTR};
use object::read::elf::{ElfFile64, FileHeader, SectionHeader};
use object::{Architecture, Endianness, Object, ObjectSection, ObjectSymbol, SymbolKind};

use crate::process_e2e::sha256_hex;

/// Exact 32-bit little-endian encoding of AArch64 `svc #0`.
pub const AARCH64_SVC_0: u32 = 0xd400_0001;

/// Contiguous 4-byte-aligned instruction slice belonging to one function or executable span.
#[derive(Debug, Clone)]
pub struct FunctionCode {
    pub addr: u64,
    pub name: String,
    pub words: Vec<u32>,
}

impl FunctionCode {
    pub fn end_addr(&self) -> u64 {
        self.addr + (self.words.len() as u64) * 4
    }
}

/// Resolution of `x8` at a single static `svc #0` instruction site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticX8Value {
    /// `x8` holds a unique compile-time constant syscall number on all reachable intra-function paths.
    Resolved(u64),
    /// `x8` receives entry `x0`/`w0` (e.g. `syscall` or `__syscall_cp`), with constant `x0`/`w0`
    /// values recovered across all direct and tail-call callers in the ELF.
    IndirectArg0 {
        caller_nrs: Vec<u64>,
        unresolved_callers: usize,
    },
    /// `x8` could not be statically resolved to a single constant or `arg0` wrapper.
    DynamicUnknown,
}

/// Raw static `svc #0` site produced by [`analyze_functions`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticSvcSite {
    pub pc: u64,
    pub function: String,
    pub offset_in_fn: u64,
    pub x8: StaticX8Value,
}

/// Deterministic static `svc #0` scan summary for one ELF64 AArch64 executable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticBinaryScan {
    pub size_bytes: u64,
    pub sha256: String,
    pub entry_va: u64,
    pub sites: Vec<StaticSvcSite>,
    /// Sorted deduplicated syscall numbers resolved across all `Resolved` and `IndirectArg0` sites.
    pub distinct_resolved_nrs: Vec<u64>,
}

/// Symbolic provenance of a 64-bit general-purpose register inside a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegOrigin {
    Const(u64),
    EntryArg(u8),
}

/// Constant-propagation lattice element for a single general-purpose register `x0..=x30`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AbsReg {
    Unreached,
    Known(RegOrigin),
    Clobbered,
}

impl AbsReg {
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unreached, x) | (x, Self::Unreached) => x,
            (Self::Known(a), Self::Known(b)) if a == b => Self::Known(a),
            _ => Self::Clobbered,
        }
    }
}

type RegState = [AbsReg; 31];

fn read_zr(state: &RegState, reg: u32) -> AbsReg {
    if reg >= 31 {
        AbsReg::Known(RegOrigin::Const(0))
    } else {
        state[reg as usize]
    }
}

fn write_gpr(state: &mut RegState, reg: u32, val: AbsReg) {
    if reg < 31 {
        state[reg as usize] = val;
    }
}

fn sign_extend_word_offset(pc: u64, raw_imm: u32, bits: u32) -> u64 {
    let shift = 64 - bits;
    let signed = ((raw_imm as i64) << shift) >> shift;
    pc.wrapping_add((signed * 4) as u64)
}

/// Decode an A64 `N:imms:immr` logical bitmask immediate (`DecodeBitMasks` in the ARM ARM).
fn decode_bitmask_imm(sf: u32, n: u32, imms: u32, immr: u32) -> Option<u64> {
    if sf == 0 && n != 0 {
        return None;
    }
    let combined = (n << 6) | ((!imms) & 0x3f);
    if combined == 0 {
        return None;
    }
    let len = 31 - combined.leading_zeros();
    if len == 0 {
        return None;
    }
    let esize = 1u32 << len;
    if sf == 0 && esize > 32 {
        return None;
    }
    let levels = esize - 1;
    let s = imms & levels;
    let r = immr & levels;
    if s == levels {
        return None;
    }
    let welem = if s + 1 == 64 {
        u64::MAX
    } else {
        (1u64 << (s + 1)) - 1
    };
    let elem_mask = if esize == 64 {
        u64::MAX
    } else {
        (1u64 << esize) - 1
    };
    let rotated = if r == 0 {
        welem
    } else {
        ((welem >> r) | (welem << (esize - r))) & elem_mask
    };
    let mut val = rotated;
    let mut width = esize;
    while width < 64 {
        val |= val << width;
        width *= 2;
    }
    if sf == 0 {
        val &= 0xffff_ffff;
    }
    Some(val)
}

fn eval_shifted_reg(sf: u32, shift: u32, amount: u32, raw: u64) -> Option<u64> {
    if sf == 0 {
        if amount >= 32 {
            return None;
        }
        let w = raw as u32;
        let out = match shift {
            0 => w.wrapping_shl(amount),
            1 => w.wrapping_shr(amount),
            2 => ((w as i32).wrapping_shr(amount)) as u32,
            3 => w.rotate_right(amount),
            _ => return None,
        };
        Some(out as u64)
    } else {
        let out = match shift {
            0 => raw.wrapping_shl(amount),
            1 => raw.wrapping_shr(amount),
            2 => ((raw as i64).wrapping_shr(amount)) as u64,
            3 => raw.rotate_right(amount),
            _ => return None,
        };
        Some(out)
    }
}

/// Recorded inter-procedural direct call or tail-call (`BL target` or out-of-function `B target`).
#[derive(Debug, Clone, Copy)]
struct CallEdge {
    caller_fn_addr: u64,
    call_pc: u64,
    target_addr: u64,
    arg0: AbsReg,
}

#[derive(Debug, Clone)]
struct IntraFnAnalysis {
    svc_sites: Vec<(u64, AbsReg)>,
    calls: Vec<CallEdge>,
}

/// Run intra-procedural Kildall constant propagation over a single function's instruction words.
fn analyze_single_function(func: &FunctionCode) -> IntraFnAnalysis {
    let n = func.words.len();
    if n == 0 {
        return IntraFnAnalysis {
            svc_sites: Vec::new(),
            calls: Vec::new(),
        };
    }

    let fn_start = func.addr;
    let fn_end = func.end_addr();

    let mut in_states: Vec<RegState> = vec![[AbsReg::Unreached; 31]; n];
    let mut entry_state = [AbsReg::Unreached; 31];
    for (r, slot) in entry_state.iter_mut().enumerate() {
        *slot = AbsReg::Known(RegOrigin::EntryArg(r as u8));
    }
    in_states[0] = entry_state;

    let mut queued = vec![false; n];
    let mut worklist = VecDeque::new();
    queued[0] = true;
    worklist.push_back(0usize);

    let propagate = |target_idx: usize,
                     cand: &RegState,
                     in_states: &mut [RegState],
                     queued: &mut [bool],
                     worklist: &mut VecDeque<usize>| {
        let cur = &mut in_states[target_idx];
        let mut changed = false;
        for r in 0..31 {
            let next = cur[r].meet(cand[r]);
            if next != cur[r] {
                cur[r] = next;
                changed = true;
            }
        }
        if changed && !queued[target_idx] {
            queued[target_idx] = true;
            worklist.push_back(target_idx);
        }
    };

    while let Some(idx) = worklist.pop_front() {
        queued[idx] = false;
        let pc = fn_start + (idx as u64) * 4;
        let insn = func.words[idx];
        let mut state = in_states[idx];

        // 1. `SVC #0`
        if insn == AARCH64_SVC_0 {
            state[0] = AbsReg::Clobbered;
            if idx + 1 < n {
                propagate(idx + 1, &state, &mut in_states, &mut queued, &mut worklist);
            }
            continue;
        }

        // 2. Unconditional `B imm26`
        if (insn & 0xfc00_0000) == 0x1400_0000 {
            let target = sign_extend_word_offset(pc, insn & 0x03ff_ffff, 26);
            if target >= fn_start && target < fn_end && (target - fn_start).is_multiple_of(4) {
                let target_idx = ((target - fn_start) / 4) as usize;
                propagate(target_idx, &state, &mut in_states, &mut queued, &mut worklist);
            }
            continue;
        }

        // 3. `BL imm26`
        if (insn & 0xfc00_0000) == 0x9400_0000 {
            for r in 0..=18 {
                state[r] = AbsReg::Clobbered;
            }
            state[30] = AbsReg::Clobbered;
            if idx + 1 < n {
                propagate(idx + 1, &state, &mut in_states, &mut queued, &mut worklist);
            }
            continue;
        }

        // 4. `BLR Xn`
        if (insn & 0xffff_fc1f) == 0xd63f_0000 {
            for r in 0..=18 {
                state[r] = AbsReg::Clobbered;
            }
            state[30] = AbsReg::Clobbered;
            if idx + 1 < n {
                propagate(idx + 1, &state, &mut in_states, &mut queued, &mut worklist);
            }
            continue;
        }

        // 5. `RET`, `BR`, `BRK`, `HLT`, `UDF`: no intra-function fall-through
        if (insn & 0xffff_fc1f) == 0xd65f_0000
            || (insn & 0xffff_fc1f) == 0xd61f_0000
            || (insn & 0xffe0_001f) == 0xd420_0000
            || (insn & 0xffe0_001f) == 0xd440_0000
            || (insn & 0xffff_0000) == 0x0000_0000
        {
            continue;
        }

        // 6. Conditional branches (`B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`)
        let cond_target = if (insn & 0xff00_0010) == 0x5400_0000
            || (insn & 0x7e00_0000) == 0x3400_0000
        {
            Some(sign_extend_word_offset(pc, (insn >> 5) & 0x7ffff, 19))
        } else if (insn & 0x7e00_0000) == 0x3600_0000 {
            Some(sign_extend_word_offset(pc, (insn >> 5) & 0x3fff, 14))
        } else {
            None
        };
        if let Some(target) = cond_target {
            if target >= fn_start && target < fn_end && (target - fn_start).is_multiple_of(4) {
                let target_idx = ((target - fn_start) / 4) as usize;
                propagate(target_idx, &state, &mut in_states, &mut queued, &mut worklist);
            }
            if idx + 1 < n {
                propagate(idx + 1, &state, &mut in_states, &mut queued, &mut worklist);
            }
            continue;
        }

        // 7. Data-processing & memory instructions (fall through to `idx + 1`)
        step_non_branch(insn, &mut state);
        if idx + 1 < n {
            propagate(idx + 1, &state, &mut in_states, &mut queued, &mut worklist);
        }
    }

    // Collect every `svc #0` site in `[fn_start, fn_end)` (even if unreachable from `idx == 0`,
    // in which case `in_states[idx][8]` is `Unreached` -> `DynamicUnknown`) and every external
    // `BL` / tail-call `B` from reachable instructions.
    let mut svc_sites = Vec::new();
    let mut calls = Vec::new();
    for (idx, &insn) in func.words.iter().enumerate() {
        let pc = fn_start + (idx as u64) * 4;
        let state = &in_states[idx];
        if insn == AARCH64_SVC_0 {
            svc_sites.push((pc, state[8]));
        } else if state[0] != AbsReg::Unreached {
            if (insn & 0xfc00_0000) == 0x9400_0000 {
                let target = sign_extend_word_offset(pc, insn & 0x03ff_ffff, 26);
                calls.push(CallEdge {
                    caller_fn_addr: fn_start,
                    call_pc: pc,
                    target_addr: target,
                    arg0: state[0],
                });
            } else if (insn & 0xfc00_0000) == 0x1400_0000 {
                let target = sign_extend_word_offset(pc, insn & 0x03ff_ffff, 26);
                if target < fn_start || target >= fn_end {
                    calls.push(CallEdge {
                        caller_fn_addr: fn_start,
                        call_pc: pc,
                        target_addr: target,
                        arg0: state[0],
                    });
                }
            }
        }
    }

    IntraFnAnalysis { svc_sites, calls }
}

/// Apply the abstract register effect of a single non-branch AArch64 instruction.
fn step_non_branch(insn: u32, state: &mut RegState) {
    // 1. Move wide immediate (`MOVN`, `MOVZ`, `MOVK`)
    if (insn & 0x1f80_0000) == 0x1280_0000 {
        let sf = (insn >> 31) & 1;
        let opc = (insn >> 29) & 3;
        let hw = (insn >> 21) & 3;
        let imm16 = ((insn >> 5) & 0xffff) as u64;
        let rd = insn & 0x1f;
        if sf == 0 && hw >= 2 {
            write_gpr(state, rd, AbsReg::Clobbered);
            return;
        }
        let shift = hw * 16;
        let next = match opc {
            0 => {
                let v = if sf == 1 {
                    !(imm16 << shift)
                } else {
                    (!((imm16 as u32) << shift)) as u64
                };
                AbsReg::Known(RegOrigin::Const(v))
            }
            2 => {
                let v = if sf == 1 {
                    imm16 << shift
                } else {
                    ((imm16 as u32) << shift) as u64
                };
                AbsReg::Known(RegOrigin::Const(v))
            }
            3 => match read_zr(state, rd) {
                AbsReg::Known(RegOrigin::Const(prev)) => {
                    let mask = 0xffffu64 << shift;
                    let mut v = (prev & !mask) | (imm16 << shift);
                    if sf == 0 {
                        v &= 0xffff_ffff;
                    }
                    AbsReg::Known(RegOrigin::Const(v))
                }
                _ => AbsReg::Clobbered,
            },
            _ => AbsReg::Clobbered,
        };
        write_gpr(state, rd, next);
        return;
    }

    // 2. Logical (shifted register) — includes `MOV Xd, Xm` (`ORR Xd, XZR, Xm`)
    if (insn & 0x1f00_0000) == 0x0a00_0000 {
        let sf = (insn >> 31) & 1;
        let opc = (insn >> 29) & 3;
        let shift = (insn >> 22) & 3;
        let n_bit = (insn >> 21) & 1;
        let rm = (insn >> 16) & 0x1f;
        let imm6 = (insn >> 10) & 0x3f;
        let rn = (insn >> 5) & 0x1f;
        let rd = insn & 0x1f;

        if opc == 1 && n_bit == 0 && rn == 31 && imm6 == 0 {
            let copied = match read_zr(state, rm) {
                AbsReg::Known(RegOrigin::Const(v)) => {
                    AbsReg::Known(RegOrigin::Const(if sf == 1 { v } else { v & 0xffff_ffff }))
                }
                AbsReg::Known(RegOrigin::EntryArg(a)) => AbsReg::Known(RegOrigin::EntryArg(a)),
                _ => AbsReg::Clobbered,
            };
            write_gpr(state, rd, copied);
            return;
        }

        let next = match (read_zr(state, rn), read_zr(state, rm)) {
            (AbsReg::Known(RegOrigin::Const(lhs)), AbsReg::Known(RegOrigin::Const(rhs_raw))) => {
                if let Some(mut rhs) = eval_shifted_reg(sf, shift, imm6, rhs_raw) {
                    if n_bit == 1 {
                        rhs = !rhs;
                    }
                    let mut res = match opc {
                        0 | 3 => lhs & rhs,
                        1 => lhs | rhs,
                        2 => lhs ^ rhs,
                        _ => unreachable!(),
                    };
                    if sf == 0 {
                        res &= 0xffff_ffff;
                    }
                    AbsReg::Known(RegOrigin::Const(res))
                } else {
                    AbsReg::Clobbered
                }
            }
            _ => AbsReg::Clobbered,
        };
        write_gpr(state, rd, next);
        return;
    }

    // 3. Logical (immediate) — includes bitmask-immediate `MOV Xd, #imm` (`ORR Xd, XZR, #imm`)
    if (insn & 0x1f80_0000) == 0x1200_0000 {
        let sf = (insn >> 31) & 1;
        let opc = (insn >> 29) & 3;
        let n = (insn >> 22) & 1;
        let immr = (insn >> 16) & 0x3f;
        let imms = (insn >> 10) & 0x3f;
        let rn = (insn >> 5) & 0x1f;
        let rd = insn & 0x1f;

        let next = match (decode_bitmask_imm(sf, n, imms, immr), read_zr(state, rn)) {
            (Some(mask), AbsReg::Known(RegOrigin::Const(lhs))) => {
                let mut res = match opc {
                    0 | 3 => lhs & mask,
                    1 => lhs | mask,
                    2 => lhs ^ mask,
                    _ => unreachable!(),
                };
                if sf == 0 {
                    res &= 0xffff_ffff;
                }
                AbsReg::Known(RegOrigin::Const(res))
            }
            _ => AbsReg::Clobbered,
        };
        write_gpr(state, rd, next);
        return;
    }

    // 4. Add/subtract (immediate)
    if (insn & 0x1f00_0000) == 0x1100_0000 {
        let sf = (insn >> 31) & 1;
        let op = (insn >> 30) & 1;
        let sh = (insn >> 22) & 3;
        let imm12 = ((insn >> 10) & 0xfff) as u64;
        let rn = (insn >> 5) & 0x1f;
        let rd = insn & 0x1f;

        let next = if rn < 31 && sh <= 1 {
            match state[rn as usize] {
                AbsReg::Known(RegOrigin::Const(base)) => {
                    let delta = imm12 << (if sh == 1 { 12 } else { 0 });
                    let mut v = if op == 0 {
                        base.wrapping_add(delta)
                    } else {
                        base.wrapping_sub(delta)
                    };
                    if sf == 0 {
                        v &= 0xffff_ffff;
                    }
                    AbsReg::Known(RegOrigin::Const(v))
                }
                _ => AbsReg::Clobbered,
            }
        } else {
            AbsReg::Clobbered
        };
        write_gpr(state, rd, next);
        return;
    }

    // 5. Bitfield (`UXTW Xd, Wn` / `SXTW Xd, Wn` / general `BFM`)
    if (insn & 0x1f80_0000) == 0x1300_0000 {
        let rd = insn & 0x1f;
        let rn = (insn >> 5) & 0x1f;
        let next = if (insn & 0xffff_fc00) == 0xd340_7c00 {
            match read_zr(state, rn) {
                AbsReg::Known(RegOrigin::Const(v)) => {
                    AbsReg::Known(RegOrigin::Const(v & 0xffff_ffff))
                }
                AbsReg::Known(RegOrigin::EntryArg(a)) => AbsReg::Known(RegOrigin::EntryArg(a)),
                _ => AbsReg::Clobbered,
            }
        } else if (insn & 0xffff_fc00) == 0x9340_7c00 {
            match read_zr(state, rn) {
                AbsReg::Known(RegOrigin::Const(v)) => {
                    AbsReg::Known(RegOrigin::Const((v as i32 as i64) as u64))
                }
                AbsReg::Known(RegOrigin::EntryArg(a)) => AbsReg::Known(RegOrigin::EntryArg(a)),
                _ => AbsReg::Clobbered,
            }
        } else {
            AbsReg::Clobbered
        };
        write_gpr(state, rd, next);
        return;
    }

    // 6. System hints and barriers (`NOP`, `ISB`, `DMB`, `DSB`) do not write any GPR.
    if (insn & 0xffff_e000) == 0xd503_2000 {
        return;
    }

    // 7. Load/store pair (`STP`, `LDP`, `LDPSW`, `STNP`, `LDNP`)
    if (insn & 0x3a00_0000) == 0x2800_0000 {
        let v_bit = (insn >> 26) & 1;
        let wb_kind = (insn >> 23) & 3;
        let l_bit = (insn >> 22) & 1;
        let rt2 = (insn >> 10) & 0x1f;
        let rn = (insn >> 5) & 0x1f;
        let rt = insn & 0x1f;
        if wb_kind == 1 || wb_kind == 3 {
            write_gpr(state, rn, AbsReg::Clobbered);
        }
        if l_bit == 1 && v_bit == 0 {
            write_gpr(state, rt, AbsReg::Clobbered);
            write_gpr(state, rt2, AbsReg::Clobbered);
        }
        return;
    }

    // 8. Load/store exclusive & atomic (`LDXR`, `LDAXR`, `STXR`, `STLXR`, `CAS`, `CASP`)
    if (insn & 0x3f00_0000) == 0x0800_0000 {
        let rs = (insn >> 16) & 0x1f;
        let rt2 = (insn >> 10) & 0x1f;
        let rt = insn & 0x1f;
        write_gpr(state, rt, AbsReg::Clobbered);
        write_gpr(state, rt2, AbsReg::Clobbered);
        write_gpr(state, rs, AbsReg::Clobbered);
        if (insn & 0xbf80_0000) == 0x0820_0000 && rs + 1 < 31 {
            write_gpr(state, rs + 1, AbsReg::Clobbered);
        }
        return;
    }

    // 9. Single-register load/store (unsigned offset, unscaled/pre/post, register offset, LSE atomics)
    if (insn & 0x3b00_0000) == 0x3800_0000 || (insn & 0x3b00_0000) == 0x3900_0000 {
        let v_bit = (insn >> 26) & 1;
        let opc = (insn >> 22) & 3;
        let rs = (insn >> 16) & 0x1f;
        let rn = (insn >> 5) & 0x1f;
        let rt = insn & 0x1f;

        // LSE atomic memory ops (`LDADD`, `SWP`, etc.)
        if (insn & 0x3b20_0c00) == 0x3820_0000 {
            if v_bit == 0 {
                write_gpr(state, rt, AbsReg::Clobbered);
                write_gpr(state, rs, AbsReg::Clobbered);
            }
            return;
        }

        // Pre/post-indexed addressing writes back `Rn`.
        if ((insn >> 24) & 1) == 0 {
            let mode = (insn >> 10) & 3;
            if mode == 1 || mode == 3 {
                write_gpr(state, rn, AbsReg::Clobbered);
            }
        }

        if v_bit == 0 && opc != 0 {
            write_gpr(state, rt, AbsReg::Clobbered);
        }
        return;
    }

    // 10. PC-relative literal load (`LDR Xt/Wt/LDRSW, label`)
    if (insn & 0x3b00_0000) == 0x1800_0000 {
        if ((insn >> 26) & 1) == 0 {
            write_gpr(state, insn & 0x1f, AbsReg::Clobbered);
        }
        return;
    }

    // 11. All remaining A64 instructions that modify a GPR write solely `Rd = bits[4:0]`.
    write_gpr(state, insn & 0x1f, AbsReg::Clobbered);
}

/// Analyze a set of disassembled functions, resolving both direct `x8` constants and transitive
/// `arg0 -> x8` syscall wrappers (`syscall`, `__syscall_cp` -> `sccp`, etc.).
pub fn analyze_functions(functions: &[FunctionCode]) -> Vec<StaticSvcSite> {
    let mut raw_sites: Vec<(u64, String, u64, AbsReg)> = Vec::new();
    let mut all_calls: Vec<CallEdge> = Vec::new();
    // Map wrapper `fn_addr` -> indices into `raw_sites` whose `x8` receives `fn_addr`'s `arg0`.
    let mut wrapper_to_sites: BTreeMap<u64, BTreeSet<usize>> = BTreeMap::new();

    for func in functions {
        let intra = analyze_single_function(func);
        for (pc, x8_abs) in intra.svc_sites {
            let site_idx = raw_sites.len();
            if x8_abs == AbsReg::Known(RegOrigin::EntryArg(0)) {
                wrapper_to_sites
                    .entry(func.addr)
                    .or_default()
                    .insert(site_idx);
            }
            raw_sites.push((pc, func.name.clone(), pc - func.addr, x8_abs));
        }
        all_calls.extend(intra.calls);
    }

    // Propagate `EntryArg(0)` forwarding across wrapper-to-wrapper `BL` / tail-call `B` edges
    // (such as `__syscall_cp` tail-branching `b sccp` with `x0` unchanged) until fixpoint.
    loop {
        let mut changed = false;
        for edge in &all_calls {
            if edge.arg0 == AbsReg::Known(RegOrigin::EntryArg(0))
                && let Some(owned) = wrapper_to_sites.get(&edge.target_addr).cloned()
            {
                let entry = wrapper_to_sites.entry(edge.caller_fn_addr).or_default();
                for idx in owned {
                    if entry.insert(idx) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut caller_nrs_by_site: BTreeMap<usize, BTreeSet<u64>> = BTreeMap::new();
    let mut unresolved_by_site: BTreeMap<usize, BTreeSet<u64>> = BTreeMap::new();
    for edge in &all_calls {
        let Some(site_indices) = wrapper_to_sites.get(&edge.target_addr) else {
            continue;
        };
        match edge.arg0 {
            AbsReg::Known(RegOrigin::Const(nr)) => {
                for &idx in site_indices {
                    caller_nrs_by_site.entry(idx).or_default().insert(nr);
                }
            }
            AbsReg::Known(RegOrigin::EntryArg(0)) => {
                // Pure forwarding trampoline (`caller_fn_addr` itself is in `wrapper_to_sites`).
            }
            _ => {
                for &idx in site_indices {
                    unresolved_by_site
                        .entry(idx)
                        .or_default()
                        .insert(edge.call_pc);
                }
            }
        }
    }

    let mut sites: Vec<StaticSvcSite> = raw_sites
        .into_iter()
        .enumerate()
        .map(|(idx, (pc, function, offset_in_fn, x8_abs))| {
            let x8 = match x8_abs {
                AbsReg::Known(RegOrigin::Const(nr)) => StaticX8Value::Resolved(nr),
                AbsReg::Known(RegOrigin::EntryArg(0)) => {
                    let caller_nrs: Vec<u64> = caller_nrs_by_site
                        .remove(&idx)
                        .unwrap_or_default()
                        .into_iter()
                        .collect();
                    let unresolved_callers = unresolved_by_site
                        .remove(&idx)
                        .map_or(0, |pcs| pcs.len());
                    StaticX8Value::IndirectArg0 {
                        caller_nrs,
                        unresolved_callers,
                    }
                }
                _ => StaticX8Value::DynamicUnknown,
            };
            StaticSvcSite {
                pc,
                function,
                offset_in_fn,
                x8,
            }
        })
        .collect();

    sites.sort_by_key(|s| s.pc);
    sites
}

fn is_arm64_mapping_symbol(name: &str) -> bool {
    name.is_empty()
        || name == "$x"
        || name.starts_with("$x.")
        || name == "$d"
        || name.starts_with("$d.")
}

/// Scan an ELF64 little-endian AArch64 `ET_EXEC` binary and resolve all static `svc #0` sites.
pub fn scan_elf_bytes(bin_id: &str, elf_bytes: &[u8]) -> Result<StaticBinaryScan> {
    let elf = ElfFile64::<Endianness>::parse(elf_bytes)
        .with_context(|| format!("failed to parse ELF64 header for `{bin_id}`"))?;
    if !elf.is_little_endian() {
        bail!("binary `{bin_id}` is not little-endian ELF64");
    }
    if elf.architecture() != Architecture::Aarch64 {
        bail!(
            "binary `{bin_id}` architecture is {:?}, expected AArch64",
            elf.architecture()
        );
    }
    let e_type = elf.elf_header().e_type(elf.endian());
    if e_type != ET_EXEC {
        bail!("binary `{bin_id}` ELF e_type is 0x{e_type:x}, expected static ET_EXEC (0x{ET_EXEC:x})");
    }

    let entry_va = elf.entry();
    let sha256 = sha256_hex(elf_bytes);
    let size_bytes = elf_bytes.len() as u64;

    // Collect executable sections (`SHF_EXECINSTR`).
    let mut exec_sections = Vec::new();
    for section in elf.sections() {
        let flags = section.elf_section_header().sh_flags(elf.endian());
        if (flags & u64::from(SHF_EXECINSTR)) == 0 {
            continue;
        }
        let data = section
            .data()
            .with_context(|| format!("failed to read executable section in `{bin_id}`"))?;
        if data.is_empty() {
            continue;
        }
        let sec_name = section.name().unwrap_or(".text").to_owned();
        exec_sections.push((section.index(), sec_name, section.address(), data));
    }
    if exec_sections.is_empty() {
        bail!("binary `{bin_id}` contains no non-empty SHF_EXECINSTR sections");
    }

    // Group `.symtab` symbols per executable section and address, picking a deterministic alias.
    #[derive(Debug, Clone)]
    struct SymCand {
        name: String,
        size: u64,
        is_global: bool,
        is_func: bool,
    }

    let mut syms_by_sec: BTreeMap<usize, BTreeMap<u64, Vec<SymCand>>> = BTreeMap::new();
    for sym in elf.symbols() {
        let Some(sec_idx) = sym.section_index() else {
            continue;
        };
        let Some(&( _, _, sec_addr, sec_data)) =
            exec_sections.iter().find(|(idx, _, _, _)| *idx == sec_idx)
        else {
            continue;
        };
        let kind = sym.kind();
        if kind != SymbolKind::Text && kind != SymbolKind::Unknown {
            continue;
        }
        let Ok(name) = sym.name() else {
            continue;
        };
        if is_arm64_mapping_symbol(name) {
            continue;
        }
        let addr = sym.address();
        let sec_end = sec_addr + sec_data.len() as u64;
        if addr < sec_addr || addr >= sec_end || !(addr - sec_addr).is_multiple_of(4) {
            continue;
        }
        syms_by_sec
            .entry(sec_idx.0)
            .or_default()
            .entry(addr)
            .or_default()
            .push(SymCand {
                name: name.to_owned(),
                size: sym.size(),
                is_global: sym.is_global(),
                is_func: kind == SymbolKind::Text,
            });
    }

    let mut functions = Vec::new();
    let mut raw_svc_word_count = 0usize;

    for &(sec_idx, ref sec_name, sec_addr, sec_data) in &exec_sections {
        let aligned_len = sec_data.len() & !3;
        let sec_end = sec_addr + aligned_len as u64;
        let words_at = |start_va: u64, end_va: u64| -> Vec<u32> {
            let off_start = (start_va - sec_addr) as usize;
            let off_end = (end_va - sec_addr) as usize;
            sec_data[off_start..off_end]
                .chunks_exact(4)
                .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
                .collect()
        };

        for chunk in sec_data[..aligned_len].chunks_exact(4) {
            if u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]) == AARCH64_SVC_0 {
                raw_svc_word_count += 1;
            }
        }

        let mut canonical_syms: Vec<(u64, String, u64)> = Vec::new();
        if let Some(addr_map) = syms_by_sec.get(&sec_idx.0) {
            for (&addr, cands) in addr_map {
                let max_size = cands.iter().map(|c| c.size).max().unwrap_or(0);
                let best = cands
                    .iter()
                    .min_by(|a, b| {
                        (!a.is_global, !a.is_func, a.name.starts_with("__"), a.name.len(), &a.name)
                            .cmp(&(
                                !b.is_global,
                                !b.is_func,
                                b.name.starts_with("__"),
                                b.name.len(),
                                &b.name,
                            ))
                    })
                    .ok_or_else(|| anyhow!("unexpected empty symbol group at 0x{addr:x}"))?;
                canonical_syms.push((addr, best.name.clone(), max_size));
            }
        }

        let mut cursor = sec_addr;
        for (i, (sym_addr, sym_name, sym_size)) in canonical_syms.iter().enumerate() {
            if *sym_addr > cursor {
                functions.push(FunctionCode {
                    addr: cursor,
                    name: format!("{sec_name}+0x{:x}", cursor - sec_addr),
                    words: words_at(cursor, *sym_addr),
                });
            }
            let next_bound = canonical_syms
                .get(i + 1)
                .map_or(sec_end, |(next_addr, _, _)| *next_addr);
            let raw_end = if *sym_size == 0 {
                next_bound
            } else {
                sym_addr.saturating_add(*sym_size & !3).min(next_bound)
            };
            let end = raw_end.max(*sym_addr);
            if end > *sym_addr {
                functions.push(FunctionCode {
                    addr: *sym_addr,
                    name: sym_name.clone(),
                    words: words_at(*sym_addr, end),
                });
            }
            cursor = end;
        }
        if cursor < sec_end {
            functions.push(FunctionCode {
                addr: cursor,
                name: format!("{sec_name}+0x{:x}", cursor - sec_addr),
                words: words_at(cursor, sec_end),
            });
        }
    }

    let sites = analyze_functions(&functions);
    if sites.len() != raw_svc_word_count {
        bail!(
            "internal static-scan invariant violated in `{bin_id}`: found {} `svc #0` words in \
             SHF_EXECINSTR sections, but function partition produced {} sites",
            raw_svc_word_count,
            sites.len()
        );
    }

    let mut distinct = BTreeSet::new();
    for site in &sites {
        match &site.x8 {
            StaticX8Value::Resolved(nr) => {
                distinct.insert(*nr);
            }
            StaticX8Value::IndirectArg0 { caller_nrs, .. } => {
                distinct.extend(caller_nrs.iter().copied());
            }
            StaticX8Value::DynamicUnknown => {}
        }
    }

    Ok(StaticBinaryScan {
        size_bytes,
        sha256,
        entry_va,
        sites,
        distinct_resolved_nrs: distinct.into_iter().collect(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const RET: u32 = 0xd65f_03c0;

    fn movz_x(rd: u32, imm16: u16, hw: u32) -> u32 {
        0xd280_0000 | (hw << 21) | ((imm16 as u32) << 5) | rd
    }

    fn movz_w(rd: u32, imm16: u16, hw: u32) -> u32 {
        0x5280_0000 | (hw << 21) | ((imm16 as u32) << 5) | rd
    }

    fn movn_x(rd: u32, imm16: u16, hw: u32) -> u32 {
        0x9280_0000 | (hw << 21) | ((imm16 as u32) << 5) | rd
    }

    fn movk_x(rd: u32, imm16: u16, hw: u32) -> u32 {
        0xf280_0000 | (hw << 21) | ((imm16 as u32) << 5) | rd
    }

    fn mov_reg_x(rd: u32, rm: u32) -> u32 {
        0xaa00_03e0 | (rm << 16) | rd
    }

    fn add_imm_x(rd: u32, rn: u32, imm12: u32) -> u32 {
        0x9100_0000 | ((imm12 & 0xfff) << 10) | (rn << 5) | rd
    }

    fn bl_rel(from_pc: u64, target_pc: u64) -> u32 {
        let diff_words = ((target_pc as i64) - (from_pc as i64)) / 4;
        0x9400_0000 | ((diff_words as u32) & 0x03ff_ffff)
    }

    fn b_rel(from_pc: u64, target_pc: u64) -> u32 {
        let diff_words = ((target_pc as i64) - (from_pc as i64)) / 4;
        0x1400_0000 | ((diff_words as u32) & 0x03ff_ffff)
    }

    fn b_eq_rel(from_pc: u64, target_pc: u64) -> u32 {
        let diff_words = ((target_pc as i64) - (from_pc as i64)) / 4;
        0x5400_0000 | (((diff_words as u32) & 0x7ffff) << 5)
    }

    #[test]
    fn decodes_movz_movn_movk_mov_add_and_backward_branch_svc() {
        // Function 1: `MOVZ x9, #60; ADD x8, x9, #4; SVC #0` -> 64 (`write`)
        //             followed by `MOVN x8, #0; MOVK x8, #0x00de, lsl #0; MOVK x8, #0, lsl #16`...
        let f1 = FunctionCode {
            addr: 0x20_0000,
            name: "alpha_direct".into(),
            words: vec![
                movz_x(9, 60, 0),
                add_imm_x(8, 9, 4),
                AARCH64_SVC_0,
                // Build `222` (`0xde`) via `MOVN` + `MOVK` + `MOV`:
                movn_x(10, 0xffff, 0), // ~0xffff = 0xffff_ffff_ffff_0000
                movk_x(10, 0, 1),
                movk_x(10, 0, 2),
                movk_x(10, 0, 3),      // x10 == 0
                movk_x(10, 222, 0),    // x10 == 222
                mov_reg_x(8, 10),      // x8 == 222
                AARCH64_SVC_0,
                RET,
            ],
        };

        // Function 2: Backward conditional branch setting `x8 = 98` below the target `svc #0`
        // (mirrors musl `__lockfile` / `__lock` `-ENOSYS` retry layout).
        //   0x201000: b 0x20100c
        //   0x201004: svc #0         <-- reached ONLY from 0x201014 with x8 == 98
        //   0x201008: ret
        //   0x20100c: movz x8, #98
        //   0x201010: svc #0
        //   0x201014: b.eq 0x201004
        //   0x201018: ret
        let f2 = FunctionCode {
            addr: 0x20_1000,
            name: "beta_backedge".into(),
            words: vec![
                b_rel(0x20_1000, 0x20_100c),
                AARCH64_SVC_0,
                RET,
                movz_x(8, 98, 0),
                AARCH64_SVC_0,
                b_eq_rel(0x20_1014, 0x20_1004),
                RET,
            ],
        };

        let sites = analyze_functions(&[f1, f2]);
        assert_eq!(sites.len(), 4);
        assert_eq!(sites[0].x8, StaticX8Value::Resolved(64));
        assert_eq!(sites[1].x8, StaticX8Value::Resolved(222));
        assert_eq!(sites[2].pc, 0x20_1004);
        assert_eq!(sites[2].x8, StaticX8Value::Resolved(98));
        assert_eq!(sites[3].pc, 0x20_1010);
        assert_eq!(sites[3].x8, StaticX8Value::Resolved(98));
    }

    #[test]
    fn resolves_indirect_arg0_wrappers_across_direct_and_tail_callers() {
        // `sccp` at `0x202000`: `mov x8, x0; mov x0, x1; svc #0; ret`
        let sccp = FunctionCode {
            addr: 0x20_2000,
            name: "sccp".into(),
            words: vec![mov_reg_x(8, 0), mov_reg_x(0, 1), AARCH64_SVC_0, RET],
        };
        // `__syscall_cp` at `0x202010`: `b sccp` (tail-call trampoline forwarding `x0`)
        let syscall_cp = FunctionCode {
            addr: 0x20_2010,
            name: "__syscall_cp".into(),
            words: vec![b_rel(0x20_2010, 0x20_2000)],
        };
        // `syscall` at `0x202020`: `uxtw x8, w0; mov x0, x1; svc #0; ret`
        let syscall_fn = FunctionCode {
            addr: 0x20_2020,
            name: "syscall".into(),
            words: vec![0xd340_7c08, mov_reg_x(0, 1), AARCH64_SVC_0, RET],
        };
        // Callers invoking `syscall` with `23` (`dup`) and `278` (`getrandom`), and
        // invoking `__syscall_cp` with `63` (`read`) and `73` (`ppoll`).
        let callers = FunctionCode {
            addr: 0x20_3000,
            name: "widget_callers".into(),
            words: vec![
                movz_w(0, 23, 0),
                bl_rel(0x20_3004, 0x20_2020),
                movz_w(0, 278, 0),
                bl_rel(0x20_300c, 0x20_2020),
                movz_x(0, 63, 0),
                bl_rel(0x20_3014, 0x20_2010),
                movz_x(0, 73, 0),
                bl_rel(0x20_301c, 0x20_2010),
                RET,
            ],
        };

        let sites = analyze_functions(&[sccp, syscall_cp, syscall_fn, callers]);
        assert_eq!(sites.len(), 2);
        assert_eq!(sites[0].function, "sccp");
        assert_eq!(
            sites[0].x8,
            StaticX8Value::IndirectArg0 {
                caller_nrs: vec![63, 73],
                unresolved_callers: 0,
            }
        );
        assert_eq!(sites[1].function, "syscall");
        assert_eq!(
            sites[1].x8,
            StaticX8Value::IndirectArg0 {
                caller_nrs: vec![23, 278],
                unresolved_callers: 0,
            }
        );
    }
}
