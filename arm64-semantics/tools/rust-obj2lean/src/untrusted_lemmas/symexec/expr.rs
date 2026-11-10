// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Symbolic Expression AST (`SymExpr`), Flag State (`FlagState`), Lean 4 `BitVec` Formatter,
//! and Concrete Evaluator (`ConcreteContext`) (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (expression AST and algebraic simplifier for the `symexec`
//!   advisor; concrete evaluation is tested against Unicorn and `Arm64.execInst`).
//! - **Purpose:** Defines symbolic bitvector expressions ([`SymExpr`]), processor flag states
//!   ([`FlagState`]), and branch conditions ([`SymCond`]), providing both:
//!   1. Canonical Lean 4 `BitVec` rendering ([`SymExpr::to_lean`], [`render_cond`]), and
//!   2. Exact concrete evaluation ([`SymExpr::eval`], [`FlagState::eval_nzcv`], [`SymCond::eval`]).
//!
//! # Key Types & Functions
//! - [`SymExpr`], [`BinOpKind`], [`UnaryOpKind`], [`BitfieldOp`], [`SymMemWrite`]: Expression AST.
//! - [`Nzcv`], [`FlagState`], [`SymCond`], [`condition_holds`], [`render_cond`]: Condition flags.
//! - [`ConcreteContext`], [`add_with_carry_64`], [`add_with_carry_32`], [`eval_binop`],
//!   [`eval_bitfield`]: Concrete evaluation primitives.
//!
//! # When to Read This File
//! - Read this file when adding algebraic simplification rules to [`SymExpr`], tuning Lean 4
//!   `BitVec` pretty-printing, or extending [`ConcreteContext`] evaluation.

use std::collections::BTreeMap;

use serde::Serialize;

use crate::untrusted_lemmas::sign_extend;

// ---------------------------------------------------------------------------
// 1. Architectural NZCV Flags & Pure Bitvector Primitives
// ---------------------------------------------------------------------------

/// Architectural `PSTATE.NZCV` condition flags (`N`, `Z`, `C`, `V`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Nzcv {
    pub n: bool,
    pub z: bool,
    pub c: bool,
    pub v: bool,
}

impl Nzcv {
    /// Decode a 4-bit `nzcv` immediate (`bit 3 = N, bit 2 = Z, bit 1 = C, bit 0 = V`, as in `CCMP`).
    pub fn from_u8(bits4: u8) -> Self {
        Self {
            n: ((bits4 >> 3) & 1) != 0,
            z: ((bits4 >> 2) & 1) != 0,
            c: ((bits4 >> 1) & 1) != 0,
            v: (bits4 & 1) != 0,
        }
    }

    /// Encode into a 4-bit value (`bit 3 = N, bit 2 = Z, bit 1 = C, bit 0 = V`).
    pub fn to_u8(self) -> u8 {
        ((self.n as u8) << 3) | ((self.z as u8) << 2) | ((self.c as u8) << 1) | (self.v as u8)
    }

    /// Decode from the architectural 64-bit `NZCV` system register (bits `31..28`).
    pub fn from_pstate_u64(nzcv_reg: u64) -> Self {
        Self::from_u8(((nzcv_reg >> 28) & 0xf) as u8)
    }

    /// Encode into the architectural 64-bit `NZCV` system register (bits `31..28`).
    pub fn to_pstate_u64(self) -> u64 {
        (self.to_u8() as u64) << 28
    }
}

/// 32-bit `AddWithCarry` matching `Arm64.AddWithCarry32` in `Arm64/Trusted/ISA/Eval.lean`.
pub fn add_with_carry_32(x: u32, y: u32, carry_in: bool) -> (u32, Nzcv) {
    let cin = u64::from(carry_in);
    let usum = u64::from(x) + u64::from(y) + cin;
    let ssum = i64::from(x as i32) + i64::from(y as i32) + (cin as i64);
    let res = usum as u32;
    let n = (res >> 31) != 0;
    let z = res == 0;
    let c = (usum >> 32) != 0;
    let v = ssum != i64::from(res as i32);
    (res, Nzcv { n, z, c, v })
}

/// 64-bit `AddWithCarry` matching `Arm64.AddWithCarry64` in `Arm64/Trusted/ISA/Eval.lean`.
pub fn add_with_carry_64(x: u64, y: u64, carry_in: bool) -> (u64, Nzcv) {
    let cin = u128::from(carry_in);
    let usum = u128::from(x) + u128::from(y) + cin;
    let ssum = i128::from(x as i64) + i128::from(y as i64) + (cin as i128);
    let res = usum as u64;
    let n = (res >> 63) != 0;
    let z = res == 0;
    let c = (usum >> 64) != 0;
    let v = ssum != i128::from(res as i64);
    (res, Nzcv { n, z, c, v })
}

/// Evaluate `ADD`/`ADDS`/`SUB`/`SUBS`/`ADC`/`ADCS`/`SBC`/`SBCS` at `width` (32 or 64) with carry `c_in`.
/// When `is_sub` is true, the second operand is bitwise-inverted before `AddWithCarry`.
pub fn eval_add_sub_with_carry(
    width: u32,
    is_sub: bool,
    lhs: u64,
    rhs: u64,
    c_in: bool,
) -> (u64, Nzcv) {
    if width == 32 {
        let x32 = lhs as u32;
        let y32 = if is_sub { !(rhs as u32) } else { rhs as u32 };
        let (res32, nzcv) = add_with_carry_32(x32, y32, c_in);
        (res32 as u64, nzcv)
    } else {
        let y64 = if is_sub { !rhs } else { rhs };
        add_with_carry_64(lhs, y64, c_in)
    }
}

/// Evaluate `ConditionHolds(cond, ps)` matching `Arm64.ConditionHolds` in `Arm64/Trusted/ISA/Eval.lean`.
pub fn condition_holds(cond_bits: u8, ps: Nzcv) -> bool {
    match cond_bits & 0xf {
        0x0 => ps.z,                        // EQ
        0x1 => !ps.z,                       // NE
        0x2 => ps.c,                        // CS / HS
        0x3 => !ps.c,                       // CC / LO
        0x4 => ps.n,                        // MI
        0x5 => !ps.n,                       // PL
        0x6 => ps.v,                        // VS
        0x7 => !ps.v,                       // VC
        0x8 => ps.c && !ps.z,               // HI
        0x9 => !(ps.c && !ps.z),            // LS
        0xa => ps.n == ps.v,                // GE
        0xb => ps.n != ps.v,                // LT
        0xc => !ps.z && (ps.n == ps.v),     // GT
        0xd => !(!ps.z && (ps.n == ps.v)),  // LE
        _ => true,                          // AL (0xe), NV (0xf)
    }
}

/// Bitfield move operation kind (`SBFM`, `BFM`, `UBFM`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum BitfieldOp {
    Sbfm,
    Bfm,
    Ubfm,
}

impl BitfieldOp {
    pub fn from_opc(opc: u64) -> Option<Self> {
        match opc {
            0 => Some(Self::Sbfm),
            1 => Some(Self::Bfm),
            2 => Some(Self::Ubfm),
            _ => None,
        }
    }

    pub fn mnemonic(self) -> &'static str {
        match self {
            Self::Sbfm => "sbfm",
            Self::Bfm => "bfm",
            Self::Ubfm => "ubfm",
        }
    }
}

/// Evaluate `SBFM`, `BFM`, `UBFM` bitfield move at `width` (32 or 64), matching `Arm64.evalBitfield`
/// in `Arm64/Trusted/ISA/Eval.lean`.
pub fn eval_bitfield(
    width: u32,
    op: BitfieldOp,
    dst: u64,
    src: u64,
    immr: u32,
    imms: u32,
) -> u64 {
    let n = if width == 32 { 32u32 } else { 64u32 };
    let src_w = if width == 32 { src & 0xffff_ffff } else { src };
    let dst_w = if width == 32 { dst & 0xffff_ffff } else { dst };
    let immr = immr % n;
    let imms = imms % n;
    let mask_of_len = |len: u32| -> u64 {
        if len >= 64 {
            u64::MAX
        } else if len == 0 {
            0
        } else {
            (1u64 << len) - 1
        }
    };
    let res64 = if imms >= immr {
        let len = imms - immr + 1;
        let field_mask = mask_of_len(len);
        let extracted = (src_w >> immr) & field_mask;
        match op {
            BitfieldOp::Ubfm => extracted,
            BitfieldOp::Sbfm => {
                let sign_bit = ((src_w >> imms) & 1) != 0;
                let sign_fill = if sign_bit { u64::MAX } else { 0 };
                extracted | (sign_fill & !field_mask)
            }
            BitfieldOp::Bfm => (dst_w & !field_mask) | extracted,
        }
    } else {
        let len = imms + 1;
        let pos = n - immr;
        let low_mask = mask_of_len(len);
        let field_mask = low_mask.wrapping_shl(pos);
        let positioned = (src_w & low_mask).wrapping_shl(pos);
        match op {
            BitfieldOp::Ubfm => positioned,
            BitfieldOp::Sbfm => {
                let sign_bit = ((src_w >> imms) & 1) != 0;
                let sign_fill = if sign_bit { u64::MAX } else { 0 };
                let top_mask = if pos + len >= 64 {
                    0
                } else {
                    !mask_of_len(pos + len)
                };
                positioned | (sign_fill & top_mask)
            }
            BitfieldOp::Bfm => (dst_w & !field_mask) | positioned,
        }
    };
    if width == 32 {
        res64 & 0xffff_ffff
    } else {
        res64
    }
}

/// Evaluate `EXTR` at `width` (32 or 64) with shift `lsb`, matching `Operation.EXTR` in `Arm64/Trusted/ISA/Eval.lean`.
pub fn eval_extr(width: u32, rn: u64, rm: u64, lsb: u32) -> u64 {
    if width == 32 {
        let lsb = lsb % 32;
        let n32 = rn as u32;
        let m32 = rm as u32;
        let res = if lsb == 0 {
            m32
        } else {
            (n32 << (32 - lsb)) | (m32 >> lsb)
        };
        res as u64
    } else {
        let lsb = lsb % 64;
        if lsb == 0 {
            rm
        } else {
            (rn << (64 - lsb)) | (rm >> lsb)
        }
    }
}

/// Binary operators in [`SymExpr::BinOp`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    And,
    Or,
    Xor,
    Lsl,
    Lsr,
    Asr,
    Ror,
    Smulh,
    Umulh,
}

impl BinOpKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::UDiv => "/",
            Self::SDiv => "/ₛ",
            Self::And => "&&&",
            Self::Or => "|||",
            Self::Xor => "^^^",
            Self::Lsl => "<<<",
            Self::Lsr => ">>>",
            Self::Asr => ">>>ₛ",
            Self::Ror => "ror",
            Self::Smulh => "*ₛₕ",
            Self::Umulh => "*ᵤₕ",
        }
    }
}

/// Evaluate a binary operation at `width` (32 or 64) on concrete 64-bit operands `l0, r0`.
pub fn eval_binop(op: BinOpKind, width: u32, l0: u64, r0: u64) -> u64 {
    if width == 32 {
        let l = l0 as u32;
        let r = r0 as u32;
        let res32: u32 = match op {
            BinOpKind::Add => l.wrapping_add(r),
            BinOpKind::Sub => l.wrapping_sub(r),
            BinOpKind::Mul => l.wrapping_mul(r),
            BinOpKind::UDiv => {
                if r == 0 {
                    0
                } else {
                    l / r
                }
            }
            BinOpKind::SDiv => {
                if r == 0 {
                    0
                } else {
                    (l as i32).wrapping_div(r as i32) as u32
                }
            }
            BinOpKind::And => l & r,
            BinOpKind::Or => l | r,
            BinOpKind::Xor => l ^ r,
            BinOpKind::Lsl => l.wrapping_shl(r & 31),
            BinOpKind::Lsr => l.wrapping_shr(r & 31),
            BinOpKind::Asr => ((l as i32).wrapping_shr(r & 31)) as u32,
            BinOpKind::Ror => l.rotate_right(r & 31),
            BinOpKind::Smulh | BinOpKind::Umulh => 0,
        };
        res32 as u64
    } else {
        match op {
            BinOpKind::Add => l0.wrapping_add(r0),
            BinOpKind::Sub => l0.wrapping_sub(r0),
            BinOpKind::Mul => l0.wrapping_mul(r0),
            BinOpKind::UDiv => {
                if r0 == 0 {
                    0
                } else {
                    l0 / r0
                }
            }
            BinOpKind::SDiv => {
                if r0 == 0 {
                    0
                } else {
                    (l0 as i64).wrapping_div(r0 as i64) as u64
                }
            }
            BinOpKind::And => l0 & r0,
            BinOpKind::Or => l0 | r0,
            BinOpKind::Xor => l0 ^ r0,
            BinOpKind::Lsl => l0.wrapping_shl((r0 as u32) & 63),
            BinOpKind::Lsr => l0.wrapping_shr((r0 as u32) & 63),
            BinOpKind::Asr => ((l0 as i64).wrapping_shr((r0 as u32) & 63)) as u64,
            BinOpKind::Ror => l0.rotate_right((r0 as u32) & 63),
            BinOpKind::Smulh => ((i128::from(l0 as i64) * i128::from(r0 as i64)) >> 64) as u64,
            BinOpKind::Umulh => ((u128::from(l0) * u128::from(r0)) >> 64) as u64,
        }
    }
}

/// 1-source / unary operators in [`SymExpr::UnaryOp`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum UnaryOpKind {
    Not,
    Rbit,
    Rev16,
    Rev32,
    Rev64,
    Clz,
    Cls,
}

impl UnaryOpKind {
    pub fn mnemonic(self) -> &'static str {
        match self {
            Self::Not => "~~~",
            Self::Rbit => "rbit",
            Self::Rev16 => "rev16",
            Self::Rev32 => "rev32",
            Self::Rev64 => "rev64",
            Self::Clz => "clz",
            Self::Cls => "cls",
        }
    }
}

/// Evaluate a 1-source / unary operation at `width` (32 or 64) on concrete 64-bit operand `v0`.
pub fn eval_unary(op: UnaryOpKind, width: u32, v0: u64) -> u64 {
    if width == 32 {
        let v = v0 as u32;
        let res32: u32 = match op {
            UnaryOpKind::Not => !v,
            UnaryOpKind::Rbit => v.reverse_bits(),
            UnaryOpKind::Rev16 => ((v >> 8) & 0x00ff_00ff) | ((v & 0x00ff_00ff) << 8),
            UnaryOpKind::Rev32 | UnaryOpKind::Rev64 => v.swap_bytes(),
            UnaryOpKind::Clz => v.leading_zeros(),
            UnaryOpKind::Cls => {
                let inv = if (v as i32) < 0 { !v } else { v };
                inv.leading_zeros().saturating_sub(1).min(31)
            }
        };
        res32 as u64
    } else {
        match op {
            UnaryOpKind::Not => !v0,
            UnaryOpKind::Rbit => v0.reverse_bits(),
            UnaryOpKind::Rev16 => {
                ((v0 >> 8) & 0x00ff_00ff_00ff_00ff) | ((v0 & 0x00ff_00ff_00ff_00ff) << 8)
            }
            UnaryOpKind::Rev32 => {
                let lo = (v0 as u32).swap_bytes() as u64;
                let hi = ((v0 >> 32) as u32).swap_bytes() as u64;
                lo | (hi << 32)
            }
            UnaryOpKind::Rev64 => v0.swap_bytes(),
            UnaryOpKind::Clz => v0.leading_zeros() as u64,
            UnaryOpKind::Cls => {
                let inv = if (v0 as i64) < 0 { !v0 } else { v0 };
                (inv.leading_zeros().saturating_sub(1).min(63)) as u64
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 2. Concrete Context for Differential Testing
// ---------------------------------------------------------------------------

/// Concrete initial machine state (`X0..X30`, `SP`, `base_pc`, `NZCV`, `TPIDR_EL0`, and byte memory)
/// against which symbolic expressions (`SymExpr`), flags (`FlagState`), and conditions (`SymCond`)
/// can be evaluated.
#[derive(Clone, Debug, Default)]
pub struct ConcreteContext {
    /// Initial general-purpose registers `X0..X30` (`regs[0..31]`) and `SP` (`regs[31]`).
    pub regs: [u64; 32],
    /// Architectural address corresponding to function-relative offset `0x0`.
    pub base_pc: u64,
    /// Initial architectural `NZCV` flags.
    pub nzcv: Nzcv,
    /// Initial `TPIDR_EL0` system register value.
    pub tpidr_el0: u64,
    /// Initial byte-addressable memory (`addr -> byte`). Unmapped bytes read as `0`.
    pub mem: BTreeMap<u64, u8>,
}

impl ConcreteContext {
    /// Read a little-endian value of `width_bits` (8, 16, 32, or 64) at `addr` after replaying
    /// `prior_writes`.
    pub fn read_mem_with_writes(
        &self,
        addr: u64,
        width_bits: u32,
        prior_writes: &[SymMemWrite],
    ) -> u64 {
        self.read_mem_with_writes_and_vars(addr, width_bits, prior_writes, &BTreeMap::new())
    }

    /// Read a little-endian value of `width_bits` (8, 16, 32, or 64) at `addr` after replaying
    /// `prior_writes` under `let`-bound `vars`.
    pub fn read_mem_with_writes_and_vars(
        &self,
        addr: u64,
        width_bits: u32,
        prior_writes: &[SymMemWrite],
        vars: &BTreeMap<String, u64>,
    ) -> u64 {
        let num_bytes = (width_bits / 8) as u64;
        let mut bytes = [0u8; 8];
        for i in 0..num_bytes {
            let b_addr = addr.wrapping_add(i);
            bytes[i as usize] = self.mem.get(&b_addr).copied().unwrap_or(0);
        }
        for w in prior_writes {
            let w_addr = w.addr.eval_with_vars(self, vars);
            let w_val = w.val.eval_with_vars(self, vars);
            let w_bytes = (w.width_bits / 8) as u64;
            for j in 0..w_bytes {
                let b_addr = w_addr.wrapping_add(j);
                let delta = b_addr.wrapping_sub(addr);
                if delta < num_bytes {
                    bytes[delta as usize] = ((w_val >> (j * 8)) & 0xff) as u8;
                }
            }
        }
        let val = u64::from_le_bytes(bytes);
        if width_bits >= 64 {
            val
        } else {
            val & ((1u64 << width_bits) - 1)
        }
    }
}

/// Recorded symbolic memory store for exact byte-level replay under concrete evaluation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymMemWrite {
    pub addr: Box<SymExpr>,
    pub width_bits: u32,
    pub val: Box<SymExpr>,
}

// ---------------------------------------------------------------------------
// 3. Symbolic Expression AST (`SymExpr`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(tag = "kind", content = "val")]
pub enum SymExpr {
    /// 64-bit constant `0x...#64`.
    Const(u64),
    /// Initial register value at entry (`0..=30` for `x0`..`x30`, `31` for `sp`, `32` for `tpidr_el0`).
    InitReg(u8),
    /// Named intermediate `let`-bound checkpoint variable (`r{reg}_step{n}`).
    Var(String),
    /// Initial memory value at `(base_expr_str, signed_offset, width_bits)`.
    InitMem {
        base: String,
        offset: i64,
        width_bits: u32,
        #[serde(skip)]
        addr: Option<Box<SymExpr>>,
        #[serde(skip)]
        prior_writes: Vec<SymMemWrite>,
    },
    /// Return value of a `BL` call at `(callee, call_offset)`.
    CallRet {
        callee: String,
        call_offset: u64,
    },
    /// PC-relative address (`ADR`: `(base_pc + pc_off) + offset`; `ADRP`: `((base_pc + pc_off) & !0xfff) + offset`).
    PcRel {
        pc_off: u64,
        offset: i64,
        is_page: bool,
    },
    /// Pointer/value + constant offset (`base + offset`), normalized so nested `AddConst` fold.
    AddConst(Box<SymExpr>, u64),
    /// Zero-extended 32/16/8-bit value to 64 bits.
    ZeroExt {
        width: u32,
        inner: Box<SymExpr>,
    },
    /// Sign-extended 32/16/8-bit value to 64 bits.
    SignExt {
        width: u32,
        inner: Box<SymExpr>,
    },
    /// Binary operation in Lean `BitVec` syntax.
    BinOp {
        op: &'static str,
        #[serde(skip)]
        op_kind: Option<BinOpKind>,
        width: u32,
        lhs: Box<SymExpr>,
        rhs: Box<SymExpr>,
    },
    /// Structured unary / 1-source operation (`Not`, `Rbit`, `Rev16`, `Rev32`, `Rev64`, `Clz`, `Cls`).
    UnaryOp {
        op: UnaryOpKind,
        width: u32,
        arg: Box<SymExpr>,
    },
    /// Bitfield move (`SBFM`, `BFM`, `UBFM`) when not reduced to a simpler shift/extension.
    Bitfield {
        op: BitfieldOp,
        width: u32,
        dst: Box<SymExpr>,
        src: Box<SymExpr>,
        immr: u32,
        imms: u32,
    },
    /// Extract (`EXTR`) when `rn != rm`.
    Extr {
        width: u32,
        rn: Box<SymExpr>,
        rm: Box<SymExpr>,
        lsb: u32,
    },
    /// Add/subtract with carry (`ADC`, `ADCS`, `SBC`, `SBCS`).
    AdcSbc {
        is_sub: bool,
        width: u32,
        lhs: Box<SymExpr>,
        rhs: Box<SymExpr>,
        #[serde(skip)]
        flags: Box<FlagState>,
    },
    /// Unstructured symbolic expression (e.g. user `--init` override).
    Unary {
        desc: String,
    },
    /// Conditional expression (`if cond then t else f`).
    Ite {
        cond: String,
        #[serde(skip)]
        cond_sym: Option<Box<SymCond>>,
        then_val: Box<SymExpr>,
        else_val: Box<SymExpr>,
    },
}

pub fn reg_name(r: u8) -> &'static str {
    match r {
        0 => "x0",
        1 => "x1",
        2 => "x2",
        3 => "x3",
        4 => "x4",
        5 => "x5",
        6 => "x6",
        7 => "x7",
        8 => "x8",
        9 => "x9",
        10 => "x10",
        11 => "x11",
        12 => "x12",
        13 => "x13",
        14 => "x14",
        15 => "x15",
        16 => "x16",
        17 => "x17",
        18 => "x18",
        19 => "x19",
        20 => "x20",
        21 => "x21",
        22 => "x22",
        23 => "x23",
        24 => "x24",
        25 => "x25",
        26 => "x26",
        27 => "x27",
        28 => "x28",
        29 => "x29",
        30 => "x30",
        31 => "sp",
        32 => "tpidr_el0",
        _ => "xzr",
    }
}

pub fn format_bv64(c: u64) -> String {
    format!("0x{c:x}#64")
}

impl SymExpr {
    pub fn zero() -> Self {
        SymExpr::Const(0)
    }

    /// Normalize `self + delta` (mod 2^64), folding constants and nested `AddConst` exactly like
    /// `reduceBitVecAddAssoc`, `reduceBitVecAddSub`, `reduceBitVecSubSub`, `reduceBitVecSubAdd`.
    pub fn add_const(self, delta: u64) -> Self {
        if delta == 0 {
            return self;
        }
        match self {
            SymExpr::Const(c) => SymExpr::Const(c.wrapping_add(delta)),
            SymExpr::AddConst(base, c1) => {
                let c = c1.wrapping_add(delta);
                if c == 0 {
                    *base
                } else {
                    SymExpr::AddConst(base, c)
                }
            }
            other => SymExpr::AddConst(Box::new(other), delta),
        }
    }

    pub fn sub_const(self, delta: u64) -> Self {
        self.add_const(delta.wrapping_neg())
    }

    pub fn add(lhs: Self, rhs: Self, is_64: bool) -> Self {
        if is_64 {
            match (lhs, rhs) {
                (SymExpr::Const(a), SymExpr::Const(b)) => SymExpr::Const(a.wrapping_add(b)),
                (e, SymExpr::Const(b)) => e.add_const(b),
                (SymExpr::Const(a), e) => e.add_const(a),
                (SymExpr::AddConst(base, c), rhs) => {
                    SymExpr::BinOp {
                        op: "+",
                        op_kind: Some(BinOpKind::Add),
                        width: 64,
                        lhs: base,
                        rhs: Box::new(rhs),
                    }
                    .add_const(c)
                }
                (lhs, SymExpr::AddConst(base, c)) => {
                    SymExpr::BinOp {
                        op: "+",
                        op_kind: Some(BinOpKind::Add),
                        width: 64,
                        lhs: Box::new(lhs),
                        rhs: base,
                    }
                    .add_const(c)
                }
                (l, r) => SymExpr::BinOp {
                    op: "+",
                    op_kind: Some(BinOpKind::Add),
                    width: 64,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                },
            }
        } else {
            match (&lhs, &rhs) {
                (SymExpr::Const(a), SymExpr::Const(b)) => {
                    SymExpr::Const(((*a as u32).wrapping_add(*b as u32)) as u64)
                }
                _ => SymExpr::ZeroExt {
                    width: 32,
                    inner: Box::new(SymExpr::BinOp {
                        op: "+",
                        op_kind: Some(BinOpKind::Add),
                        width: 32,
                        lhs: Box::new(lhs.trunc32()),
                        rhs: Box::new(rhs.trunc32()),
                    }),
                },
            }
        }
    }

    pub fn sub(lhs: Self, rhs: Self, is_64: bool) -> Self {
        if is_64 {
            if lhs == rhs {
                return SymExpr::Const(0);
            }
            match (lhs, rhs) {
                (SymExpr::Const(a), SymExpr::Const(b)) => SymExpr::Const(a.wrapping_sub(b)),
                (e, SymExpr::Const(b)) => e.sub_const(b),
                (SymExpr::AddConst(b1, c1), SymExpr::AddConst(b2, c2)) if b1 == b2 => {
                    SymExpr::Const(c1.wrapping_sub(c2))
                }
                (SymExpr::AddConst(b1, c1), r) if *b1 == r => SymExpr::Const(c1),
                (l, r) => SymExpr::BinOp {
                    op: "-",
                    op_kind: Some(BinOpKind::Sub),
                    width: 64,
                    lhs: Box::new(l),
                    rhs: Box::new(r),
                },
            }
        } else {
            if lhs == rhs {
                return SymExpr::Const(0);
            }
            match (&lhs, &rhs) {
                (SymExpr::Const(a), SymExpr::Const(b)) => {
                    SymExpr::Const(((*a as u32).wrapping_sub(*b as u32)) as u64)
                }
                _ => SymExpr::ZeroExt {
                    width: 32,
                    inner: Box::new(SymExpr::BinOp {
                        op: "-",
                        op_kind: Some(BinOpKind::Sub),
                        width: 32,
                        lhs: Box::new(lhs.trunc32()),
                        rhs: Box::new(rhs.trunc32()),
                    }),
                },
            }
        }
    }

    /// Construct a binary operation, folding constants immediately via [`eval_binop`].
    pub fn binop(kind: BinOpKind, width: u32, lhs: Self, rhs: Self) -> Self {
        if let (SymExpr::Const(a), SymExpr::Const(b)) = (&lhs, &rhs) {
            return SymExpr::Const(eval_binop(kind, width, *a, *b));
        }
        SymExpr::BinOp {
            op: kind.as_str(),
            op_kind: Some(kind),
            width,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    /// Construct a 1-source / unary operation, folding constants immediately via [`eval_unary`].
    pub fn unary_op(op: UnaryOpKind, width: u32, arg: Self) -> Self {
        if let SymExpr::Const(c) = &arg {
            return SymExpr::Const(eval_unary(op, width, *c));
        }
        SymExpr::UnaryOp {
            op,
            width,
            arg: Box::new(arg),
        }
    }

    /// Bitwise NOT (`~~~x`) at `width` bits.
    pub fn bit_not(arg: Self, width: u32) -> Self {
        Self::unary_op(UnaryOpKind::Not, width, arg)
    }

    /// Construct a conditional (`ite`) expression, simplifying when both arms are equal or when
    /// the condition evaluates to a constant.
    pub fn ite(cond: SymCond, then_val: Self, else_val: Self) -> Self {
        if then_val == else_val {
            return then_val;
        }
        if let Some(b) = cond.try_eval_const() {
            return if b { then_val } else { else_val };
        }
        let cond_str = cond.to_lean();
        SymExpr::Ite {
            cond: cond_str,
            cond_sym: Some(Box::new(cond)),
            then_val: Box::new(then_val),
            else_val: Box::new(else_val),
        }
    }

    pub fn trunc32(&self) -> Self {
        match self {
            SymExpr::Const(c) => SymExpr::Const(*c & 0xffff_ffff),
            SymExpr::ZeroExt { width: 32, inner } => (**inner).clone(),
            SymExpr::ZeroExt { width, .. } if *width < 32 => self.clone(),
            _ => self.clone(),
        }
    }

    pub fn zero_ext(self, width: u32) -> Self {
        let mask = if width >= 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        match self {
            SymExpr::Const(c) => SymExpr::Const(c & mask),
            SymExpr::ZeroExt {
                width: w_inner,
                inner,
            } if w_inner <= width => SymExpr::ZeroExt {
                width: w_inner,
                inner,
            },
            SymExpr::ZeroExt {
                width: w_inner,
                inner,
            } if w_inner > width => inner.zero_ext(width),
            other if width >= 64 => other,
            other => SymExpr::ZeroExt {
                width,
                inner: Box::new(other),
            },
        }
    }

    pub fn sign_ext(self, width: u32) -> Self {
        match self {
            SymExpr::Const(c) => SymExpr::Const(sign_extend(c, width)),
            other if width >= 64 => other,
            other => SymExpr::SignExt {
                width,
                inner: Box::new(other),
            },
        }
    }

    /// Count the number of AST nodes in `self` (used to bound inline expression blowup).
    pub fn node_count(&self) -> usize {
        match self {
            SymExpr::Const(_)
            | SymExpr::InitReg(_)
            | SymExpr::Var(_)
            | SymExpr::CallRet { .. }
            | SymExpr::PcRel { .. }
            | SymExpr::Unary { .. } => 1,
            SymExpr::InitMem { addr, .. } => 1 + addr.as_ref().map_or(0, |a| a.node_count()),
            SymExpr::AddConst(base, _)
            | SymExpr::ZeroExt { inner: base, .. }
            | SymExpr::SignExt { inner: base, .. }
            | SymExpr::UnaryOp { arg: base, .. } => 1 + base.node_count(),
            SymExpr::BinOp { lhs, rhs, .. } | SymExpr::AdcSbc { lhs, rhs, .. } => {
                1 + lhs.node_count() + rhs.node_count()
            }
            SymExpr::Bitfield { dst, src, .. } => 1 + dst.node_count() + src.node_count(),
            SymExpr::Extr { rn, rm, .. } => 1 + rn.node_count() + rm.node_count(),
            SymExpr::Ite {
                then_val, else_val, ..
            } => 1 + then_val.node_count() + else_val.node_count(),
        }
    }

    /// Evaluate `self` to a concrete 64-bit value under `ctx`.
    pub fn eval(&self, ctx: &ConcreteContext) -> u64 {
        self.eval_with_vars(ctx, &BTreeMap::new())
    }

    /// Evaluate `self` to a concrete 64-bit value under `ctx` and `let`-bound `vars`.
    pub fn eval_with_vars(&self, ctx: &ConcreteContext, vars: &BTreeMap<String, u64>) -> u64 {
        match self {
            SymExpr::Const(c) => *c,
            SymExpr::InitReg(r) => {
                if *r <= 31 {
                    ctx.regs[*r as usize]
                } else if *r == 32 {
                    ctx.tpidr_el0
                } else {
                    0
                }
            }
            SymExpr::Var(name) => vars.get(name).copied().unwrap_or(0),
            SymExpr::InitMem {
                width_bits,
                addr,
                prior_writes,
                ..
            } => {
                let ea = addr.as_ref().map(|a| a.eval_with_vars(ctx, vars)).unwrap_or(0);
                ctx.read_mem_with_writes_and_vars(ea, *width_bits, prior_writes, vars)
            }
            SymExpr::CallRet { .. } => 0,
            SymExpr::PcRel {
                pc_off,
                offset,
                is_page,
            } => {
                let insn_pc = ctx.base_pc.wrapping_add(*pc_off);
                let base = if *is_page {
                    insn_pc & !0xfff
                } else {
                    insn_pc
                };
                base.wrapping_add(*offset as u64)
            }
            SymExpr::AddConst(base, off) => base.eval_with_vars(ctx, vars).wrapping_add(*off),
            SymExpr::ZeroExt { width, inner } => {
                let v = inner.eval_with_vars(ctx, vars);
                if *width >= 64 {
                    v
                } else {
                    v & ((1u64 << *width) - 1)
                }
            }
            SymExpr::SignExt { width, inner } => {
                let v = inner.eval_with_vars(ctx, vars);
                if *width >= 64 {
                    v
                } else {
                    sign_extend(v, *width)
                }
            }
            SymExpr::BinOp {
                op,
                op_kind,
                width,
                lhs,
                rhs,
            } => {
                let kind = op_kind.unwrap_or_else(|| match *op {
                    "+" => BinOpKind::Add,
                    "-" => BinOpKind::Sub,
                    "*" => BinOpKind::Mul,
                    "/" => BinOpKind::UDiv,
                    "/ₛ" => BinOpKind::SDiv,
                    "&&&" => BinOpKind::And,
                    "|||" => BinOpKind::Or,
                    "^^^" => BinOpKind::Xor,
                    "<<<" => BinOpKind::Lsl,
                    ">>>" => BinOpKind::Lsr,
                    ">>>ₛ" => BinOpKind::Asr,
                    "ror" => BinOpKind::Ror,
                    "*ₛₕ" => BinOpKind::Smulh,
                    "*ᵤₕ" => BinOpKind::Umulh,
                    _ => BinOpKind::Add,
                });
                eval_binop(
                    kind,
                    *width,
                    lhs.eval_with_vars(ctx, vars),
                    rhs.eval_with_vars(ctx, vars),
                )
            }
            SymExpr::UnaryOp { op, width, arg } => {
                eval_unary(*op, *width, arg.eval_with_vars(ctx, vars))
            }
            SymExpr::Bitfield {
                op,
                width,
                dst,
                src,
                immr,
                imms,
            } => eval_bitfield(
                *width,
                *op,
                dst.eval_with_vars(ctx, vars),
                src.eval_with_vars(ctx, vars),
                *immr,
                *imms,
            ),
            SymExpr::Extr {
                width,
                rn,
                rm,
                lsb,
            } => eval_extr(
                *width,
                rn.eval_with_vars(ctx, vars),
                rm.eval_with_vars(ctx, vars),
                *lsb,
            ),
            SymExpr::AdcSbc {
                is_sub,
                width,
                lhs,
                rhs,
                flags,
            } => {
                let c = flags.eval_nzcv_with_vars(ctx, vars).c;
                eval_add_sub_with_carry(
                    *width,
                    *is_sub,
                    lhs.eval_with_vars(ctx, vars),
                    rhs.eval_with_vars(ctx, vars),
                    c,
                )
                .0
            }
            SymExpr::Unary { .. } => 0,
            SymExpr::Ite {
                cond_sym,
                then_val,
                else_val,
                ..
            } => {
                let take_then = cond_sym
                    .as_ref()
                    .map(|c| c.eval_with_vars(ctx, vars))
                    .unwrap_or(true);
                if take_then {
                    then_val.eval_with_vars(ctx, vars)
                } else {
                    else_val.eval_with_vars(ctx, vars)
                }
            }
        }
    }

    /// Decompose `self` as `(base_reg, signed_offset)` when `self` is `InitReg(r) + off`.
    pub fn as_reg_offset(&self) -> Option<(u8, i64)> {
        match self {
            SymExpr::InitReg(r) => Some((*r, 0)),
            SymExpr::AddConst(inner, off) => {
                if let SymExpr::InitReg(r) = **inner {
                    Some((r, *off as i64))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Decompose `self` as `(base_lean_str, signed_offset)` for symbolic memory indexing.
    pub fn as_base_offset(&self) -> (String, i64) {
        match self {
            SymExpr::AddConst(inner, off) => (inner.to_lean(), *off as i64),
            other => (other.to_lean(), 0),
        }
    }

    /// Render the symbolic expression in Lean 4 `BitVec` syntax matching `ProofLib`.
    pub fn to_lean(&self) -> String {
        match self {
            SymExpr::Const(c) => format_bv64(*c),
            SymExpr::InitReg(r) => reg_name(*r).to_string(),
            SymExpr::Var(name) => name.clone(),
            SymExpr::InitMem {
                base,
                offset,
                width_bits,
                ..
            } => {
                let w = match width_bits {
                    8 => "₈",
                    16 => "₁₆",
                    32 => "₃₂",
                    _ => "₆₄",
                };
                if *offset == 0 {
                    format!("mem{w}[{base}]")
                } else if *offset < 0 {
                    format!("mem{w}[{base} - 0x{:x}#64]", offset.unsigned_abs())
                } else {
                    format!("mem{w}[{base} + 0x{:x}#64]", *offset as u64)
                }
            }
            SymExpr::CallRet {
                callee,
                call_offset,
            } => format!("ret_{callee}_0x{call_offset:x}"),
            SymExpr::PcRel {
                pc_off,
                offset,
                is_page,
            } => {
                let off_u64 = *offset as u64;
                if *is_page {
                    format!("(adrp_0x{pc_off:x} + 0x{off_u64:x}#64)")
                } else {
                    format!("(pc_0x{pc_off:x} + 0x{off_u64:x}#64)")
                }
            }
            SymExpr::AddConst(base, off) => {
                let signed = *off as i64;
                if signed < 0 && signed > -0x1_0000_0000 {
                    format!("({} - 0x{:x}#64)", base.to_lean(), signed.unsigned_abs())
                } else {
                    format!("({} + 0x{:x}#64)", base.to_lean(), off)
                }
            }
            SymExpr::ZeroExt { width, inner } => {
                format!(
                    "(ZeroExtend.zeroExtend 64 (BitVec.truncate {width} {}))",
                    inner.to_lean()
                )
            }
            SymExpr::SignExt { width, inner } => {
                format!(
                    "(SignExtend.signExtend 64 (BitVec.truncate {width} {}))",
                    inner.to_lean()
                )
            }
            SymExpr::BinOp {
                op,
                width,
                lhs,
                rhs,
                ..
            } => {
                if *width == 64 {
                    format!("({} {op} {})", lhs.to_lean(), rhs.to_lean())
                } else {
                    format!("({} {op}_{width} {})", lhs.to_lean(), rhs.to_lean())
                }
            }
            SymExpr::UnaryOp { op, arg, .. } => match op {
                UnaryOpKind::Not => format!("(~~~{})", arg.to_lean()),
                other => format!("({} {})", other.mnemonic(), arg.to_lean()),
            },
            SymExpr::Bitfield {
                op,
                src,
                immr,
                imms,
                ..
            } => {
                format!("({} {} {immr} {imms})", op.mnemonic(), src.to_lean())
            }
            SymExpr::Extr { rn, rm, lsb, .. } => {
                format!("(extr {} {} {lsb})", rn.to_lean(), rm.to_lean())
            }
            SymExpr::AdcSbc {
                is_sub, lhs, rhs, ..
            } => {
                if *is_sub {
                    format!("({} - {} - !c_flag)", lhs.to_lean(), rhs.to_lean())
                } else {
                    format!("({} + {} + c_flag)", lhs.to_lean(), rhs.to_lean())
                }
            }
            SymExpr::Unary { desc } => desc.clone(),
            SymExpr::Ite {
                cond,
                then_val,
                else_val,
                ..
            } => format!("(if {cond} then {} else {})", then_val.to_lean(), else_val.to_lean()),
        }
    }
}

// ---------------------------------------------------------------------------
// 4. Flag State (`FlagState`) & Condition Representation (`SymCond`)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FlagState {
    /// Entry / unknown processor flags (`ctx.nzcv` under concrete evaluation).
    #[default]
    Unknown,
    /// Concrete 4-bit `NZCV` flags.
    Literal(Nzcv),
    /// Flags set by `SUBS` / `CMP` (`lhs - rhs` at `width` bits).
    Cmp {
        width: u32,
        lhs: SymExpr,
        rhs: SymExpr,
    },
    /// Flags set by `ADDS` / `CMN` (`lhs + rhs` at `width` bits).
    Cmn {
        width: u32,
        lhs: SymExpr,
        rhs: SymExpr,
    },
    /// Flags set by `ANDS` / `BICS` / `TST` (`lhs &&& rhs` at `width` bits).
    Tst {
        width: u32,
        res: SymExpr,
    },
    /// Flags set by `ADCS` / `SBCS` (`AddWithCarry(lhs, rhs, carry_in.c)` at `width` bits).
    AdcSbc {
        is_sub: bool,
        width: u32,
        lhs: SymExpr,
        rhs: SymExpr,
        carry_in: Box<FlagState>,
    },
    /// Flags set by `CCMP` / `CCMN` (`if cond(prev_flags) then AddWithCarry(lhs, rhs) else nzcv_imm`).
    Ccmp {
        is_sub: bool,
        width: u32,
        lhs: SymExpr,
        rhs: SymExpr,
        cond_bits: u8,
        nzcv_imm: u8,
        prev_flags: Box<FlagState>,
    },
}

impl FlagState {
    /// Evaluate `self` to concrete [`Nzcv`] flags under `ctx`.
    pub fn eval_nzcv(&self, ctx: &ConcreteContext) -> Nzcv {
        self.eval_nzcv_with_vars(ctx, &BTreeMap::new())
    }

    /// Evaluate `self` to concrete [`Nzcv`] flags under `ctx` and `let`-bound `vars`.
    pub fn eval_nzcv_with_vars(&self, ctx: &ConcreteContext, vars: &BTreeMap<String, u64>) -> Nzcv {
        match self {
            FlagState::Unknown => ctx.nzcv,
            FlagState::Literal(nzcv) => *nzcv,
            FlagState::Cmp { width, lhs, rhs } => {
                eval_add_sub_with_carry(
                    *width,
                    true,
                    lhs.eval_with_vars(ctx, vars),
                    rhs.eval_with_vars(ctx, vars),
                    true,
                )
                .1
            }
            FlagState::Cmn { width, lhs, rhs } => {
                eval_add_sub_with_carry(
                    *width,
                    false,
                    lhs.eval_with_vars(ctx, vars),
                    rhs.eval_with_vars(ctx, vars),
                    false,
                )
                .1
            }
            FlagState::Tst { width, res } => {
                let v = res.eval_with_vars(ctx, vars);
                if *width == 32 {
                    let v32 = v as u32;
                    Nzcv {
                        n: (v32 >> 31) != 0,
                        z: v32 == 0,
                        c: false,
                        v: false,
                    }
                } else {
                    Nzcv {
                        n: (v >> 63) != 0,
                        z: v == 0,
                        c: false,
                        v: false,
                    }
                }
            }
            FlagState::AdcSbc {
                is_sub,
                width,
                lhs,
                rhs,
                carry_in,
            } => {
                let c = carry_in.eval_nzcv_with_vars(ctx, vars).c;
                eval_add_sub_with_carry(
                    *width,
                    *is_sub,
                    lhs.eval_with_vars(ctx, vars),
                    rhs.eval_with_vars(ctx, vars),
                    c,
                )
                .1
            }
            FlagState::Ccmp {
                is_sub,
                width,
                lhs,
                rhs,
                cond_bits,
                nzcv_imm,
                prev_flags,
            } => {
                let prev = prev_flags.eval_nzcv_with_vars(ctx, vars);
                if condition_holds(*cond_bits, prev) {
                    eval_add_sub_with_carry(
                        *width,
                        *is_sub,
                        lhs.eval_with_vars(ctx, vars),
                        rhs.eval_with_vars(ctx, vars),
                        *is_sub,
                    )
                    .1
                } else {
                    Nzcv::from_u8(*nzcv_imm)
                }
            }
        }
    }

    /// Try to evaluate `self` to constant `Nzcv` when all inputs are `SymExpr::Const`.
    pub fn try_eval_const(&self) -> Option<Nzcv> {
        match self {
            FlagState::Unknown => None,
            FlagState::Literal(nzcv) => Some(*nzcv),
            FlagState::Cmp {
                width,
                lhs: SymExpr::Const(l),
                rhs: SymExpr::Const(r),
            } => Some(eval_add_sub_with_carry(*width, true, *l, *r, true).1),
            FlagState::Cmn {
                width,
                lhs: SymExpr::Const(l),
                rhs: SymExpr::Const(r),
            } => Some(eval_add_sub_with_carry(*width, false, *l, *r, false).1),
            FlagState::Tst {
                width,
                res: SymExpr::Const(v),
            } => {
                if *width == 32 {
                    let v32 = *v as u32;
                    Some(Nzcv {
                        n: (v32 >> 31) != 0,
                        z: v32 == 0,
                        c: false,
                        v: false,
                    })
                } else {
                    Some(Nzcv {
                        n: (*v >> 63) != 0,
                        z: *v == 0,
                        c: false,
                        v: false,
                    })
                }
            }
            FlagState::AdcSbc {
                is_sub,
                width,
                lhs: SymExpr::Const(l),
                rhs: SymExpr::Const(r),
                carry_in,
            } => {
                let c = carry_in.try_eval_const()?.c;
                Some(eval_add_sub_with_carry(*width, *is_sub, *l, *r, c).1)
            }
            FlagState::Ccmp {
                is_sub,
                width,
                lhs,
                rhs,
                cond_bits,
                nzcv_imm,
                prev_flags,
            } => {
                let prev = prev_flags.try_eval_const()?;
                if condition_holds(*cond_bits, prev) {
                    if let (SymExpr::Const(l), SymExpr::Const(r)) = (lhs, rhs) {
                        Some(eval_add_sub_with_carry(*width, *is_sub, *l, *r, *is_sub).1)
                    } else {
                        None
                    }
                } else {
                    Some(Nzcv::from_u8(*nzcv_imm))
                }
            }
            _ => None,
        }
    }
}

/// Structured symbolic branch / select condition.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SymCond {
    /// Condition code `cond_bits` (`0..15`) evaluated against processor `flags`.
    FlagCond {
        cond_bits: u8,
        flags: FlagState,
    },
    /// `CBZ` (`is_nz = false`) or `CBNZ` (`is_nz = true`) on `val` at `width` (32 or 64).
    Cbz {
        is_nz: bool,
        width: u32,
        val: SymExpr,
    },
    /// `TBZ` (`is_nz = false`) or `TBNZ` (`is_nz = true`) on bit `bit_pos` of `val`.
    Tbz {
        is_nz: bool,
        bit_pos: u32,
        val: SymExpr,
    },
}

impl SymCond {
    /// Evaluate `self` to a concrete `bool` under `ctx`.
    pub fn eval(&self, ctx: &ConcreteContext) -> bool {
        self.eval_with_vars(ctx, &BTreeMap::new())
    }

    /// Evaluate `self` to a concrete `bool` under `ctx` and `let`-bound `vars`.
    pub fn eval_with_vars(&self, ctx: &ConcreteContext, vars: &BTreeMap<String, u64>) -> bool {
        match self {
            SymCond::FlagCond { cond_bits, flags } => {
                condition_holds(*cond_bits, flags.eval_nzcv_with_vars(ctx, vars))
            }
            SymCond::Cbz { is_nz, width, val } => {
                let v = val.eval_with_vars(ctx, vars);
                let z = if *width == 32 {
                    (v as u32) == 0
                } else {
                    v == 0
                };
                if *is_nz { !z } else { z }
            }
            SymCond::Tbz {
                is_nz,
                bit_pos,
                val,
            } => {
                let v = val.eval_with_vars(ctx, vars);
                let bit_set = ((v >> (*bit_pos & 63)) & 1) != 0;
                if *is_nz { bit_set } else { !bit_set }
            }
        }
    }

    /// Try to evaluate `self` to a constant `bool` when its inputs are constants.
    pub fn try_eval_const(&self) -> Option<bool> {
        match self {
            SymCond::FlagCond { cond_bits, flags } => {
                if *cond_bits == 14 || *cond_bits == 15 {
                    return Some(true);
                }
                let nzcv = flags.try_eval_const()?;
                Some(condition_holds(*cond_bits, nzcv))
            }
            SymCond::Cbz {
                is_nz,
                width,
                val: SymExpr::Const(v),
            } => {
                let z = if *width == 32 {
                    (*v as u32) == 0
                } else {
                    *v == 0
                };
                Some(if *is_nz { !z } else { z })
            }
            SymCond::Tbz {
                is_nz,
                bit_pos,
                val: SymExpr::Const(v),
            } => {
                let bit_set = ((*v >> (*bit_pos & 63)) & 1) != 0;
                Some(if *is_nz { bit_set } else { !bit_set })
            }
            _ => None,
        }
    }

    /// Render `self` in Lean 4 `ProofLib` syntax.
    pub fn to_lean(&self) -> String {
        match self {
            SymCond::FlagCond { cond_bits, flags } => render_cond(*cond_bits, flags),
            SymCond::Cbz { is_nz, width, val } => {
                let operand = fmt_operand_for_width(val, *width);
                if *is_nz {
                    format!("(!({operand} == 0#{width}))")
                } else {
                    format!("({operand} == 0#{width})")
                }
            }
            SymCond::Tbz {
                is_nz,
                bit_pos,
                val,
            } => {
                if *is_nz {
                    format!("(BitVec.extractLsb' {bit_pos} 1 {} == 1#1)", val.to_lean())
                } else {
                    format!("(BitVec.extractLsb' {bit_pos} 1 {} == 0#1)", val.to_lean())
                }
            }
        }
    }
}

pub fn fmt_operand_for_width(e: &SymExpr, width: u32) -> String {
    if width == 32 {
        match e {
            SymExpr::Const(c) => format!("0x{:x}#32", *c as u32),
            SymExpr::ZeroExt { width: 32, inner } => {
                format!("(BitVec.truncate 32 {})", inner.to_lean())
            }
            other => format!("(BitVec.truncate 32 {})", other.to_lean()),
        }
    } else {
        e.to_lean()
    }
}

/// Render an AArch64 condition code `cond_bits` (0..15) against `flags` into Lean `ProofLib` syntax.
pub fn render_cond(cond_bits: u8, flags: &FlagState) -> String {
    let cond_names = [
        "EQ", "NE", "CS", "CC", "MI", "PL", "VS", "VC", "HI", "LS", "GE", "LT", "GT", "LE", "AL",
        "NV",
    ];
    let cname = cond_names.get(cond_bits as usize).copied().unwrap_or("AL");
    match flags {
        FlagState::Cmp { width, lhs, rhs } => {
            let l = fmt_operand_for_width(lhs, *width);
            let r = fmt_operand_for_width(rhs, *width);
            match cond_bits {
                0x0 => format!("({l} == {r})"),            // EQ: Z == 1
                0x1 => format!("(!({l} == {r}))"),         // NE: Z == 0
                0x2 => format!("({r} ≤ᵤ {l})"),            // CS/HS: lhs >=_u rhs
                0x3 => format!("({l} <ᵤ {r})"),            // CC/LO: lhs <_u rhs
                0x4 => format!("(BitVec.slt {l} {r})"),    // MI (approx after cmp)
                0x5 => format!("(!(BitVec.slt {l} {r}))"), // PL
                0x8 => format!("({r} <ᵤ {l})"),            // HI: lhs >_u rhs (i.e. rhs < lhs)
                0x9 => format!("({l} ≤ᵤ {r})"),            // LS: lhs <=_u rhs
                0xa => format!("(!(BitVec.slt {l} {r}))"), // GE: lhs >=_s rhs
                0xb => format!("(BitVec.slt {l} {r})"),    // LT: lhs <_s rhs
                0xc => format!("(BitVec.slt {r} {l})"),    // GT: lhs >_s rhs (i.e. rhs <_s lhs)
                0xd => format!("(!(BitVec.slt {r} {l}))"), // LE: lhs <=_s rhs
                _ => format!("cond_{cname}"),
            }
        }
        FlagState::Cmn { width, lhs, rhs } => {
            let l = fmt_operand_for_width(lhs, *width);
            let r = fmt_operand_for_width(rhs, *width);
            match cond_bits {
                0x0 => format!("(({l} + {r}) == 0#{width})"),
                0x1 => format!("(!(({l} + {r}) == 0#{width}))"),
                _ => format!("cond_{cname}({l} + {r})"),
            }
        }
        FlagState::Tst { width, res } => {
            let v = fmt_operand_for_width(res, *width);
            match cond_bits {
                0x0 => format!("({v} == 0#{width})"),
                0x1 => format!("(!({v} == 0#{width}))"),
                _ => format!("cond_{cname}({v})"),
            }
        }
        FlagState::Literal(nzcv) => {
            if condition_holds(cond_bits, *nzcv) {
                "true".to_string()
            } else {
                "false".to_string()
            }
        }
        FlagState::AdcSbc { .. } | FlagState::Ccmp { .. } | FlagState::Unknown => {
            format!("cond_{cname}")
        }
    }
}

pub fn negate_cond_str(c: &str) -> String {
    if let Some(inner) = c.strip_prefix("(!").and_then(|s| s.strip_suffix(')')) {
        inner.to_string()
    } else {
        format!("(!{c})")
    }
}
