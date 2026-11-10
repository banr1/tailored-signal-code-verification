// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Symbolic Machine State (`SymState`), Memory Slot Tracking, and Concrete State Evaluation
//! (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (in-memory symbolic architectural state for `symexec`).
//! - **Purpose:** Tracks the 31 general-purpose registers (`x0..x30`), `sp`, `NZCV` flags,
//!   `tpidr_el0`, base+offset symbolic memory slots (`sp`/`xN`-relative), byte-level store log
//!   (`mem_writes`), and path execution trace (`path_branches`, `mem_accesses`, `call_sites`).
//!
//! # Key Types & Functions
//! - [`SymState`]: Symbolic machine state with `get_reg`, `set_reg`, `read_mem`, `write_mem`,
//!   and `eval_concrete`.
//! - [`MemAccessRecord`], [`CallSiteRecord`], [`BranchRecord`]: Per-path trace records.
//! - [`ConcreteMachineState`]: Concrete state snapshot produced by [`SymState::eval_concrete`].
//!
//! # When to Read This File
//! - Read this file when modifying how `symexec` resolves `(base, offset)` memory aliases,
//!   records store/load footprints, or initializes symbolic registers.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use super::expr::{ConcreteContext, FlagState, Nzcv, SymExpr, SymMemWrite};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MemAccessRecord {
    pub insn_offset: u64,
    pub insn_offset_hex: String,
    pub is_store: bool,
    pub base: String,
    pub offset: i64,
    pub addr_lean: String,
    pub width_bits: u32,
    pub points_to_op: &'static str,
    pub value_lean: String,
    /// Structured effective address actually accessed (after pre/post-index resolution).
    #[serde(skip)]
    pub addr_expr: SymExpr,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CallSiteRecord {
    pub call_offset: u64,
    pub call_offset_hex: String,
    pub callee: String,
    pub is_tail_call: bool,
    pub is_extern: bool,
    pub args: BTreeMap<String, String>,
    pub sp_lean: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BranchRecord {
    pub insn_offset: u64,
    pub insn_offset_hex: String,
    pub mnemonic: String,
    pub cond_lean: String,
    pub taken_offset: u64,
    pub taken_offset_hex: String,
    pub fallthrough_offset: u64,
    pub fallthrough_offset_hex: String,
    pub is_back_edge: bool,
}

/// Concrete architectural state produced by evaluating a [`SymState`] on a [`ConcreteContext`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteMachineState {
    /// General-purpose registers `X0..X30` (`regs[0..31]`) and `SP` (`regs[31]`).
    pub regs: [u64; 32],
    /// Architectural program counter (`ctx.base_pc + state.pc_off`).
    pub pc: u64,
    /// Architectural `NZCV` flags.
    pub nzcv: Nzcv,
    /// `TPIDR_EL0` system register value.
    pub tpidr_el0: u64,
    /// Byte-addressable memory after applying all stores in [`SymState::mem_writes`].
    pub mem: BTreeMap<u64, u8>,
}

impl ConcreteMachineState {
    /// Read a little-endian word of `num_bytes` (1..=8) from `self.mem` (unmapped bytes read as 0).
    pub fn read_le(&self, addr: u64, num_bytes: usize) -> u64 {
        let mut buf = [0u8; 8];
        for (i, slot) in buf.iter_mut().enumerate().take(num_bytes.min(8)) {
            *slot = self.mem.get(&addr.wrapping_add(i as u64)).copied().unwrap_or(0);
        }
        u64::from_le_bytes(buf)
    }
}

/// AST node threshold at which `write_gpr_zr` emits an intermediate `let r{reg}_step{n} := ...`
/// checkpoint binding to prevent exponential $O(2^N)$ inline-substitution blowup on ARX/crypto loops.
pub const LET_BINDING_NODE_THRESHOLD: usize = 32;

/// Default maximum AST node count allowed in a single symbolic expression (`--max-expr-nodes`).
pub const DEFAULT_MAX_EXPR_NODES: usize = 5000;

#[derive(Clone, Debug)]
pub struct SymState {
    pub pc_off: u64,
    pub regs: [SymExpr; 32],
    pub flags: FlagState,
    pub tpidr_el0: SymExpr,
    /// Symbolic memory keyed by `(base_lean, byte_offset)` -> `(width_bits, SymExpr)`.
    pub mem: BTreeMap<(String, i64), (u32, SymExpr)>,
    /// Ordered store log for exact byte-level concrete evaluation and sub-word aliasing.
    pub mem_writes: Vec<SymMemWrite>,
    /// Ordered intermediate `let` checkpoint bindings `(var_name, expr)` emitted when a register's
    /// symbolic AST exceeds [`LET_BINDING_NODE_THRESHOLD`].
    pub bindings: Vec<(String, SymExpr)>,
    /// Maximum AST nodes permitted per expression before truncation (`0` disables limit).
    pub max_expr_nodes: usize,
    /// Set to `true` if any expression on this path exceeded `max_expr_nodes`.
    pub exceeded_max_expr_nodes: bool,
    pub path_conds: Vec<String>,
    pub visited_pcs: BTreeSet<u64>,
    pub steps: usize,
}

impl SymState {
    pub fn new(start_off: u64) -> Self {
        let regs = std::array::from_fn(|i| SymExpr::InitReg(i as u8));
        Self {
            pc_off: start_off,
            regs,
            flags: FlagState::Unknown,
            tpidr_el0: SymExpr::InitReg(32),
            mem: BTreeMap::new(),
            mem_writes: Vec::new(),
            bindings: Vec::new(),
            max_expr_nodes: DEFAULT_MAX_EXPR_NODES,
            exceeded_max_expr_nodes: false,
            path_conds: Vec::new(),
            visited_pcs: BTreeSet::new(),
            steps: 0,
        }
    }

    fn alloc_let_name(&self, reg_idx: u64) -> String {
        let step = if self.steps == 0 {
            self.bindings.len() + 1
        } else {
            self.steps
        };
        let base = format!("r{reg_idx}_step{step}");
        if !self.bindings.iter().any(|(k, _)| k == &base) {
            return base;
        }
        let mut suffix = 2usize;
        loop {
            let cand = format!("{base}_{suffix}");
            if !self.bindings.iter().any(|(k, _)| k == &cand) {
                return cand;
            }
            suffix += 1;
        }
    }

    pub fn read_gpr_zr(&self, idx: u64, is_64: bool) -> SymExpr {
        if idx >= 31 {
            SymExpr::Const(0)
        } else {
            let v = self.regs[idx as usize].clone();
            if is_64 { v } else { v.zero_ext(32) }
        }
    }

    pub fn read_gpr_sp(&self, idx: u64, is_64: bool) -> SymExpr {
        let v = self.regs[(idx & 31) as usize].clone();
        if is_64 { v } else { v.zero_ext(32) }
    }

    pub fn write_gpr_zr(&mut self, idx: u64, is_64: bool, val: SymExpr) {
        if idx < 31 {
            let v = if is_64 { val } else { val.zero_ext(32) };
            let nodes = v.node_count();
            if self.max_expr_nodes > 0 && nodes > self.max_expr_nodes {
                self.exceeded_max_expr_nodes = true;
                let var_name = self.alloc_let_name(idx);
                self.bindings.push((
                    var_name.clone(),
                    SymExpr::Unary {
                        desc: format!(
                            "/* truncated ({nodes} AST nodes > max_expr_nodes={}) */",
                            self.max_expr_nodes
                        ),
                    },
                ));
                self.regs[idx as usize] = SymExpr::Var(var_name);
            } else if nodes > LET_BINDING_NODE_THRESHOLD {
                let var_name = self.alloc_let_name(idx);
                self.bindings.push((var_name.clone(), v));
                self.regs[idx as usize] = SymExpr::Var(var_name);
            } else {
                self.regs[idx as usize] = v;
            }
        }
    }

    pub fn write_gpr_sp(&mut self, idx: u64, is_64: bool, val: SymExpr) {
        let r = idx & 31;
        if r < 31 {
            self.write_gpr_zr(r, is_64, val);
        } else {
            self.regs[31] = if is_64 { val } else { val.zero_ext(32) };
        }
    }

    pub fn store_mem(
        &mut self,
        insn_off: u64,
        addr: &SymExpr,
        width_bits: u32,
        val: SymExpr,
        accesses: &mut Vec<MemAccessRecord>,
    ) {
        let (base, offset) = addr.as_base_offset();
        let stored = if width_bits < 64 {
            val.zero_ext(width_bits)
        } else {
            val
        };
        let points_to_op = match width_bits {
            8 => "↦₈",
            16 => "↦₁₆",
            32 => "↦₃₂",
            _ => "↦₆₄",
        };
        accesses.push(MemAccessRecord {
            insn_offset: insn_off,
            insn_offset_hex: format!("0x{insn_off:x}"),
            is_store: true,
            base: base.clone(),
            offset,
            addr_lean: addr.to_lean(),
            width_bits,
            points_to_op,
            value_lean: stored.to_lean(),
            addr_expr: addr.clone(),
        });

        // Invalidate any partially-overlapping entry on the same symbolic base so subsequent
        // sub-word or super-word loads fall back to byte-exact `prior_writes` replay.
        let new_end = offset + (width_bits as i64 / 8);
        self.mem.retain(|(b, old_off), (old_w, _)| {
            if b != &base {
                return true;
            }
            if *old_off == offset && *old_w == width_bits {
                return true;
            }
            let old_end = *old_off + (*old_w as i64 / 8);
            old_end <= offset || new_end <= *old_off
        });

        self.mem
            .insert((base, offset), (width_bits, stored.clone()));
        self.mem_writes.push(SymMemWrite {
            addr: Box::new(addr.clone()),
            width_bits,
            val: Box::new(stored),
        });
    }

    pub fn load_mem(
        &self,
        insn_off: u64,
        addr: &SymExpr,
        width_bits: u32,
        signed_to: Option<u32>,
        accesses: &mut Vec<MemAccessRecord>,
    ) -> SymExpr {
        let (base, offset) = addr.as_base_offset();
        // Forward from `self.mem` only when an exact `(base, offset, width_bits)` match exists
        // and all stores in `mem_writes` share the same symbolic base (so no store via another
        // register base could have aliased it).
        let same_base_only = self
            .mem_writes
            .iter()
            .all(|w| w.addr.as_base_offset().0 == base);
        let raw = if same_base_only
            && let Some((w, existing)) = self.mem.get(&(base.clone(), offset))
            && *w == width_bits
        {
            existing.clone()
        } else {
            SymExpr::InitMem {
                base: base.clone(),
                offset,
                width_bits,
                addr: Some(Box::new(addr.clone())),
                prior_writes: self.mem_writes.clone(),
            }
        };
        let points_to_op = match width_bits {
            8 => "↦₈",
            16 => "↦₁₆",
            32 => "↦₃₂",
            _ => "↦₆₄",
        };
        accesses.push(MemAccessRecord {
            insn_offset: insn_off,
            insn_offset_hex: format!("0x{insn_off:x}"),
            is_store: false,
            base,
            offset,
            addr_lean: addr.to_lean(),
            width_bits,
            points_to_op,
            value_lean: raw.to_lean(),
            addr_expr: addr.clone(),
        });
        if let Some(_sign_target) = signed_to {
            raw.sign_ext(width_bits)
        } else if width_bits < 64 {
            raw.zero_ext(width_bits)
        } else {
            raw
        }
    }

    /// Evaluate all intermediate `let` checkpoint bindings in order on `ctx`.
    pub fn eval_vars(&self, ctx: &ConcreteContext) -> BTreeMap<String, u64> {
        let mut vars = BTreeMap::new();
        for (name, expr) in &self.bindings {
            let val = expr.eval_with_vars(ctx, &vars);
            vars.insert(name.clone(), val);
        }
        vars
    }

    /// Evaluate the entire symbolic machine state `(regs, sp, pc, nzcv, tpidr_el0, mem)` on a
    /// concrete initial state `ctx`.
    pub fn eval_concrete(&self, ctx: &ConcreteContext) -> ConcreteMachineState {
        let vars = self.eval_vars(ctx);
        let regs = std::array::from_fn(|i| self.regs[i].eval_with_vars(ctx, &vars));
        let pc = ctx.base_pc.wrapping_add(self.pc_off);
        let nzcv = self.flags.eval_nzcv_with_vars(ctx, &vars);
        let tpidr_el0 = self.tpidr_el0.eval_with_vars(ctx, &vars);
        let mut mem = ctx.mem.clone();
        for w in &self.mem_writes {
            let ea = w.addr.eval_with_vars(ctx, &vars);
            let val = w.val.eval_with_vars(ctx, &vars);
            let num_bytes = (w.width_bits / 8) as u64;
            for i in 0..num_bytes {
                let b = ((val >> (i * 8)) & 0xff) as u8;
                mem.insert(ea.wrapping_add(i), b);
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
}
