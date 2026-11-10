// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Per-Path Block-Hint Certificates for `symexec --block-hints` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (untrusted advice only; a Lean tactic re-checks every step,
//!   so a wrong hint can only make a proof search fail or fall back, never prove a false goal).
//! - **Purpose:** Records, for each explored symbolic path, a compact line-oriented hint stream
//!   telling a Lean stepping tactic what each instruction does (pure, load/store at an
//!   entry-state root + constant, conditional branch direction, call/return) so it can pick the
//!   right step lemma and memory-cell frame without searching.
//!
//! # Text Format (version 1)
//! ```text
//! # symexec-block-hints v1
//! path <i> fn <symbol-or-0xFNOFF> entry 0x<fn-relative start offset>
//! 0x<off> auto                                   pure instruction (ALU, mov, adrp, cmp, b, ...)
//! 0x<off> load  <addr>:<bytes>                   single load
//! 0x<off> store <addr>:<bytes>                   single store
//! 0x<off> load2 <addr1>:<bytes> <addr2>:<bytes>  load pair
//! 0x<off> store2 <addr1>:<bytes> <addr2>:<bytes> store pair
//! 0x<off> unknown                                other memory shape (atomics, ...): search
//! 0x<off> br taken|fallthrough cond <cond>       <cond> holds on this path
//! 0x<off> end call 0x<image-off>|?               BL/BLR: ends a block, path continues after it
//! 0x<off> end ret | end tailcall 0x<image-off>|? path terminator executed at <off>
//! 0x<off> end stop                               path cut before executing <off>
//! ```
//! `<off>` is function-relative; call/tail-call targets are image-relative. `<addr>` is
//! `<root><+|->0x<OFF>` with `<root>` one of `sp0` (entry `sp`), `x<N>` (entry `x<N>`), or
//! `g:base` (PC-relative/ADRP address as an image-relative offset, assuming a page-aligned image
//! base), or `?` when the effective address is not an entry root plus a constant.
//!
//! # Key Types & Functions
//! - [`HintAddr`], [`HintStep`], [`HintLine`], [`PathHints`], [`BlockHintsReport`]: schema
//!   (also serialized by `--block-hints-json`).
//! - [`resolve_addr`], [`classify_straight_line`]: build hints from executor records.
//! - [`format_block_hints_text`]: renders the version-1 text stream.
//!
//! # When to Read This File
//! - Read this file when changing the block-hint format; path exploration lives in `driver.rs`.

use serde::Serialize;

use crate::untrusted_lemmas::{extract, sign_extend};

use super::expr::SymExpr;
use super::state::{CallSiteRecord, MemAccessRecord};

/// First line of every version-1 text certificate.
pub const BLOCK_HINTS_HEADER: &str = "# symexec-block-hints v1";

/// Effective address of one memory access, as an entry-state root plus a signed constant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HintAddr {
    /// `sp0`, `x<N>`, or `g:base`; `None` when the address is not of the form root + constant.
    pub root: Option<String>,
    pub offset: i64,
    pub bytes: u64,
}

impl HintAddr {
    pub fn render(&self) -> String {
        match &self.root {
            Some(root) => format!("{root}{}:{}", fmt_signed_hex(self.offset), self.bytes),
            None => format!("?:{}", self.bytes),
        }
    }
}

/// What a single hint line says about the instruction at [`HintLine::offset`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HintStep {
    Auto,
    Load {
        addr: HintAddr,
    },
    Store {
        addr: HintAddr,
    },
    Load2 {
        addr1: HintAddr,
        addr2: HintAddr,
    },
    Store2 {
        addr1: HintAddr,
        addr2: HintAddr,
    },
    Unknown,
    /// Conditional branch; `cond` is the condition that holds along this path.
    Br {
        taken: bool,
        cond: String,
    },
    /// `BL` / `BLR`: ends a basic block; the path continues at the return address.
    Call {
        target: Option<u64>,
        callee: Option<String>,
    },
    Ret,
    Tailcall {
        target: Option<u64>,
        callee: Option<String>,
    },
    /// Path cut before executing the instruction at the line's offset.
    Stop {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HintLine {
    /// Function-relative instruction offset.
    pub offset: u64,
    #[serde(flatten)]
    pub step: HintStep,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PathHints {
    pub index: usize,
    /// Same label as the matching `PathSnapshot` (`ret_0x..`, `cut_0x..`, ...).
    pub label: String,
    /// Function-relative start offset (`--from`).
    pub entry: u64,
    pub lines: Vec<HintLine>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BlockHintsReport {
    pub version: u32,
    pub symbol: String,
    pub fn_offset: u64,
    pub paths: Vec<PathHints>,
}

fn fmt_signed_hex(v: i64) -> String {
    if v < 0 {
        format!("-0x{:x}", v.unsigned_abs())
    } else {
        format!("+0x{v:x}")
    }
}

/// Image-relative address denoted by a PC-relative expression in a function at `fn_offset`.
fn pcrel_image_off(fn_offset: u64, pc_off: u64, offset: i64, is_page: bool) -> u64 {
    let pc = fn_offset.wrapping_add(pc_off);
    let base = if is_page { pc & !0xfff } else { pc };
    base.wrapping_add(offset as u64)
}

/// Resolve `addr` to an entry-state `(root, offset)` pair, if it is a root plus a constant.
pub fn resolve_addr(addr: &SymExpr, fn_offset: u64) -> Option<(String, i64)> {
    let (inner, k) = match addr {
        SymExpr::AddConst(base, c) => (&**base, *c),
        other => (other, 0u64),
    };
    match inner {
        SymExpr::InitReg(31) => Some(("sp0".to_string(), k as i64)),
        SymExpr::InitReg(r) if *r < 31 => Some((format!("x{r}"), k as i64)),
        SymExpr::PcRel {
            pc_off,
            offset,
            is_page,
        } => {
            let img = pcrel_image_off(fn_offset, *pc_off, *offset, *is_page).wrapping_add(k);
            Some(("g:base".to_string(), img as i64))
        }
        _ => None,
    }
}

fn hint_addr(acc: &MemAccessRecord, fn_offset: u64) -> HintAddr {
    let bytes = u64::from(acc.width_bits / 8);
    match resolve_addr(&acc.addr_expr, fn_offset) {
        Some((root, offset)) => HintAddr {
            root: Some(root),
            offset,
            bytes,
        },
        None => HintAddr {
            root: None,
            offset: 0,
            bytes,
        },
    }
}

/// Image-relative target of a PC-relative branch target expression, if known.
pub fn branch_target_image_off(target: Option<&SymExpr>, fn_offset: u64) -> Option<u64> {
    match target? {
        SymExpr::PcRel {
            pc_off,
            offset,
            is_page,
        } => Some(pcrel_image_off(fn_offset, *pc_off, *offset, *is_page)),
        _ => None,
    }
}

/// Hint for an instruction that stepped straight-line (`StepOutcome::Next`), given the memory
/// accesses and call sites it recorded.
pub fn classify_straight_line(
    word: u32,
    pc: u64,
    fn_offset: u64,
    accesses: &[MemAccessRecord],
    calls: &[CallSiteRecord],
) -> HintStep {
    if (word & 0xfc00_0000) == 0x9400_0000 {
        // BL imm26
        let disp = (sign_extend(extract(word, 0, 26), 26) << 2) as i64;
        let target = fn_offset.wrapping_add((pc as i64).wrapping_add(disp) as u64);
        return HintStep::Call {
            target: Some(target),
            callee: calls.first().map(|c| c.callee.clone()),
        };
    }
    if (word & 0xffff_fc1f) == 0xd63f_0000 {
        // BLR Xn
        return HintStep::Call {
            target: None,
            callee: None,
        };
    }
    match accesses {
        [] => HintStep::Auto,
        [a] if a.is_store => HintStep::Store {
            addr: hint_addr(a, fn_offset),
        },
        [a] => HintStep::Load {
            addr: hint_addr(a, fn_offset),
        },
        [a, b] if a.is_store && b.is_store => HintStep::Store2 {
            addr1: hint_addr(a, fn_offset),
            addr2: hint_addr(b, fn_offset),
        },
        [a, b] if !a.is_store && !b.is_store => HintStep::Load2 {
            addr1: hint_addr(a, fn_offset),
            addr2: hint_addr(b, fn_offset),
        },
        _ => HintStep::Unknown,
    }
}

fn fmt_target(t: Option<u64>) -> String {
    t.map(|t| format!("0x{t:x}"))
        .unwrap_or_else(|| "?".to_string())
}

fn render_step(step: &HintStep) -> String {
    match step {
        HintStep::Auto => "auto".to_string(),
        HintStep::Load { addr } => format!("load {}", addr.render()),
        HintStep::Store { addr } => format!("store {}", addr.render()),
        HintStep::Load2 { addr1, addr2 } => format!("load2 {} {}", addr1.render(), addr2.render()),
        HintStep::Store2 { addr1, addr2 } => {
            format!("store2 {} {}", addr1.render(), addr2.render())
        }
        HintStep::Unknown => "unknown".to_string(),
        HintStep::Br { taken, cond } => {
            let dir = if *taken { "taken" } else { "fallthrough" };
            if cond.is_empty() {
                format!("br {dir}")
            } else {
                format!("br {dir} cond {cond}")
            }
        }
        HintStep::Call { target, .. } => format!("end call {}", fmt_target(*target)),
        HintStep::Ret => "end ret".to_string(),
        HintStep::Tailcall { target, .. } => format!("end tailcall {}", fmt_target(*target)),
        HintStep::Stop { .. } => "end stop".to_string(),
    }
}

/// Render `r` in the version-1 line-oriented text format.
pub fn format_block_hints_text(r: &BlockHintsReport) -> String {
    let fn_name =
        if r.symbol.is_empty() || r.symbol == "<hex>" || r.symbol.contains(char::is_whitespace) {
            format!("0x{:x}", r.fn_offset)
        } else {
            r.symbol.clone()
        };
    let mut out = String::new();
    out.push_str(BLOCK_HINTS_HEADER);
    out.push('\n');
    for p in &r.paths {
        out.push_str(&format!(
            "path {} fn {fn_name} entry 0x{:x}\n",
            p.index, p.entry
        ));
        for l in &p.lines {
            out.push_str(&format!("0x{:x} {}\n", l.offset, render_step(&l.step)));
        }
    }
    out
}
