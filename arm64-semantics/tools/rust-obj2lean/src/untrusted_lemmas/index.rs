// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Untrusted Symbol Index, Callee Extractor, and Prologue Frame-Size Inference (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (produces `<ObjName>Index.json` / `<Target>Index.json`
//!   sidecars for host tools and `FuncTableEntry` metadata whose Lean lemmas are kernel-checked
//!   against `Arm64.Obj.funcTable` and `inferPrologueFrameBytes?`).
//! - **Purpose:** Computes per-function metadata from extracted [`ObjObject`]s and [`LinkedImage`]:
//!   - Symbol name, canonical byte offset, and byte/instruction sizes,
//!   - Generated `fnOff`, `fnSize`, `frameBytes`, and `decode_prefix` lemma identifiers,
//!   - Direct callees and call-site offsets (`CALL26` / `JUMP26` relocations and direct branches,
//!     distinguishing tail calls and extern stubs),
//!   - Prologue stack frame size (`sub sp, sp, #n`, pre-indexed `stp`/`str ..., [sp, #-n]!`).
//!
//! # Key Types & Functions
//! - [`TargetSymbolIndex`], [`FunctionIndexEntry`], [`CalleeInfo`], [`StubIndexEntry`]: JSON
//!   schema (re-exported from [`super::index_schema`]).
//! - [`SpEffect`], [`PrologueFrameInfo`], [`infer_prologue_frame`]: Prologue stack analysis.
//! - [`FuncTableEntry`], [`build_func_table`], [`build_target_index`], [`build_code_index`]:
//!   Index builders for `Code.lean` and `*Index.json`.
//!
//! # When to Read This File
//! - Read this file when modifying the `*Index.json` schema, callee discovery, or prologue stack
//!   frame inference (keep in sync with `inferPrologueFrameBytes?` in `ProofLib/PrologueFrame.lean`).

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use anyhow::Result;

use super::code::{FuncRange, ordered_symbols, selected_function_symbols, text_end_offset};
use crate::trusted_common::{ObjObject, RelocType, SecKind, SymKind};
use crate::untrusted_legacy_linker::LinkedImage;
use crate::untrusted_driver::{ExportConfig, ExportTarget};

type Canonical = LinkedImage;

// ---------------------------------------------------------------------------
// 1. Prologue Stack Frame Inference
// ---------------------------------------------------------------------------

/// Effect of a single 32-bit AArch64 instruction on `SP`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpEffect {
    /// Does not modify `SP`.
    None,
    /// Subtracts a positive constant `delta` bytes from `SP` (`sub sp, sp, #delta`,
    /// pre-indexed `stp ..., [sp, #-delta]!`, or pre-indexed `str ..., [sp, #-delta]!`).
    Alloc(u64),
    /// Adds a constant `delta` bytes to `SP` (`add sp, sp, #delta`, post-indexed
    /// `ldp ..., [sp], #delta`, post-indexed `ldr ..., [sp], #delta`, or `mov sp, x29`).
    Dealloc(u64),
    /// Modifies `SP` in a dynamic or unrecognized way (`sub sp, sp, xN`, `and sp, ...`, etc.).
    Unknown,
}

/// Control-flow classification of an instruction for prologue boundary detection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlowKind {
    /// Ordinary straight-line instruction.
    Normal,
    /// Call (`bl`, `blr`), return (`ret`), unconditional branch (`b`, `br`), or backward
    /// conditional branch.
    EndPrologue,
    /// Forward conditional branch (`b.cond`, `cbz`, `cbnz`, `tbz`, `tbnz`) targeting word
    /// index `target_idx > idx`.
    FwdCond(usize),
}

/// Classify how a 32-bit AArch64 instruction word `w` modifies `SP`.
///
/// Mirrors `Arm64.classifySpWord` in `ProofLib/PrologueFrame.lean`.
pub fn classify_sp_word(w: u32) -> SpEffect {
    // 1. `sub sp, sp, #imm12[, lsl #12]`: sf=1, op=1, S=0, 100010, sh, imm12, Rn=31, Rd=31
    if (w & 0xff80_03ff) == 0xd100_03ff {
        let sh = (w >> 22) & 1;
        let imm12 = ((w >> 10) & 0xfff) as u64;
        let delta = if sh == 1 { imm12 << 12 } else { imm12 };
        return if delta > 0 {
            SpEffect::Alloc(delta)
        } else {
            SpEffect::None
        };
    }
    // 2. `add sp, sp, #imm12[, lsl #12]`: sf=1, op=0, S=0, 100010, sh, imm12, Rn=31, Rd=31
    if (w & 0xff80_03ff) == 0x9100_03ff {
        let sh = (w >> 22) & 1;
        let imm12 = ((w >> 10) & 0xfff) as u64;
        let delta = if sh == 1 { imm12 << 12 } else { imm12 };
        return if delta > 0 {
            SpEffect::Dealloc(delta)
        } else {
            SpEffect::None
        };
    }
    // 3. Load/Store Pair (`stp` / `ldp`) with base `Rn = 31` (`sp`):
    //    bits 29..27 = 101, bit 25 = 0, bits 9..5 = 31.
    if (w & 0x3a00_03e0) == 0x2800_03e0 {
        let idx_mode = (w >> 23) & 3;
        if idx_mode != 0b011 && idx_mode != 0b001 {
            // Signed-offset (`0b010`) or no-allocate (`0b000`): does not write back to `sp`.
            // (`Rt`/`Rt2` = 31 in `ldp` is `xzr`/`wzr`, never `sp`.)
            return SpEffect::None;
        }
        let opc = (w >> 30) & 3;
        let v = (w >> 26) & 1;
        let l = (w >> 22) & 1;
        let imm7 = ((w >> 15) & 0x7f) as u64;
        let scale = if v == 0 {
            match opc {
                0 => Some(2u32),
                2 => Some(3u32),
                _ => None,
            }
        } else {
            match opc {
                0 => Some(2u32),
                1 => Some(3u32),
                2 => Some(4u32),
                _ => None,
            }
        };
        let Some(scale) = scale else {
            return SpEffect::Unknown;
        };
        if idx_mode == 0b011 && l == 0 && imm7 >= 64 {
            return SpEffect::Alloc((128 - imm7) << scale);
        }
        if idx_mode == 0b001 && l == 1 && imm7 > 0 && imm7 < 64 {
            return SpEffect::Dealloc(imm7 << scale);
        }
        return SpEffect::Unknown;
    }
    // 4. Load/Store Register immediate (`str` / `ldr`) with base `Rn = 31` (`sp`):
    //    bits 29..27 = 111, bits 25..24 = 00, bit 21 = 0, bits 9..5 = 31.
    if (w & 0x3b20_03e0) == 0x3800_03e0 {
        let idx_mode = (w >> 10) & 3;
        if idx_mode != 0b11 && idx_mode != 0b01 {
            return SpEffect::None;
        }
        let opc = (w >> 22) & 3;
        let imm9 = ((w >> 12) & 0x1ff) as u64;
        if idx_mode == 0b11 && opc == 0 && imm9 >= 256 {
            return SpEffect::Alloc(512 - imm9);
        }
        if idx_mode == 0b01 && opc != 0 && imm9 > 0 && imm9 < 256 {
            return SpEffect::Dealloc(imm9);
        }
        return SpEffect::Unknown;
    }
    // 5. `mov sp, x29` (`add sp, x29, #0`, encoding `0x910003bf`) in epilogues:
    if w == 0x9100_03bf {
        return SpEffect::Dealloc(0);
    }
    // 6. Other instructions writing `Rd = 31` where `Rd` denotes `SP`:
    //    - Add/Sub immediate with `S = 0` and `Rd = 31` (`Rn != 31` since `Rn = 31` was handled above)
    if (w & 0x3f00_001f) == 0x1100_001f {
        return SpEffect::Unknown;
    }
    //    - Add/Sub extended register with `S = 0` and `Rd = 31` (e.g. `sub sp, sp, x8`)
    if (w & 0x3f20_001f) == 0x0b20_001f {
        return SpEffect::Unknown;
    }
    //    - Logical immediate with `opc != 3` (`ands` writes `xzr`) and `Rd = 31` (e.g. `and sp, x9, #-16`)
    if (w & 0x1f80_001f) == 0x1200_001f && ((w >> 29) & 3) != 3 {
        return SpEffect::Unknown;
    }
    SpEffect::None
}

/// Classify the control-flow behavior of instruction word `w` at word index `idx`.
fn classify_flow_word(w: u32, idx: usize) -> FlowKind {
    // `bl` or `b`
    if (w & 0xfc00_0000) == 0x9400_0000 || (w & 0xfc00_0000) == 0x1400_0000 {
        return FlowKind::EndPrologue;
    }
    // `blr`, `br`, or `ret`
    if (w & 0xffff_fc1f) == 0xd63f_0000
        || (w & 0xffff_fc1f) == 0xd61f_0000
        || (w & 0xffff_fc1f) == 0xd65f_0000
    {
        return FlowKind::EndPrologue;
    }
    // `b.cond` or `cbz`/`cbnz` (19-bit signed word displacement in bits 23..5)
    if (w & 0xff00_0010) == 0x5400_0000 || (w & 0x7e00_0000) == 0x3400_0000 {
        let imm19 = ((w >> 5) & 0x7ffff) as usize;
        if imm19 == 0 || imm19 >= 0x40000 {
            return FlowKind::EndPrologue;
        }
        return FlowKind::FwdCond(idx + imm19);
    }
    // `tbz`/`tbnz` (14-bit signed word displacement in bits 18..5)
    if (w & 0x7e00_0000) == 0x3600_0000 {
        let imm14 = ((w >> 5) & 0x3fff) as usize;
        if imm14 == 0 || imm14 >= 0x2000 {
            return FlowKind::EndPrologue;
        }
        return FlowKind::FwdCond(idx + imm14);
    }
    FlowKind::Normal
}

#[derive(Clone, Copy, Debug)]
enum PrologueState {
    Before(Option<usize>),
    InPrologue(u64, Option<usize>),
    After(u64),
}

fn past_min_fwd(idx: usize, min_fwd: Option<usize>) -> bool {
    min_fwd.is_some_and(|t| idx >= t)
}

/// Number of 32-bit words in `code_bytes` after stripping trailing `0x0000_0000`
/// alignment padding words (keeping at least 1 word if `code_bytes` is non-empty).
/// Mirrors `trimTrailingZeroWords` in `Arm64/Trusted/Spec/SepLogic.lean`.
pub fn trimmed_word_count(code_bytes: &[u8]) -> Option<usize> {
    if code_bytes.len() % 4 != 0 {
        return None;
    }
    let mut total_words = code_bytes.len() / 4;
    while total_words > 1 {
        let i = total_words - 1;
        let w = u32::from_le_bytes(code_bytes[4 * i..4 * i + 4].try_into().unwrap());
        if w == 0 {
            total_words -= 1;
        } else {
            break;
        }
    }
    Some(total_words)
}

/// Byte length of `code_bytes` after stripping trailing 4-byte `0x0000_0000` padding words
/// (keeping at least 4 bytes when non-empty).
/// Mirrors `trimTrailingZeroBytesLen` in `Arm64/Trusted/Spec/SepLogic.lean`.
pub fn trim_trailing_zero_bytes_len(code_bytes: &[u8]) -> u64 {
    match trimmed_word_count(code_bytes) {
        Some(words) => (words * 4) as u64,
        None => code_bytes.len() as u64,
    }
}

/// Infer the downward stack frame size in bytes allocated by a function's prologue from its
/// raw code bytes (`Some(0)` for leaf functions that do not allocate a frame; `None` if the
/// function uses dynamic/non-standard `SP` adjustments or has a misaligned frame).
///
/// Mirrors `Arm64.inferPrologueFrameBytes?` in `ProofLib/PrologueFrame.lean`.
pub fn infer_prologue_frame(code_bytes: &[u8]) -> Option<u64> {
    let total_words = trimmed_word_count(code_bytes)?;
    let mut state = PrologueState::Before(None);
    for idx in 0..total_words {
        if let PrologueState::InPrologue(acc, min_fwd) = state
            && past_min_fwd(idx, min_fwd)
        {
            state = PrologueState::After(acc);
        }
        let w = u32::from_le_bytes(code_bytes[4 * idx..4 * idx + 4].try_into().unwrap());
        match (state, classify_sp_word(w)) {
            (_, SpEffect::Unknown) => return None,
            (PrologueState::Before(min_fwd), SpEffect::Alloc(d)) => {
                if past_min_fwd(idx, min_fwd) {
                    return None;
                }
                state = PrologueState::InPrologue(d, min_fwd);
            }
            (PrologueState::InPrologue(acc, min_fwd), SpEffect::Alloc(d)) => {
                state = PrologueState::InPrologue(acc + d, min_fwd);
            }
            (PrologueState::After(_), SpEffect::Alloc(_)) => return None,
            (PrologueState::Before(_), SpEffect::Dealloc(_)) => return None,
            (PrologueState::InPrologue(acc, _), SpEffect::Dealloc(_)) => {
                state = PrologueState::After(acc);
            }
            (PrologueState::After(acc), SpEffect::Dealloc(_)) => {
                state = PrologueState::After(acc);
            }
            (PrologueState::Before(min_fwd), SpEffect::None) => match classify_flow_word(w, idx) {
                FlowKind::Normal => {}
                FlowKind::EndPrologue => {
                    state = PrologueState::After(0);
                }
                FlowKind::FwdCond(target_idx) => {
                    let next_min = Some(min_fwd.map_or(target_idx, |t| t.min(target_idx)));
                    state = PrologueState::Before(next_min);
                }
            },
            (PrologueState::InPrologue(acc, min_fwd), SpEffect::None) => {
                match classify_flow_word(w, idx) {
                    FlowKind::Normal => {
                        state = PrologueState::InPrologue(acc, min_fwd);
                    }
                    FlowKind::EndPrologue | FlowKind::FwdCond(_) => {
                        state = PrologueState::After(acc);
                    }
                }
            }
            (PrologueState::After(acc), SpEffect::None) => {
                state = PrologueState::After(acc);
            }
        }
    }
    let total = match state {
        PrologueState::Before(_) => 0,
        PrologueState::InPrologue(acc, min_fwd) => {
            if past_min_fwd(total_words, min_fwd) {
                return None;
            }
            acc
        }
        PrologueState::After(acc) => acc,
    };
    if total % 16 == 0 { Some(total) } else { None }
}

// ---------------------------------------------------------------------------
// 2. Symbol Index Data Model & Extraction
// ---------------------------------------------------------------------------

pub use super::index_schema::{
    CalleeInfo, FunctionIndexEntry, GENERATED_DIR, StubIndexEntry, TargetSymbolIndex,
    default_repo_root, load_symbol_indices, symbol_index_paths,
};

/// One entry of `Obj.funcTable` (mirrors `Arm64.Obj.funcTable` in `ProofLib/PrologueFrame.lean`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncTableEntry {
    pub name: String,
    pub off: u64,
    pub span: u64,
    pub size: u64,
    pub frame_bytes: Option<u64>,
    pub fn_size_lemma: String,
    pub frame_bytes_lemma: Option<String>,
}

/// Compute `Obj.funcTable` entries in the exact order of `li.symbols` (restricted to `.text`),
/// using $O(n \log n)$ span assignment and preserving discovery-order `_fnSize_0x...` /
/// `_frameBytes_0x...` suffixes for symbol aliases at the same offset.
pub fn build_func_table(
    cfg: &ExportConfig,
    objs: &[ObjObject],
    canon: &Canonical,
) -> Vec<FuncTableEntry> {
    let c = cfg.code_def_name();
    let text_end = text_end_offset(canon);
    let mut text_offs: Vec<u64> = canon
        .symbols
        .iter()
        .map(|(_, o)| *o)
        .filter(|&o| o < text_end)
        .collect();
    text_offs.sort_unstable();
    text_offs.dedup();

    let mut sym_to_ft: Vec<Option<usize>> = vec![None; canon.symbols.len()];
    let mut entries = Vec::new();
    for (sym_k, (name, off)) in canon.symbols.iter().enumerate() {
        let off = *off;
        if off >= text_end {
            continue;
        }
        let next_idx = text_offs.partition_point(|&o| o <= off);
        let next_off = text_offs.get(next_idx).copied().unwrap_or(text_end);
        let span = next_off.saturating_sub(off);
        let start = (off as usize).min(canon.code.len());
        let end = start.saturating_add(span as usize).min(canon.code.len());
        let slice = &canon.code[start..end];
        let size = trim_trailing_zero_bytes_len(slice);
        let frame_bytes = infer_prologue_frame(slice);
        sym_to_ft[sym_k] = Some(entries.len());
        entries.push(FuncTableEntry {
            name: name.clone(),
            off,
            span,
            size,
            frame_bytes,
            fn_size_lemma: String::new(),
            frame_bytes_lemma: None,
        });
    }

    let mut used = BTreeSet::new();
    let mut uniq = |base: String| {
        let mut name = base.clone();
        let mut i = 1;
        while !used.insert(name.clone()) {
            name = format!("{base}_{i}");
            i += 1;
        }
        name
    };

    for (sym_k, _) in ordered_symbols(objs, canon) {
        if let Some(ft_k) = sym_to_ft[sym_k] {
            let entry = &mut entries[ft_k];
            let off = entry.off;
            entry.fn_size_lemma = uniq(format!("{c}_fnSize_0x{off:x}"));
            entry.frame_bytes_lemma = entry
                .frame_bytes
                .map(|_| uniq(format!("{c}_frameBytes_0x{off:x}")));
        }
    }

    entries
}

/// Compute the exact `fnOff` and `stubOff` lemma names emitted by `render_code_module`.
pub fn compute_symbol_lemma_names(
    code_def: &str,
    objs: &[ObjObject],
    canon: &Canonical,
    emit_hook_at_off: bool,
) -> (BTreeMap<String, String>, Vec<StubIndexEntry>) {
    let mut used = BTreeSet::new();
    let mut uniq = |base: String| {
        let mut name = base.clone();
        let mut i = 1;
        while !used.insert(name.clone()) {
            name = format!("{base}_{i}");
            i += 1;
        }
        name
    };
    let mut fn_off_lemmas = BTreeMap::new();
    for (_, (name, off)) in ordered_symbols(objs, canon) {
        let thm = uniq(format!("{code_def}_fnOff_0x{off:x}"));
        fn_off_lemmas.entry(name.clone()).or_insert(thm);
    }
    let mut stubs = Vec::with_capacity(canon.stubs.len());
    for (name, off) in &canon.stubs {
        let stub_off_lemma = uniq(format!("{code_def}_stubOff_0x{off:x}"));
        let hook_lemma = if emit_hook_at_off {
            Some(uniq(format!("{code_def}_hookAtOff?_0x{off:x}")))
        } else {
            None
        };
        stubs.push(StubIndexEntry {
            name: name.clone(),
            offset: *off,
            offset_hex: format!("0x{off:x}"),
            stub_off_lemma,
            hook_lemma,
        });
    }
    (fn_off_lemmas, stubs)
}

/// Extract direct callees for function `f` from `objs` relocations and `canon.code` branch words.
pub fn extract_callees(
    f: &FuncRange,
    objs: &[ObjObject],
    canon: &Canonical,
    funcs: &[FuncRange],
) -> Vec<CalleeInfo> {
    let mut off_to_sym: BTreeMap<u64, (String, bool)> = BTreeMap::new();
    for func in funcs {
        off_to_sym
            .entry(func.off)
            .or_insert_with(|| (func.name.clone(), false));
    }
    for (name, off) in &canon.symbols {
        off_to_sym
            .entry(*off)
            .or_insert_with(|| (name.clone(), false));
    }
    for (name, off) in &canon.stubs {
        off_to_sym
            .entry(*off)
            .or_insert_with(|| (name.clone(), true));
    }
    let stub_names: BTreeSet<&str> = canon.stubs.iter().map(|(n, _)| n.as_str()).collect();
    let sym_offs: BTreeMap<&str, u64> = canon
        .symbols
        .iter()
        .chain(&canon.stubs)
        .map(|(n, o)| (n.as_str(), *o))
        .collect();

    let mut callees = Vec::new();
    let mut covered_sites = BTreeSet::new();
    let fn_end = f.off + f.size;

    // 1. Check `CALL26` and `JUMP26` relocations in the section containing `f`.
    for (o, offs) in objs.iter().zip(&canon.sec_off) {
        for (sec_idx, sec) in o.sections.iter().enumerate() {
            if sec.kind() != Some(SecKind::Text) {
                continue;
            }
            let Some(sec_off) = offs.get(sec_idx).copied().flatten() else {
                continue;
            };
            let sec_end = sec_off + sec.size;
            if f.off < sec_off || f.off >= sec_end {
                continue;
            }
            for r in &sec.relocs {
                if !matches!(r.rtype, RelocType::Call26 | RelocType::Jump26) {
                    continue;
                }
                let site_off = sec_off + r.offset;
                if site_off < f.off || site_off >= fn_end {
                    continue;
                }
                let is_tail_call = r.rtype == RelocType::Jump26;
                let resolved_target = (site_off as usize + 4 <= canon.code.len()).then(|| {
                    let idx = site_off as usize;
                    let w = u32::from_le_bytes(canon.code[idx..idx + 4].try_into().unwrap());
                    let imm26 = (w & 0x03ff_ffff) as i32;
                    let disp = (((imm26 << 6) >> 6) as i64) * 4;
                    (site_off as i64).wrapping_add(disp) as u64
                });
                let sym = o.symbols.get(r.sym);

                // Resolve `(callee_name, is_extern, target_offset)`:
                let resolved = if let Some(s) = sym
                    && s.kind != SymKind::Section
                    && r.addend == 0
                    && !s.name.is_empty()
                {
                    let is_ext = stub_names.contains(s.name.as_str());
                    let tgt_off =
                        resolved_target.or_else(|| sym_offs.get(s.name.as_str()).copied());
                    if is_tail_call
                        && let Some(t) = tgt_off
                        && t >= f.off
                        && t < fn_end
                        && s.name == f.name
                    {
                        None
                    } else {
                        Some((s.name.clone(), is_ext, tgt_off))
                    }
                } else if let Some(t) = resolved_target {
                    if is_tail_call && t >= f.off && t < fn_end {
                        None
                    } else {
                        off_to_sym
                            .get(&t)
                            .map(|(n, is_ext)| (n.clone(), *is_ext, Some(t)))
                    }
                } else {
                    None
                };

                if let Some((callee, is_extern, target_offset)) = resolved {
                    covered_sites.insert(site_off);
                    let call_offset = site_off - f.off;
                    callees.push(CalleeInfo {
                        call_offset,
                        call_offset_hex: format!("0x{call_offset:x}"),
                        site_offset: site_off,
                        site_offset_hex: format!("0x{site_off:x}"),
                        callee,
                        target_offset,
                        is_tail_call,
                        is_extern,
                        reloc_type: if is_tail_call {
                            "JUMP26".into()
                        } else {
                            "CALL26".into()
                        },
                    });
                }
            }
        }
    }

    // 2. Scan `canon.code` for direct `bl` / `b` instructions without relocations that target
    //    another symbol or stub.
    let code_end = fn_end.min(canon.code.len() as u64);
    let mut site_off = f.off.next_multiple_of(4);
    while site_off + 4 <= code_end {
        if !covered_sites.contains(&site_off) {
            let o = site_off as usize;
            let w = u32::from_le_bytes(canon.code[o..o + 4].try_into().unwrap());
            let is_bl = (w & 0xfc00_0000) == 0x9400_0000;
            let is_b = (w & 0xfc00_0000) == 0x1400_0000;
            if is_bl || is_b {
                let imm26 = (w & 0x03ff_ffff) as i32;
                let disp = (((imm26 << 6) >> 6) as i64) * 4;
                let target_off = (site_off as i64).wrapping_add(disp) as u64;
                let is_intra_branch = is_b && target_off >= f.off && target_off < fn_end;
                if !is_intra_branch && let Some((callee, is_extern)) = off_to_sym.get(&target_off) {
                    let call_offset = site_off - f.off;
                    callees.push(CalleeInfo {
                        call_offset,
                        call_offset_hex: format!("0x{call_offset:x}"),
                        site_offset: site_off,
                        site_offset_hex: format!("0x{site_off:x}"),
                        callee: callee.clone(),
                        target_offset: Some(target_off),
                        is_tail_call: is_b,
                        is_extern: *is_extern,
                        reloc_type: "DIRECT".into(),
                    });
                }
            }
        }
        site_off += 4;
    }

    callees.sort_by_key(|c| c.call_offset);
    callees
}

/// Derive `<Target>Index.json` path from `target.lean_file` (stripping trailing `"Fns"` or
/// `"Fetch"` from the stem when non-empty and appending `"Index.json"`).
pub fn target_index_file(target: &ExportTarget) -> PathBuf {
    let stem = target
        .lean_file
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy();
    let base = stem
        .strip_suffix("Fns")
        .or_else(|| stem.strip_suffix("Fetch"))
        .filter(|s| !s.is_empty())
        .unwrap_or(&stem);
    target.lean_file.with_file_name(format!("{base}Index.json"))
}

/// Derive `<ObjName>Index.json` path from `cfg.code_file` (stripping trailing `"Code"` from
/// the stem when non-empty and appending `"Index.json"`).
pub fn code_index_file(cfg: &ExportConfig) -> PathBuf {
    let stem = cfg
        .code_file
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy();
    let base = stem
        .strip_suffix("Code")
        .filter(|s| !s.is_empty())
        .unwrap_or(&stem);
    cfg.code_file.with_file_name(format!("{base}Index.json"))
}

/// Build the `FunctionIndexEntry` for a single function `f`.
fn build_function_entry(
    cfg: &ExportConfig,
    f: &FuncRange,
    canon: &Canonical,
    objs: &[ObjObject],
    funcs: &[FuncRange],
    fn_off_lemmas: &BTreeMap<String, String>,
    ft_map: &BTreeMap<&str, &FuncTableEntry>,
    decode_prefix: Option<(&str, String)>,
) -> FunctionIndexEntry {
    let c = cfg.code_def_name();
    let root_ns = &cfg.namespace_prefix;
    let fn_off_lemma = fn_off_lemmas
        .get(&f.name)
        .cloned()
        .unwrap_or_else(|| format!("{c}_fnOff_0x{:x}", f.off));
    let fn_off_lemma_full = format!("{root_ns}.{fn_off_lemma}");

    let ft = ft_map.get(f.name.as_str()).copied();
    let fn_size_lemma = ft
        .map(|e| e.fn_size_lemma.clone())
        .unwrap_or_else(|| format!("{c}_fnSize_0x{:x}", f.off));
    let frame_bytes_lemma = ft.and_then(|e| e.frame_bytes_lemma.clone());

    let frame_bytes = ft.and_then(|e| e.frame_bytes).or_else(|| {
        let start = (f.off as usize).min(canon.code.len());
        let end = start.saturating_add(f.size as usize).min(canon.code.len());
        infer_prologue_frame(&canon.code[start..end])
    });
    let callees = extract_callees(f, objs, canon, funcs);

    FunctionIndexEntry {
        name: f.name.clone(),
        offset: f.off,
        offset_hex: format!("0x{:x}", f.off),
        size_bytes: f.size,
        size_insns: f.size / 4,
        fn_off_lemma,
        fn_off_lemma_full,
        fn_size_lemma,
        frame_bytes_lemma,
        decode_prefix: decode_prefix.as_ref().map(|(p, _)| (*p).to_string()),
        decode_prefix_full: decode_prefix.map(|(_, full)| full),
        frame_bytes,
        frame_unknown: frame_bytes.is_none(),
        callees,
        dwarf: None,
    }
}

/// Build the `TargetSymbolIndex` for `target` (and optionally a combined index for `cfg`).
pub fn build_target_index(
    cfg: &ExportConfig,
    target: &ExportTarget,
    objs: &[ObjObject],
    canon: &Canonical,
    funcs: &[FuncRange],
    ft_entries: &[FuncTableEntry],
    fn_off_lemmas: &BTreeMap<String, String>,
    stubs: &[StubIndexEntry],
) -> Result<TargetSymbolIndex> {
    let c = cfg.code_def_name();
    let root_ns = &cfg.namespace_prefix;
    let target_ns = cfg.target_namespace(target);
    let dec_full = format!("{target_ns}.{}", target.prog_name);
    let ft_map: BTreeMap<&str, &FuncTableEntry> =
        ft_entries.iter().map(|e| (e.name.as_str(), e)).collect();

    let selected = selected_function_symbols(target, funcs)?;
    let text_end = text_end_offset(canon);
    let mut entries = Vec::with_capacity(selected.len());
    for f in selected {
        let dec = (f.off < text_end).then(|| (target.prog_name.as_str(), dec_full.clone()));
        entries.push(build_function_entry(
            cfg,
            f,
            canon,
            objs,
            funcs,
            fn_off_lemmas,
            &ft_map,
            dec,
        ));
    }

    Ok(TargetSymbolIndex {
        schema_version: 1,
        target: Some(target.name.clone()),
        obj_name: cfg.obj_name.clone(),
        code_def: c.clone(),
        objs_expr: cfg.image_def_name(),
        namespace_prefix: cfg.namespace_prefix.clone(),
        sub_namespace: target.sub_namespace.clone(),
        code_file: format!("{}.lean", cfg.code_module.replace('.', "/")),
        lean_file: Some(format!("{}.lean", target.lean_module.replace('.', "/"))),
        code_module: cfg.code_module.clone(),
        code_const: format!("{root_ns}.{c}"),
        target_module: Some(target.lean_module.clone()),
        prog_name: Some(target.prog_name.clone()),
        functions: entries,
        stubs: stubs.to_vec(),
        dwarf_types: Vec::new(),
    })
}

/// Build a combined `TargetSymbolIndex` covering all functions in `cfg` across all targets.
pub fn build_combined_code_index(
    cfg: &ExportConfig,
    objs: &[ObjObject],
    canon: &Canonical,
    funcs: &[FuncRange],
    ft_entries: &[FuncTableEntry],
    fn_off_lemmas: &BTreeMap<String, String>,
    stubs: &[StubIndexEntry],
) -> Result<TargetSymbolIndex> {
    let c = cfg.code_def_name();
    let root_ns = &cfg.namespace_prefix;
    let ft_map: BTreeMap<&str, &FuncTableEntry> =
        ft_entries.iter().map(|e| (e.name.as_str(), e)).collect();

    let mut fn_to_target: BTreeMap<&str, (&str, String)> = BTreeMap::new();
    for target in &cfg.targets {
        let target_ns = cfg.target_namespace(target);
        let dec_full = format!("{target_ns}.{}", target.prog_name);
        for f in selected_function_symbols(target, funcs)? {
            fn_to_target
                .entry(f.name.as_str())
                .or_insert((target.prog_name.as_str(), dec_full.clone()));
        }
    }

    let text_end = text_end_offset(canon);
    let mut seen_names = BTreeSet::new();
    let mut entries = Vec::new();
    for f in funcs {
        if !seen_names.insert(f.name.as_str()) {
            continue;
        }
        let dec = (f.off < text_end)
            .then(|| fn_to_target.get(f.name.as_str()).cloned())
            .flatten();
        entries.push(build_function_entry(
            cfg,
            f,
            canon,
            objs,
            funcs,
            fn_off_lemmas,
            &ft_map,
            dec,
        ));
    }

    let first_target = cfg.targets.first();
    Ok(TargetSymbolIndex {
        schema_version: 1,
        target: None,
        obj_name: cfg.obj_name.clone(),
        code_def: c.clone(),
        objs_expr: cfg.image_def_name(),
        namespace_prefix: cfg.namespace_prefix.clone(),
        sub_namespace: None,
        code_file: format!("{}.lean", cfg.code_module.replace('.', "/")),
        lean_file: first_target.map(|t| format!("{}.lean", t.lean_module.replace('.', "/"))),
        code_module: cfg.code_module.clone(),
        code_const: format!("{root_ns}.{c}"),
        target_module: first_target.map(|t| t.lean_module.clone()),
        prog_name: first_target.map(|t| t.prog_name.clone()),
        functions: entries,
        stubs: stubs.to_vec(),
        dwarf_types: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trusted_common::{
        ExternDecl, ExternKind, ObjReloc, ObjSection, ObjSymbol, SymBind, SymSection,
    };
    use crate::untrusted_legacy_linker::link;
    use crate::untrusted_lemmas::code::func_ranges;
    use object::elf;

    fn words(ws: &[u32]) -> Vec<u8> {
        ws.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    #[test]
    fn prologue_frame_inference_leaf_and_standard_prologues() {
        // 1. Leaf function: `add x0, x0, #1; ret` -> Some(0)
        let leaf = words(&[0x9100_0400, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&leaf), Some(0));

        // 2. Pre-indexed `stp x29, x30, [sp, #-16]!; mov x29, sp; ldp x29, x30, [sp], #16; ret` -> Some(16)
        let stp16 = words(&[0xa9bf_7bfd, 0x9100_03fd, 0xa8c1_7bfd, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&stp16), Some(16));

        // 3. `sub sp, sp, #48; stp x29, x30, [sp, #32]; add sp, sp, #48; ret` -> Some(48)
        let sub48 = words(&[0xd100_c3ff, 0xa902_7bfd, 0x9100_c3ff, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&sub48), Some(48));

        // 4. Two-step allocation: `stp x29, x30, [sp, #-32]!; sub sp, sp, #16; add sp, sp, #16; ldp x29, x30, [sp], #32; ret` -> Some(48)
        let two_step = words(&[
            0xa9be_7bfd, // stp x29, x30, [sp, #-32]!
            0xd100_43ff, // sub sp, sp, #16
            0x9100_43ff, // add sp, sp, #16
            0xa8c2_7bfd, // ldp x29, x30, [sp], #32
            0xd65f_03c0, // ret
        ]);
        assert_eq!(infer_prologue_frame(&two_step), Some(48));

        // 5. Pre-indexed single register `str x30, [sp, #-16]!; ldr x30, [sp], #16; ret` -> Some(16)
        let str16 = words(&[0xf81f_0ffe, 0xf841_07fe, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&str16), Some(16));

        // 6. Shrink-wrapped early return guard:
        //    `cbz x0, +4 words (.Lret); stp x29, x30, [sp, #-32]!; bl 0; ldp x29, x30, [sp], #32; .Lret: ret`
        let shrink_wrapped = words(&[
            0xb400_0080, // cbz x0, +16 (to word 4)
            0xa9be_7bfd, // stp x29, x30, [sp, #-32]!
            0x9400_0000, // bl ...
            0xa8c2_7bfd, // ldp x29, x30, [sp], #32
            0xd65f_03c0, // ret
        ]);
        assert_eq!(infer_prologue_frame(&shrink_wrapped), Some(32));
    }

    #[test]
    fn prologue_frame_inference_rejects_dynamic_or_malformed_sp() {
        // 1. Dynamic stack allocation `sub sp, sp, x8` (`0xcb2863ff`) -> None
        let dyn_sub = words(&[0xcb28_63ff, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&dyn_sub), None);

        // 2. Misaligned frame size `sub sp, sp, #8` (`0xd10023ff`) -> None
        let misaligned = words(&[0xd100_23ff, 0x9100_23ff, 0xd65f_03c0]);
        assert_eq!(infer_prologue_frame(&misaligned), None);

        // 3. Allocation after a `bl` call -> None
        let alloc_after_call = words(&[
            0xa9bf_7bfd, // stp x29, x30, [sp, #-16]!
            0x9400_0000, // bl ...
            0xd100_43ff, // sub sp, sp, #16 (after call!)
            0xd65f_03c0, // ret
        ]);
        assert_eq!(infer_prologue_frame(&alloc_after_call), None);
    }

    #[test]
    fn extracts_callees_including_tail_calls_and_externs() {
        let text = ObjSection {
            name: ".text".into(),
            sh_type: elf::SHT_PROGBITS,
            sh_flags: (elf::SHF_ALLOC | elf::SHF_EXECINSTR) as u64,
            addr: 0,
            align: 4,
            entsize: 0,
            size: 24,
            file_offset: 0,
            bytes: words(&[
                0xa9bf_7bfd, // 0x00: stp x29, x30, [sp, #-16]!
                0x9400_0000, // 0x04: bl helper (CALL26)
                0x9400_0000, // 0x08: bl ext_fn (CALL26)
                0xa8c1_7bfd, // 0x0c: ldp x29, x30, [sp], #16
                0x1400_0000, // 0x10: b helper (JUMP26 tail call)
                0xd65f_03c0, // 0x14: ret (helper at 0x14)
            ]),
            relocs: vec![
                ObjReloc {
                    offset: 4,
                    rtype: RelocType::Call26,
                    sym: 2,
                    addend: 0,
                },
                ObjReloc {
                    offset: 8,
                    rtype: RelocType::Call26,
                    sym: 3,
                    addend: 0,
                },
                ObjReloc {
                    offset: 16,
                    rtype: RelocType::Jump26,
                    sym: 2,
                    addend: 0,
                },
            ],
            is_rel: false,
            elf_index: 1,
        };
        let obj = ObjObject {
            name: "test".into(),
            sections: vec![text],
            symbols: vec![
                ObjSymbol {
                    name: String::new(),
                    raw_name: String::new(),
                    kind: SymKind::Notype,
                    bind: SymBind::Local,
                    vis: 0,
                    sec: SymSection::Undef,
                    value: 0,
                    size: 0,
                },
                ObjSymbol {
                    name: "caller".into(),
                    raw_name: "caller".into(),
                    kind: SymKind::Func,
                    bind: SymBind::Global,
                    vis: 0,
                    sec: SymSection::Sec(0),
                    value: 0,
                    size: 20,
                },
                ObjSymbol {
                    name: "helper".into(),
                    raw_name: "helper".into(),
                    kind: SymKind::Func,
                    bind: SymBind::Local,
                    vis: 0,
                    sec: SymSection::Sec(0),
                    value: 20,
                    size: 4,
                },
                ObjSymbol {
                    name: "ext_fn".into(),
                    raw_name: "ext_fn".into(),
                    kind: SymKind::Notype,
                    bind: SymBind::Global,
                    vis: 0,
                    sec: SymSection::Undef,
                    value: 0,
                    size: 0,
                },
            ],
            groups: vec![],
            elf_bytes: vec![],
        };
        let externs = vec![ExternDecl {
            name: "ext_fn".into(),
            raw_name: "ext_fn".into(),
            kind: ExternKind::Func,
            size: 0,
            align: 4,
            origin: String::new(),
        }];
        let canon = link(std::slice::from_ref(&obj), &externs).unwrap();
        let funcs = func_ranges(std::slice::from_ref(&obj), &canon);
        assert_eq!(funcs.len(), 2);

        let callees = extract_callees(&funcs[0], std::slice::from_ref(&obj), &canon, &funcs);
        assert_eq!(callees.len(), 3);
        assert_eq!(callees[0].call_offset, 4);
        assert_eq!(callees[0].callee, "helper");
        assert!(!callees[0].is_tail_call);
        assert!(!callees[0].is_extern);

        assert_eq!(callees[1].call_offset, 8);
        assert_eq!(callees[1].callee, "ext_fn");
        assert!(!callees[1].is_tail_call);
        assert!(callees[1].is_extern);

        assert_eq!(callees[2].call_offset, 16);
        assert_eq!(callees[2].callee, "helper");
        assert!(callees[2].is_tail_call);
        assert!(!callees[2].is_extern);
    }
}
