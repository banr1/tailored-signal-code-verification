// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Multi-Path Symbolic Execution Driver and CLI Runner (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (CFG explorer and target-index loader for the read-only
//!   `rust-obj2lean symexec` / `lean-sig symexec` advisor).
//! - **Purpose:** Resolves `<Target>Index.json` and `<ObjName>Obj.code.bin` (or raw `--hex`
//!   instruction words), scans the function for static CFG metadata (branches, calls, stack slots),
//!   and runs bounded multi-path worklist symbolic execution with loop back-edge detection and
//!   optional user `--branches` / `--init` / `--from` / `--to` overrides.
//!
//! # Key Types & Functions
//! - [`analyze_and_execute`]: Core multi-path CFG and symbolic execution engine returning
//!   [`super::emit::SymexecReport`].
//! - [`run_symexec`]: Resolves CLI [`super::emit::SymexecArgs`] and produces a [`SymexecReport`].
//! - [`run_symexec_cli`]: CLI entry point printing human text or `--json` output.
//!
//! # When to Read This File
//! - Read this file when changing how `<Target>Index.json` is located, how `--init`/`--branches`
//!   flags are parsed, or how the multi-path worklist handles branches, calls, and back-edges.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result, anyhow, bail};
use clap::Parser;

use crate::untrusted_lemmas::index::{
    CalleeInfo, FunctionIndexEntry, TargetSymbolIndex, infer_prologue_frame,
};
use crate::untrusted_lemmas::{extract, parse_u32_lit, parse_u64_lit, sign_extend};

use super::emit::{
    DisasmLine, PathSnapshot, StackSlotSummary, SymexecArgs, SymexecReport, format_report_text,
};
use super::expr::{SymExpr, negate_cond_str, reg_name};
use super::hints::{
    BlockHintsReport, HintLine, HintStep, PathHints, branch_target_image_off,
    classify_straight_line, format_block_hints_text,
};
use super::insn_semantics::{StepOutcome, step_instruction};
use super::state::{
    BranchRecord, CallSiteRecord, DEFAULT_MAX_EXPR_NODES, MemAccessRecord, SymState,
};

pub fn analyze_and_execute(
    symbol: &str,
    fn_offset: u64,
    code_bytes: &[u8],
    entry_meta: Option<&FunctionIndexEntry>,
    start_off: u64,
    stop_offs: &BTreeSet<u64>,
    forced_branches: &BTreeMap<u64, bool>,
    init_overrides: &[(u8, SymExpr)],
    max_steps: usize,
    max_paths: usize,
) -> Result<SymexecReport> {
    analyze_and_execute_with_limits(
        symbol,
        fn_offset,
        code_bytes,
        entry_meta,
        start_off,
        stop_offs,
        forced_branches,
        init_overrides,
        max_steps,
        max_paths,
        DEFAULT_MAX_EXPR_NODES,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn analyze_and_execute_with_limits(
    symbol: &str,
    fn_offset: u64,
    code_bytes: &[u8],
    entry_meta: Option<&FunctionIndexEntry>,
    start_off: u64,
    stop_offs: &BTreeSet<u64>,
    forced_branches: &BTreeMap<u64, bool>,
    init_overrides: &[(u8, SymExpr)],
    max_steps: usize,
    max_paths: usize,
    max_expr_nodes: usize,
) -> Result<SymexecReport> {
    if code_bytes.len() % 4 != 0 {
        bail!(
            "function code byte length ({}) is not a multiple of 4",
            code_bytes.len()
        );
    }
    let fn_size = code_bytes.len() as u64;
    let prologue_frame_bytes = entry_meta
        .and_then(|e| e.frame_bytes)
        .or_else(|| infer_prologue_frame(code_bytes));

    let callees_by_off: BTreeMap<u64, &CalleeInfo> = entry_meta
        .map(|e| e.callees.iter().map(|c| (c.call_offset, c)).collect())
        .unwrap_or_default();

    // 1. Static CFG scan for block leaders and loop headers (back-edge targets).
    let mut block_leaders: BTreeSet<u64> = BTreeSet::from([0, start_off]);
    let mut loop_headers: BTreeSet<u64> = BTreeSet::new();
    let num_words = code_bytes.len() / 4;
    for i in 0..num_words {
        let off = (i * 4) as u64;
        let w = u32::from_le_bytes(code_bytes[4 * i..4 * i + 4].try_into().unwrap());
        // Unconditional B (not BL)
        if (w & 0xfc00_0000) == 0x1400_0000 && !callees_by_off.contains_key(&off) {
            let imm26 = extract(w, 0, 26);
            let disp = (sign_extend(imm26, 26) << 2) as i64;
            let tgt = (off as i64).wrapping_add(disp) as u64;
            if tgt < fn_size {
                block_leaders.insert(tgt);
                if tgt <= off {
                    loop_headers.insert(tgt);
                }
            }
            if off + 4 < fn_size {
                block_leaders.insert(off + 4);
            }
        }
        // Conditional B.cond or CBZ/CBNZ
        if (w & 0xff00_0010) == 0x5400_0000 || (w & 0x7e00_0000) == 0x3400_0000 {
            let imm19 = extract(w, 5, 19);
            let disp = (sign_extend(imm19, 19) << 2) as i64;
            let tgt = (off as i64).wrapping_add(disp) as u64;
            if tgt < fn_size {
                block_leaders.insert(tgt);
                if tgt <= off {
                    loop_headers.insert(tgt);
                }
            }
            if off + 4 < fn_size {
                block_leaders.insert(off + 4);
            }
        }
        // TBZ/TBNZ
        if (w & 0x7e00_0000) == 0x3600_0000 {
            let imm14 = extract(w, 5, 14);
            let disp = (sign_extend(imm14, 14) << 2) as i64;
            let tgt = (off as i64).wrapping_add(disp) as u64;
            if tgt < fn_size {
                block_leaders.insert(tgt);
                if tgt <= off {
                    loop_headers.insert(tgt);
                }
            }
            if off + 4 < fn_size {
                block_leaders.insert(off + 4);
            }
        }
    }

    let mut instructions = Vec::with_capacity(num_words);
    for i in 0..num_words {
        let off = (i * 4) as u64;
        let w = u32::from_le_bytes(code_bytes[4 * i..4 * i + 4].try_into().unwrap());
        let lean_instr = format!("0x{w:08x}");
        instructions.push(DisasmLine {
            offset: off,
            offset_hex: format!("0x{off:x}"),
            word_hex: format!("0x{w:08x}"),
            lean_instr,
            is_block_leader: block_leaders.contains(&off),
            is_loop_header: loop_headers.contains(&off),
        });
    }

    // 2. Worklist symbolic execution across acyclic paths.
    let mut init_state = SymState::new(start_off);
    init_state.max_expr_nodes = max_expr_nodes;
    for (r, expr) in init_overrides {
        if *r <= 31 {
            init_state.regs[*r as usize] = expr.clone();
        }
    }

    let max_stop_off: Option<u64> = stop_offs.iter().copied().max();
    let mut worklist: VecDeque<(SymState, Vec<HintLine>)> =
        VecDeque::from([(init_state, Vec::new())]);
    let mut all_accesses: Vec<MemAccessRecord> = Vec::new();
    let mut all_calls: Vec<CallSiteRecord> = Vec::new();
    let mut branch_map: BTreeMap<u64, BranchRecord> = BTreeMap::new();
    let mut snapshots: Vec<PathSnapshot> = Vec::new();
    let mut block_hints: Vec<PathHints> = Vec::new();
    let mut completed_paths = 0usize;

    // Close the current path: record its snapshot and its hint stream ending in `last`.
    let mut finish_path = |label: String,
                           pc: u64,
                           state: &SymState,
                           mut hints: Vec<HintLine>,
                           last: HintStep,
                           snapshots: &mut Vec<PathSnapshot>| {
        snapshots.push(build_snapshot(&label, pc, state));
        hints.push(HintLine {
            offset: pc,
            step: last,
        });
        block_hints.push(PathHints {
            index: block_hints.len(),
            label,
            entry: start_off,
            lines: hints,
        });
    };

    while let Some((mut state, mut hints)) = worklist.pop_front() {
        if completed_paths >= max_paths {
            break;
        }
        loop {
            let pc = state.pc_off;
            let cut_label = if state.steps > 0
                && (stop_offs.contains(&pc) || max_stop_off.is_some_and(|max_stop| pc > max_stop))
            {
                Some(format!("cut_0x{pc:x}"))
            } else if state.exceeded_max_expr_nodes {
                Some(format!("max_expr_nodes_0x{pc:x}"))
            } else if pc >= fn_size || pc % 4 != 0 {
                Some(format!("exit_0x{pc:x}"))
            } else if state.visited_pcs.contains(&pc) {
                Some(format!("loop_backedge_0x{pc:x}"))
            } else if state.steps >= max_steps {
                Some(format!("max_steps_0x{pc:x}"))
            } else {
                None
            };
            if let Some(label) = cut_label {
                let reason = label.clone();
                finish_path(
                    label,
                    pc,
                    &state,
                    std::mem::take(&mut hints),
                    HintStep::Stop { reason },
                    &mut snapshots,
                );
                completed_paths += 1;
                break;
            }
            // Also record a snapshot the first time a path reaches a loop header (if > start_off).
            if loop_headers.contains(&pc) && state.steps > 0 {
                snapshots.push(build_snapshot(&format!("loop_entry_0x{pc:x}"), pc, &state));
            }

            state.visited_pcs.insert(pc);
            state.steps += 1;
            let idx = (pc / 4) as usize;
            let w = u32::from_le_bytes(code_bytes[4 * idx..4 * idx + 4].try_into().unwrap());

            let acc_start = all_accesses.len();
            let call_start = all_calls.len();
            match step_instruction(
                w,
                &mut state,
                &callees_by_off,
                fn_size,
                &mut all_accesses,
                &mut all_calls,
            ) {
                StepOutcome::Next => {
                    hints.push(HintLine {
                        offset: pc,
                        step: classify_straight_line(
                            w,
                            pc,
                            fn_offset,
                            &all_accesses[acc_start..],
                            &all_calls[call_start..],
                        ),
                    });
                    continue;
                }
                StepOutcome::Return { reason, target } => {
                    let last = if reason == "ret" {
                        HintStep::Ret
                    } else {
                        HintStep::Tailcall {
                            target: branch_target_image_off(target.as_ref(), fn_offset),
                            callee: all_calls[call_start..].first().map(|c| c.callee.clone()),
                        }
                    };
                    finish_path(
                        format!("{reason}_0x{pc:x}"),
                        pc,
                        &state,
                        std::mem::take(&mut hints),
                        last,
                        &mut snapshots,
                    );
                    completed_paths += 1;
                    break;
                }
                StepOutcome::Halted { reason, .. } => {
                    let label = format!("halt_0x{pc:x} ({reason})");
                    finish_path(
                        label,
                        pc,
                        &state,
                        std::mem::take(&mut hints),
                        HintStep::Stop { reason },
                        &mut snapshots,
                    );
                    completed_paths += 1;
                    break;
                }
                StepOutcome::CondBranch {
                    mnemonic,
                    cond_lean,
                    taken_pc,
                    fallthrough_pc,
                    ..
                } => {
                    let is_back_edge = taken_pc <= pc;
                    branch_map.entry(pc).or_insert_with(|| BranchRecord {
                        insn_offset: pc,
                        insn_offset_hex: format!("0x{pc:x}"),
                        mnemonic: mnemonic.clone(),
                        cond_lean: cond_lean.clone(),
                        taken_offset: taken_pc,
                        taken_offset_hex: format!("0x{taken_pc:x}"),
                        fallthrough_offset: fallthrough_pc,
                        fallthrough_offset_hex: format!("0x{fallthrough_pc:x}"),
                        is_back_edge,
                    });
                    let neg_cond = negate_cond_str(&cond_lean);
                    let br_hint = |taken: bool| HintLine {
                        offset: pc,
                        step: HintStep::Br {
                            taken,
                            cond: if taken {
                                cond_lean.clone()
                            } else {
                                neg_cond.clone()
                            },
                        },
                    };

                    if let Some(&take) = forced_branches.get(&pc) {
                        hints.push(br_hint(take));
                        if take {
                            state.path_conds.push(cond_lean);
                            state.pc_off = taken_pc;
                        } else {
                            state.path_conds.push(neg_cond);
                            state.pc_off = fallthrough_pc;
                        }
                        continue;
                    }

                    // Explore both fallthrough and taken (pushing taken to worklist, continuing fallthrough).
                    if worklist.len() + completed_paths < max_paths {
                        let mut taken_state = state.clone();
                        taken_state.path_conds.push(cond_lean.clone());
                        taken_state.pc_off = taken_pc;
                        let mut taken_hints = hints.clone();
                        taken_hints.push(br_hint(true));
                        worklist.push_back((taken_state, taken_hints));
                    }
                    hints.push(br_hint(false));
                    state.path_conds.push(neg_cond);
                    state.pc_off = fallthrough_pc;
                }
            }
        }
    }

    // 3. Aggregate Stack Frame Slots (`base == "sp"`) & Non-Stack Pointer Accesses.
    let mut stack_map: BTreeMap<i64, StackSlotSummary> = BTreeMap::new();
    let mut non_stack_accesses: Vec<MemAccessRecord> = Vec::new();
    let mut seen_non_stack: BTreeSet<(String, i64, u32, bool)> = BTreeSet::new();

    for acc in &all_accesses {
        if acc.base == "sp" {
            let entry = stack_map
                .entry(acc.offset)
                .or_insert_with(|| StackSlotSummary {
                    sp_offset: acc.offset,
                    addr_lean: if acc.offset < 0 {
                        format!("(sp - 0x{:x}#64)", acc.offset.unsigned_abs())
                    } else if acc.offset == 0 {
                        "sp".to_string()
                    } else {
                        format!("(sp + 0x{:x}#64)", acc.offset as u64)
                    },
                    width_bits: acc.width_bits,
                    width_bytes: (acc.width_bits / 8) as u64,
                    points_to_op: acc.points_to_op,
                    first_written_by: None,
                    final_values: Vec::new(),
                });
            if acc.width_bits > entry.width_bits {
                entry.width_bits = acc.width_bits;
                entry.width_bytes = (acc.width_bits / 8) as u64;
                entry.points_to_op = acc.points_to_op;
            }
            if acc.is_store && entry.first_written_by.is_none() {
                entry.first_written_by =
                    Some(format!("+{}: {}", acc.insn_offset_hex, acc.value_lean));
            }
        } else if seen_non_stack.insert((
            acc.base.clone(),
            acc.offset,
            acc.width_bits,
            acc.is_store,
        )) {
            non_stack_accesses.push(acc.clone());
        }
    }

    for snap in &snapshots {
        for (addr, val) in &snap.modified_mem {
            for slot in stack_map.values_mut() {
                if &slot.addr_lean == addr && !slot.final_values.contains(val) {
                    slot.final_values.push(val.clone());
                }
            }
        }
    }

    // Deduplicate calls by `call_offset`
    let mut unique_calls: BTreeMap<u64, CallSiteRecord> = BTreeMap::new();
    for c in all_calls {
        unique_calls.entry(c.call_offset).or_insert(c);
    }

    Ok(SymexecReport {
        symbol: symbol.to_string(),
        fn_offset,
        fn_offset_hex: format!("0x{fn_offset:x}"),
        size_bytes: fn_size,
        size_insns: fn_size / 4,
        prologue_frame_bytes,
        fn_off_lemma: entry_meta.map(|e| e.fn_off_lemma.clone()),
        fn_size_lemma: entry_meta.map(|e| e.fn_size_lemma.clone()),
        frame_bytes_lemma: entry_meta.and_then(|e| e.frame_bytes_lemma.clone()),
        loop_headers: loop_headers.iter().map(|o| format!("+0x{o:x}")).collect(),
        instructions,
        branches: branch_map.into_values().collect(),
        calls: unique_calls.into_values().collect(),
        stack_slots: stack_map.into_values().collect(),
        non_stack_accesses,
        snapshots,
        source: None,
        block_hints,
    })
}

/// Package the per-path hint streams of `report` as a version-1 block-hint certificate.
pub fn block_hints_report(report: &SymexecReport) -> BlockHintsReport {
    BlockHintsReport {
        version: 1,
        symbol: report.symbol.clone(),
        fn_offset: report.fn_offset,
        paths: report.block_hints.clone(),
    }
}

fn build_snapshot(label: &str, pc: u64, state: &SymState) -> PathSnapshot {
    let let_bindings = state
        .bindings
        .iter()
        .map(|(name, expr)| (name.clone(), expr.to_lean()))
        .collect();
    let mut modified_regs = BTreeMap::new();
    for r in 0..32u8 {
        let cur = &state.regs[r as usize];
        if *cur != SymExpr::InitReg(r) {
            modified_regs.insert(reg_name(r).to_string(), cur.to_lean());
        }
    }
    let mut modified_mem = BTreeMap::new();
    for ((base, off), (_w, expr)) in &state.mem {
        let addr_str = if *off == 0 {
            base.clone()
        } else if *off < 0 {
            format!("({base} - 0x{:x}#64)", off.unsigned_abs())
        } else {
            format!("({base} + 0x{:x}#64)", *off as u64)
        };
        modified_mem.insert(addr_str, expr.to_lean());
    }
    PathSnapshot {
        label: label.to_string(),
        at_offset: pc,
        at_offset_hex: format!("0x{pc:x}"),
        steps: state.steps,
        path_conditions: state.path_conds.clone(),
        let_bindings,
        modified_regs,
        modified_mem,
    }
}

fn resolve_target_index(
    repo_root: &Path,
    target_query: &str,
) -> Result<(PathBuf, TargetSymbolIndex)> {
    let direct = PathBuf::from(target_query);
    if direct.is_file() {
        let s = fs::read_to_string(&direct)?;
        let idx: TargetSymbolIndex = serde_json::from_str(&s)?;
        return Ok((direct, idx));
    }
    let index_paths = crate::untrusted_lemmas::index::symbol_index_paths(repo_root);
    if index_paths.is_empty() {
        bail!(
            "no `*Index.json` files found under `{}`; run `timeout 600 lake build --no-ansi` to generate target indices",
            repo_root.display()
        );
    }
    let q_lower = target_query
        .trim_end_matches("Index.json")
        .trim_end_matches("Obj")
        .trim_end_matches("Code")
        .trim_end_matches("Fns")
        .trim_end_matches("Fetch")
        .to_ascii_lowercase();

    let mut candidates: Vec<(PathBuf, TargetSymbolIndex)> = Vec::new();
    for p in index_paths {
        let Some(fname) = p.file_name().and_then(|f| f.to_str()) else {
            continue;
        };
        if !fname.ends_with("Index.json") {
            continue;
        }
        if let Ok(s) = fs::read_to_string(&p)
            && let Ok(idx) = serde_json::from_str::<TargetSymbolIndex>(&s)
        {
            let stem_lower = fname.trim_end_matches("Index.json").to_ascii_lowercase();
            let obj_lower = idx.obj_name.to_ascii_lowercase();
            let tgt_lower = idx
                .target
                .as_deref()
                .unwrap_or_default()
                .to_ascii_lowercase();
            if stem_lower == q_lower || obj_lower == q_lower || tgt_lower == q_lower {
                if idx.target.is_none() {
                    return Ok((p, idx));
                }
                candidates.push((p, idx));
            }
        }
    }
    if let Some(first) = candidates.into_iter().next() {
        return Ok(first);
    }
    bail!(
        "could not find `<Target>Index.json` matching `{target_query}` under {}",
        repo_root.display()
    )
}

fn resolve_code_bin_path(
    repo_root: &Path,
    idx_path: &Path,
    idx: &TargetSymbolIndex,
) -> Result<PathBuf> {
    let code_rel = Path::new(&idx.code_file);
    let stem = code_rel
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    let prefix = stem.strip_suffix("Code").unwrap_or(stem);
    let candidate = repo_root
        .join(code_rel.parent().unwrap_or_else(|| Path::new("")))
        .join(format!("{prefix}Obj.code.bin"));
    if candidate.is_file() {
        return Ok(candidate);
    }
    let sibling = idx_path.with_file_name(format!("{prefix}Obj.code.bin"));
    if sibling.is_file() {
        return Ok(sibling);
    }
    bail!(
        "could not find `.code.bin` at `{}` for `{}`",
        candidate.display(),
        idx.code_file
    )
}

fn find_function_in_index<'a>(
    idx: &'a TargetSymbolIndex,
    sym_query: &str,
) -> Result<&'a FunctionIndexEntry> {
    if let Some(exact) = idx.functions.iter().find(|f| f.name == sym_query) {
        return Ok(exact);
    }
    let mut matches: Vec<&FunctionIndexEntry> = idx
        .functions
        .iter()
        .filter(|f| {
            let leaf = f.name.rsplit("::").next().unwrap_or(&f.name);
            let no_obj = f.name.split(" [").next().unwrap_or(&f.name);
            let no_obj_leaf = no_obj.rsplit("::").next().unwrap_or(no_obj);
            leaf == sym_query
                || no_obj == sym_query
                || no_obj_leaf == sym_query
                || f.name.contains(sym_query)
        })
        .collect();
    if matches.len() == 1 {
        return Ok(matches.remove(0));
    }
    if matches.len() > 1 {
        if let Some(exact_base) = matches.iter().copied().find(|f| {
            let no_obj = f.name.split(" [").next().unwrap_or(&f.name);
            let no_obj_leaf = no_obj.rsplit("::").next().unwrap_or(no_obj);
            no_obj == sym_query || no_obj_leaf == sym_query
        }) {
            return Ok(exact_base);
        }
        let names: Vec<&str> = matches.iter().take(8).map(|f| f.name.as_str()).collect();
        bail!(
            "ambiguous symbol `{sym_query}` (matches: {}); specify a more exact name",
            names.join(", ")
        );
    }
    let available: Vec<&str> = idx
        .functions
        .iter()
        .take(10)
        .map(|f| f.name.as_str())
        .collect();
    bail!(
        "symbol `{sym_query}` not found in `{}` (examples: {})",
        idx.code_def,
        available.join(", ")
    )
}

fn parse_branch_overrides(specs: &[String]) -> Result<BTreeMap<u64, bool>> {
    let mut map = BTreeMap::new();
    for s in specs {
        if s.trim().is_empty() {
            continue;
        }
        let Some((off_str, val_str)) = s.split_once('=') else {
            bail!("invalid `--branches` entry `{s}` (expected `0xOFF=taken|fallthrough|T|F|1|0`)");
        };
        let off = parse_u64_lit(off_str.trim().trim_start_matches('+'))?;
        let take = match val_str.trim().to_ascii_lowercase().as_str() {
            "t" | "true" | "1" | "taken" | "yes" => true,
            "f" | "false" | "0" | "fallthrough" | "nt" | "no" => false,
            other => bail!("invalid branch decision `{other}` in `{s}`"),
        };
        map.insert(off, take);
    }
    Ok(map)
}

fn parse_init_overrides(specs: &[String]) -> Result<Vec<(u8, SymExpr)>> {
    let mut out = Vec::new();
    for s in specs {
        if s.trim().is_empty() {
            continue;
        }
        let Some((reg_str, val_str)) = s.split_once('=') else {
            bail!("invalid `--init` entry `{s}` (expected `xN=0xVAL` or `x29=sp-0x20`)");
        };
        let r_trim = reg_str.trim().to_ascii_lowercase();
        let reg_idx: u8 = if r_trim == "sp" {
            31
        } else if let Some(num) = r_trim
            .strip_prefix('x')
            .or_else(|| r_trim.strip_prefix('w'))
        {
            num.parse::<u8>()
                .with_context(|| format!("invalid register `{reg_str}`"))?
        } else {
            bail!("invalid register `{reg_str}`");
        };
        let v_trim = val_str.trim();
        let expr = if let Ok(c) = parse_u64_lit(v_trim) {
            SymExpr::Const(c)
        } else if let Some((base, sub)) = v_trim.split_once('-')
            && base.trim() == "sp"
            && let Ok(d) = parse_u64_lit(sub.trim())
        {
            SymExpr::InitReg(31).sub_const(d)
        } else if let Some((base, add)) = v_trim.split_once('+')
            && base.trim() == "sp"
            && let Ok(d) = parse_u64_lit(add.trim())
        {
            SymExpr::InitReg(31).add_const(d)
        } else {
            SymExpr::Unary {
                desc: v_trim.to_string(),
            }
        };
        out.push((reg_idx, expr));
    }
    Ok(out)
}

pub fn run_symexec(args: &SymexecArgs) -> Result<String> {
    let start_off = parse_u64_lit(args.from.trim().trim_start_matches('+'))?;
    let mut stop_offs = BTreeSet::new();
    for t in &args.to {
        if !t.trim().is_empty() {
            stop_offs.insert(parse_u64_lit(t.trim().trim_start_matches('+'))?);
        }
    }
    let forced_branches = parse_branch_overrides(&args.branches)?;
    let init_overrides = parse_init_overrides(&args.init)?;

    let report = if let Some(hex_str) = &args.hex {
        let mut bytes = Vec::new();
        for tok in hex_str.split(|c: char| c.is_whitespace() || c == ',') {
            if tok.is_empty() {
                continue;
            }
            let w = parse_u32_lit(tok)?;
            bytes.extend_from_slice(&w.to_le_bytes());
        }
        analyze_and_execute_with_limits(
            args.symbol.as_deref().unwrap_or("<hex>"),
            0,
            &bytes,
            None,
            start_off,
            &stop_offs,
            &forced_branches,
            &init_overrides,
            args.max_steps,
            args.max_paths,
            args.max_expr_nodes,
        )?
    } else {
        let target_q = args
            .target
            .as_deref()
            .ok_or_else(|| anyhow!("missing `<TARGET>` (or pass `--hex \"...\"`)"))?;
        let sym_q = args
            .symbol
            .as_deref()
            .ok_or_else(|| anyhow!("missing `<SYMBOL>` (or pass `--hex \"...\"`)"))?;
        let repo_root = crate::untrusted_lemmas::index::default_repo_root();
        let (idx_path, idx) = resolve_target_index(&repo_root, target_q)?;
        let fn_entry = find_function_in_index(&idx, sym_q)?;
        let code_bin_path = resolve_code_bin_path(&repo_root, &idx_path, &idx)?;
        let code = fs::read(&code_bin_path)
            .with_context(|| format!("failed to read `{}`", code_bin_path.display()))?;
        let start = fn_entry.offset as usize;
        let end = start + (fn_entry.size_bytes as usize);
        if end > code.len() {
            bail!(
                "function `{}` span {}..{} exceeds `{}` length {}",
                fn_entry.name,
                start,
                end,
                code_bin_path.display(),
                code.len()
            );
        }
        let mut report = analyze_and_execute_with_limits(
            &fn_entry.name,
            fn_entry.offset,
            &code[start..end],
            Some(fn_entry),
            start_off,
            &stop_offs,
            &forced_branches,
            &init_overrides,
            args.max_steps,
            args.max_paths,
            args.max_expr_nodes,
        )?;
        report.source = fn_entry
            .dwarf
            .as_ref()
            .map(|d| super::source::annotate(d, &idx.dwarf_types, &report));
        report
    };

    if args.block_hints || args.block_hints_json {
        let hints = block_hints_report(&report);
        return Ok(if args.block_hints_json {
            serde_json::to_string_pretty(&hints)?
        } else {
            format_block_hints_text(&hints)
        });
    }

    let mut out = if args.json {
        serde_json::to_string_pretty(&report)?
    } else {
        format_report_text(&report)
    };
    if args.max_output_bytes > 0 && out.len() > args.max_output_bytes {
        if args.json {
            let orig_bytes = out.len();
            out = serde_json::to_string_pretty(&serde_json::json!({
                "symbol": report.symbol,
                "fn_offset": report.fn_offset,
                "fn_offset_hex": report.fn_offset_hex,
                "size_bytes": report.size_bytes,
                "truncated_output": true,
                "max_output_bytes": args.max_output_bytes,
                "original_output_bytes": orig_bytes,
                "paths_explored": report.snapshots.len(),
            }))?;
        } else {
            let mut cut = args.max_output_bytes;
            while cut > 0 && !out.is_char_boundary(cut) {
                cut -= 1;
            }
            out.truncate(cut);
            out.push_str(&format!(
                "\n... [symexec output truncated at --max-output-bytes={}]\n",
                args.max_output_bytes
            ));
        }
    }
    Ok(out)
}

pub fn run_symexec_cli(raw_args: &[String]) -> ExitCode {
    let mut argv = Vec::with_capacity(raw_args.len() + 1);
    argv.push("rust-obj2lean symexec".to_string());
    argv.extend(raw_args.iter().cloned());
    let args = match SymexecArgs::try_parse_from(argv) {
        Ok(a) => a,
        Err(e) => {
            let _ = e.print();
            return if e.use_stderr() {
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            };
        }
    };
    match run_symexec(&args) {
        Ok(out) => {
            print!("{out}");
            if !out.ends_with('\n') {
                println!();
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
    }
}
