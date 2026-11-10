// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Symbolic Execution Report Schema and Human/JSON Formatter (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (CLI argument struct, report types, and output formatter for
//!   `rust-obj2lean symexec` / `lean-sig symexec`).
//! - **Purpose:** Defines the CLI options ([`SymexecArgs`]) and serializable report structures
//!   ([`SymexecReport`], [`PathSnapshot`], [`StackSlotSummary`], [`DisasmLine`]) and renders
//!   human-readable proof advice (frame size, stack slots, disassembly, per-path register/memory
//!   post-states, and `wp_step_to` / `wp_call_fn` hints).
//!
//! # Key Types & Functions
//! - [`SymexecArgs`]: `clap` CLI arguments (`target`, `symbol`, `--hex`, `--from`, `--to`,
//!   `--branches`, `--init`, `--max-steps`, `--max-paths`, `--json`, `--block-hints`,
//!   `--block-hints-json`).
//! - [`SymexecReport`], [`PathSnapshot`], [`StackSlotSummary`], [`DisasmLine`]: Report schema
//!   (per-path block hints live in `SymexecReport::block_hints`; format in `hints.rs`).
//! - [`format_report_text`]: Formats [`SymexecReport`] into human-readable proof advice.
//!
//! # When to Read This File
//! - Read this file when adding CLI flags to `symexec` or changing the JSON/text report layout.

use std::collections::BTreeMap;

use clap::Parser;
use serde::Serialize;

use super::state::{BranchRecord, CallSiteRecord, MemAccessRecord};

#[derive(Parser, Debug, Clone)]
#[command(
    name = "rust-obj2lean symexec",
    about = "Fast untrusted ARM64 symbolic execution advisor (100% outside TCB)",
    after_help = "Examples:\n  .agents/skills/lean-signatures/lean-symexec MyLib my_func\n  .agents/skills/lean-signatures/lean-symexec MyLib my_func --from 0x10 --to 0x48 --branches 0x24=taken\n  .agents/skills/lean-signatures/lean-symexec --hex \"0xd10083ff 0xf9000fe0 0x910083ff 0xd65f03c0\"\n  .agents/skills/lean-signatures/lean-symexec MyLib my_func --block-hints"
)]
pub struct SymexecArgs {
    /// Target name or path to `<Target>Index.json` (e.g. `MyLib` or `path/to/MyLibIndex.json`).
    /// Omit when using `--hex`.
    pub target: Option<String>,

    /// Function symbol name (or substring) within the target. Omit when using `--hex`.
    pub symbol: Option<String>,

    /// Raw whitespace- or comma-separated 32-bit hex instruction words (e.g. `"0xd10083ff 0xd65f03c0"`).
    #[arg(long)]
    pub hex: Option<String>,

    /// Start symbolic execution at function-relative byte offset (default `0x0`).
    #[arg(long, default_value = "0x0")]
    pub from: String,

    /// Stop/report symbolic state at these function-relative byte offsets (comma-separated or repeated).
    #[arg(long, value_delimiter = ',')]
    pub to: Vec<String>,

    /// Force branch outcomes at specific function-relative offsets (`0xOFF=taken|fallthrough|T|F|1|0`).
    #[arg(long, value_delimiter = ',')]
    pub branches: Vec<String>,

    /// Initial symbolic register overrides (`x0=0x10`, `x29=sp-0x20`).
    #[arg(long, value_delimiter = ',')]
    pub init: Vec<String>,

    /// Maximum instructions to step along a single path (default `256`).
    #[arg(long, default_value_t = 256)]
    pub max_steps: usize,

    /// Maximum paths to explore across acyclic branches (default `16`).
    #[arg(long, default_value_t = 16)]
    pub max_paths: usize,

    /// Maximum AST nodes per symbolic expression before truncation (default `5000`).
    #[arg(long, default_value_t = 5000)]
    pub max_expr_nodes: usize,

    /// Maximum output size in bytes before truncation (default `2097152` = 2 MiB).
    #[arg(long, default_value_t = 2_097_152)]
    pub max_output_bytes: usize,

    /// Emit machine-readable JSON output.
    #[arg(long)]
    pub json: bool,

    /// Emit per-path block-hint certificates (version-1 line-oriented text; see `hints.rs`)
    /// instead of the human report.
    #[arg(long, conflicts_with = "json")]
    pub block_hints: bool,

    /// Emit the per-path block-hint certificates as JSON.
    #[arg(long, conflicts_with_all = ["json", "block_hints"])]
    pub block_hints_json: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StackSlotSummary {
    /// Signed offset relative to entry `sp` (e.g. `-32` for `sp - 0x20#64`).
    pub sp_offset: i64,
    pub addr_lean: String,
    pub width_bits: u32,
    pub width_bytes: u64,
    pub points_to_op: &'static str,
    pub first_written_by: Option<String>,
    pub final_values: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PathSnapshot {
    pub label: String,
    pub at_offset: u64,
    pub at_offset_hex: String,
    pub steps: usize,
    pub path_conditions: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub let_bindings: Vec<(String, String)>,
    pub modified_regs: BTreeMap<String, String>,
    pub modified_mem: BTreeMap<String, String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DisasmLine {
    pub offset: u64,
    pub offset_hex: String,
    pub word_hex: String,
    pub lean_instr: String,
    pub is_block_leader: bool,
    pub is_loop_header: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct SymexecReport {
    pub symbol: String,
    pub fn_offset: u64,
    pub fn_offset_hex: String,
    pub size_bytes: u64,
    pub size_insns: u64,
    pub prologue_frame_bytes: Option<u64>,
    pub fn_off_lemma: Option<String>,
    pub fn_size_lemma: Option<String>,
    pub frame_bytes_lemma: Option<String>,
    pub loop_headers: Vec<String>,
    pub instructions: Vec<DisasmLine>,
    pub branches: Vec<BranchRecord>,
    pub calls: Vec<CallSiteRecord>,
    pub stack_slots: Vec<StackSlotSummary>,
    pub non_stack_accesses: Vec<MemAccessRecord>,
    pub snapshots: Vec<PathSnapshot>,
    /// DWARF source annotations (when the index has DWARF for the function).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<super::source::SourceAnnotations>,
    /// Per-path block-hint streams, one per entry of `snapshots` that terminated a path
    /// (emitted only by `--block-hints` / `--block-hints-json`).
    #[serde(skip)]
    pub block_hints: Vec<super::hints::PathHints>,
}

pub fn format_report_text(r: &SymexecReport) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "=== Symbolic Execution Advice: `{}` (entry {}, {} bytes / {} insns) ===\n",
        r.symbol, r.fn_offset_hex, r.size_bytes, r.size_insns
    ));
    if let Some(fb) = r.prologue_frame_bytes {
        out.push_str(&format!(
            "Prologue Frame : {fb} bytes (0x{fb:x})  [fnOff: {}, fnSize: {}, frameBytes: {}]\n",
            r.fn_off_lemma.as_deref().unwrap_or("-"),
            r.fn_size_lemma.as_deref().unwrap_or("-"),
            r.frame_bytes_lemma.as_deref().unwrap_or("-"),
        ));
    }
    if !r.loop_headers.is_empty() {
        out.push_str(&format!(
            "Loop Headers   : {} (use `wp_loop` / `SepWPp.of_sepWP` cut at these offsets)\n",
            r.loop_headers.join(", ")
        ));
    }
    if let Some(src) = &r.source {
        let exact = if src.exact { "exact" } else { "approximate: -g code differs" };
        out.push_str(&format!("\n--- DWARF Source ({exact}) ---\n  {}  [{}]\n", src.signature, src.decl));
        for p in &src.params {
            out.push_str(&format!("  param {p}\n"));
        }
        for (off, vars) in &src.vars {
            out.push_str(&format!("  DWARF vars @ +0x{off:x}: {}\n", vars.join(", ")));
        }
        let leaders: Vec<String> = r
            .instructions
            .iter()
            .filter(|i| i.is_block_leader)
            .filter_map(|i| src.lines.get(&i.offset).map(|l| format!("+0x{:x} {l}", i.offset)))
            .collect();
        if !leaders.is_empty() {
            out.push_str(&format!("  block leaders: {}\n", leaders.join(", ")));
        }
    }
    let note = |off: u64| r.source.as_ref().map(|s| s.note_at(off)).unwrap_or_default();

    // 1. Stack Frame Layout & `memRegion` Split Advice
    out.push_str("\n--- Stack Frame Slots (`sp`-relative) ---\n");
    if r.stack_slots.is_empty() {
        out.push_str("  (no stack slots accessed)\n");
    } else {
        for slot in &r.stack_slots {
            out.push_str(&format!(
                "  {} {} _   ({}B at sp{:+#x})  first store: {}\n",
                slot.addr_lean,
                slot.points_to_op,
                slot.width_bytes,
                slot.sp_offset,
                slot.first_written_by.as_deref().unwrap_or("read-only"),
            ));
        }
        // Compute gaps if prologue_frame_bytes > 0
        if let Some(fb) = r.prologue_frame_bytes
            && fb > 0
        {
            let mut cursor = -(fb as i64);
            let mut parts = Vec::new();
            for slot in &r.stack_slots {
                if slot.sp_offset < -(fb as i64) || slot.sp_offset >= 0 {
                    continue;
                }
                if slot.sp_offset > cursor {
                    let gap = (slot.sp_offset - cursor) as u64;
                    let gap_off = cursor.unsigned_abs();
                    parts.push(format!("memRegion (sp - 0x{gap_off:x}#64) {gap} _"));
                }
                parts.push(format!("({} {} _)", slot.addr_lean, slot.points_to_op));
                cursor = slot.sp_offset + (slot.width_bytes as i64);
            }
            if cursor < 0 {
                let gap = (-cursor) as u64;
                let gap_off = cursor.unsigned_abs();
                parts.push(format!("memRegion (sp - 0x{gap_off:x}#64) {gap} _"));
            }
            out.push_str(&format!(
                "  Suggested Frame Split: {}\n",
                parts.join(" ** ")
            ));
        }
    }

    // 2. Non-Stack Pointer Memory Accesses (Precondition Points-To Cells)
    if !r.non_stack_accesses.is_empty() {
        out.push_str("\n--- Pointer Memory Accesses (Precondition Cells) ---\n");
        for acc in &r.non_stack_accesses {
            let rw = if acc.is_store { "WRITE" } else { "READ " };
            out.push_str(&format!(
                "  +{:<6} [{}] {} {} {}{}\n",
                acc.insn_offset_hex,
                rw,
                acc.addr_lean,
                acc.points_to_op,
                acc.value_lean,
                note(acc.insn_offset)
            ));
        }
    }

    // 3. Conditional Branch Conditions (in Lean `BitVec` Syntax)
    if !r.branches.is_empty() {
        out.push_str("\n--- Branch Conditions (Lean `BitVec` Syntax) ---\n");
        for b in &r.branches {
            let loop_tag = if b.is_back_edge { " [LOOP BACK-EDGE]" } else { "" };
            out.push_str(&format!(
                "  +{:<6} ({}): if {} then +{} else +{}{}{}\n",
                b.insn_offset_hex,
                b.mnemonic,
                b.cond_lean,
                b.taken_offset_hex,
                b.fallthrough_offset_hex,
                loop_tag,
                note(b.insn_offset)
            ));
        }
    }

    // 4. Call Sites (`BL`) & Arguments
    if !r.calls.is_empty() {
        out.push_str("\n--- Call Sites (`BL` / Tail Calls) ---\n");
        for c in &r.calls {
            let kind = if c.is_tail_call {
                "tail-call"
            } else if c.is_extern {
                "extern-call"
            } else {
                "call"
            };
            let args_str: Vec<String> = c
                .args
                .iter()
                .map(|(k, v)| format!("{k} = {v}"))
                .collect();
            out.push_str(&format!(
                "  +{:<6} {} `{}` (sp = {}): {}{}\n",
                c.call_offset_hex,
                kind,
                c.callee,
                c.sp_lean,
                args_str.join(", "),
                note(c.call_offset)
            ));
        }
    }

    // 5. Symbolic Path States (at Cuts / Loop Entries / Returns)
    out.push_str("\n--- Symbolic Path States ---\n");
    for (idx, snap) in r.snapshots.iter().enumerate() {
        out.push_str(&format!(
            "  [Path #{}] {} at +{} ({} steps)\n",
            idx + 1,
            snap.label,
            snap.at_offset_hex,
            snap.steps
        ));
        if !snap.path_conditions.is_empty() {
            out.push_str(&format!(
                "    Path Cond : {}\n",
                snap.path_conditions.join(" ∧ ")
            ));
        }
        if !snap.let_bindings.is_empty() {
            for (name, expr) in &snap.let_bindings {
                out.push_str(&format!("    let {name} := {expr}\n"));
            }
        }
        if !snap.modified_regs.is_empty() {
            let regs_str: Vec<String> = snap
                .modified_regs
                .iter()
                .map(|(k, v)| format!("{k} := {v}"))
                .collect();
            out.push_str(&format!("    Regs      : {}\n", regs_str.join(", ")));
        }
        if !snap.modified_mem.is_empty() {
            let mem_str: Vec<String> = snap
                .modified_mem
                .iter()
                .map(|(k, v)| format!("{k} := {v}"))
                .collect();
            out.push_str(&format!("    Memory    : {}\n", mem_str.join(", ")));
        }
    }

    out
}
