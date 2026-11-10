// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! DWARF Source Annotations for `symexec` Reports (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (comments in proof advice only).
//! - **Purpose:** Given a function's [`DwarfFunctionInfo`] (from `*Index.json`, produced by the
//!   `-g` companion build in `untrusted_lemmas::dwarf`) and the index's struct layouts, computes
//!   [`SourceAnnotations`]: `file:line` (+ inlined-call chain) of block leaders, branches and
//!   calls; live DWARF variables at entry and at loop headers; and `param->field` names of
//!   pointer accesses whose symbolic base is a typed pointer parameter's entry register (`x0`),
//!   or a pointer loaded from a typed field of one (`mem₆₄[x0 + 0x8#64]` → `p->next->...`).
//! - When the function's code differs from the `-g` companion's (`exact == false`), lines and
//!   variable locations are approximate; this is shown in the report.
//!
//! # Key Types & Functions
//! - [`SourceAnnotations`], [`annotate`], [`SourceAnnotations::note_at`].
//!
//! # When to Read This File
//! - Read this file when `symexec` prints a wrong source line / field name.

use std::collections::BTreeMap;

use serde::Serialize;

use super::emit::SymexecReport;
use super::expr::SymExpr;
use crate::untrusted_lemmas::index_schema::{DwarfFunctionInfo, DwarfTypeLayout};

/// Source-level annotations of one `symexec` report.
#[derive(Clone, Debug, Default, Serialize)]
pub struct SourceAnnotations {
    /// `ret name(params)` from DWARF.
    pub signature: String,
    /// `file:line` of the declaration.
    pub decl: String,
    /// Whether lines/locations are exact for this code (see module docs).
    pub exact: bool,
    /// Entry ABI location of each parameter (`p = x0 (node_t *)`, `k : optimized out`).
    pub params: Vec<String>,
    /// `file:line [inlined from ...]` keyed by function-relative offset (leaders, branches, calls).
    pub lines: BTreeMap<u64, String>,
    /// Live variables (`name = location (type)`) at entry and loop headers, keyed by offset.
    pub vars: BTreeMap<u64, Vec<String>>,
    /// Field names of pointer accesses keyed by function-relative instruction offset.
    pub fields: BTreeMap<u64, String>,
}

impl SourceAnnotations {
    /// Comment suffix for an instruction at `off` (field name and/or source line), or `""`.
    pub fn note_at(&self, off: u64) -> String {
        let parts: Vec<&str> = [self.fields.get(&off), self.lines.get(&off)]
            .into_iter()
            .flatten()
            .map(String::as_str)
            .collect();
        if parts.is_empty() {
            String::new()
        } else {
            format!("  -- {}", parts.join(" @ "))
        }
    }
}

/// `file:line` (basename) of the line row covering `off`, with its inline chain.
fn line_at(d: &DwarfFunctionInfo, off: u64) -> Option<String> {
    let row = d.lines.iter().take_while(|l| l.offset <= off).last()?;
    let file = row.file.rsplit('/').next().unwrap_or(&row.file);
    let mut s = format!("{file}:{}", row.line);
    if !row.inlined.is_empty() {
        s.push_str(&format!(" [inlined: {}]", row.inlined.join(" <- ")));
    }
    Some(s)
}

/// Variables whose location range covers `off`.
fn vars_at(d: &DwarfFunctionInfo, off: u64) -> Vec<String> {
    let mut out = Vec::new();
    for v in &d.variables {
        for l in &v.locations {
            if l.start <= off && off < l.end {
                let from = if v.inlined_from.is_empty() {
                    String::new()
                } else {
                    format!(" [{}]", v.inlined_from)
                };
                out.push(format!("{} = {} ({}){from}", v.name, l.location, v.c_type));
            }
        }
    }
    out
}

/// Member of `layout` containing byte `off` (descending into nested aggregates), as `.a.b`.
fn field_path(
    layouts: &BTreeMap<String, DwarfTypeLayout>,
    layout: &DwarfTypeLayout,
    off: u64,
    depth: usize,
) -> Option<(String, String)> {
    let m = layout
        .members
        .iter()
        .rev()
        .find(|m| m.byte_offset <= off && off < m.byte_offset + m.byte_size.max(1))?;
    let rel = off - m.byte_offset;
    let name = if m.name.is_empty() {
        String::new()
    } else {
        format!(".{}", m.name)
    };
    if let Some(inner) = m.aggregate.as_ref().and_then(|a| layouts.get(a))
        && depth < 6
        && let Some((rest, p)) = field_path(layouts, inner, rel, depth + 1)
    {
        return Some((format!("{name}{rest}"), p));
    }
    let mut s = name;
    if let Some(es) = m.array_elem_size.filter(|&e| e > 0) {
        s.push_str(&format!("[{}]", rel / es));
    } else if rel != 0 {
        s.push_str(&format!("+{rel:#x}"));
    }
    Some((s, m.c_type.clone()))
}

/// Typed pointer bases: Lean rendering of a base expression → (C expression, pointee layout key).
fn typed_bases(
    d: &DwarfFunctionInfo,
    layouts: &BTreeMap<String, DwarfTypeLayout>,
) -> BTreeMap<String, (String, String)> {
    let mut out = BTreeMap::new();
    let mut work: Vec<(SymExpr, String, String, usize)> = Vec::new();
    for p in &d.params {
        let (Some(loc), Some(pt)) = (p.entry_location.as_deref(), p.pointee.as_ref()) else {
            continue;
        };
        if let Some(r) = loc
            .strip_prefix('x')
            .and_then(|n| n.parse::<u8>().ok())
            .filter(|r| *r < 31)
        {
            work.push((SymExpr::InitReg(r), p.name.clone(), pt.clone(), 0));
        }
    }
    while let Some((e, cexpr, key, depth)) = work.pop() {
        let lean = e.to_lean();
        if out.contains_key(&lean) {
            continue;
        }
        out.insert(lean.clone(), (cexpr.clone(), key.clone()));
        let Some(l) = layouts.get(&key) else { continue };
        if depth >= 2 {
            continue;
        }
        // Pointer members loaded from this base become typed bases themselves.
        for m in &l.members {
            if let Some(pt) = &m.pointee
                && m.byte_size == 8
                && !m.name.is_empty()
            {
                let loaded = SymExpr::InitMem {
                    base: lean.clone(),
                    offset: m.byte_offset as i64,
                    width_bits: 64,
                    addr: None,
                    prior_writes: Vec::new(),
                };
                work.push((
                    loaded,
                    format!("{cexpr}->{}", m.name),
                    pt.clone(),
                    depth + 1,
                ));
            }
        }
    }
    out
}

/// Annotations for `report` from the function's DWARF and the index's `layouts`.
pub fn annotate(
    d: &DwarfFunctionInfo,
    layouts: &[DwarfTypeLayout],
    report: &SymexecReport,
) -> SourceAnnotations {
    let layouts: BTreeMap<String, DwarfTypeLayout> = layouts
        .iter()
        .map(|l| (l.name.clone(), l.clone()))
        .collect();
    let mut a = SourceAnnotations {
        signature: d.signature(),
        decl: format!("{}:{}", d.decl_file, d.decl_line),
        exact: d.exact,
        ..Default::default()
    };
    for p in &d.params {
        a.params.push(match (&p.entry_location, p.optimized_out) {
            (Some(l), false) => format!("{} = {l} ({})", p.name, p.c_type),
            _ => format!("{} : optimized out ({})", p.name, p.c_type),
        });
    }
    let mut offs: Vec<u64> = report
        .instructions
        .iter()
        .filter(|i| i.is_block_leader)
        .map(|i| i.offset)
        .collect();
    offs.extend(report.branches.iter().map(|b| b.insn_offset));
    offs.extend(report.calls.iter().map(|c| c.call_offset));
    for off in offs {
        if let Some(l) = line_at(d, off) {
            a.lines.insert(off, l);
        }
    }
    let mut var_offs = vec![0u64];
    var_offs.extend(
        report
            .instructions
            .iter()
            .filter(|i| i.is_loop_header)
            .map(|i| i.offset),
    );
    for off in var_offs {
        let v = vars_at(d, off);
        if !v.is_empty() {
            a.vars.insert(off, v);
        }
    }
    let bases = typed_bases(d, &layouts);
    for acc in &report.non_stack_accesses {
        let Some((cexpr, key)) = bases.get(&acc.base) else {
            continue;
        };
        let Some(l) = layouts.get(key) else { continue };
        if acc.offset < 0 || acc.offset as u64 >= l.byte_size {
            continue;
        }
        if let Some((path, ty)) = field_path(&layouts, l, acc.offset as u64, 0) {
            let path = path
                .strip_prefix('.')
                .map_or(path.clone(), |p| format!("->{p}"));
            let path = if path.is_empty() {
                format!("*{cexpr}")
            } else {
                format!("{cexpr}{path}")
            };
            a.fields.insert(acc.insn_offset, format!("{path} : {ty}"));
        }
    }
    a
}
