// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Chunked kernel check of a linked single-block witness (`[placed] chunked_check`,
//! `ProofLib.Placed.SplitSingleFast`).
//!
//! One `decide +kernel` on `Obj.Interned.check` needs the kernel's peak memory for the whole
//! library at once, which grows past what a build machine has for a library with thousands of
//! names and hundreds of kilobytes of code. Here the witness is split into shard modules
//! ([`super::emit::assemble_split_witness`]), each one kernel fact that Lake checks in its own
//! Lean process:
//! - `Defs`: the interned library and layout, the ELF aliases, a balanced literal symbol tree
//!   `<p>Tree : VecTree SymSlot` (every name's pre-resolved slot, [`sym_tree_literal`]), a balanced
//!   literal names tree `<p>NamesTree : VecTree String` ([`names_tree_literal`]) and the segment
//!   lengths `<p>L_segLens := seg_lens% <elf>`;
//! - `LibEq`, `SegLens`: `rfl_kernel` facts equating the library with `<p>L.toLibT n <p>NamesTree`
//!   (names resolved through the names tree, `ProofLib.Placed.NamesTree`) and the segment lengths;
//! - `Names<k>`: the names tree holds the names of chunk `k` ([`names_bounds`]), and
//!   `<p>L_namesLen`: the names table has `n` entries;
//! - `Sym<k>`: the tree holds the right slot at every name index in chunk `k` ([`tree_bounds`]);
//! - `Text<k>`: the text walk through the tree over byte range `k`, cut where no relocation
//!   straddles the cut ([`text_bounds`]);
//! - `Data<k>`: the data walk over the objects of chunk `k`;
//! - `Chk*`: the cheap whole-library checks (names, ids, placeability, exports, disjointness).
//!
//! The main module proves `<p>_ok : <obj>Lib.Placeable pl ∧ <obj>Lib.InElf <elf> pl` from these
//! facts with `Obj.Interned.checkDisjoint_spec_chunksT` (no kernel evaluation of its own) and
//! assembles `<p>_linkedIn` from it.

use super::emit::{
    LinkedOut, RELOC_COST, WitNames, chunk_bounds, chunk_chain, chunk_names, chunk_ranges,
    doc_safe, interned_names, push_elf_aliases, push_interned_lib_and_layout,
};
use super::model::PLib;
use super::patch::PPlacement;
use crate::trusted_common::lean_string_lit;

/// Names per `Names<k>` chunk (an `rfl_kernel` comparison of tree names with literal names, about
/// 1 s per thousand names).
pub const NAMES_CHUNK_NAMES: usize = 4096;
/// Names per `Sym<k>` chunk (about 3.3 GB and 15 s of kernel time per chunk at a thousand
/// names).
pub const TREE_CHUNK_NAMES: usize = 1024;
/// Code words per `Text<k>` chunk (about 3 GB and 15 s of kernel time per chunk).
pub const TEXT_CHUNK_WORDS: u64 = 12 * 1024;
/// Kernel cost (data bytes and zero tails, relocations weighted by [`RELOC_COST`]) per `Data<k>`
/// chunk: a data walk resolves each relocation by name, so it costs more per unit than a text walk.
pub const DATA_CHUNK_COST: u64 = 8 * 1024;
/// Kernel-cost weight of one data object on top of its bytes and relocations (resolving its
/// address and finding its segment walk lists linear in the library's size).
pub const DATA_OBJ_COST: u64 = 96;

/// The interior boundaries of the `Sym<k>` chunks of `n` names: `ceil(n / TREE_CHUNK_NAMES)`
/// chunks of about equal size. Empty for a single chunk.
pub fn tree_bounds(n: usize) -> Vec<usize> {
    let k = n.div_ceil(TREE_CHUNK_NAMES).max(1);
    (1..k).map(|i| i * n / k).collect()
}

/// The interior boundaries `(o, prev, k)` of the `Text<k>` chunks of `lib`'s code: byte offset
/// `o`, the walk's `prev` flag there (always `false`: `o` is never right after a relocated word)
/// and the number `k` of relocations before `o`. `ceil(words / TEXT_CHUNK_WORDS)` chunks of about
/// equal size. Empty (one chunk) when the relocations are not strictly sorted by 4-aligned offset,
/// which is the order the walk consumes them in.
pub fn text_bounds(lib: &PLib) -> Vec<(u64, bool, usize)> {
    let code_len = lib.text.code.len() as u64;
    let relocs = &lib.text.relocs;
    let sorted = relocs.windows(2).all(|w| w[0].off < w[1].off);
    if !sorted || relocs.iter().any(|r| r.off % 4 != 0) {
        return Vec::new();
    }
    let n = (code_len / 4).div_ceil(TEXT_CHUNK_WORDS).max(1);
    let mut out: Vec<(u64, bool, usize)> = Vec::new();
    for i in 1..n {
        let mut o = (i * code_len / n) & !3;
        // `prev` is set only after a relocated word: move past any.
        while relocs
            .binary_search_by_key(&(o.wrapping_sub(4)), |r| r.off)
            .is_ok()
        {
            o += 4;
        }
        if o == 0 || o >= code_len || out.last().is_some_and(|&(p, _, _)| p >= o) {
            continue;
        }
        out.push((o, false, relocs.partition_point(|r| r.off < o)));
    }
    out
}

/// The interior boundaries of the `Data<k>` chunks of `lib`'s data objects ([`chunk_bounds`]).
pub fn data_bounds(lib: &PLib) -> Vec<usize> {
    let costs = lib.data.iter().map(|d| {
        DATA_OBJ_COST + d.bytes.len() as u64 + d.zero_tail + RELOC_COST * d.relocs.len() as u64
    });
    chunk_bounds(costs, DATA_CHUNK_COST)
}

/// The balanced literal `VecTree SymSlot` holding `mkSymSlot L ly i (ly.addrs.getD i 0#64)` at
/// every index `i` of the interned name table `tbl`: `⟨false, a, base + off⟩` for a block symbol
/// at offset `off` (the first entry of `L.symbols`, which is sorted by offset, so the least), and
/// `⟨true, a, a⟩` otherwise, where `a` is the layout's address of the name. Each node starts a
/// line, indented by its depth.
pub fn sym_tree_literal(lib: &PLib, pl: &PPlacement, tbl: &[String]) -> String {
    let mut off: std::collections::BTreeMap<&str, u64> = std::collections::BTreeMap::new();
    for (n, o) in &lib.text.symbols {
        off.entry(n.as_str())
            .and_modify(|m| *m = (*m).min(*o))
            .or_insert(*o);
    }
    let slot = |i: usize| {
        let a = pl.rho(&tbl[i]);
        match off.get(tbl[i].as_str()) {
            Some(&o) => format!("⟨false, {a:#x}#64, {:#x}#64⟩", pl.base.wrapping_add(o)),
            None => format!("⟨true, {a:#x}#64, {a:#x}#64⟩"),
        }
    };
    tree_literal(tbl.len(), &slot)
}

/// The balanced literal `VecTree String` holding name `i` of the interned name table `tbl` at
/// every index `i` (checked by the `Names*` facts, `Obj.Interned.NamesTreeOkChunks`).
pub fn names_tree_literal(tbl: &[String]) -> String {
    tree_literal(tbl.len(), &|i| lean_string_lit(&tbl[i]))
}

/// The interior boundaries of the `Names<k>` chunks of `n` names:
/// `ceil(n / NAMES_CHUNK_NAMES)` chunks of about equal size. Empty for a single chunk.
pub fn names_bounds(n: usize) -> Vec<usize> {
    let k = n.div_ceil(NAMES_CHUNK_NAMES).max(1);
    (1..k).map(|i| i * n / k).collect()
}

/// A balanced literal `VecTree` of `n` entries, entry `i` rendered by `slot`: each node
/// `(.node half left (slot mid) right)` starts a line, indented by its depth.
fn tree_literal(n: usize, slot: &dyn Fn(usize) -> String) -> String {
    fn build(lo: usize, hi: usize, depth: usize, slot: &dyn Fn(usize) -> String, s: &mut String) {
        if lo >= hi {
            s.push_str(".leaf");
            return;
        }
        let mid = lo + (hi - lo) / 2;
        s.push('\n');
        s.push_str(&"  ".repeat(depth + 1));
        s.push_str(&format!("(.node {} ", mid - lo));
        build(lo, mid, depth + 1, slot, s);
        s.push_str(&format!(" {} ", slot(mid)));
        build(mid + 1, hi, depth + 1, slot, s);
        s.push(')');
    }
    let mut s = String::new();
    build(0, n, 0, slot, &mut s);
    s
}

/// The cheap whole-library facts `(suffix, statement)` of a chunked witness, each its own
/// `Chk<Suffix>` shard: `<p>L_chk_<suffix> : <statement> = true`. `pdata` resolves symbols through
/// the symbol tree (`dataPlaceableTree`), which the main module turns back into
/// `dataPlaceableR` with the `Sym*` facts.
fn chk_facts(wn: &WitNames) -> Vec<(&'static str, String)> {
    let (lib_l, ly, name_chars) = (&wn.lib_l, &wn.ly, &wn.name_chars);
    vec![
        ("nodup", format!("Obj.Interned.namesNodup {name_chars}")),
        ("ids", format!("{lib_l}.idsOk")),
        ("ptext", format!("Obj.Interned.textPlaceableR {lib_l} {ly}")),
        (
            "pdata",
            format!("Obj.Interned.dataPlaceableTree {lib_l} {lib_l}Tree"),
        ),
        (
            "exports",
            format!(
                "Obj.Interned.exportsOk {lib_l} {ly} {name_chars} (ProofLib.ObjectLoad.prepareCharAssocVal {})",
                wn.elf_sym_chars
            ),
        ),
        (
            "ddisj",
            format!("Obj.Interned.dataDisjointROB {lib_l} {ly}"),
        ),
    ]
}

/// The name of the `Placeable ∧ InElf` theorem of a chunked witness (`<p>_ok` for an extra
/// witness, `<obj>Lib_ok` for the primary one).
pub fn ok_name(wn: &WitNames) -> String {
    wn.ok
        .clone()
        .unwrap_or_else(|| format!("{}_ok", wn.lib.lib))
}

/// The interned library and layout, the ELF aliases, the symbol tree and the chunked kernel facts
/// of a linked single-block witness, each in its part of `out` ([`LinkedOut::Split`]), and the
/// main module's `Placeable ∧ InElf` and `LinkedIn` theorems composing them.
pub(super) fn push_linked_chunked(
    out: &mut LinkedOut,
    lib: &PLib,
    pl: &PPlacement,
    wn: &WitNames,
    elf_rel: &str,
) {
    let (lib_l, ly, elf, lib_eq) = (&wn.lib_l, &wn.ly, &wn.elf, &wn.lib_eq);
    let lib_name = &wn.lib.lib;
    let tree = format!("{lib_l}Tree");
    let names_tree = format!("{lib_l}NamesTree");
    let seg_lens = format!("{lib_l}_segLens");
    let tbl = interned_names(lib);
    let l = out.part("Defs");
    l.extend([
        "open Arm64.Process ProofLib.ProgramReflection".into(),
        String::new(),
    ]);
    push_interned_lib_and_layout(l, lib, pl, wn, false);
    push_elf_aliases(l, wn, elf_rel);
    l.extend([
        format!("/-- The pre-resolved symbol slot of every name of `{lib_l}`, checked by the `Sym*` facts. -/"),
        format!(
            "noncomputable def {tree} : Obj.Interned.VecTree Obj.Interned.SymSlot :={}",
            sym_tree_literal(lib, pl, &tbl)
        ),
        String::new(),
        format!("/-- The names of `{lib_l}` as a balanced tree, checked by the `Names*` facts. -/"),
        format!(
            "noncomputable def {names_tree} : Obj.Interned.VecTree String :={}",
            names_tree_literal(&tbl)
        ),
        String::new(),
        format!("/-- The byte lengths of the segments of `{elf}`. -/"),
        format!("noncomputable def {seg_lens} : List Nat := seg_lens% {elf}"),
        String::new(),
    ]);
    let n_names = tbl.len();
    out.part("LibEq").extend([
        format!(
            "theorem {lib_eq} : {lib_name} = {lib_l}.toLibT {n_names} {names_tree} := by rfl_kernel"
        ),
        String::new(),
        format!(
            "theorem {lib_l}_namesLen : ProofLib.Placed.Split.rLen {lib_l}.names = {n_names} := by rfl_kernel"
        ),
        String::new(),
    ]);
    let nb = names_bounds(n_names);
    for (k, (s, t)) in chunk_ranges(&nb).into_iter().enumerate() {
        let (part, name) = chunk_names("Names", &format!("{lib_l}_namesTree"), k, nb.len());
        let stmt = match t {
            Some(t) => format!(
                "Obj.Interned.namesFrom {names_tree} ({t} - {s}) {s} = ProofLib.Placed.Split.rTake ({t} - {s}) (ProofLib.Placed.Split.rDrop {s} {lib_l}.names)"
            ),
            None => format!(
                "Obj.Interned.namesFrom {names_tree} ({n_names} - {s}) {s} = ProofLib.Placed.Split.rDrop {s} {lib_l}.names"
            ),
        };
        out.part(&part).extend([
            format!("theorem {name} :"),
            format!("    {stmt} := by rfl_kernel"),
            String::new(),
        ]);
    }
    out.part("SegLens").extend([
        format!(
            "theorem {seg_lens}_eq : {elf}.segments.map (fun r => ProofLib.Placed.Split.rLen r.bytes) = {seg_lens} := by rfl_kernel"
        ),
        String::new(),
    ]);
    let rl = format!("({elf}.segments.zip {seg_lens})");
    let fact = |part: &str, name: String, stmt: String, out: &mut LinkedOut| {
        out.part(part).extend([
            format!("theorem {name} : {stmt} = true := by decide +kernel"),
            String::new(),
        ]);
    };
    let sb = tree_bounds(tbl.len());
    for (k, (s, t)) in chunk_ranges(&sb).into_iter().enumerate() {
        let (part, name) = chunk_names("Sym", &format!("{lib_l}_sym"), k, sb.len());
        let stmt = match t {
            Some(t) => format!("Obj.Interned.symTreeOkChunk {lib_l} {ly} {tree} {s} {t}"),
            None => format!("Obj.Interned.symTreeOkTail {lib_l} {ly} {tree} {s}"),
        };
        fact(&part, name, stmt, out);
    }
    let tb = text_bounds(lib);
    let mut from = (0u64, false, 0usize);
    for k in 0..=tb.len() {
        let (part, name) = chunk_names("Text", &format!("{lib_l}_text"), k, tb.len());
        let (o, p, r) = from;
        let stmt = match tb.get(k) {
            Some(&(o2, p2, r2)) => {
                from = (o2, p2, r2);
                format!(
                    "Obj.Interned.textOkChunkT {lib_l} {ly} {tree} {rl} {o:#x} {p} {r} {o2:#x} {p2} {r2}"
                )
            }
            None => format!("Obj.Interned.textOkTailT {lib_l} {ly} {tree} {rl} {o:#x} {p} {r}"),
        };
        fact(&part, name, stmt, out);
    }
    let db = data_bounds(lib);
    for (k, (s, t)) in chunk_ranges(&db).into_iter().enumerate() {
        let (part, name) = chunk_names("Data", &format!("{lib_l}_data"), k, db.len());
        let stmt = match t {
            Some(t) => format!("Obj.Interned.dataOkChunk {lib_l} {ly} {rl} {s} {t}"),
            None => format!("Obj.Interned.dataOkTail {lib_l} {ly} {rl} {s}"),
        };
        fact(&part, name, stmt, out);
    }
    let chks = chk_facts(wn);
    for (suffix, stmt) in &chks {
        let mut part = String::from("Chk");
        let mut cs = suffix.chars();
        part.extend(cs.next().map(|c| c.to_ascii_uppercase()));
        part.extend(cs);
        fact(&part, format!("{lib_l}_chk_{suffix}"), stmt.clone(), out);
    }
    push_main(
        out.part(""),
        lib,
        wn,
        elf_rel,
        [sb.len(), tb.len(), db.len(), nb.len()],
    );
}

/// The main module's theorems: `<ok> : <obj>Lib.Placeable pl ∧ <obj>Lib.InElf <elf> pl` from the
/// shard facts (`n` = the interior boundary counts of the `Sym`, `Text`, `Data` and `Names` chunks), and
/// `<linked_in> : <obj>Lib.LinkedIn <elf bytes>`.
fn push_main(l: &mut Vec<String>, lib: &PLib, wn: &WitNames, elf_rel: &str, n: [usize; 4]) {
    let (lib_l, ly, elf, lib_eq) = (&wn.lib_l, &wn.ly, &wn.elf, &wn.lib_eq);
    let (elf_parse, elf_syms, elf_bytes) = (&wn.elf_parse, &wn.elf_syms, &wn.elf_bytes);
    let lib_name = &wn.lib.lib;
    let ok = ok_name(wn);
    let pl_term = format!("({ly}.toPlacement {lib_l}.names)");
    let chain = |walk: &str, fact: &str, n: usize| {
        chunk_chain(
            &format!("Obj.Interned.{walk}"),
            &format!("{lib_l}_{fact}"),
            n,
        )
    };
    let chk = |s: &str| format!("{lib_l}_chk_{s}");
    l.extend([
        format!(
            "/-- `{}` is placeable at `{pl_term}` and placed there in `{elf}` (from the kernel facts of the",
            doc_safe(&lib.name)
        ),
        "    shard modules). -/".into(),
        format!("theorem {ok} : {lib_name}.Placeable {pl_term} ∧ {lib_name}.InElf {elf} {pl_term} := by"),
        format!(
            "  rw [{lib_eq}, Obj.Interned.Lib.toLibT_eq {lib_l}_namesLen {}]",
            chain("namesTreeOkChunks", "namesTree", n[3])
        ),
        format!("  have hst := {}", chain("symTreeOkChunks", "sym", n[0])),
        format!("  have hdp : Obj.Interned.dataPlaceableR {lib_l} {ly} = true :="),
        format!("    (Obj.Interned.dataPlaceableR_eq {lib_l} {ly}).trans"),
        format!(
            "      ((Obj.Interned.dataPlaceableTree_eq (Obj.Interned.Lib.idsOk_spec {}) (Obj.Interned.symTreeOk_of_chunks hst)).symm.trans {})",
            chk("ids"),
            chk("pdata")
        ),
        format!(
            "  have h := Obj.Interned.checkDisjoint_spec_chunksT {lib_l}_names {elf_syms}_eq {lib_l}_segLens_eq"
        ),
        format!("    {} {} {} hdp hst", chk("nodup"), chk("ids"), chk("ptext")),
        format!("    {}", chain("textOkChunksT", "text", n[1])),
        format!("    {}", chain("dataOkChunks", "data", n[2])),
        format!("    {} {}", chk("exports"), chk("ddisj")),
        "  exact ⟨h.1, h.2.1⟩".into(),
        String::new(),
        format!(
            "/-- `{}` is linked into the stock-linked ELF `{}` at `{}`. -/",
            doc_safe(&lib.name),
            doc_safe(elf_rel),
            wn.placement
        ),
        format!("theorem {} : {lib_name}.LinkedIn {elf_bytes} :=", wn.linked_in),
        format!("  ⟨_, {elf}, {elf_parse}, {ok}.1, {ok}.2⟩"),
        String::new(),
    ]);
}
