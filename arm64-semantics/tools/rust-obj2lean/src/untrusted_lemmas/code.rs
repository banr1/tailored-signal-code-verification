// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Untrusted `<ObjName>Code.lean` and per-target fetch/decode lemma renderer (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (all generated definitions and `@[simp, arm64_norm]` theorems
//!   are kernel-checked against `<objName>Image : Arm64.Obj.LinkedImage`).
//! - **Purpose:**
//!   1. Renders `<ObjName>Code.lean`: defines `<code> := <img>.toProgram`, `WordTree` reflection
//!      (`<code>_tree`, `<code>_fetch_at`, `<code>_fetch_rebase`), symbol/stub offset lemmas
//!      (`<code>_fnOff_0x<off>`, `<code>_stubOff_0x<off>`, `<code>_hookAtOff?_0x<off>`),
//!      layout-stable symbol-keyed constants (`<code>TextEnd`, `<code>_symOff_<sym>`,
//!      `<code>_symAddr_<sym>`, `<code>_hookOff_<sym>`, `<code>_hookAtOff?_<sym>`; see
//!      [`sanitize_symbol_ident`]), and
//!      function table / prologue frame lemmas (`<code>_fnSize_0x<off>`, `<code>_frameBytes_0x<off>`).
//!   2. Renders each target's lemma module: `<prog>_decode_0x<off>`, `<prog>_fetch_0x<off>`, and
//!      `register_fn_entry` attributes for all functions matching `lemma_allowlist`
//!      ([`register_fn_entry_lines`], also emitted in each shard and in `<ObjName>Code.lean`).
//!
//! # Key Types & Functions
//! - [`FuncRange`], [`func_ranges`], [`selected_function_symbols`]: Function range discovery.
//! - [`emit_code_lean_module`]: Generates `<ObjName>Code.lean`.
//! - [`emit_target_lean_module`]: Generates a target's `<Target>.lean` fetch/decode lemma file.
//!
//! # When to Read This File
//! - Read this file when changing the shape of generated `Code.lean` or per-target `.lean` lemmas,
//!   `WordTree` reflection boilerplate, or `register_fn_entry` emission.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::PathBuf;

use anyhow::Result;

use super::index::{FuncTableEntry, build_func_table, infer_prologue_frame};
use super::{lemma_patterns, name_selected};
use crate::trusted_common::{ObjObject, SecKind, SymKind, SymSection, lean_string_lit};
use crate::untrusted_legacy_linker::LinkedImage;
use crate::untrusted_driver::{ExportConfig, ExportTarget};

/// The linked image, as seen by the lemma generator.
type Canonical = LinkedImage;

/// A defined function in the linked code: name, offset, and size (from the symbol table).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncRange {
    pub name: String,
    pub off: u64,
    pub size: u64,
}

/// Defined `STT_FUNC` symbols in text sections, with their offsets in `li`, in object order.
pub fn func_ranges(objs: &[ObjObject], li: &LinkedImage) -> Vec<FuncRange> {
    let mut out = Vec::new();
    for (o, offs) in objs.iter().zip(&li.sec_off) {
        for s in &o.symbols {
            if s.kind != SymKind::Func {
                continue;
            }
            let SymSection::Sec(i) = s.sec else { continue };
            let is_text = o.sections.get(i).and_then(|sec| sec.kind()) == Some(SecKind::Text);
            if let (true, Some(off)) = (is_text, offs.get(i).copied().flatten()) {
                out.push(FuncRange {
                    name: s.name.clone(),
                    off: off + s.value,
                    size: s.size,
                });
            }
        }
    }
    out
}

/// Effective byte length of `<code>.code` in `<ObjName>Code.lean`.
fn code_len(cfg: &ExportConfig, canon: &Canonical) -> usize {
    if cfg.slice_stubs_in_code {
        text_end_offset(canon) as usize
    } else {
        canon.code.len()
    }
}

/// Whether the reflection helpers apply: `<code>.code` is a whole number of words.
fn has_word_tree(cfg: &ExportConfig, canon: &Canonical) -> bool {
    code_len(cfg, canon) % 4 == 0
}

/// Offset where `.text` ends and synthesized extern stubs begin (or `canon.code.len()` when
/// there are no stubs). All stubs sit at offsets `>= text_end_offset(canon)`.
pub(crate) fn text_end_offset(canon: &Canonical) -> u64 {
    canon
        .stubs
        .iter()
        .map(|(_, o)| *o)
        .min()
        .unwrap_or(canon.code.len() as u64)
}

/// Whether all symbol and stub names are distinct (needed by `fnOff_of_allFresh`).
fn names_unique(canon: &Canonical) -> bool {
    let mut seen = HashSet::new();
    canon
        .symbols
        .iter()
        .chain(&canon.stubs)
        .all(|(n, _)| seen.insert(n.as_str()))
}

/// Whether all stub offsets are distinct (needed by `hookAtOff?_of_stub`).
pub(crate) fn stub_offsets_unique(canon: &Canonical) -> bool {
    let mut seen = HashSet::new();
    canon.stubs.iter().all(|(_, o)| seen.insert(*o))
}

/// Sanitize a symbol name into a Lean identifier suffix (ASCII alphanumerics and `_`).
///
/// `.`, `$`, `@` become `_dot_`, `_dollar_`, `_at_`; any other character becomes `_`, with runs
/// of replacement underscores collapsed and trailing ones trimmed (so `helper [alpha]` becomes
/// `helper_alpha`). A result starting with a digit gets a leading `_` (so the suffix never looks
/// like a `0x<hex>` offset), and an empty result becomes `sym`.
pub(crate) fn sanitize_symbol_ident(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    // Whether `out` currently ends in a replacement (rather than a source) underscore.
    let mut after_repl = false;
    for ch in name.chars() {
        let repl = match ch {
            c if c.is_ascii_alphanumeric() || c == '_' => {
                out.push(c);
                after_repl = false;
                continue;
            }
            '.' => "dot_",
            '$' => "dollar_",
            '@' => "at_",
            _ => "",
        };
        if !after_repl {
            out.push('_');
        }
        out.push_str(repl);
        after_repl = true;
    }
    if after_repl {
        while out.ends_with('_') && !out.is_empty() {
            out.pop();
        }
    }
    if out.is_empty() {
        out.push_str("sym");
    }
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

/// Symbol-keyed identifier suffixes for `names`, in order: `None` for a repeated name (only the
/// first occurrence of a name gets a key), otherwise its [`sanitize_symbol_ident`], with `_1`,
/// `_2`, ... appended when distinct names sanitize to the same (or an already used) suffix.
pub(crate) fn symbol_keyed_idents<'a>(names: impl IntoIterator<Item = &'a str>) -> Vec<Option<String>> {
    let mut seen_names = HashSet::new();
    let mut used = HashSet::new();
    names
        .into_iter()
        .map(|name| {
            if !seen_names.insert(name) {
                return None;
            }
            let base = sanitize_symbol_ident(name);
            let mut key = base.clone();
            let mut i = 1;
            while !used.insert(key.clone()) {
                key = format!("{base}_{i}");
                i += 1;
            }
            Some(key)
        })
        .collect()
}

/// Whether `names` is strictly increasing in UTF-8 byte / `charListLt` order.
pub fn is_strict_sorted_names<'a>(mut names: impl Iterator<Item = &'a str>) -> bool {
    let Some(mut prev) = names.next() else {
        return true;
    };
    for curr in names {
        if prev.as_bytes() >= curr.as_bytes() {
            return false;
        }
        prev = curr;
    }
    true
}

/// Return `canon.symbols` paired with their index `k` in `canon.symbols`, ordered by original ELF
/// discovery order in `objs_slice` (falling back to `canon.symbols` order for synthetic tests).
///
/// This allows `canon.symbols` to be sorted in canonical strict UTF-8 byte order (for $O(n)$
/// `allFreshCharSymbols_of_strictSorted` checking in the Lean kernel) while preserving the exact
/// discovery-order `_fnOff_0x<off>_<i>` / `_fnSize_0x<off>_<i>` numbering for symbol aliases at
/// the same offset.
pub fn ordered_symbols<'a>(
    objs_slice: &[ObjObject],
    canon: &'a Canonical,
) -> Vec<(usize, &'a (String, u64))> {
    let mut by_name_off: std::collections::HashMap<(&str, u64), std::collections::VecDeque<usize>> =
        std::collections::HashMap::new();
    for (k, (name, off)) in canon.symbols.iter().enumerate() {
        by_name_off
            .entry((name.as_str(), *off))
            .or_default()
            .push_back(k);
    }
    let mut out = Vec::with_capacity(canon.symbols.len());
    let mut used = vec![false; canon.symbols.len()];
    for (o, offs) in objs_slice.iter().zip(&canon.sec_off) {
        for s in &o.symbols {
            if !matches!(s.kind, SymKind::Func | SymKind::Object) {
                continue;
            }
            let SymSection::Sec(i) = s.sec else { continue };
            let Some(off) = offs.get(i).copied().flatten() else {
                continue;
            };
            let at = off + s.value;
            if let Some(k) = by_name_off
                .get_mut(&(s.name.as_str(), at))
                .and_then(|q| q.pop_front())
            {
                used[k] = true;
                out.push((k, &canon.symbols[k]));
            }
        }
    }
    for (k, sym) in canon.symbols.iter().enumerate() {
        if !used[k] {
            out.push((k, sym));
        }
    }
    out
}

struct CodeModuleSections {
    syms_needs_sorted_import: bool,
    ft_needs_sorted_import: bool,
    obj_ft_needs_sorted_import: bool,
    has_wt: bool,
    names_are_unique: bool,
    total_leaf_items: usize,
    base_prog: Vec<String>,
    word_tree: Vec<String>,
    sym_abbrevs: Vec<String>,
    sym_pre_stubs_wf: Vec<String>,
    sym_post_stubs_wf: Vec<String>,
    stubs_wf_hdr: Vec<String>,
    stubs_offsets_fresh_hdr: Vec<String>,
    per_sym_items: Vec<Vec<String>>,
    per_stub_items: Vec<Vec<String>>,
    frame_abbrev: Vec<String>,
    ft_base: Vec<String>,
    per_ft_items: Vec<Vec<String>>,
    single_obj_ft: Vec<String>,
}

fn build_code_sections(
    cfg: &ExportConfig,
    objs_slice: &[ObjObject],
    canon: &Canonical,
) -> CodeModuleSections {
    let c = cfg.code_def_name();
    let img = cfg.image_def_name();
    let code_bytes_len = code_len(cfg, canon);
    let n_words = code_bytes_len / 4;
    let ft_entries = build_func_table(cfg, objs_slice, canon);
    let syms_strict_sorted = is_strict_sorted_names(canon.symbols.iter().map(|(n, _)| n.as_str()));
    let ft_strict_sorted = is_strict_sorted_names(ft_entries.iter().map(|e| e.name.as_str()));
    let obj_ft_strict_sorted = objs_slice
        .len()
        .eq(&1)
        .then(|| canon.objects.first())
        .flatten()
        .is_none_or(|o_info| {
            is_strict_sorted_names(
                o_info
                    .fns
                    .iter()
                    .map(|f| f.name.as_str())
                    .chain(o_info.call_fns.iter().map(|f| f.name.as_str())),
            )
        });
    let obj_fn_count = canon
        .objects
        .first()
        .map_or(0, |o| o.fns.len() + o.call_fns.len());
    // Proof term for `allFresh… = true`:
    // 1. O(N) `isStrictSorted` (`allFreshCharSymbols_of_strictSorted` / `allFreshCharAssoc_of_strictSorted`
    //    from `ProofLib.ProgramReflection`) whenever the table is in canonical strict order;
    // 2. O(N log N) `sortedFreshEntries` (`ProofLib.ProgramReflection.SortedFresh`) for multi-object
    //    or split tables with > `SORTED_FRESH_MIN_SYMBOLS` entries;
    // 3. Direct `by rfl_kernel` for small unsorted tables.
    let (fresh_syms_proof, syms_needs_sorted_import) = if syms_strict_sorted {
        ("allFreshCharSymbols_of_strictSorted (by rfl_kernel)", false)
    } else if uses_sorted_fresh(canon) {
        ("allFreshCharSymbols_of_sorted (by rfl_kernel)", true)
    } else {
        ("by rfl_kernel", false)
    };
    let (fresh_ft_proof, ft_needs_sorted_import) = if ft_strict_sorted {
        ("allFreshCharAssoc_of_strictSorted (by rfl_kernel)", false)
    } else if sorted_fresh_for_symbol_count(ft_entries.len()) {
        ("allFreshCharAssoc_of_sorted (by rfl_kernel)", true)
    } else {
        ("by rfl_kernel", false)
    };
    let (fresh_obj_ft_proof, obj_ft_needs_sorted_import) = if obj_ft_strict_sorted {
        ("allFreshCharAssoc_of_strictSorted (by rfl_kernel)", false)
    } else if sorted_fresh_for_symbol_count(obj_fn_count) {
        ("allFreshCharAssoc_of_sorted (by rfl_kernel)", true)
    } else {
        ("by rfl_kernel", false)
    };
    let mut base_prog: Vec<String> = Vec::new();
    let l = &mut base_prog;
    if cfg.slice_stubs_in_code {
        l.extend([
            format!(
                "/-- Offset where `.text` of `{c}` ends and extern stubs begin (the `.text` byte bound). \
                 Reference this instead of hardcoding the number: it shifts whenever the image changes. -/"
            ),
            format!("abbrev {c}TextEnd : Nat := {}", text_end_offset(canon)),
            String::new(),
            format!("/-- The canonical `.text` program of `{img}` (base 0, no hooks, excluding trailing extern stubs). -/"),
            format!("noncomputable def {c} : Program :="),
            format!("  {{ {img}.toProgram with code := {img}.code.take {c}TextEnd }}"),
            String::new(),
            format!(
                "theorem {c}_canonical : {{ {img}.toProgram with code := {img}.code.take {c}TextEnd }} = {c} := rfl"
            ),
            String::new(),
            format!("/-- Any `.text`-sliced image loaded from `{img}` is `{c}` rebased to `img.base`. -/"),
            format!(
                "theorem {c}_ofImage {{img : Obj.Image}} {{X O : String → Option (State → State)}}"
            ),
            format!("    (h : Obj.Loads {img} img) :"),
            format!(
                "    {{ Program.ofImage img X O with code := img.code.take {c}TextEnd }} = {c}.rebase img.base X O :="
            ),
            format!("  Program.ofImage_take_eq_rebase {c}_canonical h"),
            String::new(),
            format!(
                "/-- The `.text` code of any image loaded from `{img}` is loaded as `{c}` rebased to \
                 `img.base` (with any hooks). -/"
            ),
            format!(
                "theorem {c}_codeLoaded {{img : Obj.Image}} {{s : State}} {{X O : String → Option (State → State)}}"
            ),
            format!("    (h : Obj.Loads {img} img) (hL : img.Loaded s) :"),
            format!("    ({c}.rebase img.base X O).CodeLoaded s.mem :="),
            format!("  Program.codeLoaded_rebase_take_of_loaded {c}_canonical h hL"),
            String::new(),
        ]);
    } else {
        l.extend([
            format!("/-- The canonical program of `{img}` (base 0, no hooks). -/"),
            format!("noncomputable def {c} : Program := {img}.toProgram"),
            String::new(),
            format!(
                "/-- Offset where `.text` of `{c}` ends and extern stubs begin (the `.text` byte bound). \
                 Reference this instead of hardcoding the number: it shifts whenever the image changes. -/"
            ),
            format!("abbrev {c}TextEnd : Nat := {}", text_end_offset(canon)),
            String::new(),
            format!("theorem {c}_canonical : {img}.toProgram = {c} := rfl"),
            String::new(),
            format!("/-- Any image loaded from `{img}` is `{c}` rebased to `img.base`. -/"),
            format!(
                "theorem {c}_ofImage {{img : Obj.Image}} {{X O : String → Option (State → State)}}"
            ),
            format!("    (h : Obj.Loads {img} img) :"),
            format!("    Program.ofImage img X O = {c}.rebase img.base X O :="),
            format!("  Program.ofImage_eq_rebase {c}_canonical h"),
            String::new(),
            format!(
                "/-- The code of any image loaded from `{img}` is loaded as `{c}` rebased to `img.base` \
                 (with any hooks). -/"
            ),
            format!(
                "theorem {c}_codeLoaded {{img : Obj.Image}} {{s : State}} {{X O : String → Option (State → State)}}"
            ),
            format!("    (h : Obj.Loads {img} img) (hL : img.Loaded s) :"),
            format!("    ({c}.rebase img.base X O).CodeLoaded s.mem :="),
            format!("  Program.codeLoaded_rebase_of_loaded {c}_canonical h hL"),
            String::new(),
        ]);
    }

    let has_wt = has_word_tree(cfg, canon);
    let mut word_tree: Vec<String> = Vec::new();
    let l = &mut word_tree;
    if has_wt {
        let text_end = text_end_offset(canon);
        l.extend([
            "/-! ## Instruction fetch -/".into(),
            String::new(),
            format!("/-- `{c}.code` as a balanced tree of instruction words. -/"),
            format!("noncomputable def {c}_tree : WordTree := word_tree_of% {c}"),
            String::new(),
            format!("theorem {c}_code_eq : {c}.code = {c}_tree.toBytes := by rfl_kernel"),
            String::new(),
            format!("theorem {c}_tree_size : {c}_tree.checkSize? = some {n_words} := by rfl_kernel"),
            String::new(),
            format!("theorem {c}_noStubBefore : noStubBefore {text_end} {c}.stubs = true := by rfl_kernel"),
            String::new(),
            format!("/-- Fetch in `{c}` (base 0) at offset `off`. -/"),
            format!("theorem {c}_fetch_at {{off : Nat}} {{inst : Instr}}"),
            format!("    (h : {c}_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64 := by decide) :"),
            format!("    {c}.fetch (BitVec.ofNat 64 off) = some inst := by"),
            format!("  have h' := fetch_of_wordTree {n_words} {c}_code_eq {c}_tree_size h hoff"),
            format!("  rwa [show {c}.base = 0#64 from rfl, BitVec.zero_add] at h'"),
            String::new(),
            format!(
                "/-- Fetch at offset `off` of `{c}` loaded at any base `b` with hooks `X`, `O` that \
                 are absent at `off`."
            ),
            format!(
                "    Rewrite a loaded image to `{c}.rebase img.base X O` with `{c}_ofImage`. -/"
            ),
            format!("theorem {c}_fetch_rebase {{b : BitVec 64}} {{X O : String → Option (State → State)}}"),
            "    {off : Nat} {inst : Instr}".into(),
            format!("    (h : {c}_tree.fetchDecodeAt off = some inst)"),
            format!("    (hhook : ({c}.rebase b X O).hookAtOff? off = none)"),
            "    (hoff : off < 2 ^ 64 := by decide) :".into(),
            format!("    ({c}.rebase b X O).fetch (b + BitVec.ofNat 64 off) = some inst :="),
            format!(
                "  (Program.fetch_rebase_eq_of_hookAtOff? rfl (fun _ => rfl) (fun _ => rfl) hoff hhook).trans ({c}_fetch_at h hoff)"
            ),
            String::new(),
            format!(
                "/-- Fetch at `.text` offset `off < {text_end}` (before any extern stub) of `{c}` \
                 rebased to any base `b` with any extern hooks `X` and no overrides. -/"
            ),
            format!("theorem {c}_fetch_rebase_text {{b : BitVec 64}} {{X : String → Option (State → State)}}"),
            "    {off : Nat} {inst : Instr}".into(),
            format!("    (h : {c}_tree.fetchDecodeAt off = some inst)"),
            format!("    (htext : off < {text_end} := by decide)"),
            "    (hoff : off < 2 ^ 64 := by decide) :".into(),
            format!("    ({c}.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :="),
            format!(
                "  {c}_fetch_rebase h (hookAtOff?_eq_none_of_noStubBefore {c}_noStubBefore (fun _ => rfl) htext) hoff"
            ),
            String::new(),
            format!(
                "/-- Fetch at `fnAddr name + k` of `{c}` rebased to any base `b` with any extern \
                 hooks `H` and no overrides, for `.text` offset `off + k < {text_end}`. -/"
            ),
            format!("theorem {c}_fetch_fnAddr {{b : BitVec 64}} {{H : String → Option (State → State)}}"),
            "    {name : String} {off k : Nat} {inst : Instr}".into(),
            format!("    (hfn : {c}.fnOff name = off) (htext : off + k < {text_end})"),
            format!("    (h : {c}_tree.fetchDecodeAt (off + k) = some inst)"),
            "    (hoff : off + k < 2 ^ 64 := by decide) :".into(),
            format!("    ({c}.rebase b H).fetch (({c}.rebase b H).fnAddr name + BitVec.ofNat 64 k) = some inst :="),
            format!("  Program.fetch_fnAddr_add hfn ({c}_fetch_rebase_text h htext hoff)"),
            String::new(),
            format!("theorem {c}_fetch_fnAddr_entry {{b : BitVec 64}} {{H : String → Option (State → State)}}"),
            "    {name : String} {off : Nat} {inst : Instr}".into(),
            format!("    (hfn : {c}.fnOff name = off) (htext : off + 0 < {text_end})"),
            format!("    (h : {c}_tree.fetchDecodeAt (off + 0) = some inst)"),
            "    (hoff : off + 0 < 2 ^ 64 := by decide) :".into(),
            format!("    ({c}.rebase b H).fetch (({c}.rebase b H).fnAddr name) = some inst :="),
            format!("  Program.fetch_fnAddr_entry hfn ({c}_fetch_rebase_text h htext hoff)"),
            String::new(),
        ]);
    } else {
        l.extend([
            format!("-- `{c}.code` is not a whole number of instruction words; no fetch helpers."),
            String::new(),
        ]);
    }

    let ordered_syms = ordered_symbols(objs_slice, canon);
    let sym_keys = symbol_keyed_idents(ordered_syms.iter().map(|(_, (n, _))| n.as_str()));
    let stub_keys = symbol_keyed_idents(canon.stubs.iter().map(|(n, _)| n.as_str()));
    let mut sym_abbrevs: Vec<String> = Vec::new();
    let l = &mut sym_abbrevs;
    l.extend([
        "/-! ## Symbol-keyed offsets".into(),
        String::new(),
        "Stable names for symbol and stub offsets: reference these (rather than `0x<hex>` literals) so \
         proofs do not break when the image layout shifts. `_symAddr_` is the address at base 0."
            .into(),
        "-/".into(),
        String::new(),
    ]);
    for ((_, (name, off)), key) in ordered_syms.iter().zip(&sym_keys) {
        let Some(key) = key else { continue };
        l.push(format!("/-- `{}` -/", name.replace('`', "'").replace("-/", "- /")));
        l.push(format!("abbrev {c}_symOff_{key} : Nat := 0x{off:x}"));
        l.push(format!("abbrev {c}_symAddr_{key} : BitVec 64 := 0x{off:x}#64"));
    }
    for ((name, off), key) in canon.stubs.iter().zip(&stub_keys) {
        let Some(key) = key else { continue };
        l.push(format!("/-- `{}` (extern stub) -/", name.replace('`', "'").replace("-/", "- /")));
        l.push(format!("abbrev {c}_hookOff_{key} : Nat := 0x{off:x}"));
    }
    l.push(String::new());

    let names_are_unique = names_unique(canon);
    let mut sym_pre_stubs_wf: Vec<String> = Vec::new();
    let mut sym_post_stubs_wf: Vec<String> = Vec::new();
    let mut stubs_wf_hdr: Vec<String> = Vec::new();
    let mut stubs_offsets_fresh_hdr: Vec<String> = Vec::new();
    let mut per_sym_items: Vec<Vec<String>> = Vec::new();
    let mut per_stub_items: Vec<Vec<String>> = Vec::new();
    if names_are_unique {
        let emit_hook_at_off = !canon.stubs.is_empty() && stub_offsets_unique(canon);
        let l = &mut sym_pre_stubs_wf;
        l.extend([
            "/-! ## Symbol and stub offsets -/".into(),
            String::new(),
            format!("noncomputable def {c}_symChars : List (List Char × Nat) := sym_chars_of% {c}"),
            format!("noncomputable def {c}_stubChars : List (List Char × Nat) := stub_chars_of% {c}"),
        ]);
        if cfg.emit_symbol_unique_lemmas {
            l.extend([
                format!(
                    "noncomputable def {c}_symEnc : ProofLib.ObjectLoad.EncSymTable Nat := sym_enc_of% {c}"
                ),
                format!(
                    "noncomputable def {c}_stubEnc : ProofLib.ObjectLoad.EncSymTable Nat := stub_enc_of% {c}"
                ),
            ]);
        }
        l.extend([
            String::new(),
            format!("theorem {c}_symbols_eq : {c}.symbols = toStringSymbols {c}_symChars := by rfl_kernel"),
            format!("theorem {c}_stubs_eq : {c}.stubs = toStringSymbols {c}_stubChars := by rfl_kernel"),
        ]);
        if cfg.emit_symbol_unique_lemmas {
            l.extend([
                format!(
                    "theorem {c}_symEnc_eq : ProofLib.ObjectLoad.prepareCharAssocVal {c}_symChars = {c}_symEnc := by rfl_kernel"
                ),
                format!(
                    "theorem {c}_stubEnc_eq : ProofLib.ObjectLoad.prepareCharAssocVal {c}_stubChars = {c}_stubEnc := by rfl_kernel"
                ),
            ]);
        }
        l.push(format!(
            "theorem {c}_symbols_fresh : allFreshCharSymbols {c}_symChars = true := {fresh_syms_proof}"
        ));
        stubs_wf_hdr.push(format!(
            "theorem {c}_stubs_wf : wfStubCharSymbols {c}_stubChars {c}_symChars = true := by rfl_kernel"
        ));
        if cfg.emit_symbol_unique_lemmas {
            sym_post_stubs_wf.extend([
                format!(
                    "theorem {c}_lookup_eq_symEnc {{name : String}} {{cs : List Char}} (hname : name = String.ofList cs) :"
                ),
                format!(
                    "    Obj.lookup name {c}.symbols = ProofLib.ObjectLoad.lookupEnc (encodeCharKey cs) {c}_symEnc :="
                ),
                format!(
                    "  ProofLib.ObjectLoad.lookupSymbols_eq_lookupEnc {c}_symbols_eq {c}_symEnc_eq hname"
                ),
                format!(
                    "theorem {c}_lookupUnique_eq_symEnc {{name : String}} {{cs : List Char}} (hname : name = String.ofList cs) :"
                ),
                format!(
                    "    Obj.lookupUnique name {c}.symbols = ProofLib.ObjectLoad.lookupUniqueEnc (encodeCharKey cs) {c}_symEnc :="
                ),
                format!(
                    "  ProofLib.ObjectLoad.lookupUniqueSymbols_eq_lookupUniqueEnc {c}_symbols_eq {c}_symEnc_eq hname"
                ),
                format!(
                    "theorem {c}_filter_length_eq_symEnc {{name : String}} {{cs : List Char}} (hname : name = String.ofList cs) :"
                ),
                format!(
                    "    ({c}.symbols.filter (·.1 == name)).length = (ProofLib.ObjectLoad.filterEnc (encodeCharKey cs) {c}_symEnc).length :="
                ),
                format!(
                    "  ProofLib.ObjectLoad.filterSymbols_length_eq_filterEnc {c}_symbols_eq {c}_symEnc_eq hname"
                ),
            ]);
        }
        if emit_hook_at_off {
            stubs_offsets_fresh_hdr.push(format!(
                "theorem {c}_stubs_offsets_fresh : allFreshOffsets {c}.stubs = true := by rfl_kernel"
            ));
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
        for (k, (name, off)) in &ordered_syms {
            let mut item = Vec::new();
            let thm = uniq(format!("{c}_fnOff_0x{off:x}"));
            item.push(format!(
                "/-- `{}` -/",
                name.replace('`', "'").replace("-/", "- /")
            ));
            item.push(format!(
                "@[simp, arm64_norm] theorem {thm} : {c}.fnOff {} = {off} :=",
                lean_string_lit(name)
            ));
            item.push(format!(
                "  fnOff_of_allFresh {c}_symChars {c}_symbols_eq {c}_symbols_fresh {k} (by rfl_kernel)"
            ));
            if cfg.emit_symbol_unique_lemmas {
                let lookup_thm = uniq(format!("{c}_lookup_0x{off:x}"));
                item.push(format!(
                    "theorem {lookup_thm} : Obj.lookup {} {c}.symbols = some {off} :=",
                    lean_string_lit(name)
                ));
                item.push(format!(
                    "  lookup_of_allFresh {c}_symChars {c}_symbols_eq {c}_symbols_fresh {k} (by rfl_kernel)"
                ));
                let unique_thm = uniq(format!("{c}_unique_0x{off:x}"));
                item.push(format!(
                    "theorem {unique_thm} : Obj.lookupUnique {} {c}.symbols = some {off} :=",
                    lean_string_lit(name)
                ));
                item.push(format!(
                    "  lookupUnique_of_allFresh {c}_symChars {c}_symbols_eq {c}_symbols_fresh {k} (by rfl_kernel)"
                ));
            }
            per_sym_items.push(item);
        }
        for (k, (name, off)) in canon.stubs.iter().enumerate() {
            let mut item = Vec::new();
            let thm = uniq(format!("{c}_stubOff_0x{off:x}"));
            item.push(format!(
                "/-- `{}` (extern stub) -/",
                name.replace('`', "'").replace("-/", "- /")
            ));
            item.push(format!(
                "@[simp, arm64_norm] theorem {thm} : {c}.fnOff {} = {off} :=",
                lean_string_lit(name)
            ));
            item.push(format!(
                "  fnOff_of_stub {c}_symChars {c}_stubChars {c}_symbols_eq {c}_stubs_eq {c}_stubs_wf {k} \
                 (by rfl_kernel)"
            ));
            if emit_hook_at_off {
                let hook_thm = uniq(format!("{c}_hookAtOff?_0x{off:x}"));
                item.push(format!(
                    "@[simp, arm64_norm] theorem {hook_thm} {{b : BitVec 64}} (H : String → Option (State → State)) :"
                ));
                item.push(format!(
                    "    ({c}.rebase b H).hookAtOff? {off} = H {} :=",
                    lean_string_lit(name)
                ));
                item.push(format!(
                    "  hookAtOff?_of_stub (prog := {c}.rebase b H) {c}_stubs_offsets_fresh (fun _ => rfl) {k} \
                     (by rfl_kernel)"
                ));
                if let Some(key) = &stub_keys[k] {
                    let alias = uniq(format!("{c}_hookAtOff?_{key}"));
                    item.push(format!(
                        "theorem {alias} {{b : BitVec 64}} (H : String → Option (State → State)) :"
                    ));
                    item.push(format!(
                        "    ({c}.rebase b H).hookAtOff? {c}_hookOff_{key} = H {} :=",
                        lean_string_lit(name)
                    ));
                    item.push(format!("  {hook_thm} (b := b) H"));
                }
            }
            per_stub_items.push(item);
        }
    } else {
        sym_pre_stubs_wf.extend([
            "-- Symbol or stub names are not distinct; no `fnOff` lemmas.".into(),
            String::new(),
        ]);
    }
    let ft_names_unique = {
        let mut s = BTreeSet::new();
        ft_entries.iter().all(|e| s.insert(e.name.as_str()))
    };
    let frame_abbrev = vec![
        "/-! ## Function sizes and prologue stack frames -/".into(),
        String::new(),
        format!("/-- Stack frame of function `name` in `{img}` at stack pointer `sp`. -/"),
        format!("noncomputable abbrev {c}_frame (name : String) (sp : BitVec 64) : SepProp :="),
        format!("  stackFrameFor {img} name sp"),
        String::new(),
    ];
    let mut ft_base: Vec<String> = Vec::new();
    let mut per_ft_items: Vec<Vec<String>> = Vec::new();
    let mut single_obj_ft: Vec<String> = Vec::new();
    if !ft_entries.is_empty() && ft_names_unique {
        ft_base.extend([
            format!("noncomputable def {c}_funcTable : List (String × (Nat × Nat)) :="),
            format!("  Obj.funcTable {img}"),
            String::new(),
            format!("noncomputable def {c}_funcChars : List (List Char × (Nat × Nat)) :="),
            format!("  assoc_chars_of% {c}_funcTable"),
            String::new(),
            format!("theorem {c}_funcTable_eq : {c}_funcTable = toStringAssoc {c}_funcChars := by rfl_kernel"),
            String::new(),
            format!("theorem {c}_funcTable_fresh : allFreshCharAssoc {c}_funcChars = true := {fresh_ft_proof}"),
            String::new(),
        ]);
        let allowlist_patterns: Vec<_> = cfg
            .targets
            .iter()
            .flat_map(|t| lemma_patterns(t).unwrap_or_default())
            .collect();
        let use_wt = has_wt;
        let wt_fn_size_lemma = if cfg.slice_stubs_in_code {
            "fnSize_of_wordTree_take"
        } else {
            "fnSize_of_wordTree"
        };
        let wt_frame_lemma = if cfg.slice_stubs_in_code {
            "fnFrameBytes_of_wordTree_take"
        } else {
            "fnFrameBytes_of_wordTree"
        };
        for (k, entry) in ft_entries.iter().enumerate() {
            if !allowlist_patterns.is_empty() && !name_selected(&entry.name, &allowlist_patterns) {
                continue;
            }
            let mut item = Vec::new();
            let safe_name = entry.name.replace('`', "'").replace("-/", "- /");
            let entry_in_wt = use_wt
                && entry.off % 4 == 0
                && entry.span % 4 == 0
                && (entry.off + entry.span) as usize <= code_bytes_len;
            item.push(format!("/-- `{safe_name}` (size {} bytes) -/", entry.size));
            item.push(format!(
                "@[simp, arm64_norm, wp_norm] theorem {} : Obj.fnSize {img} {} = {} :=",
                entry.fn_size_lemma,
                lean_string_lit(&entry.name),
                entry.size
            ));
            if entry_in_wt {
                item.push(format!(
                    "  {wt_fn_size_lemma} {img} {c}_code_eq {c}_tree_size {c}_funcChars \
                     {c}_funcTable_eq {c}_funcTable_fresh {k} {} (by rfl_kernel) (by rfl_kernel)",
                    entry.size
                ));
            } else {
                item.push(format!(
                    "  fnSize_of_allFresh {img} {c}_funcChars {c}_funcTable_eq {c}_funcTable_fresh {k} {} \
                     (by rfl_kernel) (by rfl_kernel)",
                    entry.size
                ));
            }
            if let (Some(fb), Some(fb_lemma)) = (entry.frame_bytes, &entry.frame_bytes_lemma) {
                item.push(format!(
                    "/-- `{safe_name}` (prologue stack frame {fb} bytes) -/"
                ));
                item.push(format!(
                    "@[simp, arm64_norm, wp_norm] theorem {fb_lemma} : fnFrameBytes {img} {} = {fb} :=",
                    lean_string_lit(&entry.name)
                ));
                if entry_in_wt {
                    item.push(format!(
                        "  {wt_frame_lemma} {img} {c}_code_eq {c}_tree_size {c}_funcChars \
                         {c}_funcTable_eq {c}_funcTable_fresh {k} {fb} (by rfl_kernel) (by rfl_kernel)"
                    ));
                } else {
                    item.push(format!(
                        "  fnFrameBytes_of_allFresh {img} {c}_funcChars {c}_funcTable_eq {c}_funcTable_fresh {k} {fb} \
                         (by rfl_kernel) (by rfl_kernel)"
                    ));
                }
            }
            per_ft_items.push(item);
        }
        let l = &mut single_obj_ft;
        if objs_slice.len() == 1
            && let Some(o_info) = canon.objects.first()
            && (!o_info.fns.is_empty() || !o_info.call_fns.is_empty())
        {
            let obj_def = cfg.obj_def_name_for(&o_info.name, 1);
            l.extend([
                String::new(),
                format!("noncomputable def {obj_def}_funcTable : List (String × List (BitVec 8)) :="),
                format!("  {obj_def}.funcTable"),
                String::new(),
                format!("noncomputable def {obj_def}_funcChars : List (List Char × List (BitVec 8)) :="),
                format!("  assoc_chars_of% {obj_def}_funcTable"),
                String::new(),
                format!(
                    "theorem {obj_def}_funcTable_eq : {obj_def}_funcTable = toStringAssoc {obj_def}_funcChars := by rfl_kernel"
                ),
                String::new(),
                format!(
                    "theorem {obj_def}_funcTable_fresh : allFreshCharAssoc {obj_def}_funcChars = true := {fresh_obj_ft_proof}"
                ),
                String::new(),
            ]);
            let mut obj_used = BTreeSet::new();
            let mut uniq_obj = |base: String| {
                let mut name = base.clone();
                let mut i = 1;
                while !obj_used.insert(name.clone()) {
                    name = format!("{base}_{i}");
                    i += 1;
                }
                name
            };
            let obj_fns = o_info
                .fns
                .iter()
                .map(|f| (&f.name, f.off, f.size))
                .chain(o_info.call_fns.iter().map(|f| (&f.name, f.off, f.size)));
            for (idx, (fn_name, fn_off, fn_size)) in obj_fns.enumerate() {
                if !allowlist_patterns.is_empty() && !name_selected(fn_name, &allowlist_patterns) {
                    continue;
                }
                let start = (fn_off as usize).min(canon.code.len());
                let end = start.saturating_add(fn_size as usize).min(canon.code.len());
                if let Some(fb) = infer_prologue_frame(&canon.code[start..end]) {
                    let obj_fb_lemma = uniq_obj(format!("{obj_def}_frameBytes_0x{fn_off:x}"));
                    l.push(format!(
                        "@[simp, arm64_norm, wp_norm] theorem {obj_fb_lemma} : fnFrameBytes {obj_def} {} = {fb} :=",
                        lean_string_lit(fn_name)
                    ));
                    l.push(format!(
                        "  objectInfo_fnFrameBytes_of_allFresh {obj_def} {obj_def}_funcChars {obj_def}_funcTable_eq \
                         {obj_def}_funcTable_fresh {idx} {fb} (by rfl_kernel) (by rfl_kernel)"
                    ));
                }
            }
        }
    }
    let total_leaf_items = per_sym_items.len() + per_stub_items.len() + per_ft_items.len();
    CodeModuleSections {
        syms_needs_sorted_import,
        ft_needs_sorted_import,
        obj_ft_needs_sorted_import,
        has_wt,
        names_are_unique,
        total_leaf_items,
        base_prog,
        word_tree,
        sym_abbrevs,
        sym_pre_stubs_wf,
        sym_post_stubs_wf,
        stubs_wf_hdr,
        stubs_offsets_fresh_hdr,
        per_sym_items,
        per_stub_items,
        frame_abbrev,
        ft_base,
        per_ft_items,
        single_obj_ft,
    }
}

/// Render the `Code` module of `cfg` as a single file, ending with `registrations` (the
/// `register_fn_entry` commands of every target, see [`register_fn_entry_lines`]), so importing the
/// `Code` module alone populates `fnEntryExt`.
pub fn render_code_module(
    cfg: &ExportConfig,
    objs_slice: &[ObjObject],
    canon: &Canonical,
    registrations: &[String],
) -> String {
    let c = cfg.code_def_name();
    let img = cfg.image_def_name();
    let ns = &cfg.namespace_prefix;
    let s = build_code_sections(cfg, objs_slice, canon);
    let needs_sorted_fresh_import =
        s.syms_needs_sorted_import || s.ft_needs_sorted_import || s.obj_ft_needs_sorted_import;
    let mut l: Vec<String> = vec![
        "module".into(),
        String::new(),
        format!("public import {}", cfg.obj_module),
        "public import ProofLib.ObjectLoad".into(),
        "public import ProofLib.ProgramReflection".into(),
    ];
    if needs_sorted_fresh_import {
        l.push("public import ProofLib.ProgramReflection.SortedFresh".into());
    }
    l.extend([
        "public import ProofLib.SimpAttrs".into(),
        String::new(),
        format!("/-! # Canonical code of {}", cfg.title.replace("-/", "- /")),
        String::new(),
        "Generated by `rust-obj2lean` (untrusted: every theorem is checked by the kernel).".into(),
        "DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "`{c}` is the base-independent part of the linked image `{img}`: its code at base 0, \
             its symbol offsets, and its stub offsets. For any image `img` loaded from `{img}`,"
        ),
        format!(
            "`Program.ofImage img X O = {c}.rebase img.base X O` (`{c}_ofImage h`), and \
             `{c}_codeLoaded h hL` discharges the `CodeLoaded` premise of Hoare judgments about \
             `{c}.rebase img.base X O` from `hL : img.Loaded s`."
        ),
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64 ProofLib.ProgramReflection".into(),
        String::new(),
        "set_option Elab.async false".into(),
        "set_option maxHeartbeats 0".into(),
        "set_option maxRecDepth 2000000".into(),
        String::new(),
    ]);
    l.extend(s.base_prog);
    l.extend(s.word_tree);
    l.extend(s.sym_abbrevs);
    l.extend(s.sym_pre_stubs_wf);
    if s.names_are_unique {
        l.extend(s.stubs_wf_hdr);
        l.extend(s.sym_post_stubs_wf);
        l.extend(s.stubs_offsets_fresh_hdr);
        l.push(String::new());
        for item in s.per_sym_items {
            l.extend(item);
        }
        for item in s.per_stub_items {
            l.extend(item);
        }
        l.push(String::new());
    }
    l.extend(s.frame_abbrev);
    if !s.ft_base.is_empty() {
        l.extend(s.ft_base);
        for item in s.per_ft_items {
            l.extend(item);
        }
        l.extend(s.single_obj_ft);
        l.push(String::new());
    }
    if !registrations.is_empty() {
        l.extend([
            "/-! ## Function entries (`fnEntryExt`) of every target, for `wp_entry` / `wp_init_fn` -/"
                .into(),
            String::new(),
        ]);
        l.extend(registrations.iter().cloned());
        l.push(String::new());
    }
    l.extend([format!("end {ns}"), String::new()]);
    l.join("\n")
}

/// Render the `Code` module of `cfg` and, when its leaf lemma count exceeds
/// [`AUTO_CODE_SHARD_DECL_THRESHOLD`], split independent reflected sub-tables and leaf theorems
/// across companion `<CodeStem>Shard<i>.lean` modules re-exported via `public import` from
/// `cfg.code_file` so Lake compiles them concurrently across cores.
pub fn render_code_modules(
    cfg: &ExportConfig,
    objs_slice: &[ObjObject],
    canon: &Canonical,
    registrations: &[String],
) -> Vec<(PathBuf, String)> {
    let s = build_code_sections(cfg, objs_slice, canon);
    if s.total_leaf_items <= AUTO_CODE_SHARD_DECL_THRESHOLD {
        return vec![(
            cfg.code_file.clone(),
            render_code_module(cfg, objs_slice, canon, registrations),
        )];
    }
    let c = cfg.code_def_name();
    let img = cfg.image_def_name();
    let ns = &cfg.namespace_prefix;
    let title = cfg.title.replace("-/", "- /");
    let mut shards: Vec<(PathBuf, String, String)> = Vec::new();
    let mut emit_shard = |role: &str, imports: &[String], body: Vec<String>| -> String {
        let idx = shards.len();
        let (path, mod_name) = cfg.code_shard_file(idx);
        let mut sl = vec!["module".to_string(), String::new()];
        for imp in imports {
            sl.push(format!("public import {imp}"));
        }
        sl.extend([
            String::new(),
            format!("/-! # Canonical code of {title} ({role})"),
            String::new(),
            "Generated by `rust-obj2lean` (untrusted: every theorem is checked by the kernel)."
                .into(),
            "DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
            format!("Imported by `{}`.", cfg.code_module),
            "-/".into(),
            String::new(),
            "@[expose] public section".into(),
            String::new(),
            format!("namespace {ns}"),
            String::new(),
            "open Arm64 ProofLib.ProgramReflection".into(),
            String::new(),
            "set_option Elab.async false".into(),
            "set_option maxHeartbeats 0".into(),
            "set_option maxRecDepth 2000000".into(),
            String::new(),
        ]);
        sl.extend(body);
        sl.extend([String::new(), format!("end {ns}"), String::new()]);
        shards.push((path, mod_name.clone(), sl.join("\n")));
        mod_name
    };

    let mut base_body = s.base_prog;
    if !s.has_wt {
        base_body.extend(s.word_tree.clone());
    }
    base_body.extend(s.sym_abbrevs);
    if !s.names_are_unique {
        base_body.extend(s.sym_pre_stubs_wf.clone());
    }
    base_body.extend(s.frame_abbrev);
    let base_imports = vec![
        cfg.obj_module.clone(),
        "ProofLib.ObjectLoad".into(),
        "ProofLib.ProgramReflection".into(),
        "ProofLib.SimpAttrs".into(),
    ];
    let base_mod = emit_shard("base definitions and symbol offsets", &base_imports, base_body);

    let wt_mod = s
        .has_wt
        .then(|| emit_shard("word tree and fetch helpers", std::slice::from_ref(&base_mod), s.word_tree));

    if s.names_are_unique {
        let mut sym_imports = vec![base_mod.clone()];
        if s.syms_needs_sorted_import {
            sym_imports.push("ProofLib.ProgramReflection.SortedFresh".into());
        }
        let mut sym_hdr = s.sym_pre_stubs_wf;
        sym_hdr.extend(s.sym_post_stubs_wf);
        let sym_mod = emit_shard("symbol reflection tables", &sym_imports, sym_hdr);
        if !s.per_sym_items.is_empty() {
            let chunk_len = s.per_sym_items.len().div_ceil(4).max(1);
            for (ci, chunk) in s.per_sym_items.chunks(chunk_len).enumerate() {
                let body: Vec<String> = chunk.iter().flatten().cloned().collect();
                emit_shard(
                    &format!("symbol offset lemmas {}", ci + 1),
                    std::slice::from_ref(&sym_mod),
                    body,
                );
            }
        }
        let mut stub_body = s.stubs_wf_hdr;
        stub_body.extend(s.stubs_offsets_fresh_hdr);
        for item in s.per_stub_items {
            stub_body.extend(item);
        }
        emit_shard("extern stub well-formedness and lookup lemmas", &[sym_mod], stub_body);
    }

    if !s.ft_base.is_empty() {
        let mut ft_imports = vec![base_mod.clone()];
        if s.ft_needs_sorted_import {
            ft_imports.push("ProofLib.ProgramReflection.SortedFresh".into());
        }
        let ft_mod = emit_shard("function table reflection", &ft_imports, s.ft_base);
        if !s.per_ft_items.is_empty() {
            let mut item_imports = vec![ft_mod];
            if let Some(wt) = &wt_mod {
                item_imports.push(wt.clone());
            }
            let chunk_len = s.per_ft_items.len().div_ceil(6).max(1);
            for (ci, chunk) in s.per_ft_items.chunks(chunk_len).enumerate() {
                let body: Vec<String> = chunk.iter().flatten().cloned().collect();
                emit_shard(
                    &format!("function size and stack frame lemmas {}", ci + 1),
                    &item_imports,
                    body,
                );
            }
        }
        if !s.single_obj_ft.is_empty() {
            let mut obj_ft_imports = vec![base_mod];
            if s.obj_ft_needs_sorted_import {
                obj_ft_imports.push("ProofLib.ProgramReflection.SortedFresh".into());
            }
            emit_shard("object function frame lemmas", &obj_ft_imports, s.single_obj_ft);
        }
    }

    let mut barrel = vec!["module".to_string(), String::new()];
    for (_, mod_name, _) in &shards {
        barrel.push(format!("public import {mod_name}"));
    }
    barrel.extend([
        String::new(),
        format!("/-! # Canonical code of {title}"),
        String::new(),
        "Generated by `rust-obj2lean` (untrusted: every theorem is checked by the kernel).".into(),
        "DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "`{c}` is the base-independent part of the linked image `{img}`: its code at base 0, \
             its symbol offsets, and its stub offsets, split across {} companion shard modules so \
             Lake elaborates and kernel-checks them in parallel.",
            shards.len()
        ),
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64 ProofLib.ProgramReflection".into(),
        String::new(),
    ]);
    if !registrations.is_empty() {
        barrel.extend([
            "/-! ## Function entries (`fnEntryExt`) of every target, for `wp_entry` / `wp_init_fn` -/"
                .into(),
            String::new(),
        ]);
        barrel.extend(registrations.iter().cloned());
        barrel.push(String::new());
    }
    barrel.extend([format!("end {ns}"), String::new()]);

    let mut out = Vec::with_capacity(shards.len() + 1);
    out.push((cfg.code_file.clone(), barrel.join("\n")));
    for (path, _, text) in shards {
        out.push((path, text));
    }
    out
}

/// The functions of `funcs` selected by `target`'s `lemma_allowlist`, without aliases
/// (functions at an offset already selected). Warns about patterns that select nothing.
pub fn selected_functions<'a>(
    target: &ExportTarget,
    funcs: &'a [FuncRange],
) -> Result<Vec<&'a FuncRange>> {
    let patterns = lemma_patterns(target)?;
    for (pat, raw) in patterns.iter().zip(&target.lemma_allowlist) {
        if !funcs
            .iter()
            .any(|f| name_selected(&f.name, std::slice::from_ref(pat)))
        {
            eprintln!(
                "warning: target `{}`: `lemma_allowlist` entry `{raw}` matches no defined function",
                target.name
            );
        }
    }
    let mut offs = BTreeSet::new();
    Ok(funcs
        .iter()
        .filter(|f| name_selected(&f.name, &patterns) && offs.insert(f.off))
        .collect())
}

/// All function symbols of `funcs` selected by `target`'s `lemma_allowlist` (including
/// aliases at the same offset, deduplicated by symbol name).
pub fn selected_function_symbols<'a>(
    target: &ExportTarget,
    funcs: &'a [FuncRange],
) -> Result<Vec<&'a FuncRange>> {
    let patterns = lemma_patterns(target)?;
    let mut names = BTreeSet::new();
    Ok(funcs
        .iter()
        .filter(|f| name_selected(&f.name, &patterns) && names.insert(f.name.as_str()))
        .collect())
}

/// Symbol-table size above which a `Code` module proves its key-freshness theorems
/// (`<code>_symbols_fresh`, `<code>_funcTable_fresh`) through the $O(n \log n)$ sorted check of
/// `ProofLib.ProgramReflection.SortedFresh` instead of evaluating the quadratic `allFreshEntries`
/// directly. Tables of several hundred entries otherwise spend tens of seconds in single-threaded
/// kernel reduction; smaller tables keep the direct check so their generated modules need no extra
/// import and stay byte-identical.
pub const SORTED_FRESH_MIN_SYMBOLS: usize = 256;

/// Leaf symbol/stub/function item count above which [`render_code_modules`] splits a `Code` module
/// across companion `<CodeStem>Shard<i>.lean` modules re-exported via `public import`.
pub const AUTO_CODE_SHARD_DECL_THRESHOLD: usize = 256;

/// Whether `canon`'s `Code` module uses the sorted key-freshness check (see
/// [`SORTED_FRESH_MIN_SYMBOLS`]). The decision is per module: the function table is a subset of the
/// symbol table, so the symbol count bounds both.
pub fn uses_sorted_fresh(canon: &Canonical) -> bool {
    sorted_fresh_for_symbol_count(canon.symbols.len())
}

/// [`uses_sorted_fresh`] on the symbol-table size alone.
pub fn sorted_fresh_for_symbol_count(n_symbols: usize) -> bool {
    n_symbols > SORTED_FRESH_MIN_SYMBOLS
}

/// Default declaration threshold above which a target lemma module is automatically split into
/// shard modules (`<Target>Shard<i>.lean`) when `lemma_shards` is omitted in `translation.toml`.
pub const AUTO_LEMMA_SHARD_DECL_THRESHOLD: usize = 2_500;

/// Maximum number of auto-selected shard modules when `lemma_shards` is omitted in `translation.toml`.
pub const MAX_AUTO_LEMMA_SHARDS: usize = 8;

/// Compute the effective number of lemma shards for `target` given `total_decls` emitted theorems.
///
/// - If `target.lemma_shards > 1` (either configured in `translation.toml` or set by caller), uses
///   `target.lemma_shards`.
/// - If `lemma_shards = 1` was explicitly set in `translation.toml` (`explicit_lemma_shards == Some(1)`),
///   keeps a single unsharded module (`1`).
/// - Otherwise (`lemma_shards` omitted in `translation.toml`), automatically shards modules with
///   `total_decls > AUTO_LEMMA_SHARD_DECL_THRESHOLD` (`2,500` declarations, ~500 instructions)
///   into `ceil(total_decls / 2500)` shards (capped at `MAX_AUTO_LEMMA_SHARDS`).
pub fn effective_lemma_shards(target: &ExportTarget, total_decls: usize) -> usize {
    if target.lemma_shards > 1 {
        target.lemma_shards
    } else if target.explicit_lemma_shards == Some(1) {
        1
    } else if total_decls > AUTO_LEMMA_SHARD_DECL_THRESHOLD {
        total_decls
            .div_ceil(AUTO_LEMMA_SHARD_DECL_THRESHOLD)
            .clamp(2, MAX_AUTO_LEMMA_SHARDS)
    } else {
        1
    }
}

/// The `register_fn_entry` commands (fully qualified, so valid in any namespace that opens
/// `ProofLib.ProgramReflection`) for every `.text` function symbol selected by `target`'s
/// `lemma_allowlist`. Every argument refers only to the configuration's `Code` module (the decode
/// prefix is stored as a name), so the commands are emitted in the `Code` module, each shard, and the
/// barrel target module alike; repeated registrations are idempotent (`lookupFnEntry?` takes the last).
/// Empty when the code is not a whole number of instruction words.
pub fn register_fn_entry_lines(
    cfg: &ExportConfig,
    target: &ExportTarget,
    canon: &Canonical,
    funcs: &[FuncRange],
    ft_entries: &[FuncTableEntry],
    fn_off_lemmas: &BTreeMap<String, String>,
) -> Result<Vec<String>> {
    if !has_word_tree(cfg, canon) {
        return Ok(Vec::new());
    }
    let root_ns = &cfg.namespace_prefix;
    let code_full = format!("{root_ns}.{}", cfg.code_def_name());
    let dec_full = format!("{}.{}", cfg.target_namespace(target), target.prog_name);
    let text_end = text_end_offset(canon);
    let ft_map: BTreeMap<&str, &FuncTableEntry> =
        ft_entries.iter().map(|e| (e.name.as_str(), e)).collect();
    let mut out = Vec::new();
    for f in selected_function_symbols(target, funcs)? {
        if f.off >= text_end {
            continue;
        }
        let Some(fn_off_thm) = fn_off_lemmas.get(&f.name) else {
            continue;
        };
        let fn_off_full = format!("{root_ns}.{fn_off_thm}");
        let frame_bytes = ft_map.get(f.name.as_str()).and_then(|e| e.frame_bytes).or_else(|| {
            let start = (f.off as usize).min(canon.code.len());
            let end = start.saturating_add(f.size as usize).min(canon.code.len());
            infer_prologue_frame(&canon.code[start..end])
        });
        let fb = frame_bytes.map(|fb| format!(" {fb}")).unwrap_or_default();
        out.push(format!(
            "register_fn_entry {} {code_full} {dec_full} {fn_off_full} {} {}{fb}",
            lean_string_lit(&f.name),
            f.off,
            f.size
        ));
    }
    Ok(out)
}

/// Render the lemma module(s) of `target`: fetch lemmas for every instruction of the selected
/// functions, stated about the configuration's `Code` program. Returns `(path, contents)` pairs:
/// first `target.lean_file` (with the `register_fn_entry` commands), then, when
/// `effective_lemma_shards > 1`, the shard modules it imports, which hold the per-instruction lemmas
/// split into contiguous, equally sized runs (same lemma names and namespace as unsharded), each
/// followed by the target's `register_fn_entry` commands.
pub fn render_target_module(
    cfg: &ExportConfig,
    target: &ExportTarget,
    canon: &Canonical,
    funcs: &[FuncRange],
    ft_entries: &[FuncTableEntry],
    fn_off_lemmas: &BTreeMap<String, String>,
    emitted_code_offs: &mut BTreeSet<u64>,
) -> Result<Vec<(PathBuf, String)>> {
    let c = cfg.code_def_name();
    let p = &target.prog_name;
    let ns = cfg.target_namespace(target);
    let text_end = text_end_offset(canon);
    let selected = selected_functions(target, funcs)?;
    let registrations =
        register_fn_entry_lines(cfg, target, canon, funcs, ft_entries, fn_off_lemmas)?;
    let mut per_fn: Vec<(String, Vec<(u64, bool)>)> = Vec::new();
    let mut total_decls: usize = 0;
    let code_bytes_len = code_len(cfg, canon) as u64;
    if has_word_tree(cfg, canon) {
        // Per selected function: its section header and 4-byte instruction slots `(off, is_root)`.
        for f in selected {
            let end = (f.off + f.size).min(code_bytes_len);
            let header = format!(
                "/-! ### `{}` (offset 0x{:x}, {} bytes) -/",
                f.name.replace('`', "'").replace("-/", "- /"),
                f.off,
                f.size
            );
            let mut slots: Vec<(u64, bool)> = Vec::new();
            let mut off = f.off.next_multiple_of(4);
            while off + 4 <= end {
                let is_root = emitted_code_offs.insert(off);
                let in_text = off < text_end;
                let is_zero = in_text && off == 0;
                total_decls += 2 + usize::from(in_text) + usize::from(is_zero);
                if is_root {
                    total_decls += 1 + usize::from(in_text) + usize::from(is_zero);
                }
                slots.push((off, is_root));
                off += 4;
            }
            per_fn.push((header, slots));
        }
    }
    let emit_slots = |dst: &mut Vec<String>, slots: &[(u64, bool)]| {
        let mut runs: Vec<(bool, Vec<(u64, u64)>)> = Vec::new();
        for &(off, is_root) in slots {
            if let Some((last_root, ranges)) = runs.last_mut()
                && *last_root == is_root
            {
                if let Some(last_range) = ranges.last_mut()
                    && last_range.1 + 4 == off
                {
                    last_range.1 = off;
                } else {
                    ranges.push((off, off));
                }
            } else {
                runs.push((is_root, vec![(off, off)]));
            }
        }
        for (is_root, ranges) in runs {
            let items: Vec<String> = ranges
                .into_iter()
                .map(|(a, b)| {
                    if a == b {
                        format!("0x{a:x}")
                    } else {
                        format!("0x{a:x} → 0x{b:x}")
                    }
                })
                .collect();
            dst.push(format!(
                "gen_fetches {c} {p} {is_root} [{}]",
                items.join(", ")
            ));
        }
    };
    let n_shards = effective_lemma_shards(target, total_decls);
    let shard_files: Vec<(PathBuf, String)> = if n_shards > 1 && has_word_tree(cfg, canon) {
        (0..n_shards).map(|i| target.shard_file(i)).collect()
    } else {
        Vec::new()
    };
    let mut l: Vec<String> = vec![
        "module".into(),
        String::new(),
        format!("public import {}", cfg.code_module),
        "public import ProofLib.GenDecodes".into(),
    ];
    l.extend(shard_files.iter().map(|(_, m)| format!("public import {m}")));
    l.extend([
        String::new(),
        format!(
            "/-! # Fetch lemmas for {}",
            target.title.replace("-/", "- /")
        ),
        String::new(),
        "Generated by `rust-obj2lean` (untrusted: every lemma is checked by the kernel).".into(),
        "DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "For each instruction at offset `off` of a function selected by `lemma_allowlist` ({}):",
            target
                .lemma_allowlist
                .iter()
                .map(|p| format!("`{}`", p.replace('`', "'")))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        format!("* `{p}_decode_0x<off> : {c}_tree.fetchDecodeAt off = some inst`,"),
        format!("* `{p}_fetch_0x<off> : {c}.fetch off = some inst` (base 0), and"),
        format!(
            "* `{p}_rebase_fetch_0x<off> : ({c}.rebase b X).fetch (b + off) = some inst` \
             (any base `b` and extern hooks `X`, no overrides)."
        ),
    ]);
    if !shard_files.is_empty() {
        l.extend([
            String::new(),
            format!(
                "The lemmas are split over {n_shards} shard modules (`lemma_shards`), {}, so that \
                 Lake checks them in parallel.",
                shard_files
                    .iter()
                    .map(|(_, m)| format!("`{m}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ]);
    }
    let preamble = |l: &mut Vec<String>| {
        l.extend([
            String::new(),
            "@[expose] public section".into(),
            String::new(),
            format!("namespace {ns}"),
            String::new(),
            "open Arm64 ProofLib.ProgramReflection ProofLib.GenDecodes".into(),
            String::new(),
            "set_option Elab.async false".into(),
            "set_option maxHeartbeats 0".into(),
            String::new(),
        ]);
    };
    l.push("-/".into());
    preamble(&mut l);
    let mut shard_bodies: Vec<Vec<String>> = vec![Vec::new(); shard_files.len()];
    if !has_word_tree(cfg, canon) {
        l.push(format!(
            "-- `{c}.code` is not a whole number of instruction words."
        ));
    } else {
        if shard_files.is_empty() {
            for (header, slots) in &per_fn {
                l.push(header.clone());
                l.push(String::new());
                emit_slots(&mut l, slots);
                l.push(String::new());
            }
        } else {
            // Contiguous runs of about `total / n_shards` instruction slots per shard; a function
            // split across shards gets its section header in each of them.
            let total: usize = per_fn.iter().map(|(_, s)| s.len()).sum();
            let per_shard = total.div_ceil(n_shards).max(1);
            let mut k = 0usize;
            let mut cur: Option<(usize, usize)> = None; // (shard, function) of the open section
            let mut cur_slots: Vec<(u64, bool)> = Vec::new();
            for (fi, (header, slots)) in per_fn.iter().enumerate() {
                for &slot in slots {
                    let si = (k / per_shard).min(n_shards - 1);
                    if cur != Some((si, fi)) {
                        if let Some((prev, _)) = cur {
                            emit_slots(&mut shard_bodies[prev], &cur_slots);
                            cur_slots.clear();
                            shard_bodies[prev].push(String::new());
                        }
                        shard_bodies[si].push(header.clone());
                        shard_bodies[si].push(String::new());
                        cur = Some((si, fi));
                    }
                    cur_slots.push(slot);
                    k += 1;
                }
            }
            if let Some((prev, _)) = cur {
                emit_slots(&mut shard_bodies[prev], &cur_slots);
                shard_bodies[prev].push(String::new());
            }
        }

        l.extend(registrations.iter().cloned());
        l.push(String::new());
    }
    l.extend([format!("end {ns}"), String::new()]);
    let mut out = vec![(target.lean_file.clone(), l.join("\n"))];
    for (i, ((path, _), mut body)) in shard_files.iter().zip(shard_bodies).enumerate() {
        // Every shard registers all functions of the target, so importing any single shard (without
        // the barrel `target.lean_module`) populates `fnEntryExt`; duplicates are idempotent.
        body.extend(registrations.iter().cloned());
        body.push(String::new());
        let mut sl: Vec<String> = vec![
            "module".into(),
            String::new(),
            format!("public import {}", cfg.code_module),
            "public import ProofLib.GenDecodes".into(),
            String::new(),
            format!(
                "/-! # Fetch lemmas for {}, shard {} of {n_shards}",
                target.title.replace("-/", "- /"),
                i + 1
            ),
            String::new(),
            "Generated by `rust-obj2lean` (untrusted: every lemma is checked by the kernel).".into(),
            "DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
            format!("Imported by `{}`, which lists the lemma shapes.", target.lean_module),
            "-/".into(),
        ];
        preamble(&mut sl);
        sl.extend(body);
        sl.extend([format!("end {ns}"), String::new()]);
        out.push((path.clone(), sl.join("\n")));
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{
        AUTO_CODE_SHARD_DECL_THRESHOLD, SORTED_FRESH_MIN_SYMBOLS, is_strict_sorted_names,
        render_code_module, render_code_modules, sanitize_symbol_ident,
        sorted_fresh_for_symbol_count, symbol_keyed_idents,
    };
    use crate::trusted_common::{ObjObject, ObjSection, ObjSymbol, SymBind, SymKind, SymSection};
    use crate::untrusted_legacy_linker::link;
    use crate::untrusted_driver::load_config;

    #[test]
    fn is_strict_sorted_names_cases() {
        assert!(is_strict_sorted_names(std::iter::empty()));
        assert!(is_strict_sorted_names(["alpha"].into_iter()));
        assert!(is_strict_sorted_names(
            ["", "a", "alpha", "alphb", "widget", "widget_init"].into_iter()
        ));
        assert!(!is_strict_sorted_names(["alpha", "alpha"].into_iter()));
        assert!(!is_strict_sorted_names(["beta", "alpha"].into_iter()));
    }

    #[test]
    fn sorted_fresh_gate_switches_above_threshold() {
        // Small and threshold-sized tables keep the direct quadratic `rfl_kernel` check; anything
        // larger routes through `ProofLib.ProgramReflection.SortedFresh`.
        assert!(!sorted_fresh_for_symbol_count(0));
        assert!(!sorted_fresh_for_symbol_count(SORTED_FRESH_MIN_SYMBOLS));
        assert!(sorted_fresh_for_symbol_count(SORTED_FRESH_MIN_SYMBOLS + 1));
    }

    #[test]
    fn sanitize_symbol_ident_cases() {
        assert_eq!(sanitize_symbol_ident("curl_easy_escape"), "curl_easy_escape");
        assert_eq!(sanitize_symbol_ident("__libc_start"), "__libc_start");
        assert_eq!(sanitize_symbol_ident("foo.cold"), "foo_dot_cold");
        assert_eq!(sanitize_symbol_ident("foo.part.0"), "foo_dot_part_dot_0");
        assert_eq!(sanitize_symbol_ident("$x"), "_dollar_x");
        assert_eq!(sanitize_symbol_ident("memcpy@GLIBC_2.17"), "memcpy_at_GLIBC_2_dot_17");
        assert_eq!(sanitize_symbol_ident("helper [alpha]"), "helper_alpha");
        assert_eq!(sanitize_symbol_ident("0x26df0"), "_0x26df0");
        assert_eq!(sanitize_symbol_ident("1abc"), "_1abc");
        assert_eq!(sanitize_symbol_ident(""), "sym");
        assert_eq!(sanitize_symbol_ident("[]"), "sym");
        assert_eq!(sanitize_symbol_ident("héllo"), "h_llo");
    }

    #[test]
    fn symbol_keyed_idents_dedup() {
        let keys = symbol_keyed_idents(["a.b", "a_dot_b", "f", "f", "a.b", "a_dot_b_1", "g h", "g-h"]);
        assert_eq!(
            keys,
            vec![
                Some("a_dot_b".into()),
                Some("a_dot_b_1".into()),
                Some("f".into()),
                None,
                None,
                Some("a_dot_b_1_1".into()),
                Some("g_h".into()),
                Some("g_h_1".into()),
            ]
        );
        // Deterministic.
        assert_eq!(keys, symbol_keyed_idents(["a.b", "a_dot_b", "f", "f", "a.b", "a_dot_b_1", "g h", "g-h"]));
    }

    #[test]
    fn sharded_code_modules_match_single_file_declarations() {
        let tmp = tempfile::tempdir().unwrap();
        let cfg_path = tmp.path().join("Implementation/widget/translation.toml");
        std::fs::create_dir_all(cfg_path.parent().unwrap()).unwrap();
        std::fs::write(
            &cfg_path,
            r#"
obj_name = "Widget"
title = "widget synthetic fixture"
c_sources = ["widget.c"]

[[targets]]
name = "Widget"
title = "widget"
prog_name = "widget"
lean_file = "Examples/Generated/WidgetFns.lean"
lemma_allowlist = ["*"]
"#,
        )
        .unwrap();
        let cfg = load_config(&cfg_path, tmp.path(), None).unwrap();

        let n_funcs = AUTO_CODE_SHARD_DECL_THRESHOLD + 40;
        let ret_word = 0xd65f03c0_u32.to_le_bytes();
        let mut bytes = Vec::with_capacity(n_funcs * 4);
        let mut symbols = vec![ObjSymbol {
            name: String::new(),
            raw_name: String::new(),
            kind: SymKind::Notype,
            bind: SymBind::Local,
            vis: 0,
            sec: SymSection::Undef,
            value: 0,
            size: 0,
        }];
        for i in 0..n_funcs {
            bytes.extend_from_slice(&ret_word);
            let sym_name = format!("widget_fn_{i:04}");
            symbols.push(ObjSymbol {
                name: sym_name.clone(),
                raw_name: sym_name,
                kind: SymKind::Func,
                bind: SymBind::Global,
                vis: 0,
                sec: SymSection::Sec(0),
                value: (i * 4) as u64,
                size: 4,
            });
        }
        let obj = ObjObject {
            name: "widget".into(),
            sections: vec![ObjSection {
                name: ".text".into(),
                sh_type: object::elf::SHT_PROGBITS,
                sh_flags: (object::elf::SHF_ALLOC | object::elf::SHF_EXECINSTR) as u64,
                addr: 0,
                align: 4,
                entsize: 0,
                size: bytes.len() as u64,
                file_offset: 0,
                bytes,
                relocs: Vec::new(),
                is_rel: false,
                elf_index: 1,
            }],
            symbols,
            groups: Vec::new(),
            elf_bytes: Vec::new(),
        };
        let canon = link(std::slice::from_ref(&obj), &[]).unwrap();
        let regs = vec!["register_fn_entry widget_fn_0000 := 0x0".to_string()];

        let single = render_code_module(&cfg, std::slice::from_ref(&obj), &canon, &regs);
        let sharded = render_code_modules(&cfg, std::slice::from_ref(&obj), &canon, &regs);
        assert!(sharded.len() > 4, "expected parallel code shards, got {}", sharded.len());
        assert_eq!(sharded[0].0, cfg.code_file);

        // Barrel must directly `public import` every companion shard so Lake's 1-hop
        // `generatedImportsOfFile` check tracks every shard on disk.
        for i in 0..(sharded.len() - 1) {
            let (_, shard_mod) = cfg.code_shard_file(i);
            assert!(
                sharded[0].1.contains(&format!("public import {shard_mod}")),
                "barrel missing direct `public import {shard_mod}`"
            );
        }

        let collect_decls = |text: &str| -> Vec<String> {
            text.lines()
                .filter(|line| {
                    line.starts_with("def ")
                        || line.starts_with("abbrev ")
                        || line.starts_with("noncomputable def ")
                        || line.starts_with("noncomputable abbrev ")
                        || line.starts_with("theorem ")
                        || line.starts_with("@[simp")
                        || line.starts_with("register_fn_entry ")
                })
                .map(str::to_string)
                .collect()
        };
        let mut single_decls = collect_decls(&single);
        let mut sharded_decls: Vec<String> = sharded
            .iter()
            .flat_map(|(_, content)| collect_decls(content))
            .collect();
        single_decls.sort();
        sharded_decls.sort();
        assert_eq!(single_decls, sharded_decls);
    }
}
