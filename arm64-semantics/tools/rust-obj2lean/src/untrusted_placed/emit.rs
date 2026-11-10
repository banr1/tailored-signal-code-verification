// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Lean rendering of placed libraries and placements (`[OUTSIDE TCB]`).
//!
//! - [`render_lib`]: `<Obj>PlacedObj.lean` with `<obj>Text : Obj.CodeBlock`,
//!   `<obj>Data : List Obj.SymDataInfo` and `<obj>Lib : Obj.PlacedLib`; the code and data bytes
//!   are spliced from a `<Obj>PlacedObj.bin` sidecar (text, then each data object's bytes) with
//!   `include_bytes%`.
//! - [`render_multi_lib`] / [`render_multi_lib_sharded`]: the multi-block `Obj.MultiPlacedLib`
//!   form, optionally with its code blocks split over `<Obj>PlacedObjShard<k>.lean` modules.
//! - [`render_elf`]: `<Obj>ElfObj.lean` with the SHA-256-pinned bytes of the linked ELF
//!   (`<obj>ElfBytes`) and nothing else.
//! - [`render_witness`]: `<Obj>PlacedWitness.lean` with `<obj>Placement : Obj.Placement` and,
//!   when linked, the interned form of both and the kernel-checked
//!   `<obj>Lib_linkedIn : <obj>Lib.LinkedIn <obj>ElfBytes`.
//!
//! The `*Obj` modules hold data only (no theorems) and import only `Arm64`, so campaign `Spec`
//! modules may import them; the witness is a `Proof` module.

use std::path::Path;

use crate::trusted_common::lean_string_lit;

use super::model::{PLib, PMultiLib, PReloc};
use super::patch::{PMultiPlacement, PPlacement};

/// Lean-safe text inside a `/-! … -/` or `/-- … -/` comment.
pub(super) fn doc_safe(s: &str) -> String {
    s.replace("-/", "- /").replace("/-", "/ -")
}

fn render_reloc(r: &PReloc) -> String {
    let mut parts = vec![
        format!("off := {}", r.off),
        format!("kind := {}", r.kind.lean_name()),
        format!("sym := {}", lean_string_lit(&r.sym)),
    ];
    if r.addend != 0 {
        parts.push(format!("addend := {}", r.addend));
    }
    format!("{{ {} }}", parts.join(", "))
}

fn push_list(l: &mut Vec<String>, indent: &str, field: &str, items: Vec<String>) {
    if items.is_empty() {
        l.push(format!("{indent}{field} := []"));
        return;
    }
    l.push(format!("{indent}{field} := ["));
    let n = items.len();
    for (i, it) in items.into_iter().enumerate() {
        let sep = if i + 1 < n { "," } else { "]" };
        l.push(format!("{indent}  {it}{sep}"));
    }
}

/// `push_list`, omitted when `items` is empty (so the field keeps its default and outputs of
/// libraries that do not use it are unchanged).
fn push_list_nonempty(l: &mut Vec<String>, indent: &str, field: &str, items: Vec<String>) {
    if !items.is_empty() {
        push_list(l, indent, field, items);
    }
}

/// `undefWeak := fun s => [...].contains s` (omitted when `undef_weak` is empty).
fn push_undef_weak(l: &mut Vec<String>, undef_weak: &std::collections::BTreeSet<String>) {
    if !undef_weak.is_empty() {
        let items: Vec<String> = undef_weak.iter().map(|s| lean_string_lit(s)).collect();
        l.push(format!(
            "  undefWeak := fun s => [{}].contains s",
            items.join(", ")
        ));
    }
}

/// Names of the Lean definitions for library `obj_name`.
#[derive(Clone, Debug)]
pub struct LibNames {
    pub text: String,
    pub data: String,
    pub lib: String,
    pub placement: String,
    pub rho: String,
    pub relax: String,
    pub b2b: String,
    pub elf_bytes: String,
    /// Shared byte constants: the text block's code and each data object's bytes.
    pub code: String,
    pub data_bytes: String,
}

impl LibNames {
    /// The byte constant of data object `i`.
    pub fn data_bytes(&self, i: usize) -> String {
        format!("{}{i}", self.data_bytes)
    }

    /// The byte constant of code block `i` in a `MultiPlacedLib`.
    pub fn block_code(&self, i: usize) -> String {
        format!("{}{i}", self.code)
    }

    /// The `List Obj.CodeBlock` constant of a `MultiPlacedLib`.
    pub fn blocks(&self) -> String {
        format!("{}Blocks", self.text.strip_suffix("Text").unwrap_or(&self.text))
    }

    /// The `List Obj.CodeBlock` constant of shard `k` of a sharded `MultiPlacedLib`.
    pub fn blocks_shard(&self, k: usize) -> String {
        format!("{}Shard{k}", self.blocks())
    }

    /// The `Obj.MultiPlacedLib` constant of a `MultiPlacedLib`.
    pub fn multi_lib(&self) -> String {
        format!("{}MultiLib", self.lib.strip_suffix("Lib").unwrap_or(&self.lib))
    }
}

impl LibNames {
    pub fn new(obj_name: &str) -> Self {
        LibNames {
            text: format!("{obj_name}Text"),
            data: format!("{obj_name}Data"),
            lib: format!("{obj_name}Lib"),
            placement: format!("{obj_name}Placement"),
            rho: format!("{obj_name}Rho"),
            relax: format!("{obj_name}Relaxed"),
            b2b: format!("{obj_name}B2b"),
            elf_bytes: format!("{obj_name}ElfBytes"),
            code: format!("{obj_name}PlacedCode"),
            data_bytes: format!("{obj_name}PlacedData"),
        }
    }
}

/// Names a `<…>PlacedWitness.lean` module defines or refers to. The primary witness
/// ([`WitNames::primary`]) derives every name from the library's `obj_name`; an extra witness
/// ([`WitNames::extra`], `[[placed.extra_witnesses]]`) defines its own names from `prefix` and
/// refers to ELF bytes defined elsewhere, so several witnesses can be imported together.
#[derive(Clone, Debug)]
pub struct WitNames {
    /// The library's names (`<obj>Lib`, `<obj>PlacedCode`, …), shared by all witnesses.
    pub lib: LibNames,
    /// The ELF bytes constant the witness is about.
    pub elf_bytes: String,
    pub rho: String,
    pub relax: String,
    pub b2b: String,
    pub placement: String,
    /// The interned library (`<p>L`), its name table (`<p>NameChars`) and layout (`<p>Ly`).
    pub lib_l: String,
    pub name_chars: String,
    pub ly: String,
    /// The parsed ELF (`<p>Elf`), its parse theorem (`<p>_parse` for extra witnesses,
    /// `<p>Elf_parse` for the primary one) and symbol tables.
    pub elf: String,
    pub elf_parse: String,
    pub elf_syms: String,
    pub elf_sym_chars: String,
    /// `<obj>Lib = <p>L.toLib` and `<obj>Lib.LinkedIn <elf_bytes>`.
    pub lib_eq: String,
    pub linked_in: String,
    /// ELF-free `Placeable` and extern-distinctness theorems.
    pub placeable_and_externs: String,
    pub placeable_at: String,
    pub externs_nodup: String,
    pub placeable: String,
    pub exists_placeable: String,
    /// Extra witnesses only: `<p>_ok : <obj>Lib.Placeable pl ∧ <obj>Lib.InElf <p>Elf pl`, the one
    /// kernel check, from which `<p>_linkedIn` is assembled (so importers reuse it instead of
    /// re-running the check against another name for the same ELF).
    pub ok: Option<String>,
    /// Linked witnesses only: the facts module (`<Base>ElfFacts`) holding the parsed ELF, its
    /// parse theorem and symbol tables, which the witness imports and re-exports under the names
    /// above ([`push_elf_aliases`]).
    pub facts: Option<super::facts::ElfFacts>,
    /// Linked multi-block witnesses only: the externs whose `.symtab` entry is unique and at the
    /// placed address (`<p>ExternIds`, `<p>_externSymtab`), and the other externs with the reason
    /// each is left out ([`super::witness::extern_symtab_split`]).
    pub extern_symtab: Option<(Vec<String>, Vec<(String, String)>)>,
    /// Linked multi-block witnesses only: the module (and namespace) of the split check
    /// (`[placed] split_check_module`); `None` keeps the single `decide +kernel`.
    pub split_check: Option<String>,
    /// Linked single-block witnesses only (`[placed] chunked_check`): prove the placement from
    /// separate kernel facts in shard modules ([`super::chunked`]) instead of one `decide +kernel`.
    pub chunked: bool,
    /// Namespace of the library module, `open`ed by a chunked witness whose own namespace
    /// differs (an extra witness with its own `namespace`), so its names resolve unqualified.
    pub lib_ns: Option<String>,
}

impl WitNames {
    /// The names of `<Obj>PlacedWitness.lean`.
    pub fn primary(obj_name: &str) -> Self {
        let lib = LibNames::new(obj_name);
        let placeable_and_externs = format!("{}_placeable_and_externs", lib.placement);
        let placeable_at = format!("{}_placeable", lib.placement);
        let externs_nodup = format!("{}_externs_nodup", lib.placement);
        let placeable = format!("{}_placeable", lib.lib);
        let exists_placeable = format!("{}_exists_placeable", lib.lib);
        WitNames {
            elf_bytes: lib.elf_bytes.clone(),
            rho: lib.rho.clone(),
            relax: lib.relax.clone(),
            b2b: lib.b2b.clone(),
            placement: lib.placement.clone(),
            lib_l: format!("{obj_name}L"),
            name_chars: format!("{obj_name}NameChars"),
            ly: format!("{obj_name}Ly"),
            elf: format!("{obj_name}Elf"),
            elf_parse: format!("{obj_name}Elf_parse"),
            elf_syms: format!("{obj_name}ElfSyms"),
            elf_sym_chars: format!("{obj_name}ElfSymChars"),
            lib_eq: format!("{}_eq", lib.lib),
            linked_in: format!("{}_linkedIn", lib.lib),
            placeable_and_externs,
            placeable_at,
            externs_nodup,
            placeable,
            exists_placeable,
            ok: None,
            facts: None,
            extern_symtab: None,
            split_check: None,
            chunked: false,
            lib_ns: None,
            lib,
        }
    }

    /// The names of an extra witness with name prefix `prefix` about the ELF bytes constant
    /// `elf_bytes` (e.g. `myLibAlt`: `myLibAltPlacement`, `myLibAltElf`,
    /// `myLibAlt_parse`, `myLibAlt_linkedIn`).
    pub fn extra(obj_name: &str, prefix: &str, elf_bytes: &str) -> Self {
        WitNames {
            lib: LibNames::new(obj_name),
            elf_bytes: elf_bytes.to_string(),
            rho: format!("{prefix}Rho"),
            relax: format!("{prefix}Relaxed"),
            b2b: format!("{prefix}B2b"),
            placement: format!("{prefix}Placement"),
            lib_l: format!("{prefix}L"),
            name_chars: format!("{prefix}NameChars"),
            ly: format!("{prefix}Ly"),
            elf: format!("{prefix}Elf"),
            elf_parse: format!("{prefix}_parse"),
            elf_syms: format!("{prefix}ElfSyms"),
            elf_sym_chars: format!("{prefix}ElfSymChars"),
            lib_eq: format!("{prefix}L_eq"),
            linked_in: format!("{prefix}_linkedIn"),
            placeable_and_externs: format!("{prefix}Placement_placeable_and_externs"),
            placeable_at: format!("{prefix}Placement_placeable"),
            externs_nodup: format!("{prefix}Placement_externs_nodup"),
            placeable: format!("{prefix}_placeable"),
            exists_placeable: format!("{prefix}_exists_placeable"),
            ok: Some(format!("{prefix}_ok")),
            facts: None,
            extern_symtab: None,
            split_check: None,
            chunked: false,
            lib_ns: None,
        }
    }
}

/// The sidecar bytes of `lib`: its code, then each data object's bytes in order.
pub fn sidecar_bytes(lib: &PLib) -> Vec<u8> {
    let mut out = lib.text.code.clone();
    for d in &lib.data {
        out.extend_from_slice(&d.bytes);
    }
    out
}

/// The sidecar bytes of a multi-block `lib`: each block's code in order, then each data object's
/// bytes in order.
pub fn sidecar_multi_bytes(lib: &PMultiLib) -> Vec<u8> {
    let mut out = Vec::new();
    for b in &lib.blocks {
        out.extend_from_slice(&b.code);
    }
    for d in &lib.data {
        out.extend_from_slice(&d.bytes);
    }
    out
}

/// Header lines shared by all modules.
pub(super) fn header(license: &[String]) -> Vec<String> {
    let mut l = Vec::new();
    if !license.is_empty() {
        l.push("/-".to_string());
        l.extend(license.iter().map(|s| doc_safe(s)));
        l.push("-/".to_string());
    }
    l
}

/// `<Obj>PlacedObj.lean` for `lib`, in namespace `ns`, reading bytes from sidecar `bin_name` (a file
/// next to the module). With `noncomputable` (`[placed] noncomputable_code`), the code bytes, the
/// text block and the library are `noncomputable def`s, which Lean does not compile.
pub fn render_lib(
    lib: &PLib,
    obj_name: &str,
    ns: &str,
    bin_name: &str,
    license: &[String],
    noncomputable: bool,
) -> String {
    let names = LibNames::new(obj_name);
    let bin = lean_string_lit(bin_name);
    let nc = if noncomputable { "noncomputable " } else { "" };
    let mut l = header(license);
    l.extend([
        "module".to_string(),
        String::new(),
        "public import Arm64.Trusted.Object.Placed".into(),
        "public import Arm64.Trusted.Surface.IncludeBytes".into(),
        String::new(),
        format!("/-! # Placed library `{}` (generated, Spec role)", doc_safe(&lib.name)),
        String::new(),
        "Generated by `rust-obj2lean` (`untrusted_placed`), which `lake build` runs before compiling"
            .into(),
        "this library. DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "`{}` is the library's relocatable text block (all `.text*` input sections in stock",
            names.lib
        ),
        "`ld.lld` input order, alignment gaps zero-filled, relocated fields as in the objects), its".into(),
        "data objects (one per data input section, or per `SHF_MERGE` piece) and its exports.".into(),
        String::new(),
        "This module has the Spec role: campaign `Spec` statements quantify over placements of".into(),
        format!(
            "`{}`, and the trust guard classes this gitignored build product as Spec. It is",
            names.lib
        ),
        "anchored by the tracked stock-linked ELF and its pinned SHA-256 (the `ElfObj` module):".into(),
        format!(
            "the kernel-checked `Obj.PlacedLib.LinkedIn {} {}` ties `{}` to those bytes.",
            names.lib, names.elf_bytes, names.lib
        ),
        String::new(),
        "## Text input sections".into(),
        String::new(),
    ]);
    for (ts, (name, sz)) in lib.text_secs.iter().zip(text_sec_names(lib)) {
        l.push(format!(
            "* `{:#06x}` (+{sz}): `{}`",
            ts.off,
            doc_safe(&name).replace('`', "'")
        ));
    }
    if !lib.unreferenced_data.is_empty() {
        l.extend([
            String::new(),
            "## Unreferenced data (not modelled)".into(),
            String::new(),
        ]);
        for n in &lib.unreferenced_data {
            l.push(format!("* `{}`", doc_safe(n).replace('`', "'")));
        }
    }
    l.extend([
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64".into(),
        String::new(),
        "set_option maxHeartbeats 10000000".into(),
        "set_option maxRecDepth 2000000".into(),
        String::new(),
    ]);
    // Byte constants (shared with the interned form in `<Obj>PlacedWitness.lean`).
    l.push(format!(
        "/-- The code bytes of `{}` (relocated fields as in the objects). -/",
        doc_safe(&lib.name)
    ));
    l.push(format!(
        "{nc}def {} : List (BitVec 8) := include_bytes% {bin} 0 {}",
        names.code,
        lib.text.code.len()
    ));
    let mut off = lib.text.code.len();
    for (i, d) in lib.data.iter().enumerate() {
        l.push(format!(
            "/-- The bytes of data object `{}`. -/",
            doc_safe(&d.sym).replace('`', "'")
        ));
        l.push(format!(
            "def {} : List (BitVec 8) := include_bytes% {bin} {off} {}",
            names.data_bytes(i),
            d.bytes.len()
        ));
        off += d.bytes.len();
    }
    l.push(String::new());
    // Text.
    l.push(format!(
        "/-- The text block of `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("{nc}def {} : Obj.CodeBlock where", names.text));
    l.push(format!("  code := {}", names.code));
    l.push(format!("  align := {}", lib.text.align));
    let mut syms = lib.text.symbols.clone();
    syms.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    push_list(
        &mut l,
        "  ",
        "symbols",
        syms.iter()
            .map(|(n, o)| format!("({}, {o:#x})", lean_string_lit(n)))
            .collect(),
    );
    push_list(
        &mut l,
        "  ",
        "relocs",
        lib.text.relocs.iter().map(render_reloc).collect(),
    );
    push_list(
        &mut l,
        "  ",
        "externs",
        lib.text
            .externs
            .iter()
            .map(|e| lean_string_lit(e))
            .collect(),
    );
    push_list_nonempty(
        &mut l,
        "  ",
        "weakRefs",
        lib.text
            .weak_refs
            .iter()
            .map(|e| lean_string_lit(e))
            .collect(),
    );
    l.push(String::new());
    // Data.
    l.push(format!(
        "/-- The data objects of `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {} : List Obj.SymDataInfo := [", names.data));
    let n = lib.data.len();
    for (i, d) in lib.data.iter().enumerate() {
        l.push(format!("  {{ sym := {}", lean_string_lit(&d.sym)));
        l.push(format!("    align := {}", d.align));
        l.push(format!("    readOnly := {}", d.read_only));
        l.push(format!("    bytes := {}", names.data_bytes(i)));
        l.push(format!("    zeroTail := {}", d.zero_tail));
        let rs: Vec<String> = d.relocs.iter().map(render_reloc).collect();
        if rs.is_empty() {
            l.push("    relocs := [] }".into());
        } else {
            push_list(&mut l, "    ", "relocs", rs);
            let last = l.pop().unwrap();
            l.push(format!("{last} }}"));
        }
        if i + 1 < n {
            let last = l.pop().unwrap();
            l.push(format!("{last},"));
        }
    }
    l.push("]".into());
    l.push(String::new());
    l.push(format!(
        "/-- The placed library `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("{nc}def {} : Obj.PlacedLib where", names.lib));
    l.push(format!("  name := {}", lean_string_lit(&lib.name)));
    l.push(format!("  text := {}", names.text));
    l.push(format!("  data := {}", names.data));
    push_list(
        &mut l,
        "  ",
        "exports",
        lib.exports.iter().map(|e| lean_string_lit(e)).collect(),
    );
    l.push(String::new());
    l.push(format!("end {ns}"));
    l.push(String::new());
    l.join("\n")
}

/// `* Block `i` (+size): `label`` doc lines for the code blocks of `lib` with index in `range`.
fn push_block_docs(l: &mut Vec<String>, lib: &PMultiLib, range: std::ops::Range<usize>) {
    for (i, ts) in lib.text_secs.iter().enumerate() {
        if !range.contains(&i) {
            continue;
        }
        l.push(format!(
            "* Block `{i}` (+{}): `{}`",
            ts.size,
            doc_safe(&ts.label).replace('`', "'")
        ));
    }
}

/// The section, namespace and options opening a multi-block library module body.
fn push_multi_preamble(l: &mut Vec<String>, ns: &str) {
    l.extend([
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64".into(),
        String::new(),
        "set_option maxHeartbeats 10000000".into(),
        "set_option maxRecDepth 2000000".into(),
        String::new(),
    ]);
}

/// `def <obj>PlacedCode<i> := include_bytes% …` for the code blocks in `range`, whose bytes start
/// at sidecar offset `off`; returns the sidecar offset after them.
fn push_block_code_defs(
    l: &mut Vec<String>,
    lib: &PMultiLib,
    names: &LibNames,
    bin: &str,
    range: std::ops::Range<usize>,
    mut off: usize,
) -> usize {
    for i in range {
        let b = &lib.blocks[i];
        let label = lib
            .text_secs
            .get(i)
            .map(|ts| ts.label.as_str())
            .unwrap_or(&lib.name);
        l.push(format!(
            "/-- The code bytes of block `{i}` (`{}`). -/",
            doc_safe(label).replace('`', "'")
        ));
        l.push(format!(
            "def {} : List (BitVec 8) := include_bytes% {bin} {off} {}",
            names.block_code(i),
            b.code.len()
        ));
        off += b.code.len();
    }
    off
}

/// `def <obj>PlacedData<i> := include_bytes% …` for every data object, whose bytes start at
/// sidecar offset `off` (after all code blocks).
fn push_data_byte_defs(
    l: &mut Vec<String>,
    lib: &PMultiLib,
    names: &LibNames,
    bin: &str,
    mut off: usize,
) {
    for (i, d) in lib.data.iter().enumerate() {
        l.push(format!(
            "/-- The bytes of data object `{}`. -/",
            doc_safe(&d.sym).replace('`', "'")
        ));
        l.push(format!(
            "def {} : List (BitVec 8) := include_bytes% {bin} {off} {}",
            names.data_bytes(i),
            d.bytes.len()
        ));
        off += d.bytes.len();
    }
}

/// The `Obj.CodeBlock` list elements for the code blocks in `range` (comma-separated).
fn push_block_entries(
    l: &mut Vec<String>,
    lib: &PMultiLib,
    names: &LibNames,
    range: std::ops::Range<usize>,
) {
    let end = range.end;
    for i in range {
        let b = &lib.blocks[i];
        l.push(format!("  {{ code := {}", names.block_code(i)));
        l.push(format!("    align := {}", b.align));
        let mut syms = b.symbols.clone();
        syms.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
        push_list(
            l,
            "    ",
            "symbols",
            syms.iter()
                .map(|(n, o)| format!("({}, {o:#x})", lean_string_lit(n)))
                .collect(),
        );
        push_list(
            l,
            "    ",
            "relocs",
            b.relocs.iter().map(render_reloc).collect(),
        );
        push_list(
            l,
            "    ",
            "externs",
            b.externs.iter().map(|e| lean_string_lit(e)).collect(),
        );
        push_list_nonempty(
            l,
            "    ",
            "weakRefs",
            b.weak_refs.iter().map(|e| lean_string_lit(e)).collect(),
        );
        let last = l.pop().unwrap();
        let sep = if i + 1 < end { " }," } else { " }" };
        l.push(format!("{last}{sep}"));
    }
}

/// The data list, `<obj>MultiLib`, `<obj>Lib` and the namespace end of a multi-block library
/// module (everything after the code-block list).
fn push_multi_lib_tail(l: &mut Vec<String>, lib: &PMultiLib, names: &LibNames, ns: &str) {
    let blocks_name = names.blocks();
    let multi_lib_name = names.multi_lib();
    l.push(format!(
        "/-- The data objects of `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {} : List Obj.SymDataInfo := [", names.data));
    let n = lib.data.len();
    for (i, d) in lib.data.iter().enumerate() {
        l.push(format!("  {{ sym := {}", lean_string_lit(&d.sym)));
        l.push(format!("    align := {}", d.align));
        l.push(format!("    readOnly := {}", d.read_only));
        l.push(format!("    bytes := {}", names.data_bytes(i)));
        l.push(format!("    zeroTail := {}", d.zero_tail));
        let rs: Vec<String> = d.relocs.iter().map(render_reloc).collect();
        if rs.is_empty() {
            l.push("    relocs := [] }".into());
        } else {
            push_list(l, "    ", "relocs", rs);
            let last = l.pop().unwrap();
            l.push(format!("{last} }}"));
        }
        if i + 1 < n {
            let last = l.pop().unwrap();
            l.push(format!("{last},"));
        }
    }
    l.push("]".into());
    l.push(String::new());
    l.push(format!(
        "/-- The multi-block placed library `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {multi_lib_name} : Obj.MultiPlacedLib where"));
    l.push(format!("  name := {}", lean_string_lit(&lib.name)));
    l.push(format!("  blocks := {blocks_name}"));
    l.push(format!("  data := {}", names.data));
    push_list(
        l,
        "  ",
        "exports",
        lib.exports.iter().map(|e| lean_string_lit(e)).collect(),
    );
    push_list_nonempty(
        l,
        "  ",
        "exportSyms",
        lib.export_syms
            .iter()
            .map(|(e, raw)| format!("({}, {})", lean_string_lit(e), lean_string_lit(raw)))
            .collect(),
    );
    l.push(String::new());
    l.push(format!(
        "abbrev {} : Obj.MultiPlacedLib := {multi_lib_name}",
        names.lib
    ));
    l.push(String::new());
    l.push(format!("end {ns}"));
    l.push(String::new());
}

/// The opening lines (license, `module`, imports) of a multi-block library module.
fn multi_module_head(license: &[String], extra_imports: &[String]) -> Vec<String> {
    let mut l = header(license);
    l.extend([
        "module".to_string(),
        String::new(),
        "public import Arm64.Trusted.Object.Placed".into(),
        "public import Arm64.Trusted.Surface.IncludeBytes".into(),
    ]);
    l.extend(extra_imports.iter().map(|m| format!("public import {m}")));
    l.push(String::new());
    l
}

/// The module-doc paragraph shared by the unsharded and sharded top modules.
fn push_multi_doc_intro(l: &mut Vec<String>, lib: &PMultiLib, names: &LibNames) {
    l.extend([
        format!(
            "/-! # Multi-block placed library `{}` (generated, Spec role)",
            doc_safe(&lib.name)
        ),
        String::new(),
        "Generated by `rust-obj2lean` (`untrusted_placed --multi-placed`), which `lake build` runs"
            .into(),
        "before compiling this library. DO NOT EDIT MANUALLY: this file is a gitignored build product."
            .into(),
        String::new(),
        format!(
            "`{}` (`{}`) is the library's multi-block placed representation (`Obj.MultiPlacedLib`):",
            names.multi_lib(),
            names.lib
        ),
        "one independently placed `Obj.CodeBlock` per `.text.<fn>` input section (or `STT_FUNC`".into(),
        "slice), per-symbol `Obj.SymDataInfo` entries, and the library's exported functions.".into(),
        String::new(),
    ]);
}

/// `## Unreferenced data (not modelled)` doc lines (nothing when every data object is modelled).
fn push_unreferenced_docs(l: &mut Vec<String>, lib: &PMultiLib) {
    if !lib.unreferenced_data.is_empty() {
        l.extend([
            String::new(),
            "## Unreferenced data (not modelled)".into(),
            String::new(),
        ]);
        for n in &lib.unreferenced_data {
            l.push(format!("* `{}`", doc_safe(n).replace('`', "'")));
        }
    }
}

/// `<Obj>PlacedObj.lean` for a multi-block `lib` (`Obj.MultiPlacedLib`), in namespace `ns`,
/// reading bytes from sidecar `bin_name` (a file next to the module).
pub fn render_multi_lib(
    lib: &PMultiLib,
    obj_name: &str,
    ns: &str,
    bin_name: &str,
    license: &[String],
) -> String {
    let names = LibNames::new(obj_name);
    let bin = lean_string_lit(bin_name);
    let nb = lib.blocks.len();
    let mut l = multi_module_head(license, &[]);
    push_multi_doc_intro(&mut l, lib, &names);
    l.extend(["## Code blocks".into(), String::new()]);
    push_block_docs(&mut l, lib, 0..lib.text_secs.len());
    push_unreferenced_docs(&mut l, lib);
    l.extend(["-/".into(), String::new()]);
    push_multi_preamble(&mut l, ns);
    let off = push_block_code_defs(&mut l, lib, &names, &bin, 0..nb, 0);
    push_data_byte_defs(&mut l, lib, &names, &bin, off);
    l.push(String::new());
    l.push(format!(
        "/-- The code blocks of `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {} : List Obj.CodeBlock := [", names.blocks()));
    push_block_entries(&mut l, lib, &names, 0..nb);
    l.push("]".into());
    l.push(String::new());
    push_multi_lib_tail(&mut l, lib, &names, ns);
    l.join("\n")
}

/// Contiguous ranges of the code blocks of `lib` covering all of them in order, one per shard
/// (`n.max(1)` ranges, some possibly empty), balanced by code size.
pub fn shard_ranges(lib: &PMultiLib, n: usize) -> Vec<std::ops::Range<usize>> {
    let n = n.max(1);
    let weight = |b: &super::model::PBlock| b.code.len().max(1);
    let total: usize = lib.blocks.iter().map(weight).sum();
    let mut out = Vec::with_capacity(n);
    let (mut start, mut acc) = (0usize, 0usize);
    for (i, b) in lib.blocks.iter().enumerate() {
        acc += weight(b);
        // Close shard `k` once the blocks so far reach `(k + 1) / n` of the total weight.
        while out.len() + 1 < n && acc * n >= total * (out.len() + 1) {
            out.push(start..i + 1);
            start = i + 1;
        }
    }
    while out.len() < n {
        out.push(start..lib.blocks.len());
        start = lib.blocks.len();
    }
    out
}

/// [`render_multi_lib`] with the code blocks split over the shard modules `shard_modules`
/// (Lean module names, one per shard, siblings of the top module sharing its sidecar
/// `bin_name`): shard `k` defines the code constants of its blocks and `<obj>BlocksShard<k>`, and
/// the top module imports every shard and defines `<obj>Blocks` as their concatenation, so
/// `<obj>MultiLib` is the same value. Returns the top module and the shard modules in order;
/// with at most one shard module, the top module is exactly [`render_multi_lib`] and there are
/// no shards.
pub fn render_multi_lib_sharded(
    lib: &PMultiLib,
    obj_name: &str,
    ns: &str,
    bin_name: &str,
    license: &[String],
    shard_modules: &[String],
) -> (String, Vec<String>) {
    let n = shard_modules.len();
    if n <= 1 {
        return (render_multi_lib(lib, obj_name, ns, bin_name, license), vec![]);
    }
    let names = LibNames::new(obj_name);
    let bin = lean_string_lit(bin_name);
    let ranges = shard_ranges(lib, n);
    let mut shards = Vec::with_capacity(n);
    let mut off = 0usize;
    for (k, range) in ranges.iter().enumerate() {
        let mut l = multi_module_head(license, &[]);
        l.extend([
            format!(
                "/-! # Code blocks {}..{} of multi-block placed library `{}` (generated, Spec role)",
                range.start,
                range.end,
                doc_safe(&lib.name)
            ),
            String::new(),
            "Generated by `rust-obj2lean` (`untrusted_placed --multi-placed`, `placed_shards`), which"
                .into(),
            "`lake build` runs before compiling this library. DO NOT EDIT MANUALLY: this file is a"
                .into(),
            "gitignored build product.".into(),
            String::new(),
            format!(
                "Shard {k} of {n}: `{}` lists code blocks `{}..{}`; the top module joins the shards'",
                names.blocks_shard(k),
                range.start,
                range.end
            ),
            format!("lists into `{}`.", names.blocks()),
            String::new(),
            "## Code blocks".into(),
            String::new(),
        ]);
        push_block_docs(&mut l, lib, range.clone());
        l.extend(["-/".into(), String::new()]);
        push_multi_preamble(&mut l, ns);
        off = push_block_code_defs(&mut l, lib, &names, &bin, range.clone(), off);
        l.push(String::new());
        l.push(format!(
            "/-- Code blocks `{}..{}` of `{}`. -/",
            range.start,
            range.end,
            doc_safe(&lib.name)
        ));
        l.push(format!(
            "def {} : List Obj.CodeBlock := [",
            names.blocks_shard(k)
        ));
        push_block_entries(&mut l, lib, &names, range.clone());
        l.push("]".into());
        l.push(String::new());
        l.push(format!("end {ns}"));
        l.push(String::new());
        shards.push(l.join("\n"));
    }
    let mut l = multi_module_head(license, shard_modules);
    push_multi_doc_intro(&mut l, lib, &names);
    l.extend(["## Code block shards".into(), String::new()]);
    for (m, range) in shard_modules.iter().zip(&ranges) {
        l.push(format!("* `{m}`: blocks `{}..{}`", range.start, range.end));
    }
    push_unreferenced_docs(&mut l, lib);
    l.extend(["-/".into(), String::new()]);
    push_multi_preamble(&mut l, ns);
    push_data_byte_defs(&mut l, lib, &names, &bin, off);
    l.push(String::new());
    l.push(format!(
        "/-- The code blocks of `{}` (the concatenation of its shards' lists). -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {} : List Obj.CodeBlock :=", names.blocks()));
    // Right-nested, so the head of each shard is reached without re-walking earlier appends.
    let mut joined = names.blocks_shard(n - 1);
    for k in (0..n - 1).rev() {
        joined = if k + 2 == n {
            format!("{} ++ {joined}", names.blocks_shard(k))
        } else {
            format!("{} ++ ({joined})", names.blocks_shard(k))
        };
    }
    l.push(format!("  {joined}"));
    l.push(String::new());
    push_multi_lib_tail(&mut l, lib, &names, ns);
    (l.join("\n"), shards)
}

fn text_sec_names(lib: &PLib) -> Vec<(String, u64)> {
    lib.text_secs
        .iter()
        .map(|ts| (ts.label.clone(), ts.size))
        .collect()
}

/// Relative path from directory `from` to `to` (both absolute or both relative to the same root),
/// computed lexically.
pub fn relative_path(from: &Path, to: &Path) -> String {
    let fc: Vec<_> = from.components().collect();
    let tc: Vec<_> = to.components().collect();
    let common = fc.iter().zip(&tc).take_while(|(a, b)| a == b).count();
    let mut parts: Vec<String> = Vec::new();
    for _ in common..fc.len() {
        parts.push("..".into());
    }
    for c in &tc[common..] {
        parts.push(c.as_os_str().to_string_lossy().into_owned());
    }
    parts.join("/")
}

/// `<Obj>ElfObj.lean`: the bytes of the stock-linked ELF at `elf_rel` (relative to the module),
/// pinned by SHA-256 `elf_sha`, as `<obj>ElfBytes`.
pub fn render_elf(
    lib: &PLib,
    obj_name: &str,
    ns: &str,
    elf_rel: &str,
    elf_sha: &str,
    license: &[String],
) -> String {
    render_elf_named(&lib.name, obj_name, ns, elf_rel, elf_sha, license)
}

/// [`render_elf`] by library display name (shared by single-block and multi-block emitters).
pub fn render_elf_named(
    lib_name: &str,
    obj_name: &str,
    ns: &str,
    elf_rel: &str,
    elf_sha: &str,
    license: &[String],
) -> String {
    let names = LibNames::new(obj_name);
    let mut l = header(license);
    l.extend([
        "module".to_string(),
        String::new(),
        "public import Arm64.Trusted.Process".into(),
        String::new(),
        format!(
            "/-! # Stock-linked ELF of `{}` (generated, Spec role)",
            doc_safe(lib_name)
        ),
        String::new(),
        "Generated by `rust-obj2lean` (`untrusted_placed`), which `lake build` runs before compiling"
            .into(),
        "this library. DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "`{}` is the byte content of the tracked ELF `{}`, checked when this module is",
            names.elf_bytes,
            doc_safe(elf_rel)
        ),
        "elaborated (`file_bytes%`) against the SHA-256 pinned by `[placed] elf_sha256` in the".into(),
        "library's `translation.toml`. It does not depend on the placement.".into(),
        String::new(),
        "This module has the Spec role: campaign `Spec` statements about the real binary refer to".into(),
        "these bytes, and the trust guard classes this gitignored build product as Spec. The".into(),
        "tracked ELF and the pinned SHA-256 are its anchor; `Obj.PlacedLib.LinkedIn` ties the".into(),
        "placed library to exactly these bytes.".into(),
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "set_option maxRecDepth 2000000 in".into(),
        format!(
            "/-- The bytes of the stock-linked ELF `{}`. -/",
            doc_safe(elf_rel)
        ),
        format!("noncomputable def {} : List (BitVec 8) :=", names.elf_bytes),
        format!(
            "  file_bytes% {} sha256 {}",
            lean_string_lit(elf_rel),
            lean_string_lit(elf_sha)
        ),
        String::new(),
        format!("end {ns}"),
        String::new(),
    ]);
    l.join("\n")
}

/// Witness-wide options, emitted right after the `open` and before the first definition: the
/// placement lists (`<obj>Rho`, `<obj>Relaxed`, multi-block `<obj>Bases`, ...) of a large library
/// already exceed the default `maxRecDepth` when elaborated, so the option must precede them.
/// Linked witnesses also lift `maxHeartbeats` for the ELF parse and kernel checks.
fn push_witness_options(l: &mut Vec<String>, linked: bool) {
    if linked {
        l.push("set_option maxHeartbeats 0".into());
    }
    l.extend(["set_option maxRecDepth 2000000".into(), String::new()]);
}

/// `<…>PlacedWitness.lean`: the placement `pl` of `lib` in the ELF at `elf_rel` (relative to
/// the module), importing `<Obj>PlacedObj` (`lib_module`) and the module defining the ELF bytes
/// (`elf_module`); with `linked`, also the kernel-checked `Obj.PlacedLib.LinkedIn <obj>Lib
/// <elf bytes>`. `names` picks the names the module defines ([`WitNames`]). The main module of
/// [`render_witness_files`] for a witness without shards (`wn.chunked` unset).
#[allow(clippy::too_many_arguments)]
pub fn render_witness(
    lib: &PLib,
    pl: &PPlacement,
    wn: &WitNames,
    ns: &str,
    lib_module: &str,
    elf_module: &str,
    elf_rel: &str,
    linked: bool,
    license: &[String],
) -> String {
    let files = render_witness_files(
        lib, pl, wn, ns, "", lib_module, elf_module, elf_rel, linked, license,
    );
    assert!(files.shards.is_empty(), "a chunked witness has shard modules");
    files.main
}

/// [`render_witness`] as the modules of witness module `witness_module`: with `linked` and
/// `wn.chunked`, a `Defs` shard, one shard per kernel fact and a main module composing them
/// ([`super::chunked`]); otherwise one module.
#[allow(clippy::too_many_arguments)]
pub fn render_witness_files(
    lib: &PLib,
    pl: &PPlacement,
    wn: &WitNames,
    ns: &str,
    witness_module: &str,
    lib_module: &str,
    elf_module: &str,
    elf_rel: &str,
    linked: bool,
    license: &[String],
) -> MultiWitnessFiles {
    let names = wn;
    let chunked = linked && wn.chunked;
    let mut imports = vec![
        format!("public import {lib_module}"),
        format!("public import {elf_module}"),
    ];
    if linked {
        imports.push(format!("public import {}", linked_facts(wn).module));
        imports.extend([
            "public import ProofLib.Placed.Check".into(),
            "public meta import ProofLib.Process".into(),
            "public meta import ProofLib.ProgramReflection".into(),
        ]);
    }
    if chunked {
        imports.extend([
            "public import ProofLib.Placed.SplitSingleFast".into(),
            "public import ProofLib.Placed.NamesTree".into(),
            "public meta import ProofLib.Placed.Split".into(),
        ]);
    }
    let title = format!(
        "/-! # Placement of `{}` in a stock-linked ELF (untrusted generator output)",
        doc_safe(&lib.name)
    );
    let generated = [
        "Generated by `rust-obj2lean` (`untrusted_placed`), which `lake build` runs before compiling"
            .to_string(),
        "this library. DO NOT EDIT MANUALLY: this file is a gitignored build product.".to_string(),
    ];
    let census = format!(
        "Census: {} relocations, {} relaxed pairs, {} branch-to-branch sites.",
        lib.text.relocs.len(),
        pl.relax.len(),
        pl.b2b.len()
    );
    let mut l = header(license);
    l.extend(["module".to_string(), String::new()]);
    l.extend(imports.iter().cloned());
    l.extend([String::new(), title.clone(), String::new()]);
    l.extend(generated.iter().cloned());
    l.extend([
        String::new(),
        format!(
            "`{}` is read off the ELF `{}` (pinned by SHA-256 in `{}`): the block",
            names.placement,
            doc_safe(elf_rel),
            names.elf_bytes
        ),
        "base, the address of every non-block symbol the library references, the relaxed".into(),
        "`ADRP`+`ADD` pairs and the branch-to-branch retargeted branches. The generator checked it"
            .into(),
        "against the ELF bytes before emitting it, but nothing here is trusted: the kernel checks"
            .into(),
        format!("`Obj.PlacedLib.LinkedIn {} {}`.", names.lib.lib, names.elf_bytes),
    ]);
    if linked && !chunked {
        l.extend([
            String::new(),
            format!(
                "`{} : {}.LinkedIn {}` is checked by the kernel (`decide +kernel` on",
                names.linked_in, names.lib.lib, names.elf_bytes
            ),
            "`Obj.Interned.check`), from the interned form of the library (symbol names replaced by"
                .into(),
            "indices into a code-point-sorted name table), the interned placement and the parsed ELF."
                .into(),
        ]);
    }
    l.extend([String::new(), census.clone()]);
    if chunked {
        l.extend([
            String::new(),
            format!(
                "The definitions shard of `{witness_module}`: the kernel facts are in its other shard"
            ),
            "modules, and the main module composes them.".into(),
        ]);
    }
    l.extend([
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64".into(),
    ]);
    let lib_open = wn.lib_ns.as_deref().filter(|o| chunked && *o != ns);
    if let Some(o) = lib_open {
        l.push(format!("open {o}"));
    }
    l.push(String::new());
    push_witness_options(&mut l, linked);
    l.extend([
        "/-- Addresses of the non-block symbols the library references. -/".into(),
    ]);
    l.push(format!("def {} : List (String × Nat) := [", names.rho));
    let n = pl.rho.len();
    for (i, (s, a)) in pl.rho.iter().enumerate() {
        let sep = if i + 1 < n { "," } else { "" };
        l.push(format!("  ({}, {a:#x}){sep}", lean_string_lit(s)));
    }
    l.push("]".into());
    l.push(String::new());
    l.push("/-- `ADRP` byte offsets of the relaxed `ADRP`+`ADD` pairs. -/".into());
    l.push(format!(
        "def {} : List Nat := [{}]",
        names.relax,
        pl.relax
            .iter()
            .map(|o| format!("{o:#x}"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    l.push(String::new());
    l.push("/-- Byte offsets of the branches retargeted past a block `B`. -/".into());
    l.push(format!(
        "def {} : List Nat := [{}]",
        names.b2b,
        pl.b2b
            .iter()
            .map(|o| format!("{o:#x}"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    l.push(String::new());
    l.push(format!(
        "/-- Where the stock link placed `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {} : Obj.Placement where", names.placement));
    l.push(format!("  base := {:#x}#64", pl.base));
    l.push(format!(
        "  ρ := fun s => BitVec.ofNat 64 ((Obj.lookup s {}).getD 0)",
        names.rho
    ));
    l.push(format!(
        "  relax := fun off => {}.contains off",
        names.relax
    ));
    l.push(format!("  b2b := fun off => {}.contains off", names.b2b));
    push_undef_weak(&mut l, &pl.undef_weak);
    l.push(String::new());
    if chunked {
        let mut out = LinkedOut::Split(Vec::new());
        super::chunked::push_linked_chunked(&mut out, lib, pl, wn, elf_rel);
        let LinkedOut::Split(parts) = out else {
            unreachable!()
        };
        return assemble_split_witness(SplitWitness {
            defs_head: l,
            parts,
            imports: &imports,
            witness_module,
            ns,
            lib_open,
            title,
            generated: &generated,
            census,
            license,
        });
    }
    if linked {
        push_linked(&mut l, lib, pl, wn, elf_rel);
    }
    l.push(format!("end {ns}"));
    l.push(String::new());
    MultiWitnessFiles {
        main: l.join("\n"),
        shards: Vec::new(),
    }
}

/// Every symbol name `lib` uses (block symbols, externs, relocation targets, data objects,
/// exports), sorted by code point (byte order of UTF-8), without duplicates.
pub fn interned_names(lib: &PLib) -> Vec<String> {
    let mut set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    set.extend(lib.text.symbols.iter().map(|(n, _)| n.clone()));
    set.extend(lib.text.externs.iter().cloned());
    set.extend(lib.text.relocs.iter().map(|r| r.sym.clone()));
    for d in &lib.data {
        set.insert(d.sym.clone());
        set.extend(d.relocs.iter().map(|r| r.sym.clone()));
    }
    set.extend(lib.exports.iter().cloned());
    set.into_iter().collect()
}

pub(super) fn name_idx(names: &[String], s: &str) -> usize {
    names
        .binary_search_by(|n| n.as_str().cmp(s))
        .unwrap_or_else(|_| panic!("symbol {s} missing from the interned name table"))
}

fn render_interned_reloc(names: &[String], r: &PReloc) -> String {
    let mut parts = vec![
        format!("off := {}", r.off),
        format!("kind := {}", r.kind.lean_name()),
        format!("sym := {}", name_idx(names, &r.sym)),
    ];
    if r.addend != 0 {
        parts.push(format!("addend := {}", r.addend));
    }
    format!("{{ {} }}", parts.join(", "))
}

pub(super) fn push_interned_lib_and_layout(
    l: &mut Vec<String>,
    lib: &PLib,
    pl: &PPlacement,
    wn: &WitNames,
    with_lib_eq: bool,
) {
    let names = &wn.lib;
    let tbl = interned_names(lib);
    let idx = |s: &str| name_idx(&tbl, s);
    let lib_l = &wn.lib_l;
    let ly = &wn.ly;
    let name_chars = &wn.name_chars;
    let lib_eq = &wn.lib_eq;
    // Name table.
    l.push("/-- The interned name table, sorted by code point. -/".into());
    l.push(format!(
        "noncomputable def {name_chars} : List (List Char) := ["
    ));
    for (i, n) in tbl.iter().enumerate() {
        let sep = if i + 1 < tbl.len() { "," } else { "]" };
        l.push(format!("  str_chars% {}{sep}", lean_string_lit(n)));
    }
    if tbl.is_empty() {
        l.push("]".into());
    }
    l.push(String::new());
    // Interned library.
    let mut syms = lib.text.symbols.clone();
    syms.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    l.push(format!(
        "/-- `{}` with symbol names interned. -/",
        names.lib
    ));
    l.push(format!("def {lib_l} : Obj.Interned.Lib where"));
    l.push(format!("  name := {}", lean_string_lit(&lib.name)));
    push_list(
        l,
        "  ",
        "names",
        tbl.iter().map(|n| lean_string_lit(n)).collect(),
    );
    l.push(format!("  code := {}", names.code));
    l.push(format!("  align := {}", lib.text.align));
    push_list(
        l,
        "  ",
        "symbols",
        syms.iter()
            .map(|(n, o)| format!("({}, {o:#x})", idx(n)))
            .collect(),
    );
    push_list(
        l,
        "  ",
        "relocs",
        lib.text
            .relocs
            .iter()
            .map(|r| render_interned_reloc(&tbl, r))
            .collect(),
    );
    push_list(
        l,
        "  ",
        "externs",
        lib.text
            .externs
            .iter()
            .map(|e| idx(e).to_string())
            .collect(),
    );
    push_list_nonempty(
        l,
        "  ",
        "weakRefs",
        lib.text
            .weak_refs
            .iter()
            .map(|e| idx(e).to_string())
            .collect(),
    );
    let data: Vec<String> = lib
        .data
        .iter()
        .enumerate()
        .map(|(i, d)| {
            let rs: Vec<String> = d
                .relocs
                .iter()
                .map(|r| render_interned_reloc(&tbl, r))
                .collect();
            format!(
                "{{ sym := {}, align := {}, readOnly := {}, bytes := {}, zeroTail := {}, relocs := [{}] }}",
                idx(&d.sym),
                d.align,
                d.read_only,
                names.data_bytes(i),
                d.zero_tail,
                rs.join(", ")
            )
        })
        .collect();
    push_list(l, "  ", "data", data);
    push_list(
        l,
        "  ",
        "exports",
        lib.exports.iter().map(|e| idx(e).to_string()).collect(),
    );
    l.push(String::new());
    if with_lib_eq {
        l.push(format!(
            "theorem {lib_eq} : {} = {lib_l}.toLib := by rfl_kernel",
            names.lib
        ));
        l.push(String::new());
    }
    l.push(format!(
        "theorem {lib_l}_names : {lib_l}.names = {name_chars}.map String.ofList := by rfl_kernel"
    ));
    l.push(String::new());
    // Interned layout.
    l.push(format!(
        "/-- `{}` with addresses indexed by the name table (`0` for block symbols). -/",
        wn.placement
    ));
    l.push(format!("def {ly} : Obj.Interned.Layout where"));
    l.push(format!("  base := {:#x}#64", pl.base));
    push_list(
        l,
        "  ",
        "addrs",
        tbl.iter()
            .map(|n| format!("{:#x}#64", pl.rho.get(n).copied().unwrap_or(0)))
            .collect(),
    );
    l.push(format!(
        "  relax := [{}]",
        pl.relax
            .iter()
            .map(|o| format!("{o:#x}"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    l.push(format!(
        "  b2b := [{}]",
        pl.b2b
            .iter()
            .map(|o| format!("{o:#x}"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    push_list_nonempty(
        l,
        "  ",
        "undefWeak",
        pl.undef_weak.iter().map(|s| idx(s).to_string()).collect(),
    );
    l.push(String::new());
}

/// The facts module of a linked witness (set by the generator for every linked witness).
fn linked_facts(wn: &WitNames) -> &super::facts::ElfFacts {
    wn.facts
        .as_ref()
        .expect("a linked witness names its ELF facts module")
}

/// The witness's names for the parsed ELF at `elf_rel`, its parse theorem and symbol tables, as
/// reducible aliases of the declarations of its facts module. Each theorem is restated against
/// the witness's own bytes constant and checked at reducible transparency, so it is O(1) and a
/// facts module about other bytes fails to elaborate.
pub(super) fn push_elf_aliases(l: &mut Vec<String>, wn: &WitNames, elf_rel: &str) {
    let f = linked_facts(wn);
    let (elf, elf_parse, elf_syms, elf_sym_chars, elf_bytes) = (
        &wn.elf,
        &wn.elf_parse,
        &wn.elf_syms,
        &wn.elf_sym_chars,
        &wn.elf_bytes,
    );
    l.extend([
        format!(
            "/-- The parsed ELF `{}` (`{}`, checked against `{elf_bytes}` by `{elf_parse}`). -/",
            doc_safe(elf_rel),
            f.image
        ),
        format!("noncomputable abbrev {elf} : ElfImage := {}", f.image),
        String::new(),
        format!("theorem {elf_parse} : ElfImage.parse {elf_bytes} = .ok {elf} := by"),
        format!("  with_reducible exact {}", f.parse),
        String::new(),
        format!(
            "noncomputable abbrev {elf_syms} : List (String × BitVec 64) := {}",
            f.syms
        ),
        String::new(),
        format!(
            "noncomputable abbrev {elf_sym_chars} : List (List Char × BitVec 64) := {}",
            f.sym_chars
        ),
        String::new(),
        format!("theorem {elf_syms}_eq : {elf}.symbols = toStringAssoc {elf_sym_chars} := by"),
        format!("  with_reducible exact {}", f.syms_eq),
        String::new(),
    ]);
}

/// The interned form of `lib` and `pl`, the parsed ELF at `elf_rel` and the kernel-checked
/// `Obj.PlacedLib.LinkedIn <obj>Lib <elf bytes>` (`ProofLib.Placed.Check`), appended to `l`
/// inside the witness module's namespace.
fn push_linked(l: &mut Vec<String>, lib: &PLib, pl: &PPlacement, wn: &WitNames, elf_rel: &str) {
    let names = &wn.lib;
    let lib_l = &wn.lib_l;
    let ly = &wn.ly;
    let elf = &wn.elf;
    let elf_parse = &wn.elf_parse;
    let elf_syms = &wn.elf_syms;
    let elf_bytes = &wn.elf_bytes;
    let lib_eq = &wn.lib_eq;
    l.extend([
        "open Arm64.Process ProofLib.ProgramReflection".into(),
        String::new(),
    ]);
    push_interned_lib_and_layout(l, lib, pl, wn, true);
    push_elf_aliases(l, wn, elf_rel);
    if let Some(ok) = &wn.ok {
        let pl_term = format!("({ly}.toPlacement {lib_l}.names)");
        l.push(format!(
            "/-- `{}` is placeable at `{pl_term}` and placed there in `{elf}` (kernel-checked). -/",
            doc_safe(&lib.name)
        ));
        l.push(format!(
            "theorem {ok} : {lib}.Placeable {pl_term} ∧ {lib}.InElf {elf} {pl_term} := by",
            lib = names.lib
        ));
        l.push(format!("  rw [{lib_eq}]"));
        l.push(format!(
            "  exact Obj.Interned.check_spec {lib_l}_names {elf_syms}_eq (by decide +kernel)"
        ));
        l.push(String::new());
    }
    l.push(format!(
        "/-- `{}` is linked into the stock-linked ELF `{}` at `{}`. -/",
        doc_safe(&lib.name),
        doc_safe(elf_rel),
        wn.placement
    ));
    l.push(format!(
        "theorem {} : {}.LinkedIn {elf_bytes} :=",
        wn.linked_in, names.lib
    ));
    if let Some(ok) = &wn.ok {
        l.push(format!("  ⟨_, {elf}, {elf_parse}, {ok}.1, {ok}.2⟩"));
    } else {
        l.push(format!(
            "  Obj.Interned.linkedIn_of_check (ly := {ly}) {lib_eq} {lib_l}_names {elf_parse} {elf_syms}_eq"
        ));
        l.push("    (by decide +kernel)".into());
    }
    l.push(String::new());
}

/// The ELF-free `Placeable` + extern-distinctness theorem `wn.placeable_and_externs`, assembled
/// from one `decide +kernel` theorem per conjunct of `Obj.Interned.checkPlaceableExt` (names
/// sorted, indices in range, table size, text fields, data objects, text relocations, extern
/// distinctness). Each tree conjunct re-builds the symbol tree, which is cheap; checking them in
/// separate declarations keeps the kernel's peak memory to that of the largest conjunct.
fn push_split_placeable_check(l: &mut Vec<String>, wn: &WitNames, lib_doc_name: &str) {
    let lib_name = &wn.lib.lib;
    let lib_l = &wn.lib_l;
    let ly = &wn.ly;
    let lib_eq = &wn.lib_eq;
    let p = &wn.placement;
    let pl_term = format!("({ly}.toPlacement {lib_l}.names)");
    let tree = |body: &str| {
        format!(
            "(withNat {lib_l}.names.length fun n =>\n    buildSymTree {lib_l} {ly} 20 0 n {ly}.addrs \
             fun t _ => {body}) = true"
        )
    };
    let thm =
        |name: &str, stmt: String| format!("theorem {p}_{name} : {stmt} := by\n  decide +kernel");
    l.extend([
        "section".to_string(),
        String::new(),
        "open Arm64.Obj.Interned".into(),
        String::new(),
        format!("private theorem {p}_tree {{L : Lib}} {{ly : Layout}} {{p : VecTree SymSlot → Bool}}"),
        "    (hn : Nat.blt L.names.length 1048576 = true)".into(),
        "    (h : (withNat L.names.length fun n =>".into(),
        "      buildSymTree L ly 20 0 n ly.addrs fun t _ => p t) = true) :".into(),
        "    ∃ t, p t = true ∧ ∀ i < L.names.length,".into(),
        "      t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64) := by".into(),
        "  rw [withNat_eq] at h".into(),
        "  obtain ⟨t, hk, ht⟩ := buildSymTree_spec L ly 20 0 _ ly.addrs _".into(),
        "    (by rw [Nat.blt_eq] at hn; exact hn) h".into(),
        "  exact ⟨t, hk, fun i hi => by simpa using ht i hi⟩".into(),
        String::new(),
        thm("namesOk", format!("namesNodup {} = true", wn.name_chars)),
        thm("idsOk", format!("{lib_l}.idsOk = true")),
        thm("sizeOk", format!("Nat.blt {lib_l}.names.length 1048576 = true")),
        thm("textOk", tree(&format!("textPlaceableTree {lib_l} {ly} t"))),
        thm("dataOk", tree(&format!("dataPlaceableTree {lib_l} t"))),
        thm("relocsOk", tree(&format!("textRelocsOkTree {lib_l} {ly} t"))),
        thm("externsOk", tree(&format!("externsDisjointTree {lib_l} t"))),
        String::new(),
        format!(
            "/-- `{}` is placeable at `{pl_term}` with pairwise-distinct extern addresses (kernel-checked). -/",
            doc_safe(lib_doc_name)
        ),
        format!("theorem {} :", wn.placeable_and_externs),
        format!(
            "    {lib_name}.Placeable {pl_term} ∧ ({lib_name}.text.externs.map {pl_term}.ρ).Nodup := by"
        ),
        format!("  have hnd := nodup_of_namesNodup {lib_l}_names {p}_namesOk"),
        format!("  have hok := Lib.idsOk_spec {p}_idsOk"),
        format!("  obtain ⟨t1, h1, ht1⟩ := {p}_tree {p}_sizeOk {p}_textOk"),
        format!("  obtain ⟨t2, h2, ht2⟩ := {p}_tree {p}_sizeOk {p}_dataOk"),
        format!("  obtain ⟨t3, h3, ht3⟩ := {p}_tree {p}_sizeOk {p}_relocsOk"),
        format!("  obtain ⟨t4, h4, ht4⟩ := {p}_tree {p}_sizeOk {p}_externsOk"),
        "  rw [textPlaceableTree_eq hok ht1] at h1".into(),
        "  rw [dataPlaceableTree_eq hok ht2] at h2".into(),
        "  rw [textRelocsOkTree_eq hok ht3] at h3".into(),
        "  rw [externsDisjointTree_eq hok ht4] at h4".into(),
        format!("  rw [{lib_eq}]"),
        "  exact ⟨placeable_of hnd hok h1 h2 (walkOk_of_textRelocsOkB h3),".into(),
        "    externsDisjoint_of_externsDisjointB rfl rfl hnd hok h4⟩".into(),
        String::new(),
        "end".into(),
        String::new(),
    ]);
}

/// Every symbol name a multi-block `lib` uses, sorted by code point without duplicates.
pub fn interned_multi_names(lib: &PMultiLib) -> Vec<String> {
    let mut set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for b in &lib.blocks {
        set.extend(b.symbols.iter().map(|(n, _)| n.clone()));
        set.extend(b.externs.iter().cloned());
        set.extend(b.relocs.iter().map(|r| r.sym.clone()));
    }
    for d in &lib.data {
        set.insert(d.sym.clone());
        set.extend(d.relocs.iter().map(|r| r.sym.clone()));
    }
    set.extend(lib.exports.iter().cloned());
    set.extend(lib.export_syms.iter().map(|(_, raw)| raw.clone()));
    set.into_iter().collect()
}

/// The modules of a multi-block witness. `main` is `<…>PlacedWitness.lean`. With
/// `split_check_module` (and `linked`), `shards` lists `(suffix, text)` for the sibling modules
/// `<…>PlacedWitnessShard<suffix>.lean`: `Defs` (the definitions and the cheap facts), then one
/// module per heavy kernel fact, which `main` imports and composes. Lake checks each module in
/// its own Lean process, so a module's peak memory is that of one fact.
pub struct MultiWitnessFiles {
    pub main: String,
    pub shards: Vec<(String, String)>,
}

/// Where [`push_multi_linked`] writes: one module, or the named parts of a split witness, which
/// [`render_multi_witness_files`] turns into the `Defs` shard, one shard per other part, and the
/// main module (part `""`).
pub(super) enum LinkedOut<'a> {
    One(&'a mut Vec<String>),
    Split(Vec<(String, Vec<String>)>),
}

impl LinkedOut<'_> {
    /// The lines of part `name`, created on first use (the whole module when not split).
    pub(super) fn part(&mut self, name: &str) -> &mut Vec<String> {
        match self {
            LinkedOut::One(l) => l,
            LinkedOut::Split(parts) => {
                let i = match parts.iter().position(|(n, _)| n == name) {
                    Some(i) => i,
                    None => {
                        parts.push((name.to_string(), Vec::new()));
                        parts.len() - 1
                    }
                };
                &mut parts[i].1
            }
        }
    }
}

/// The main module of [`render_multi_witness_files`] for a witness without shards.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub fn render_multi_witness(
    lib: &PMultiLib,
    mpl: &PMultiPlacement,
    wn: &WitNames,
    ns: &str,
    lib_module: &str,
    elf_module: &str,
    elf_rel: &str,
    linked: bool,
    license: &[String],
) -> String {
    let files = render_multi_witness_files(
        lib, mpl, wn, ns, "", lib_module, elf_module, elf_rel, linked, license,
    );
    assert!(files.shards.is_empty(), "a split witness has shard modules");
    files.main
}

/// `<…>PlacedWitness.lean` (module `witness_module`) for a multi-block library
/// (`Obj.MultiPlacedLib`), and its shard modules ([`MultiWitnessFiles`]).
#[allow(clippy::too_many_arguments)]
pub fn render_multi_witness_files(
    lib: &PMultiLib,
    mpl: &PMultiPlacement,
    wn: &WitNames,
    ns: &str,
    witness_module: &str,
    lib_module: &str,
    elf_module: &str,
    elf_rel: &str,
    linked: bool,
    license: &[String],
) -> MultiWitnessFiles {
    let names = wn;
    let bases_name = format!(
        "{}Bases",
        names
            .placement
            .strip_suffix("Placement")
            .unwrap_or(&names.placement)
    );
    let mut imports = vec![
        format!("public import {lib_module}"),
        format!("public import {elf_module}"),
    ];
    if linked {
        imports.push(format!("public import {}", linked_facts(wn).module));
        imports.push("public import ProofLib.Placed.Multi".into());
        if wn.extern_symtab.as_ref().is_some_and(|(ok, _)| !ok.is_empty()) {
            imports.push("public import ProofLib.Placed.ExternSymtab".into());
        }
        imports.extend([
            "public meta import ProofLib.Process".into(),
            "public meta import ProofLib.ProgramReflection".into(),
        ]);
        if let Some(m) = &wn.split_check {
            imports.push(format!("public import {m}"));
            imports.push(format!("public meta import {m}"));
        }
    }
    let split = linked && wn.split_check.is_some();
    let mut l = header(license);
    l.extend(["module".to_string(), String::new()]);
    l.extend(imports.iter().cloned());
    let total_relocs: usize = lib.blocks.iter().map(|b| b.relocs.len()).sum();
    let total_relax: usize = mpl.relax.iter().map(|r| r.len()).sum();
    let total_b2b: usize = mpl.b2b.iter().map(|b| b.len()).sum();
    let title = format!(
        "/-! # Multi-block placement of `{}` in a stock-linked ELF (untrusted generator output)",
        doc_safe(&lib.name)
    );
    let generated = [
        "Generated by `rust-obj2lean` (`untrusted_placed`), which `lake build` runs before compiling"
            .to_string(),
        "this library. DO NOT EDIT MANUALLY: this file is a gitignored build product.".to_string(),
    ];
    let census = format!(
        "Census: {} blocks, {} relocations, {} relaxed pairs, {} branch-to-branch sites.",
        lib.blocks.len(),
        total_relocs,
        total_relax,
        total_b2b
    );
    l.extend([String::new(), title.clone(), String::new()]);
    l.extend(generated.iter().cloned());
    l.extend([String::new(), census.clone()]);
    if split {
        l.extend([
            String::new(),
            format!(
                "The definitions shard of `{witness_module}`: the kernel facts are in its other shard"
            ),
            "modules, and the main module composes them.".into(),
        ]);
    }
    l.extend([
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64".into(),
        String::new(),
    ]);
    push_witness_options(&mut l, linked);
    push_list(
        &mut l,
        "",
        &format!("def {bases_name} : List (BitVec 64)"),
        mpl.bases.iter().map(|b| format!("{b:#x}#64")).collect(),
    );
    l.push(String::new());
    l.push(format!("def {} : List (String × Nat) := [", names.rho));
    let n = mpl.rho.len();
    for (i, (s, a)) in mpl.rho.iter().enumerate() {
        let sep = if i + 1 < n { "," } else { "" };
        l.push(format!("  ({}, {a:#x}){sep}", lean_string_lit(s)));
    }
    l.push("]".into());
    l.push(String::new());
    let relax_items: Vec<String> = mpl
        .relax
        .iter()
        .map(|s| {
            format!(
                "[{}]",
                s.iter()
                    .map(|o| format!("{o:#x}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .collect();
    push_list(
        &mut l,
        "",
        &format!("def {} : List (List Nat)", names.relax),
        relax_items,
    );
    l.push(String::new());
    let b2b_items: Vec<String> = mpl
        .b2b
        .iter()
        .map(|s| {
            format!(
                "[{}]",
                s.iter()
                    .map(|o| format!("{o:#x}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
        .collect();
    push_list(
        &mut l,
        "",
        &format!("def {} : List (List Nat)", names.b2b),
        b2b_items,
    );
    l.push(String::new());
    l.push(format!("def {} : Obj.MultiPlacement where", names.placement));
    l.push(format!("  base := fun i => {bases_name}.getD i 0#64"));
    l.push(format!(
        "  ρ := fun s => BitVec.ofNat 64 ((Obj.lookup s {}).getD 0)",
        names.rho
    ));
    l.push(format!(
        "  relax := fun i off => ({}.getD i []).contains off",
        names.relax
    ));
    l.push(format!(
        "  b2b := fun i off => ({}.getD i []).contains off",
        names.b2b
    ));
    push_undef_weak(&mut l, &mpl.undef_weak);
    l.push(String::new());
    if !split {
        if linked {
            push_multi_linked(&mut LinkedOut::One(&mut l), lib, mpl, wn, elf_rel);
        }
        l.push(format!("end {ns}"));
        l.push(String::new());
        return MultiWitnessFiles {
            main: l.join("\n"),
            shards: Vec::new(),
        };
    }
    let mut out = LinkedOut::Split(Vec::new());
    push_multi_linked(&mut out, lib, mpl, wn, elf_rel);
    let LinkedOut::Split(parts) = out else {
        unreachable!()
    };
    assemble_split_witness(SplitWitness {
        defs_head: l,
        parts,
        imports: &imports,
        witness_module,
        ns,
        lib_open: None,
        title,
        generated: &generated,
        census,
        license,
    })
}

/// The pieces [`assemble_split_witness`] turns into the modules of a split witness.
pub(super) struct SplitWitness<'a> {
    /// The `Defs` shard up to and including its options (header, imports, module doc, namespace).
    pub defs_head: Vec<String>,
    /// The named parts of [`LinkedOut::Split`]: `Defs`, the heavy facts, and `""` (main).
    pub parts: Vec<(String, Vec<String>)>,
    /// The imports every module of the witness repeats.
    pub imports: &'a [String],
    pub witness_module: &'a str,
    pub ns: &'a str,
    /// An extra namespace every module `open`s (that of the library module, when it differs).
    pub lib_open: Option<&'a str>,
    /// The module-doc title line (`/-! # …`) of the main module.
    pub title: String,
    /// The module-doc lines saying the file is generated.
    pub generated: &'a [String],
    /// The module-doc census line of the main module.
    pub census: String,
    pub license: &'a [String],
}

/// The `Defs` shard (`defs_head` plus part `Defs`), one shard per other named part (importing
/// `Defs`), and the main module (part `""`, importing every shard) of a split witness.
pub(super) fn assemble_split_witness(w: SplitWitness) -> MultiWitnessFiles {
    let SplitWitness {
        defs_head: mut l,
        parts,
        imports,
        witness_module,
        ns,
        lib_open,
        title,
        generated,
        census,
        license,
    } = w;
    let shard_module = |s: &str| format!("{witness_module}Shard{s}");
    // Each module repeats the namespace, `open`s and options (they are module-local).
    let preamble = |l: &mut Vec<String>| {
        l.extend([
            String::new(),
            "@[expose] public section".into(),
            String::new(),
            format!("namespace {ns}"),
            String::new(),
            "open Arm64".into(),
            "open Arm64.Process ProofLib.ProgramReflection".into(),
        ]);
        l.extend(lib_open.map(|o| format!("open {o}")));
        l.push(String::new());
        push_witness_options(l, true);
    };
    let defs_import = format!("public import {}", shard_module("Defs"));
    let mut shards = Vec::new();
    let mut main_body = Vec::new();
    for (name, body) in parts {
        if name == "Defs" {
            l.extend(body);
            l.push(format!("end {ns}"));
            l.push(String::new());
            shards.push(("Defs".to_string(), std::mem::take(&mut l).join("\n")));
            continue;
        }
        if name.is_empty() {
            main_body = body;
            continue;
        }
        let mut s = header(license);
        s.extend(["module".to_string(), String::new()]);
        s.extend(imports.iter().cloned());
        s.push(defs_import.clone());
        s.extend([
            String::new(),
            format!(
                "/-! # `{name}` kernel fact of `{witness_module}` (untrusted generator output)"
            ),
            String::new(),
        ]);
        s.extend(generated.iter().cloned());
        s.extend([
            String::new(),
            "Lake checks this module in its own Lean process, so its peak memory is that of this"
                .into(),
            "fact alone.".into(),
            "-/".into(),
        ]);
        preamble(&mut s);
        s.extend(body);
        s.push(format!("end {ns}"));
        s.push(String::new());
        shards.push((name, s.join("\n")));
    }
    let mut m = header(license);
    m.extend(["module".to_string(), String::new()]);
    m.extend(imports.iter().cloned());
    m.extend(
        shards
            .iter()
            .map(|(s, _)| format!("public import {}", shard_module(s))),
    );
    m.extend([String::new(), title, String::new()]);
    m.extend(generated.iter().cloned());
    m.extend([
        String::new(),
        census,
        String::new(),
        format!("The definitions are in `{}`, and each heavy kernel fact", shard_module("Defs")),
        format!("in its own `{witness_module}Shard*` module (checked in a separate Lean process);"),
        "this module composes them.".into(),
        "-/".into(),
    ]);
    preamble(&mut m);
    m.extend(main_body);
    m.push(format!("end {ns}"));
    m.push(String::new());
    MultiWitnessFiles {
        main: m.join("\n"),
        shards,
    }
}

/// The interned library, layout, ELF aliases and kernel-checked placement theorems of a linked
/// multi-block witness. Each group of declarations goes to its part of `out` ([`LinkedOut`]):
/// `Defs` for the definitions and cheap facts, one part per heavy kernel fact of a split check,
/// and `""` (the main module) for the theorems that compose them.
fn push_multi_linked(
    out: &mut LinkedOut,
    lib: &PMultiLib,
    mpl: &PMultiPlacement,
    wn: &WitNames,
    elf_rel: &str,
) {
    let names = &wn.lib;
    let tbl = interned_multi_names(lib);
    let idx = |s: &str| name_idx(&tbl, s);
    let lib_l = &wn.lib_l;
    let ly = &wn.ly;
    let name_chars = &wn.name_chars;
    let elf = &wn.elf;
    let elf_parse = &wn.elf_parse;
    let elf_syms = &wn.elf_syms;
    let elf_bytes = &wn.elf_bytes;
    let lib_eq = &wn.lib_eq;
    let ok_name = wn
        .ok
        .clone()
        .unwrap_or_else(|| format!("{}_ok", names.lib));
    let l = out.part("Defs");
    l.extend([
        "open Arm64.Process ProofLib.ProgramReflection".into(),
        String::new(),
    ]);
    l.push("/-- The interned name table, sorted by code point. -/".into());
    l.push(format!(
        "noncomputable def {name_chars} : List (List Char) := ["
    ));
    for (i, n) in tbl.iter().enumerate() {
        let sep = if i + 1 < tbl.len() { "," } else { "]" };
        l.push(format!("  str_chars% {}{sep}", lean_string_lit(n)));
    }
    if tbl.is_empty() {
        l.push("]".into());
    }
    l.push(String::new());
    // Every block of a multi-block library shares one extern list (`build_multi_placed_lib`), so
    // emit it once and refer to it from each block; blocks with a different list keep their own.
    let shared_externs = lib.blocks.first().map(|b| b.externs.clone());
    let shared_externs_name = format!("{lib_l}Externs");
    if let Some(ext) = &shared_externs {
        l.push("/-- The extern list shared by the blocks of the interned library. -/".into());
        let ext_s: Vec<String> = ext.iter().map(|e| idx(e).to_string()).collect();
        l.push(format!(
            "def {shared_externs_name} : List Nat := [{}]",
            ext_s.join(", ")
        ));
        l.push(String::new());
    }
    l.push(format!("def {lib_l} : Obj.Interned.MultiLib where"));
    l.push(format!("  name := {}", lean_string_lit(&lib.name)));
    push_list(
        l,
        "  ",
        "names",
        tbl.iter().map(|n| lean_string_lit(n)).collect(),
    );
    let blocks: Vec<String> = lib
        .blocks
        .iter()
        .enumerate()
        .map(|(bi, b)| {
            let mut syms = b.symbols.clone();
            syms.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
            let syms_s: Vec<String> = syms
                .iter()
                .map(|(n, o)| format!("({}, {o:#x})", idx(n)))
                .collect();
            let rels_s: Vec<String> = b
                .relocs
                .iter()
                .map(|r| render_interned_reloc(&tbl, r))
                .collect();
            let exts_s = if shared_externs.as_ref() == Some(&b.externs) {
                shared_externs_name.clone()
            } else {
                let es: Vec<String> = b.externs.iter().map(|e| idx(e).to_string()).collect();
                format!("[{}]", es.join(", "))
            };
            let weak_s = if b.weak_refs.is_empty() {
                String::new()
            } else {
                let ws: Vec<String> = b.weak_refs.iter().map(|e| idx(e).to_string()).collect();
                format!(", weakRefs := [{}]", ws.join(", "))
            };
            format!(
                "{{ code := {}, align := {}, symbols := [{}], relocs := [{}], externs := {exts_s}{weak_s} }}",
                names.block_code(bi),
                b.align,
                syms_s.join(", "),
                rels_s.join(", ")
            )
        })
        .collect();
    push_list(l, "  ", "blocks", blocks);
    let data: Vec<String> = lib
        .data
        .iter()
        .enumerate()
        .map(|(i, d)| {
            let rs: Vec<String> = d
                .relocs
                .iter()
                .map(|r| render_interned_reloc(&tbl, r))
                .collect();
            format!(
                "{{ sym := {}, align := {}, readOnly := {}, bytes := {}, zeroTail := {}, relocs := [{}] }}",
                idx(&d.sym),
                d.align,
                d.read_only,
                names.data_bytes(i),
                d.zero_tail,
                rs.join(", ")
            )
        })
        .collect();
    push_list(l, "  ", "data", data);
    push_list(
        l,
        "  ",
        "exports",
        lib.exports.iter().map(|e| idx(e).to_string()).collect(),
    );
    push_list_nonempty(
        l,
        "  ",
        "exportSyms",
        lib.export_syms
            .iter()
            .map(|(e, raw)| format!("({}, {})", idx(e), idx(raw)))
            .collect(),
    );
    l.push(String::new());
    // A split witness compares against `toMultiPlacedLibR` (names looked up by the kernel-cheap
    // `rGetD`); `List.getD` over thousands of names costs the kernel tens of GB.
    let l = out.part("LibEq");
    l.push(match &wn.split_check {
        Some(m) => format!(
            "theorem {lib_eq} : {} = {lib_l}.toMultiPlacedLib := {m}.toMultiPlacedLib_of_r (by rfl_kernel)",
            names.lib
        ),
        None => format!(
            "theorem {lib_eq} : {} = {lib_l}.toMultiPlacedLib := by rfl_kernel",
            names.lib
        ),
    });
    l.push(String::new());
    let l = out.part("Defs");
    l.push(format!(
        "theorem {lib_l}_names : {lib_l}.names = {name_chars}.map String.ofList := by rfl_kernel"
    ));
    l.push(String::new());
    l.push(format!("def {ly} : Obj.Interned.MultiLayout where"));
    push_list(
        l,
        "  ",
        "bases",
        mpl.bases.iter().map(|b| format!("{b:#x}#64")).collect(),
    );
    push_list(
        l,
        "  ",
        "addrs",
        tbl.iter()
            .map(|n| format!("{:#x}#64", lib.resolve(mpl, n)))
            .collect(),
    );
    push_list(
        l,
        "  ",
        "relax",
        mpl.relax
            .iter()
            .map(|s| {
                format!(
                    "[{}]",
                    s.iter()
                        .map(|o| format!("{o:#x}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect(),
    );
    push_list(
        l,
        "  ",
        "b2b",
        mpl.b2b
            .iter()
            .map(|s| {
                format!(
                    "[{}]",
                    s.iter()
                        .map(|o| format!("{o:#x}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect(),
    );
    push_list_nonempty(
        l,
        "  ",
        "undefWeak",
        mpl.undef_weak.iter().map(|s| idx(s).to_string()).collect(),
    );
    l.push(String::new());
    push_elf_aliases(l, wn, elf_rel);
    let mpl_term = format!("({ly}.toMultiPlacement {lib_l}.names)");
    let split = wn.split_check.as_ref().map(|m| {
        let text_costs = lib
            .blocks
            .iter()
            .map(|b| b.code.len() as u64 + RELOC_COST * b.relocs.len() as u64);
        let data_costs = lib
            .data
            .iter()
            .map(|d| d.bytes.len() as u64 + d.zero_tail + RELOC_COST * d.relocs.len() as u64);
        let walks = [
            ("Text", format!("{lib_l}_text"), "lText", chunk_bounds(text_costs, TEXT_CHUNK_BUDGET)),
            ("Data", format!("{lib_l}_data"), "lData", chunk_bounds(data_costs, DATA_CHUNK_BUDGET)),
        ];
        (m, format!("{lib_l}_segLens"), walks)
    });
    if let Some((m, seg_lens, walks)) = &split {
        let l = out.part("Defs");
        l.push(format!(
            "/-- The byte lengths of the segments of `{elf}` (each fact below is its own kernel check, so the"
        ));
        l.push("    kernel's peak memory is that of the largest one). -/".into());
        l.push(format!("noncomputable def {seg_lens} : List Nat := seg_lens% {elf}"));
        l.push(String::new());
        let l = out.part("SegLens");
        l.push(format!(
            "theorem {seg_lens}_eq : {elf}.segments.map (fun r => {m}.rLen r.bytes) = {seg_lens} := by rfl_kernel"
        ));
        l.push(String::new());
        let rl = format!("({elf}.segments.zip {seg_lens})");
        for (part, fact, walk, bounds) in walks {
            for (k, (s, t)) in chunk_ranges(bounds).into_iter().enumerate() {
                let (part, fact) = chunk_names(part, fact, k, bounds.len());
                let l = out.part(&part);
                l.push(match t {
                    Some(t) => format!(
                        "theorem {fact} : {m}.{walk}Chunk {lib_l} {ly} {rl} {s} {t} = true := by rfl_kernel"
                    ),
                    None => format!(
                        "theorem {fact} : {m}.{walk}Tail {lib_l} {ly} {rl} {s} = true := by rfl_kernel"
                    ),
                });
                l.push(String::new());
            }
        }
        for (suffix, stmt) in split_check_facts(m, lib_l, ly, name_chars, &wn.elf_sym_chars) {
            let mut part = String::from("Chk");
            let mut cs = suffix.chars();
            part.extend(cs.next().map(|c| c.to_ascii_uppercase()));
            part.extend(cs);
            let fact = format!("{lib_l}_chk_{suffix}");
            let Some(ch) = split_check_chunks(m, lib_l, ly, lib, suffix) else {
                let l = out.part(&part);
                l.push(format!("theorem {fact} : {stmt} = true := by decide +kernel"));
                l.push(String::new());
                continue;
            };
            for (k, (s, t)) in chunk_ranges(&ch.bounds).into_iter().enumerate() {
                let (part, fact) = chunk_names(&part, &fact, k, ch.bounds.len());
                let l = out.part(&part);
                let (at, list) = (&ch.at, &ch.list);
                l.push(match t {
                    Some(t) => format!(
                        "theorem {fact} : {m}.allIdxChunk ({at}) {list} {s} {t} = true := by decide +kernel"
                    ),
                    None => format!(
                        "theorem {fact} : {m}.allIdxTail ({at}) {list} {s} = true := by decide +kernel"
                    ),
                });
                l.push(String::new());
            }
        }
    }
    let l = out.part("");
    l.push(format!(
        "theorem {ok_name} : {lib}.Placeable {mpl_term} ∧ {lib}.InElf {elf} {mpl_term} ∧ {lib}.DataDisjoint {mpl_term} := by",
        lib = names.lib
    ));
    l.push(format!("  rw [{lib_eq}]"));
    if let Some((m, seg_lens, walks)) = &split {
        let chks: Vec<String> = split_check_facts(m, lib_l, ly, name_chars, &wn.elf_sym_chars)
            .iter()
            .map(|(suffix, _)| {
                let fact = format!("{lib_l}_chk_{suffix}");
                match split_check_chunks(m, lib_l, ly, lib, suffix) {
                    None => fact,
                    Some(ch) => format!(
                        "({m}.{} {})",
                        ch.of_chunks,
                        chunk_chain(&format!("{m}.allIdxChunks"), &fact, ch.bounds.len())
                    ),
                }
            })
            .collect();
        // `lTextChunks_cons f₀ (… (lTextChunks_nil f_last))`, and likewise for the data walk.
        let chunks: Vec<String> = walks
            .iter()
            .map(|(_, fact, walk, bounds)| {
                chunk_chain(&format!("{m}.{walk}Chunks"), fact, bounds.len())
            })
            .collect();
        l.push(format!(
            "  exact {m}.checkMultiDisjoint_spec_chunks {lib_l}_names {elf_syms}_eq {seg_lens}_eq"
        ));
        for c in &chunks {
            l.push(format!("    {c}"));
        }
        l.push(format!("    {}", chks.join(" ")));
    } else {
        l.push(format!(
            "  exact Obj.Interned.checkMultiDisjoint_spec {lib_l}_names {elf_syms}_eq (by decide +kernel)"
        ));
    }
    l.push(String::new());
    l.push(format!(
        "theorem {} : {}.LinkedIn {elf_bytes} :=",
        wn.linked_in, names.lib
    ));
    l.push(format!("  ⟨_, {elf}, {elf_parse}, {ok_name}.1, {ok_name}.2.1⟩"));
    l.push(String::new());
    if let Some((ok, skipped)) = &wn.extern_symtab
        && !ok.is_empty()
    {
        push_extern_symtab(out.part("ExternSymtab"), wn, &tbl, &mpl_term, ok, skipped);
    }
}

/// Kernel-cost weight of one relocation in a text block or data object, in code/data bytes.
pub(super) const RELOC_COST: u64 = 16;
/// Kernel cost (code bytes, relocations weighted by [`RELOC_COST`]) of one text-walk chunk of a
/// split multi-block witness; a larger library's text walk is split into several shards.
const TEXT_CHUNK_BUDGET: u64 = 32 * 1024;
/// Kernel cost (data bytes and zero tails, relocations weighted by [`RELOC_COST`]) of one
/// data-walk chunk.
const DATA_CHUNK_BUDGET: u64 = 32 * 1024;

/// The interior boundaries `t₁ < … < tₖ` that split items with costs `costs` into chunks
/// `[0, t₁), [t₁, t₂), …, [tₖ, n)` of total cost at most `budget` each (an item costlier than
/// `budget` is a chunk of its own). Empty for a single chunk.
pub(super) fn chunk_bounds(costs: impl Iterator<Item = u64>, budget: u64) -> Vec<usize> {
    let mut bounds = Vec::new();
    let mut acc = 0u64;
    for (i, c) in costs.enumerate() {
        if i > 0 && acc > 0 && acc.saturating_add(c) > budget {
            bounds.push(i);
            acc = 0;
        }
        acc = acc.saturating_add(c);
    }
    bounds
}

/// The chunks `(start, Some end)` and the last `(start, None)` of the interior boundaries
/// `bounds` (from [`chunk_bounds`]).
pub(super) fn chunk_ranges(bounds: &[usize]) -> Vec<(usize, Option<usize>)> {
    let mut starts = vec![0];
    starts.extend_from_slice(bounds);
    starts
        .iter()
        .enumerate()
        .map(|(k, &s)| (s, bounds.get(k).copied()))
        .collect()
}

/// The shard part and theorem name of chunk `k` of a walk with `n` interior boundaries: `part`
/// and `fact` themselves for a single chunk, `<part><k>` and `<fact><k>` otherwise.
pub(super) fn chunk_names(part: &str, fact: &str, k: usize, n: usize) -> (String, String) {
    if n == 0 {
        (part.to_string(), fact.to_string())
    } else {
        (format!("{part}{k}"), format!("{fact}{k}"))
    }
}

/// `(<lemma>_cons <fact>₀ (… (<lemma>_nil <fact>ₙ)))`, the chunk facts of [`chunk_names`] for `n`
/// interior boundaries composed into one `<lemma>` (`AllIdxChunks`, `MapChunksEq`, a walk).
pub(super) fn chunk_chain(lemma: &str, fact: &str, n: usize) -> String {
    let mut term = String::new();
    for k in 0..=n {
        let (_, f) = chunk_names("", fact, k, n);
        if k < n {
            term.push_str(&format!("({lemma}_cons {f} "));
        } else {
            term.push_str(&format!("({lemma}_nil {f})"));
        }
    }
    term.push_str(&")".repeat(n));
    term
}

/// Kernel cost (symbols plus one per block) of one chunk of `blockSymsMatchB`.
const CHK_SYMS_BUDGET: u64 = 640;
/// Kernel cost (relocations plus one per block) of one chunk of `textPlaceableAllB`.
const CHK_PTEXT_BUDGET: u64 = 1024;
/// Kernel cost (block symbols scanned per data object) of one chunk of `dataNotBlockB`.
const CHK_PNONE_BUDGET: u64 = 128 * 1024;

/// A segment-free check proved as `AllIdxChunks (<at>) <list> 0 bounds`, one
/// `allIdxChunk`/`allIdxTail` fact per chunk, and turned into the check by `<m>.<of_chunks>`.
struct CheckChunks {
    at: String,
    list: String,
    of_chunks: &'static str,
    bounds: Vec<usize>,
}

/// The chunks of the per-item segment-free check `suffix` (of [`split_check_facts`]) of a library
/// over its budget; `None` for a check proved by one fact.
fn split_check_chunks(
    m: &str,
    lib_l: &str,
    ly: &str,
    lib: &PMultiLib,
    suffix: &str,
) -> Option<CheckChunks> {
    let block_syms: u64 = lib.blocks.iter().map(|b| b.symbols.len() as u64).sum();
    let (at, list, of_chunks, bounds) = match suffix {
        "syms" => (
            format!("{m}.blockSymsMatchAt {ly}"),
            format!("{lib_l}.blocks"),
            "blockSymsMatchB_of_chunks",
            chunk_bounds(lib.blocks.iter().map(|b| 1 + b.symbols.len() as u64), CHK_SYMS_BUDGET),
        ),
        "ptext" => (
            format!("{m}.textPlaceableAt {lib_l} {ly}"),
            format!("{lib_l}.blocks"),
            "textPlaceableAllB_of_chunks",
            chunk_bounds(lib.blocks.iter().map(|b| 1 + b.relocs.len() as u64), CHK_PTEXT_BUDGET),
        ),
        "pnone" => (
            format!("{m}.dataNotBlockAt {lib_l}"),
            format!("{lib_l}.data"),
            "dataNotBlockB_of_chunks",
            chunk_bounds(lib.data.iter().map(|_| 1 + block_syms), CHK_PNONE_BUDGET),
        ),
        _ => return None,
    };
    (!bounds.is_empty()).then_some(CheckChunks { at, list, of_chunks, bounds })
}

/// The segment-free checks of a split multi-block witness, as `(suffix, Bool term)` in the
/// argument order of `<m>.checkMultiDisjoint_spec_chunks`. Each becomes its own
/// `<lib_l>_chk_<suffix> : <term> = true := by decide +kernel`, a separate declaration with its
/// own kernel cache, or, for a per-item check over its budget ([`split_check_chunks`]), one such
/// declaration per chunk.
fn split_check_facts(
    m: &str,
    lib_l: &str,
    ly: &str,
    name_chars: &str,
    elf_sym_chars: &str,
) -> Vec<(&'static str, String)> {
    vec![
        ("nodup", format!("Obj.Interned.namesNodup {name_chars}")),
        ("ids", format!("{lib_l}.idsOk")),
        ("syms", format!("Obj.Interned.blockSymsMatchB {lib_l} {ly}")),
        ("ptext", format!("{m}.textPlaceableAllB {lib_l} {ly}")),
        ("pdisj", format!("{m}.blocksDisjointB {lib_l} {ly}")),
        ("psyms", format!("{m}.blockSymsNodupB {lib_l}")),
        ("pdata", format!("{m}.dataPlaceableAllB {lib_l} {ly}")),
        ("pnone", format!("{m}.dataNotBlockB {lib_l}")),
        (
            "exports",
            format!(
                "Obj.Interned.multiExportsOk {lib_l} {ly} {name_chars} (ProofLib.ObjectLoad.prepareCharAssocVal {elf_sym_chars})"
            ),
        ),
        ("ddisj", format!("{m}.dataDisjointFastB {lib_l} {ly}")),
    ]
}

/// `<p>ExternIds` (the name indices of the externs in `ok`), `<p>ExternIds_names` (their names)
/// and `<p>_externSymtab : ∀ s ∈ [...], lookupUnique s <elf>.symbols = some (<mpl>.ρ s)`, proved by
/// `Obj.Interned.externSymtab_of` with one `decide +kernel`. The externs in `skipped` are listed
/// in the docstring with the reason each is left out.
fn push_extern_symtab(
    l: &mut Vec<String>,
    wn: &WitNames,
    tbl: &[String],
    mpl_term: &str,
    ok: &[String],
    skipped: &[(String, String)],
) {
    let lib_l = &wn.lib_l;
    let p = lib_l.strip_suffix('L').unwrap_or(lib_l);
    let ids = format!("{p}ExternIds");
    l.push(format!(
        "/-- Indices into `{}` of the externs with exactly one `.symtab` entry (in `ElfImage.symbols`),",
        wn.name_chars
    ));
    l.push("    at the placed address.".into());
    if skipped.is_empty() {
        l.push("    Every extern is included. -/".into());
    } else {
        l.push("    Left out:".into());
        for (e, why) in skipped {
            l.push(format!("    - `{}`: {}", doc_safe(e), doc_safe(why)));
        }
        l.push("-/".into());
    }
    l.push(format!(
        "def {ids} : List Nat := [{}]",
        ok.iter()
            .map(|e| name_idx(tbl, e).to_string())
            .collect::<Vec<_>>()
            .join(", ")
    ));
    l.push(String::new());
    let lits = format!(
        "[{}]",
        ok.iter()
            .map(|e| lean_string_lit(e))
            .collect::<Vec<_>>()
            .join(", ")
    );
    l.push(format!(
        "theorem {ids}_names : {ids}.map ({lib_l}.names.getD · \"\") = {lits} := by rfl_kernel"
    ));
    l.push(String::new());
    l.push(format!(
        "/-- Each listed extern's address under the placement is its unique `.symtab` value in `{}`. -/",
        wn.elf
    ));
    l.push(format!(
        "theorem {p}_externSymtab : ∀ s ∈ {lits}, Obj.lookupUnique s {}.symbols = some ({mpl_term}.ρ s) := by",
        wn.elf
    ));
    l.push(format!("  rw [← {ids}_names]"));
    l.push("  intro s hs".into());
    l.push("  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs".into());
    l.push(format!(
        "  exact Obj.Interned.externSymtab_of (addrs := {}.addrs) (ids := {ids}) {lib_l}_names {}_eq",
        wn.ly, wn.elf_syms
    ));
    l.push("    (by decide +kernel) i hi".into());
    l.push(String::new());
}

/// `<…>PlacedWitness.lean` without a stock-linked ELF: emits a synthesized canonical placement
/// `pl`, the interned library and layout, and kernel-checked `Placeable` + extern-distinctness
/// theorems (`<obj>Lib_placeable : ∃ pl, <obj>Lib.Placeable pl ∧ (<obj>Lib.text.externs.map pl.ρ).Nodup`)
/// proved via `Obj.Interned.placeable_and_externs_of_checkPlaceable` (`by decide +kernel`).
pub fn render_placeable_witness(
    lib: &PLib,
    pl: &PPlacement,
    wn: &WitNames,
    ns: &str,
    lib_module: &str,
    license: &[String],
) -> String {
    let names = wn;
    let lib_name = &names.lib.lib;
    let lib_l = &names.lib_l;
    let ly = &names.ly;
    let pl_term = format!("({ly}.toPlacement {lib_l}.names)");
    let mut l = header(license);
    l.extend([
        "module".to_string(),
        String::new(),
        format!("public import {lib_module}"),
        "public import ProofLib.Placed.Check".into(),
        "public meta import ProofLib.ProgramReflection".into(),
        String::new(),
        format!(
            "/-! # Canonical placement witness for `{}` (untrusted generator output)",
            doc_safe(&lib.name)
        ),
        String::new(),
        "Generated by `rust-obj2lean` (`untrusted_placed`), which `lake build` runs before compiling"
            .into(),
        "this library. DO NOT EDIT MANUALLY: this file is a gitignored build product.".into(),
        String::new(),
        format!(
            "`{}` is a synthesized canonical placement for `{}` (`{lib_name}`), checked by the",
            names.placement,
            doc_safe(&lib.name)
        ),
        "Lean kernel without requiring a stock-linked ELF: each conjunct of".into(),
        "`Obj.Interned.checkPlaceableExt` is its own `decide +kernel` theorem, so the kernel never"
            .into(),
        "holds the whole check at once (it fits the `-M` memory cap for large libraries):".into(),
        format!(
            "* `{}` : `{lib_name}.Placeable {pl_term} ∧ ({lib_name}.text.externs.map {pl_term}.ρ).Nodup`",
            names.placeable_and_externs
        ),
        format!(
            "* `{}` : `∃ pl, {lib_name}.Placeable pl ∧ ({lib_name}.text.externs.map pl.ρ).Nodup`",
            names.placeable
        ),
        String::new(),
        format!(
            "Census: {} text relocations, {} data objects, {} externs.",
            lib.text.relocs.len(),
            lib.data.len(),
            lib.text.externs.len()
        ),
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {ns}"),
        String::new(),
        "open Arm64 ProofLib.ProgramReflection".into(),
        String::new(),
        "set_option maxHeartbeats 0".into(),
        "set_option maxRecDepth 2000000".into(),
        String::new(),
        "/-- Synthesized addresses of the non-block symbols the library references. -/".into(),
    ]);
    l.push(format!("def {} : List (String × Nat) := [", names.rho));
    let n = pl.rho.len();
    for (i, (s, a)) in pl.rho.iter().enumerate() {
        let sep = if i + 1 < n { "," } else { "" };
        l.push(format!("  ({}, {a:#x}){sep}", lean_string_lit(s)));
    }
    l.push("]".into());
    l.push(String::new());
    l.push("/-- `ADRP` byte offsets of the relaxed `ADRP`+`ADD` pairs. -/".into());
    l.push(format!("def {} : List Nat := []", names.relax));
    l.push(String::new());
    l.push("/-- Byte offsets of the branches retargeted past a block `B`. -/".into());
    l.push(format!("def {} : List Nat := []", names.b2b));
    l.push(String::new());
    l.push(format!(
        "/-- Synthesized canonical placement for `{}`. -/",
        doc_safe(&lib.name)
    ));
    l.push(format!("def {} : Obj.Placement where", names.placement));
    l.push(format!("  base := {:#x}#64", pl.base));
    l.push(format!(
        "  ρ := fun s => BitVec.ofNat 64 ((Obj.lookup s {}).getD 0)",
        names.rho
    ));
    l.push(format!(
        "  relax := fun off => {}.contains off",
        names.relax
    ));
    l.push(format!("  b2b := fun off => {}.contains off", names.b2b));
    l.push(String::new());
    push_interned_lib_and_layout(&mut l, lib, pl, wn, true);
    push_split_placeable_check(&mut l, wn, &lib.name);
    l.extend([
        format!(
            "/-- `{}` is placeable at `{pl_term}`. -/",
            doc_safe(&lib.name)
        ),
        format!(
            "theorem {} : {lib_name}.Placeable {pl_term} := {}.1",
            names.placeable_at, names.placeable_and_externs
        ),
        String::new(),
        format!(
            "/-- The externs of `{}` have pairwise-distinct addresses under `{pl_term}`. -/",
            doc_safe(&lib.name)
        ),
        format!(
            "theorem {} : ({lib_name}.text.externs.map {pl_term}.ρ).Nodup := {}.2",
            names.externs_nodup, names.placeable_and_externs
        ),
        String::new(),
        format!(
            "/-- Non-vacuity witness: `{}` has a valid placement with pairwise-distinct extern addresses. -/",
            doc_safe(&lib.name)
        ),
        format!(
            "theorem {} : ∃ pl, {lib_name}.Placeable pl ∧ ({lib_name}.text.externs.map pl.ρ).Nodup :=",
            names.placeable
        ),
        format!("  ⟨_, {}⟩", names.placeable_and_externs),
        String::new(),
        format!(
            "/-- Non-vacuity witness: `{}` has a valid placement. -/",
            doc_safe(&lib.name)
        ),
        format!(
            "theorem {} : ∃ pl, {lib_name}.Placeable pl :=",
            names.exists_placeable
        ),
        format!("  ⟨_, {}⟩", names.placeable_at),
        String::new(),
        format!("end {ns}"),
        String::new(),
    ]);
    l.join("\n")
}
