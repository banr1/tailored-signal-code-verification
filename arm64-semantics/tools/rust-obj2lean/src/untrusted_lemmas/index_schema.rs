// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Schema and discovery helpers for `*Index.json` target symbol indices and DWARF metadata
//! (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (untrusted JSON sidecar schema emitted by
//!   [`super::index`] and consumed by `symexec`, `dwarf`, and developer coverage tooling).
//!
//! # Key Types & Functions
//! - [`TargetSymbolIndex`], [`FunctionIndexEntry`], [`CalleeInfo`], [`StubIndexEntry`].
//! - [`DwarfFunctionInfo`], [`DwarfParam`], [`DwarfLineEntry`], [`DwarfVarLocation`],
//!   [`DwarfVariable`], [`DwarfMember`], [`DwarfTypeLayout`].
//! - [`GENERATED_DIR`], [`symbol_index_paths`], [`load_symbol_indices`], [`default_repo_root`].

use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

/// Legacy root-level directory of `rust-obj2lean` generated output.
pub const GENERATED_DIR: &str = "Examples/Generated";

/// Resolve the repository root (`../..` from `tools/rust-obj2lean`, else nearest ancestor
/// containing `lakefile.lean` and `Arm64/`, else current directory).
pub fn default_repo_root() -> PathBuf {
    let is_root = |d: &Path| d.join("lakefile.lean").is_file() && d.join("Arm64").is_dir();
    let from_manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    if is_root(&from_manifest) {
        return from_manifest.canonicalize().unwrap_or(from_manifest);
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    cwd.ancestors()
        .find(|d| is_root(d))
        .map(Path::to_path_buf)
        .unwrap_or(cwd)
}

/// Direct call or tail-call site inside a function.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CalleeInfo {
    /// Byte offset of the call/tail-call instruction relative to the caller function's entry.
    pub call_offset: u64,
    /// Hexadecimal string of `call_offset` (e.g. `"0x1c"`).
    pub call_offset_hex: String,
    /// Canonical byte offset of the call/tail-call instruction in `<code>`.
    pub site_offset: u64,
    /// Hexadecimal string of `site_offset` (e.g. `"0x5d0"`).
    pub site_offset_hex: String,
    /// Target function or extern stub symbol name (as used in `Program.fnAddr`).
    pub callee: String,
    /// Canonical byte offset of the target in `<code>` (if known).
    pub target_offset: Option<u64>,
    /// True when the call is a tail call (`JUMP26` / `b` targeting outside the caller).
    pub is_tail_call: bool,
    /// True when the target is an extern stub in `<code>.stubs`.
    pub is_extern: bool,
    /// Source of the call edge (`"CALL26"`, `"JUMP26"`, or `"DIRECT"`).
    pub reloc_type: String,
}

/// Per-function entry in `<Target>Index.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionIndexEntry {
    /// Demangled function symbol name (as used in `Program.fnAddr`).
    pub name: String,
    /// Canonical byte offset from `base` in `<code>`.
    pub offset: u64,
    /// Hexadecimal string of `offset` (e.g. `"0x57c"`).
    pub offset_hex: String,
    /// Function size in bytes.
    pub size_bytes: u64,
    /// Function size in 32-bit instructions (`size_bytes / 4`).
    pub size_insns: u64,
    /// Short name of the generated `fnOff` theorem in `<ObjName>Code.lean`.
    pub fn_off_lemma: String,
    /// Fully qualified Lean constant name of the `fnOff` theorem.
    pub fn_off_lemma_full: String,
    /// Short name of the generated `fnSize` theorem in `<ObjName>Code.lean`.
    pub fn_size_lemma: String,
    /// Short name of the generated `frameBytes` theorem in `<ObjName>Code.lean` (if `frame_bytes` is `Some`).
    pub frame_bytes_lemma: Option<String>,
    /// Fetch/decode lemma prefix (`<prog_name>`) when selected by a target.
    pub decode_prefix: Option<String>,
    /// Fully qualified Lean constant prefix for `<decPrefix>_decode_0x...` / `<decPrefix>_rebase_fetch_0x...`.
    pub decode_prefix_full: Option<String>,
    /// Prologue stack frame size in bytes (`None` when `frame_unknown` is `true`).
    pub frame_bytes: Option<u64>,
    /// True when the prologue frame size could not be statically determined.
    pub frame_unknown: bool,
    /// Direct callees of this function, sorted by `call_offset`.
    pub callees: Vec<CalleeInfo>,
    /// DWARF signature, source lines and variable locations (absent when the object has no DWARF).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dwarf: Option<DwarfFunctionInfo>,
}

/// One formal parameter of a function (`DW_TAG_formal_parameter`), in declaration order.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfParam {
    /// Source name (empty for unnamed parameters).
    pub name: String,
    /// C/Rust type as written by the compiler's DWARF (typedef names kept, e.g. `node_t *`).
    pub c_type: String,
    /// Size of the parameter's type in bytes, when known.
    pub byte_size: Option<u64>,
    /// Location at function entry (`x0`, `w1` is reported as `x1`, `[sp+0x10]`, ...), or `None`.
    pub entry_location: Option<String>,
    /// True when DWARF has no location for the parameter at entry (dead / optimized out).
    pub optimized_out: bool,
    /// Layout key (`DwarfTypeLayout::name`) of the struct/union the parameter points to.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pointee: Option<String>,
}

/// A row of the function's line table, at a function-relative byte offset.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfLineEntry {
    /// Function-relative byte offset of the first instruction of the row.
    pub offset: u64,
    /// Source file (DWARF path after `-fdebug-prefix-map`, e.g. `/src/lib/buf.c`).
    pub file: String,
    pub line: u64,
    /// Inlined-call chain at `offset`, innermost first (`callee (file:line of the call)`).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub inlined: Vec<String>,
}

/// A function-relative PC range where a variable lives in `location`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfVarLocation {
    /// Function-relative start offset (inclusive).
    pub start: u64,
    /// Function-relative end offset (exclusive).
    pub end: u64,
    /// Rendered DWARF location (`x19`, `[sp+0x4]`, `[x29-0x10]`, `const 0x0`, `x0 (entry)`).
    pub location: String,
}

/// A parameter or local variable with its DWARF location list.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfVariable {
    pub name: String,
    pub c_type: String,
    /// `"param"` or `"local"`.
    pub kind: String,
    /// Inlined subroutine the variable belongs to (empty for the function itself).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub inlined_from: String,
    /// Locations; a single range covering the whole function for `DW_AT_location` exprlocs.
    pub locations: Vec<DwarfVarLocation>,
}

/// DWARF view of one function (`DW_TAG_subprogram`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfFunctionInfo {
    /// Source name (`DW_AT_name`).
    pub name: String,
    /// Declaration file and line (`DW_AT_decl_file` / `DW_AT_decl_line`).
    pub decl_file: String,
    pub decl_line: u64,
    /// Return type (`void` when absent).
    pub return_type: String,
    pub params: Vec<DwarfParam>,
    /// True for `DW_AT_external` (non-`static`) functions.
    pub external: bool,
    /// Compilation unit language (`C11`, `Rust`, ...).
    pub language: String,
    /// True when this DWARF describes code byte-identical to the image's function, so `lines`
    /// and `variables` offsets are exact.
    #[serde(default)]
    pub exact: bool,
    /// Line table rows (function-relative), deduplicated by offset.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lines: Vec<DwarfLineEntry>,
    /// Parameters and locals (including those of inlined subroutines) with locations.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub variables: Vec<DwarfVariable>,
}

impl DwarfFunctionInfo {
    /// C-like one-line signature: `int sum_list(node_t * p, int unused)`.
    pub fn signature(&self) -> String {
        let params = self
            .params
            .iter()
            .map(|p| {
                if p.name.is_empty() {
                    p.c_type.clone()
                } else {
                    format!("{} {}", p.c_type, p.name)
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} {}({})", self.return_type, self.name, params)
    }
}

/// One member of a struct/union layout (`DW_TAG_member`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfMember {
    /// Field name (empty for anonymous struct/union members).
    pub name: String,
    pub byte_offset: u64,
    pub byte_size: u64,
    /// Bitfields: bit offset from `byte_offset * 8` (little-endian bit numbering) and width.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bit_offset: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bit_size: Option<u64>,
    pub c_type: String,
    /// Layout key of the member's own struct/union type (nested aggregates).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub aggregate: Option<String>,
    /// Layout key of the struct/union this member points to.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pointee: Option<String>,
    /// Arrays: element size in bytes and layout key of the element aggregate (if any).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub array_elem_size: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub array_elem_aggregate: Option<String>,
}

/// Struct or union layout (`DW_TAG_structure_type` / `DW_TAG_union_type`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DwarfTypeLayout {
    /// Layout key: `struct foo`, `union bar`, a Rust path, or `struct <anon@file:line>`.
    pub name: String,
    /// `"struct"` or `"union"` (`"class"` for C++/Rust `DW_TAG_class_type`).
    pub kind: String,
    pub byte_size: u64,
    /// `DW_AT_alignment`, else the largest member alignment (scalars aligned to their size).
    pub alignment: u64,
    pub decl_file: String,
    pub decl_line: u64,
    /// Typedef names that resolve to this layout (e.g. `node_t`).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub typedefs: Vec<String>,
    pub members: Vec<DwarfMember>,
}

/// Per-extern-stub entry in `<Target>Index.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StubIndexEntry {
    /// Extern symbol name (as used in `Program.fnAddr` and hooks).
    pub name: String,
    /// Canonical byte offset of the 4-byte stub in `<code>`.
    pub offset: u64,
    /// Hexadecimal string of `offset`.
    pub offset_hex: String,
    /// Short name of the generated `stubOff` theorem in `<ObjName>Code.lean`.
    pub stub_off_lemma: String,
    /// Short name of the generated `hookAtOff?` theorem in `<ObjName>Code.lean` (if emitted).
    #[serde(rename = "hook_at_off_lemma")]
    pub hook_lemma: Option<String>,
}

/// Top-level JSON structure written to `<GeneratedDir>/<Target>Index.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TargetSymbolIndex {
    /// Schema version (currently 1).
    pub schema_version: u32,
    /// Target name from `translation.toml`, or `None` for a combined index.
    pub target: Option<String>,
    /// Object name from `translation.toml` (e.g. `"myLib"`).
    pub obj_name: String,
    /// Lean `Code` definition name (e.g. `"myLibCode"`).
    pub code_def: String,
    /// Lean `LinkedImage` definition name (e.g. `"myLibImage"`).
    pub objs_expr: String,
    /// Root namespace prefix.
    pub namespace_prefix: String,
    /// Target sub-namespace, if specified in `translation.toml`.
    pub sub_namespace: Option<String>,
    /// Repo-relative path to the generated `Code` module.
    pub code_file: String,
    /// Repo-relative path to the generated target lemma module, if applicable.
    pub lean_file: Option<String>,
    /// Lean `Code` module name.
    pub code_module: String,
    /// Fully qualified Lean `Code` constant name.
    pub code_const: String,
    /// Lean target lemma module name.
    pub target_module: Option<String>,
    /// Fetch/decode lemma prefix in `target_module`.
    pub prog_name: Option<String>,
    /// Indexed functions in this target.
    pub functions: Vec<FunctionIndexEntry>,
    /// Extern stubs in `<code>`.
    pub stubs: Vec<StubIndexEntry>,
    /// DWARF struct/union layouts reachable from the indexed functions' parameters and
    /// variables (pointees, nested members), sorted by name. Empty without DWARF.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub dwarf_types: Vec<DwarfTypeLayout>,
}

/// Paths of every `<GENERATED_DIR>/*Index.json`, `Arm64/Testing/Generated/*Index.json`,
/// `VerifiedLibraries/<Lib>/Generated/*Index.json`, and
/// `CaseStudies/<Lib>/Generated/*Index.json` under `root`, sorted (empty if the
/// directories are missing, e.g. before the first `lake build`).
pub fn symbol_index_paths(root: &Path) -> Vec<PathBuf> {
    let mut gen_dirs = vec![
        root.join(GENERATED_DIR),
        root.join("Arm64/Testing/Generated"),
        root.join("Arm64/Testing/Fixtures/Generated"),
    ];
    for top in ["VerifiedLibraries", "CaseStudies"] {
        if let Ok(entries) = fs::read_dir(root.join(top)) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !name.starts_with('.') && !name.starts_with('_') {
                    gen_dirs.push(entry.path().join("Generated"));
                }
            }
        }
    }
    let mut out: Vec<PathBuf> = gen_dirs
        .into_iter()
        .flat_map(|dir| fs::read_dir(dir).into_iter().flatten())
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.is_file()
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with("Index.json"))
        })
        .collect();
    out.sort();
    out
}

/// Every `*Index.json` under `root` that parses as a [`TargetSymbolIndex`], with its path.
/// Files that fail to read or parse are skipped.
pub fn load_symbol_indices(root: &Path) -> Vec<(PathBuf, TargetSymbolIndex)> {
    symbol_index_paths(root)
        .into_iter()
        .filter_map(|p| {
            let s = fs::read_to_string(&p).ok()?;
            let idx = serde_json::from_str(&s).ok()?;
            Some((p, idx))
        })
        .collect()
}
