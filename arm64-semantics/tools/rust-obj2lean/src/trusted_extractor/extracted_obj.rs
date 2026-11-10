// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Pre-link `Obj.ExtractedObj` Lean emitter (`trusted_extractor::extracted_obj`) — `[TCB]`.
//!
//! Emits `<ObjStem>ExtractedObj.lean` and its companion `<ObjStem>ExtractedObj.bin` byte sidecar
//! directly from [`Extraction::objects`] without invoking any static linker.

use object::elf;
use std::fmt::Write;
use std::path::{Path, PathBuf};

use super::doc_safe;
use crate::trusted_common::{
    Extraction, ObjModuleMeta, ObjObject, ObjReloc, ObjSection, ObjSymbol, RelocKind, RelocType,
    SymBind, SymKind, SymSection, lean_string_lit,
};

/// Companion paths `(<dir>/<Stem>ExtractedObj.lean, <dir>/<Stem>ExtractedObj.bin)` derived from
/// `meta.obj_file` (`<dir>/<Stem>Obj.lean`). The `*ExtractedObj.lean` suffix places the generated
/// module in the `Role::Spec` (`[case-studies-tcb]`) bucket under `tcb-map`.
pub fn extracted_obj_files(meta: &ObjModuleMeta) -> (PathBuf, PathBuf) {
    let dir = meta.obj_file.parent().unwrap_or_else(|| Path::new(""));
    let stem = meta
        .obj_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(&meta.obj_name);
    let base = stem.strip_suffix("Obj").unwrap_or(stem);
    (
        dir.join(format!("{base}ExtractedObj.lean")),
        dir.join(format!("{base}ExtractedObj.bin")),
    )
}

fn render_raw_reloc(r: &ObjReloc) -> String {
    let kind = RelocKind::from_reloc_type(r.rtype)
        .map_or_else(|| "none".to_string(), |k| format!("some {}", k.lean_name()));
    if r.addend == 0 {
        format!(
            "{{ off := {:#x}, kind := {kind}, symIdx := {} }}",
            r.offset, r.sym
        )
    } else {
        format!(
            "{{ off := {:#x}, kind := {kind}, symIdx := {}, addend := {} }}",
            r.offset, r.sym, r.addend
        )
    }
}

fn render_raw_sec(sec: &ObjSection, bin_lit: &str, bin_bytes: &mut Vec<u8>) -> String {
    let is_nobits = sec.is_nobits();
    let bytes_expr = if is_nobits || sec.bytes.is_empty() {
        "[]".to_string()
    } else {
        let off = bin_bytes.len();
        bin_bytes.extend_from_slice(&sec.bytes);
        format!("include_bytes% {bin_lit} {off} {}", sec.bytes.len())
    };
    let is_exec = (sec.sh_flags & (elf::SHF_EXECINSTR as u64)) != 0;
    let read_only = (sec.sh_flags & (elf::SHF_WRITE as u64)) == 0;
    let is_tls = (sec.sh_flags & (elf::SHF_TLS as u64)) != 0;
    let rels: Vec<String> = sec
        .relocs
        .iter()
        .filter(|r| r.rtype != RelocType::None)
        .map(render_raw_reloc)
        .collect();
    let mut s = format!(
        "{{ name := {}, bytes := {bytes_expr}, size := {}, align := {}, isExec := {is_exec}, readOnly := {read_only}, isNobits := {is_nobits}",
        lean_string_lit(&sec.name),
        sec.size,
        sec.align,
    );
    if is_tls {
        s.push_str(", isTls := true");
    }
    if !rels.is_empty() {
        let _ = write!(s, ", relocs := [{}]", rels.join(", "));
    }
    s.push_str(" }");
    s
}

fn render_raw_sym(sym: &ObjSymbol) -> String {
    let sec = match sym.sec {
        SymSection::Undef => ".undef".to_string(),
        SymSection::Sec(idx) => format!(".sec {idx}"),
        SymSection::Abs | SymSection::Common | SymSection::Other => ".other".to_string(),
    };
    let kind = match sym.kind {
        SymKind::Func => ".func",
        SymKind::Object => ".object",
        SymKind::Tls => ".tls",
        SymKind::Section => ".section",
        _ => ".other",
    };
    let bind = match sym.bind {
        SymBind::Local => ".local",
        SymBind::Global => ".global",
        SymBind::Weak => ".weak",
        _ => ".other",
    };
    format!(
        "{{ rawName := {}, name := {}, sec := {sec}, value := {:#x}, size := {}, kind := {kind}, bind := {bind} }}",
        lean_string_lit(&sym.raw_name),
        lean_string_lit(&sym.name),
        sym.value,
        sym.size,
    )
}

fn write_list(out: &mut String, field: &str, items: &[String]) {
    if items.is_empty() {
        let _ = writeln!(out, "  {field} := []");
        return;
    }
    let _ = writeln!(out, "  {field} := [");
    for (i, item) in items.iter().enumerate() {
        let sep = if i + 1 < items.len() { "," } else { "]" };
        let _ = writeln!(out, "    {item}{sep}");
    }
}

fn write_one_object(
    out: &mut String,
    def_name: &str,
    obj: &ObjObject,
    bin_lit: &str,
    bin_bytes: &mut Vec<u8>,
) {
    let _ = writeln!(
        out,
        "/-- Extracted relocatable object `{}`. -/",
        doc_safe(&obj.name).replace('`', "'")
    );
    let _ = writeln!(out, "def {def_name} : Obj.ExtractedObj where");
    let _ = writeln!(out, "  name := {}", lean_string_lit(&obj.name));
    let secs: Vec<String> = obj
        .sections
        .iter()
        .map(|s| render_raw_sec(s, bin_lit, bin_bytes))
        .collect();
    write_list(out, "sections", &secs);
    let syms: Vec<String> = obj.symbols.iter().map(render_raw_sym).collect();
    write_list(out, "symbols", &syms);
    // Only `GRP_COMDAT` groups: other (flag `0`) groups are always kept by the linker.
    let groups: Vec<String> = obj
        .groups
        .iter()
        .filter(|g| g.is_comdat)
        .map(|g| {
            let members: Vec<String> = g.sections.iter().map(|k| k.to_string()).collect();
            format!(
                "{{ signature := {}, members := [{}] }}",
                lean_string_lit(&g.signature),
                members.join(", ")
            )
        })
        .collect();
    write_list(out, "groups", &groups);
    out.push('\n');
}

/// Render `<Stem>ExtractedObj.lean` and its companion section-byte buffer directly from `ex.objects`.
pub fn render_extracted_obj_module(
    meta: &ObjModuleMeta,
    bin_name: &str,
    ex: &Extraction,
) -> (String, Vec<u8>) {
    let bin_lit = lean_string_lit(bin_name);
    let mut out = String::new();
    if !meta.license_header.is_empty() {
        out.push_str("/-\n");
        for l in &meta.license_header {
            let _ = writeln!(out, "{}", doc_safe(l));
        }
        out.push_str("-/\n");
    }
    let title = doc_safe(&meta.title);
    let _ = write!(
        out,
        "module\n\npublic import Arm64.Trusted.Object.Labels\npublic import Arm64.Trusted.Surface.IncludeBytes\n\n\
         /-! # Extracted Relocatable Objects ({title})\n\n\
         Generated directly from `.o` inputs by `rust-obj2lean` (`trusted_extractor`) without\n\
         static linking. DO NOT EDIT MANUALLY: this file is a generated build product.\n-/\n\n\
         @[expose] public section\n\nnamespace {}\n\nopen Arm64\n\n\
         set_option maxHeartbeats 20000000\nset_option maxRecDepth 2000000\n\n",
        meta.namespace_prefix,
    );
    let mut bin_bytes = Vec::new();
    let mut obj_defs = Vec::with_capacity(ex.objects.len());
    for (i, obj) in ex.objects.iter().enumerate() {
        let def_name = format!("{}ExtractedObj{i}", meta.obj_name);
        write_one_object(&mut out, &def_name, obj, &bin_lit, &mut bin_bytes);
        obj_defs.push(def_name);
    }
    let _ = writeln!(out, "/-- All extracted relocatable objects of {title}. -/");
    let _ = writeln!(
        out,
        "def {}ExtractedObjs : List Obj.ExtractedObj := [{}]\n\nend {}",
        meta.obj_name,
        obj_defs.join(", "),
        meta.namespace_prefix
    );
    (out, bin_bytes)
}

/// Emit `((lean_path, lean_src), (bin_path, bin_bytes))` directly from `ex.objects`.
pub fn emit_extracted_obj_lean_module(
    meta: &ObjModuleMeta,
    ex: &Extraction,
) -> ((PathBuf, String), (PathBuf, Vec<u8>)) {
    let (lean_path, bin_path) = extracted_obj_files(meta);
    let bin_name = bin_path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("ExtractedObj.bin");
    let (lean_src, bin_bytes) = render_extracted_obj_module(meta, bin_name, ex);
    ((lean_path, lean_src), (bin_path, bin_bytes))
}
