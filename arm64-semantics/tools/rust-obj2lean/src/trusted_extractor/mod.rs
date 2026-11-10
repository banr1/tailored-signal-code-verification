// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Trusted ELF Object Extractor (`trusted_extractor`) — `[TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TCB]` (pure in-memory ELF64 AArch64 `.o` byte parser, symbol
//!   disambiguator/collision checker, and pre-link `Obj.ExtractedObj` emitter; contains **zero**
//!   process invocations, compiler/archive orchestration, reachability graph search, static
//!   linking, instruction decoding, or theorem generation, and never imports `untrusted_*` modules).
//! - **Purpose:**
//!   1. Parses allocated ELF64 `ET_REL` (`EM_AARCH64`) sections (`.text.*`, `.rodata.*`,
//!      `.data.rel.ro.*`, `.data.*`, `.bss.*`), symbol tables (demangled), and `Elf64_Rela`
//!      relocations from pre-loaded `.o` byte buffers into [`ObjObject`]s
//!      ([`parse_object`], [`parse_object_with`], [`parse_c_object`]).
//!   2. Disambiguates local and multi-version symbols across multi-TU builds and rejects symbol
//!      collisions ([`disambiguate_symbol_names`], [`check_name_collisions`]).
//!   3. Emits `<ObjStem>ExtractedObj.lean` (`List Obj.ExtractedObj`) and its `.bin` sidecar
//!      directly from [`Extraction::objects`] without invoking a static linker
//!      ([`emit_extracted_obj_lean_module`], [`extracted_obj_files`]).
//!
//! # Key Types & Functions
//! - [`Trim`], [`parse_object`], [`parse_object_with`], [`parse_c_object`]: Pure ELF64 `.o` byte
//!   parser.
//! - [`disambiguate_symbol_names`], [`check_name_collisions`]: Symbol disambiguation & checks.
//! - [`emit_extracted_obj_lean_module`], [`extracted_obj_files`], [`render_extracted_obj_module`]:
//!   Pre-link `Obj.ExtractedObj` Lean emitter.
//!
//! # When to Read This File
//! - Read this file when inspecting ELF section/symbol/relocation parsing invariants or pre-link
//!   `Obj.ExtractedObj` extraction.

pub mod extracted_obj;
pub use extracted_obj::{
    emit_extracted_obj_lean_module, extracted_obj_files, render_extracted_obj_module,
};

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context, Result, anyhow, bail};
use object::elf;
use object::read::elf::{FileHeader, Rel, Rela, SectionHeader, SectionTable, Sym, SymbolTable};
use object::{Endianness, SectionIndex, SymbolIndex};

use crate::trusted_common::{
    ComdatGroup, ObjObject, ObjReloc, ObjSection, ObjSymbol, RelocType, SymBind, SymKind,
    SymSection,
};

type Elf64 = elf::FileHeader64<Endianness>;

/// Largest section/extern alignment the linker accepts (it must also divide it).
const MAX_ALIGN: u64 = 4096;

pub fn demangle_rust_symbol(mangled: &str) -> String {
    format!("{:#}", rustc_demangle::demangle(mangled))
}

// ---------------------------------------------------------------------------
// ELF Relocatable Object Parsing (`object` crate)
// ---------------------------------------------------------------------------

/// Check that `align` is one the linker can honour relative to a page-aligned load base (a
/// power of two, at most 4096).
pub fn check_align(align: u64, what: &str) -> Result<()> {
    if !align.is_power_of_two() || align > MAX_ALIGN {
        bail!("{what} has unsupported alignment {align}");
    }
    Ok(())
}

/// A parsed relocatable AArch64 ELF file.
pub(crate) struct ElfRel<'data> {
    pub(crate) endian: Endianness,
    pub(crate) sections: SectionTable<'data, Elf64, &'data [u8]>,
    pub(crate) symbols: SymbolTable<'data, Elf64, &'data [u8]>,
}

/// Parse `data` as a little-endian ELF64 `ET_REL` for `EM_AARCH64`.
pub(crate) fn parse_elf_rel(data: &[u8]) -> Result<ElfRel<'_>> {
    let header = Elf64::parse(data).map_err(|e| anyhow!("not an ELF64 file: {e}"))?;
    let endian = header.endian().map_err(|e| anyhow!("bad ELF header: {e}"))?;
    if !header.is_class_64() || endian != Endianness::Little {
        bail!("not a little-endian ELF64 file");
    }
    if header.e_type(endian) != elf::ET_REL {
        bail!("not a relocatable ELF file (e_type {})", header.e_type(endian));
    }
    if header.e_machine(endian) != elf::EM_AARCH64 {
        bail!("not an AArch64 ELF file (e_machine {})", header.e_machine(endian));
    }
    let sections = header.sections(endian, data).map_err(|e| anyhow!("bad ELF section table: {e}"))?;
    let symbols = sections
        .symbols(endian, data, elf::SHT_SYMTAB)
        .map_err(|e| anyhow!("bad ELF symbol table: {e}"))?;
    Ok(ElfRel { endian, sections, symbols })
}

fn section_name(e: &ElfRel<'_>, sh: &elf::SectionHeader64<Endianness>) -> Result<String> {
    let raw = e.sections.section_name(e.endian, sh).map_err(|err| anyhow!("bad section name: {err}"))?;
    Ok(String::from_utf8(raw.to_vec())?)
}

/// How to trim an object (see [`parse_object_with`]).
#[derive(Clone, Debug)]
pub struct Trim {
    /// ELF section header indices of the sections to keep.
    pub keep: BTreeSet<usize>,
    /// Appended to the demangled names of local functions/objects/TLS variables, which may
    /// otherwise collide with the same generic instantiated in another object.
    pub local_suffix: String,
}

/// Parse the relocatable object `elf_bytes` of crate `name` into an `ObjObject`.
pub fn parse_object(name: &str, elf_bytes: Vec<u8>) -> Result<ObjObject> {
    parse_object_with(name, elf_bytes, None)
}

/// Parse the relocatable object `elf_bytes` of crate `name` into an `ObjObject`.
///
/// With `trim`, only the sections in `trim.keep` are extracted (the others are ignored,
/// as if absent), and the symbol table is reduced to the null symbol, the symbols defined
/// in kept sections and the symbols kept relocations refer to (renumbering the relocations).
/// A kept global symbol whose section is dropped becomes undefined, so it resolves like
/// any other undefined symbol; a relocation against a local symbol in a dropped section is
/// an error.
pub fn parse_object_with(name: &str, elf_bytes: Vec<u8>, trim: Option<&Trim>) -> Result<ObjObject> {
    let data: &[u8] = &elf_bytes;
    let e = parse_elf_rel(data).with_context(|| format!("{name}.o"))?;
    let endian = e.endian;
    if e.symbols.is_empty() {
        bail!("{name}.o has no symbol table");
    }
    let dropped = |idx: usize| trim.is_some_and(|t| !t.keep.contains(&idx));

    // Allocated sections (1-to-1 with ELF section headers; classification and feature checks
    // happen via `ObjSection::kind`).
    let mut sections: Vec<ObjSection> = Vec::new();
    let mut elf_to_sec: BTreeMap<usize, usize> = BTreeMap::new();
    for (idx, sh) in e.sections.enumerate() {
        if dropped(idx.0) {
            continue;
        }
        let sec_name = section_name(&e, sh)?;
        let sh_type = sh.sh_type(endian);
        let sh_flags = sh.sh_flags(endian);
        if sec_name == ".gcc_except_table" || sec_name.starts_with(".gcc_except_table.") {
            bail!("{name}.o has `{sec_name}`: unwinding is not supported (build with panic=abort)");
        }
        if sh_flags & elf::SHF_ALLOC as u64 == 0 || sec_name == ".eh_frame" {
            continue;
        }
        let align = sh.sh_addralign(endian).max(1);
        check_align(align, &format!("{name}.o: section `{sec_name}`"))?;
        let size = sh.sh_size(endian);
        let (file_offset, bytes) = if sh_type == elf::SHT_NOBITS {
            (0, Vec::new())
        } else {
            let bytes = sh.data(endian, data).map_err(|err| anyhow!("{name}.o: section `{sec_name}`: {err}"))?;
            if bytes.len() as u64 != size {
                bail!("{name}.o: section `{sec_name}` has {} bytes, expected {size}", bytes.len());
            }
            (sh.sh_offset(endian), bytes.to_vec())
        };
        elf_to_sec.insert(idx.0, sections.len());
        sections.push(ObjSection {
            name: sec_name,
            sh_type,
            sh_flags,
            addr: sh.sh_addr(endian),
            align,
            entsize: sh.sh_entsize(endian),
            size,
            file_offset,
            bytes,
            relocs: Vec::new(),
            is_rel: false,
            elf_index: idx.0,
        });
    }

    // Symbols, in ELF order (index 0 is the null symbol).
    let mut symbols = Vec::with_capacity(e.symbols.len());
    let mut in_dropped: BTreeSet<usize> = BTreeSet::new();
    for (i, sym) in e.symbols.symbols().iter().enumerate() {
        let raw_name = String::from_utf8(
            e.symbols.symbol_name(endian, sym).map_err(|err| anyhow!("{name}.o: symbol {i}: {err}"))?.to_vec(),
        )?;
        let kind = match sym.st_type() {
            elf::STT_NOTYPE => SymKind::Notype,
            elf::STT_FUNC => SymKind::Func,
            elf::STT_OBJECT => SymKind::Object,
            elf::STT_TLS => SymKind::Tls,
            elf::STT_SECTION => SymKind::Section,
            elf::STT_FILE => SymKind::File,
            elf::STT_COMMON => SymKind::Common,
            elf::STT_GNU_IFUNC => SymKind::GnuIfunc,
            t => SymKind::Other(t),
        };
        let bind = match sym.st_bind() {
            elf::STB_LOCAL => SymBind::Local,
            elf::STB_GLOBAL => SymBind::Global,
            elf::STB_WEAK => SymBind::Weak,
            elf::STB_GNU_UNIQUE => SymBind::GnuUnique,
            b => SymBind::Other(b),
        };
        let shndx = sym.st_shndx(endian);
        let elf_sec = e.symbols.symbol_section(endian, sym, SymbolIndex(i)).map_err(|err| anyhow!("{name}.o: symbol {i}: {err}"))?;
        let sec = match elf_sec {
            None if shndx == elf::SHN_UNDEF => SymSection::Undef,
            None if shndx == elf::SHN_ABS => SymSection::Abs,
            None if shndx == elf::SHN_COMMON => SymSection::Common,
            None => SymSection::Other,
            Some(SectionIndex(j)) => match elf_to_sec.get(&j) {
                Some(&k) => SymSection::Sec(k),
                None => {
                    if dropped(j) {
                        in_dropped.insert(i);
                    }
                    SymSection::Other
                }
            },
        };
        let sym_name = if kind == SymKind::Section {
            match elf_sec {
                Some(j) => section_name(&e, e.sections.section(j).map_err(|err| anyhow!("{name}.o: symbol {i}: {err}"))?)?,
                None => raw_name.clone(),
            }
        } else {
            demangle_rust_symbol(&raw_name)
        };
        symbols.push(ObjSymbol {
            name: sym_name,
            raw_name,
            kind,
            bind,
            vis: sym.st_visibility(),
            sec,
            value: sym.st_value(endian),
            size: sym.st_size(endian),
        });
    }

    // Section groups (`SHT_GROUP`), in section header order. Every group is recorded, even when
    // `trim` drops the group section itself: a COMDAT signature is claimed by the first group
    // that carries it, whether or not that group's members are kept, so dropping it would make
    // a later copy look live. `sections` lists only the extracted (kept, allocated) members.
    // Signatures follow `lld` (`.strtab` name of `.symtab[sh_info]`).
    let mut groups: Vec<ComdatGroup> = Vec::new();
    let mut grouped: BTreeSet<usize> = BTreeSet::new();
    for (idx, sh) in e.sections.enumerate() {
        if sh.sh_type(endian) != elf::SHT_GROUP {
            continue;
        }
        let sig_idx = sh.sh_info(endian) as usize;
        let Some(sig_sym) = symbols.get(sig_idx) else {
            bail!("{name}.o: SHT_GROUP section {}: signature symbol {sig_idx} out of range", idx.0);
        };
        let signature = sig_sym.raw_name.clone();
        let raw_words: &[object::U32<Endianness>] = sh
            .data_as_array(endian, data)
            .map_err(|err| anyhow!("{name}.o: SHT_GROUP section {}: {err}", idx.0))?;
        let Some((flags_word, member_words)) = raw_words.split_first() else {
            bail!("{name}.o: SHT_GROUP section {} is empty", idx.0);
        };
        let flags = flags_word.get(endian);
        if flags != 0 && flags != elf::GRP_COMDAT {
            bail!("{name}.o: SHT_GROUP section {} has unsupported flags {flags:#x}", idx.0);
        }
        // An empty signature (e.g. `sh_info == 0`) is a valid key: `lld` dedupes such groups
        // under `""` like any other signature, so it is recorded as is.
        let is_comdat = flags == elf::GRP_COMDAT;
        let mut sections: Vec<usize> = Vec::new();
        for w in member_words {
            let member = w.get(endian) as usize;
            if member >= e.sections.len() {
                bail!("{name}.o: SHT_GROUP section {}: member {member} out of range", idx.0);
            }
            if !grouped.insert(member) {
                bail!("{name}.o: section {member} is a member of more than one SHT_GROUP");
            }
            if let Some(&k) = elf_to_sec.get(&member) {
                sections.push(k);
            }
        }
        groups.push(ComdatGroup { signature, is_comdat, sections });
    }

    // Relocations of extracted sections (`SHT_RELA` and `SHT_REL`).
    for (_idx, sh) in e.sections.enumerate() {
        let sh_type = sh.sh_type(endian);
        if sh_type != elf::SHT_RELA && sh_type != elf::SHT_REL {
            continue;
        }
        let target = sh.sh_info(endian) as usize;
        let Some(&k) = elf_to_sec.get(&target) else {
            continue;
        };
        let rel_name = section_name(&e, sh)?;
        if sh.sh_link(endian) as usize != e.symbols.section().0 {
            bail!("{name}.o: `{rel_name}` does not use the symbol table");
        }
        if sections[k].is_nobits() {
            bail!("{name}.o: `{rel_name}` relocates a NOBITS section");
        }
        if sh_type == elf::SHT_REL {
            sections[k].is_rel = true;
            let rels: &[elf::Rel64<Endianness>] = sh
                .data_as_array(endian, data)
                .map_err(|err| anyhow!("{name}.o: `{rel_name}`: {err}"))?;
            for r in rels {
                let offset = r.r_offset(endian);
                let sym = r.r_sym(endian) as usize;
                if sym >= symbols.len() {
                    bail!("{name}.o: `{rel_name}` refers to symbol {sym} out of range");
                }
                if offset >= sections[k].size {
                    bail!("{name}.o: `{rel_name}` has offset {offset:#x} out of range");
                }
                sections[k].relocs.push(ObjReloc {
                    offset,
                    rtype: RelocType::from_r_type(r.r_type(endian)),
                    sym,
                    addend: 0,
                });
            }
        } else {
            let relas: &[elf::Rela64<Endianness>] = sh
                .data_as_array(endian, data)
                .map_err(|err| anyhow!("{name}.o: `{rel_name}`: {err}"))?;
            for r in relas {
                let offset = r.r_offset(endian);
                let sym = r.r_sym(endian, false) as usize;
                if sym >= symbols.len() {
                    bail!("{name}.o: `{rel_name}` refers to symbol {sym} out of range");
                }
                if offset >= sections[k].size {
                    bail!("{name}.o: `{rel_name}` has offset {offset:#x} out of range");
                }
                sections[k].relocs.push(ObjReloc {
                    offset,
                    rtype: RelocType::from_r_type(r.r_type(endian, false)),
                    sym,
                    addend: r.r_addend(endian),
                });
            }
        }
    }
    // `Arm64.Obj` patches each section in one forward pass and rejects relocations that are
    // not sorted by offset; RELA order carries no meaning, so sort (stably) here.
    for sec in &mut sections {
        sec.relocs.sort_by_key(|r| r.offset);
    }

    if let Some(t) = trim {
        // Keep the null symbol, the symbols kept relocations refer to, and the symbols
        // defined in kept sections (except `STT_FILE`).
        let referenced: BTreeSet<usize> = sections
            .iter()
            .flat_map(|s| s.relocs.iter().map(|r| r.sym))
            .collect();
        let kept: Vec<usize> = (0..symbols.len())
            .filter(|&i| {
                i == 0
                    || referenced.contains(&i)
                    || (matches!(symbols[i].sec, SymSection::Sec(_))
                        && symbols[i].kind != SymKind::File)
            })
            .collect();
        let new_index: BTreeMap<usize, usize> = kept
            .iter()
            .enumerate()
            .map(|(new, &old)| (old, new))
            .collect();
        let mut trimmed = Vec::with_capacity(kept.len());
        for &i in &kept {
            let mut s = symbols[i].clone();
            if in_dropped.contains(&i) {
                if s.bind == SymBind::Local {
                    bail!(
                        "{name}.o: a kept relocation refers to local symbol `{}` in a dropped section",
                        s.name
                    );
                }
                // Resolved by name, like the undefined symbol a linker would see.
                s.sec = SymSection::Undef;
                s.value = 0;
                s.size = 0;
            }
            if s.bind == SymBind::Local
                && matches!(s.kind, SymKind::Func | SymKind::Object | SymKind::Tls)
            {
                s.name = format!("{}{}", s.name, t.local_suffix);
            }
            trimmed.push(s);
        }
        for sec in &mut sections {
            for r in &mut sec.relocs {
                r.sym = new_index[&r.sym];
            }
        }
        symbols = trimmed;
    }

    Ok(ObjObject {
        name: name.to_string(),
        sections,
        symbols,
        groups,
        elf_bytes,
    })
}

/// Parse a native C relocatable object `elf_bytes` of object `name` into an `ObjObject`,
/// suffixing local (`STB_LOCAL`) function/object/TLS symbols with ` [<name>]` and
/// disambiguating any duplicate local symbols within the same object with `#1`, `#2`, ...
/// so multi-TU C libraries with overlapping `static` helpers or function-scoped `static`
/// variables satisfy `check_name_collisions` and `c_symbols_fresh`.
pub fn parse_c_object(name: &str, elf_bytes: Vec<u8>) -> Result<ObjObject> {
    let mut o = parse_object(name, elf_bytes)?;
    let mut local_counts: BTreeMap<String, usize> = BTreeMap::new();
    for s in &mut o.symbols {
        if s.bind == SymBind::Local
            && matches!(s.kind, SymKind::Func | SymKind::Object | SymKind::Tls)
        {
            let count = local_counts.entry(s.name.clone()).or_insert(0);
            *count += 1;
            if *count > 1 {
                s.name = format!("{}#{} [{}]", s.name, *count - 1, name);
            } else {
                s.name = format!("{} [{}]", s.name, name);
            }
        }
    }
    Ok(o)
}

/// Whether a symbol defines a function, object or TLS variable in an extracted section.
pub(crate) fn is_defined_entity(s: &ObjSymbol) -> bool {
    matches!(s.kind, SymKind::Func | SymKind::Object | SymKind::Tls)
        && matches!(s.sec, SymSection::Sec(_))
}

/// Disambiguate colliding demangled symbol names across `objects`:
/// - Non-local symbols (`STB_GLOBAL` / `STB_WEAK`, both defined and `SHN_UNDEF`) are grouped
///   by their initial demangled name across all objects. When multiple distinct `raw_name`s
///   share the same initial demangled name, the first `raw_name` in appearance order keeps the
///   base name and subsequent distinct `raw_name`s receive `#1`, `#2`, ... consistently across
///   all `ObjSymbol` entries (definitions and undefined references alike).
/// - `STB_LOCAL` defined entities (`SymKind::Func | SymKind::Object | SymKind::Tls` in
///   `SymSection::Sec(_)`) whose demangled name collides with any other defined entity or any
///   non-local symbol are disambiguated with ` [local#1]`, ` [local#2]`, .... Non-colliding
///   local symbols keep their original demangled names unchanged.
pub fn disambiguate_symbol_names(objects: &mut [ObjObject]) {
    let mut used_names: BTreeSet<String> = objects
        .iter()
        .flat_map(|o| o.symbols.iter())
        .filter(|s| !s.name.is_empty())
        .map(|s| s.name.clone())
        .collect();

    // 1. Group distinct non-local `raw_name`s by their initial demangled name in appearance order.
    let mut non_local_order: Vec<String> = Vec::new();
    let mut non_local_groups: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for o in objects.iter() {
        for s in &o.symbols {
            if s.bind == SymBind::Local || s.raw_name.is_empty() {
                continue;
            }
            let group = non_local_groups.entry(s.name.clone()).or_insert_with(|| {
                non_local_order.push(s.name.clone());
                Vec::new()
            });
            if !group.contains(&s.raw_name) {
                group.push(s.raw_name.clone());
            }
        }
    }

    let mut raw_to_name: BTreeMap<String, String> = BTreeMap::new();
    for base in non_local_order {
        let mut seq = 1usize;
        for (idx, raw) in non_local_groups[&base].iter().enumerate() {
            let assigned = if idx == 0 {
                base.clone()
            } else {
                loop {
                    let candidate = format!("{base}#{seq}");
                    seq += 1;
                    if used_names.insert(candidate.clone()) {
                        break candidate;
                    }
                }
            };
            raw_to_name.insert(raw.clone(), assigned);
        }
    }

    for o in objects.iter_mut() {
        for s in &mut o.symbols {
            if s.bind != SymBind::Local && let Some(assigned) = raw_to_name.get(&s.raw_name) {
                s.name = assigned.clone();
            }
        }
    }

    // 2. Disambiguate `STB_LOCAL` defined entities that collide with another defined entity
    //    or with any non-local symbol.
    let non_local_names: BTreeSet<String> = objects
        .iter()
        .flat_map(|o| o.symbols.iter())
        .filter(|s| s.bind != SymBind::Local && !s.raw_name.is_empty())
        .map(|s| s.name.clone())
        .collect();
    let mut defined_counts: BTreeMap<String, usize> = BTreeMap::new();
    for o in objects.iter() {
        for s in o.symbols.iter().filter(|s| is_defined_entity(s)) {
            *defined_counts.entry(s.name.clone()).or_insert(0) += 1;
        }
    }

    let mut local_seq: BTreeMap<String, usize> = BTreeMap::new();
    for o in objects.iter_mut() {
        for s in &mut o.symbols {
            if s.bind == SymBind::Local && is_defined_entity(s) {
                let collides = defined_counts.get(&s.name).copied().unwrap_or(0) > 1
                    || non_local_names.contains(&s.name);
                if collides {
                    let base = s.name.clone();
                    let seq = local_seq.entry(base.clone()).or_insert(0);
                    s.name = loop {
                        *seq += 1;
                        let candidate = format!("{base} [local#{seq}]");
                        if used_names.insert(candidate.clone()) {
                            break candidate;
                        }
                    };
                }
            }
        }
    }
}

/// Fail if two different defined functions/objects/TLS variables share a demangled name.
pub fn check_name_collisions(objects: &[ObjObject]) -> Result<()> {
    let mut seen: BTreeMap<&str, (&str, &str)> = BTreeMap::new();
    for o in objects {
        for s in o.symbols.iter().filter(|s| is_defined_entity(s)) {
            if let Some((prev_obj, prev_raw)) = seen.insert(&s.name, (&o.name, &s.raw_name)) {
                bail!(
                    "demangled name collision: `{}` is defined as `{prev_raw}` ({prev_obj}) and `{}` ({})",
                    s.name, s.raw_name, o.name
                );
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lean Doc-Comment Escaping Helper
// ---------------------------------------------------------------------------

/// Make `s` safe inside a Lean block comment (which nests and ends at `-/`).
pub fn doc_safe(s: &str) -> String {
    s.replace("/-", "/ -").replace("-/", "- /")
}

#[cfg(test)]
mod tests;
