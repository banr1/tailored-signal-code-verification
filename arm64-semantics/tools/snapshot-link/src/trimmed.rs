// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Real relocatable objects for trimmed `[[sysroot_objects]]` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. Lets `snapshot-link --stock` link exactly the trimmed object
//!   the proofs are about, not the whole codegen unit it was cut from.
//! - **Purpose:** `rust-obj2lean` extracts a `[[sysroot_objects]]` entry as a *trim* of one sysroot
//!   rlib member: only the sections reachable from the `roots` through relocations against local
//!   symbols, with every global defined in a dropped section turned undefined. The bytes on disk
//!   (`ObjObject::elf_bytes`) are still the whole member. Linking that member, even with
//!   `--gc-sections`, can resolve those globals to the member's own copies (lld's liveness follows
//!   every relocation, and `.eh_frame` keeps the personality routine and its tables alive), so
//!   the linked code would differ from the extracted code. [`emit`] writes the trim itself as an
//!   ELF64 AArch64 `ET_REL`: the kept sections byte for byte, the trimmed symbol table (dropped-
//!   section globals `SHN_UNDEF`) and the renumbered relocations. [`check_round_trip`] re-parses
//!   the result with the extractor's own `object`-crate reader and requires it to give back the
//!   same object (sections, bytes, flags, alignment, every symbol including locals and aliases,
//!   every relocation); [`check_idempotent`] re-extracts it with the same roots and requires the
//!   same trim again.
//! - Link-time guards: [`disallowed_definers`] (after the link every hooked extern resolves to an
//!   allowed object or the C runtime; the archive and single-definer checks are in
//!   [`crate::stock_hooks`]) and [`exempt_aliases`] (names the unwind-symbol audit may
//!   skip: pure aliases in a kept root section whose linked bytes equal the trimmed bytes).
//!
//! # Key Types & Functions
//! - [`write()`]: emit, check, write. [`emit`]: trimmed `ObjObject` -> `.o` bytes.
//! - [`check_round_trip`], [`check_idempotent`]: the faithfulness checks.
//! - [`keep_set_digest`]: SHA-256 of the kept sections (`<elf index>\t<name>` lines).
//!
//! # When to Read This File
//! - Read this file to see how a trimmed sysroot object becomes a linkable `.o`.

use anyhow::{Result, bail, ensure};
use object::elf;
use object::write::StringId;
use object::write::elf::{FileHeader, Rel, SectionHeader, Sym, Writer};
use object::{Endianness, Object, ObjectSection, ObjectSymbol};
use rust_obj2lean::trusted_common::{
    ObjObject, ObjReloc, ObjSection, ObjSymbol, RelocType, SymBind, SymKind, SymSection,
};
use rust_obj2lean::trusted_extractor::{Trim, parse_object, parse_object_with};
use rust_obj2lean::untrusted_driver::root_section_closure;
use std::path::Path;

/// The raw `R_AARCH64_*` number of `t` (the inverse of [`RelocType::from_r_type`]).
fn r_type_number(t: RelocType) -> Result<u32> {
    if let RelocType::Other(n) = t {
        return Ok(n);
    }
    (0..2048u32)
        .find(|&n| RelocType::from_r_type(n) == t)
        .ok_or_else(|| anyhow::anyhow!("no R_AARCH64 number for relocation type {t:?}"))
}

fn st_bind(b: SymBind) -> u8 {
    match b {
        SymBind::Local => elf::STB_LOCAL,
        SymBind::Global => elf::STB_GLOBAL,
        SymBind::Weak => elf::STB_WEAK,
        SymBind::GnuUnique => elf::STB_GNU_UNIQUE,
        SymBind::Other(n) => n,
    }
}

fn st_type(k: SymKind) -> u8 {
    match k {
        SymKind::Notype => elf::STT_NOTYPE,
        SymKind::Func => elf::STT_FUNC,
        SymKind::Object => elf::STT_OBJECT,
        SymKind::Tls => elf::STT_TLS,
        SymKind::Section => elf::STT_SECTION,
        SymKind::File => elf::STT_FILE,
        SymKind::Common => elf::STT_COMMON,
        SymKind::GnuIfunc => elf::STT_GNU_IFUNC,
        SymKind::Other(n) => n,
    }
}

/// Write the trimmed object `o` as a relocatable ELF64 AArch64 file.
///
/// Fails on what the trim cannot represent faithfully: section groups with a kept member section
/// (`SHT_GROUP` / `SHF_GROUP`), `SHF_LINK_ORDER` (its `sh_link` is not kept), symbols in sections
/// that are not extracted (`SymSection::Other`), and a symbol table with a local after a
/// non-local. Groups whose member sections were all trimmed away (empty `sections`) are ignored:
/// nothing of them is emitted.
pub fn emit(o: &ObjObject) -> Result<Vec<u8>> {
    let name = &o.name;
    ensure!(
        o.groups.iter().all(|g| g.sections.is_empty()),
        "trimmed `{name}` keeps a section group"
    );
    for s in &o.sections {
        ensure!(
            s.sh_flags & u64::from(elf::SHF_GROUP | elf::SHF_LINK_ORDER) == 0,
            "trimmed `{name}`: section `{}` has SHF_GROUP or SHF_LINK_ORDER",
            s.name
        );
    }
    let num_local = o
        .symbols
        .iter()
        .take_while(|s| s.bind == SymBind::Local)
        .count();
    ensure!(
        o.symbols[num_local..]
            .iter()
            .all(|s| s.bind != SymBind::Local),
        "trimmed `{name}`: a local symbol follows a non-local one"
    );

    let rel_sec_names: Vec<String> = o
        .sections
        .iter()
        .map(|s| format!("{}{}", if s.is_rel { ".rel" } else { ".rela" }, s.name))
        .collect();
    let mut buf = Vec::new();
    let mut w = Writer::new(Endianness::Little, true, &mut buf);
    w.reserve_file_header();

    // Section indices: null, the kept sections in order, their relocation sections, then
    // `.symtab` / `.strtab` / `.shstrtab`.
    w.reserve_null_section_index();
    let sec_names: Vec<StringId> = o
        .sections
        .iter()
        .map(|s| w.add_section_name(s.name.as_bytes()))
        .collect();
    let sec_idx: Vec<_> = o
        .sections
        .iter()
        .map(|_| w.reserve_section_index())
        .collect();
    let rel_names: Vec<Option<(StringId, object::write::elf::SectionIndex)>> = o
        .sections
        .iter()
        .zip(&rel_sec_names)
        .map(|(s, rn)| {
            (!s.relocs.is_empty())
                .then(|| (w.add_section_name(rn.as_bytes()), w.reserve_section_index()))
        })
        .collect();
    let symtab_idx = w.reserve_symtab_section_index();
    w.reserve_strtab_section_index();
    w.reserve_shstrtab_section_index();

    // Symbols, in the trimmed order (so relocation symbol indices are unchanged).
    let sym_names: Vec<Option<StringId>> = o
        .symbols
        .iter()
        .enumerate()
        .map(|(i, s)| {
            (i != 0 && !s.raw_name.is_empty() && s.kind != SymKind::Section)
                .then(|| w.add_string(s.raw_name.as_bytes()))
        })
        .collect();
    let mut syms = Vec::with_capacity(o.symbols.len());
    for (i, s) in o.symbols.iter().enumerate() {
        let (section, st_shndx) = match s.sec {
            SymSection::Undef => (None, elf::SHN_UNDEF),
            SymSection::Abs => (None, elf::SHN_ABS),
            SymSection::Common => (None, elf::SHN_COMMON),
            SymSection::Sec(k) => (Some(sec_idx[k]), 0),
            SymSection::Other => bail!(
                "trimmed `{name}`: symbol `{}` is in a section that is not extracted",
                s.raw_name
            ),
        };
        if i == 0 {
            w.reserve_null_symbol_index();
        } else {
            w.reserve_symbol_index(section);
        }
        syms.push(Sym {
            name: sym_names[i],
            section,
            st_info: (st_bind(s.bind) << 4) | st_type(s.kind),
            st_other: s.vis,
            st_shndx,
            st_value: s.value,
            st_size: s.size,
        });
    }

    // File layout: section contents, relocations, symtab, strtab, shstrtab, section headers.
    let offsets: Vec<usize> = o
        .sections
        .iter()
        .map(|s| {
            if s.is_nobits() {
                0
            } else {
                w.reserve(s.bytes.len(), s.align as usize)
            }
        })
        .collect();
    let rel_offsets: Vec<usize> = o
        .sections
        .iter()
        .map(|s| {
            if s.relocs.is_empty() {
                0
            } else {
                w.reserve_relocations(s.relocs.len(), !s.is_rel)
            }
        })
        .collect();
    w.reserve_symtab();
    w.reserve_strtab();
    w.reserve_shstrtab();
    w.reserve_section_headers();

    w.write_file_header(&FileHeader {
        os_abi: elf::ELFOSABI_NONE,
        abi_version: 0,
        e_type: elf::ET_REL,
        e_machine: elf::EM_AARCH64,
        e_entry: 0,
        e_flags: 0,
    })?;
    for (s, &off) in o.sections.iter().zip(&offsets) {
        if !s.is_nobits() {
            w.write_align(s.align as usize);
            debug_assert_eq!(w.len(), off);
            w.write(&s.bytes);
        }
    }
    for s in o.sections.iter().filter(|s| !s.relocs.is_empty()) {
        w.write_align_relocation();
        for r in &s.relocs {
            w.write_relocation(
                !s.is_rel,
                &Rel {
                    r_offset: r.offset,
                    r_sym: r.sym as u32,
                    r_type: r_type_number(r.rtype)?,
                    r_addend: r.addend,
                },
            );
        }
    }
    w.write_null_symbol();
    for s in &syms[1..] {
        w.write_symbol(s);
    }
    w.write_strtab();
    w.write_shstrtab();
    w.write_null_section_header();
    for (k, s) in o.sections.iter().enumerate() {
        w.write_section_header(&SectionHeader {
            name: Some(sec_names[k]),
            sh_type: s.sh_type,
            sh_flags: s.sh_flags,
            sh_addr: s.addr,
            sh_offset: offsets[k] as u64,
            sh_size: s.size,
            sh_link: 0,
            sh_info: 0,
            sh_addralign: s.align,
            sh_entsize: s.entsize,
        });
    }
    for (k, s) in o.sections.iter().enumerate() {
        if let Some((n, _)) = rel_names[k] {
            w.write_relocation_section_header(
                n,
                sec_idx[k],
                symtab_idx,
                rel_offsets[k],
                s.relocs.len(),
                !s.is_rel,
            );
        }
    }
    w.write_symtab_section_header(num_local as u32);
    w.write_strtab_section_header();
    w.write_shstrtab_section_header();
    ensure!(
        w.reserved_len() == w.len(),
        "trimmed `{name}`: ELF layout mismatch"
    );
    Ok(buf)
}

/// The fields of a section that the proofs see (everything but its position in the file).
#[allow(clippy::type_complexity)]
fn section_key(s: &ObjSection) -> (&str, u32, u64, u64, u64, u64, u64, &[u8], &[ObjReloc], bool) {
    (
        &s.name, s.sh_type, s.sh_flags, s.addr, s.align, s.entsize, s.size, &s.bytes, &s.relocs,
        s.is_rel,
    )
}

/// The fields of a symbol that the proofs see. The display name is derived from `raw_name` (the
/// extractor suffixes or disambiguates it afterwards), so it is not compared.
fn symbol_key(s: &ObjSymbol) -> (&str, SymKind, SymBind, u8, SymSection, u64, u64) {
    (&s.raw_name, s.kind, s.bind, s.vis, s.sec, s.value, s.size)
}

/// Check that re-parsing `bytes` (the output of [`emit`] for `trim`) with the extractor's reader
/// gives back `trim`: the same sections (name, header fields, contents, relocations) in the same
/// order, the same symbols (locals and aliases included), and no section groups.
pub fn check_round_trip(trim: &ObjObject, bytes: &[u8]) -> Result<()> {
    let back = parse_object(&trim.name, bytes.to_vec())?;
    check_same("emitted", trim, &back)
}

/// Check that extracting `bytes` (the output of [`emit`] for `trim`) again, trimmed to the closure
/// of the same `roots`, gives back `trim`: trimming the emitted object is the identity.
pub fn check_idempotent(trim: &ObjObject, bytes: &[u8], roots: &[String]) -> Result<()> {
    let name = &trim.name;
    let t = Trim {
        keep: root_section_closure(bytes, roots)?,
        local_suffix: format!(" [lib{name}]"),
    };
    let back = parse_object_with(name, bytes.to_vec(), Some(&t))?;
    check_same("re-extracted", trim, &back)
}

fn check_same(what: &str, trim: &ObjObject, back: &ObjObject) -> Result<()> {
    let name = &trim.name;
    ensure!(
        back.groups.is_empty(),
        "{what} `{name}.o` has a section group"
    );
    ensure!(
        back.sections.len() == trim.sections.len(),
        "{what} `{name}.o` has {} sections, the trim {}",
        back.sections.len(),
        trim.sections.len()
    );
    for (b, t) in back.sections.iter().zip(&trim.sections) {
        ensure!(
            section_key(b) == section_key(t),
            "{what} `{name}.o`: section `{}` differs from the trim",
            t.name
        );
    }
    ensure!(
        back.symbols.len() == trim.symbols.len(),
        "{what} `{name}.o` has {} symbols, the trim {}",
        back.symbols.len(),
        trim.symbols.len()
    );
    for (b, t) in back.symbols.iter().zip(&trim.symbols) {
        ensure!(
            symbol_key(b) == symbol_key(t),
            "{what} `{name}.o`: symbol `{}` differs from the trim",
            t.raw_name
        );
    }
    Ok(())
}

/// A trimmed `[[sysroot_objects]]` entry of a stock image.
#[derive(Clone, Debug)]
pub struct Trimmed {
    /// The extractor's provenance line (sysroot rlib, member, SHA-256, kept sections).
    pub provenance: String,
    /// The entry's `roots`.
    pub roots: Vec<String>,
}

/// Write the trim `o` (rooted at `roots`) to `path` as [`emit`] gives it, after
/// [`check_round_trip`] and [`check_idempotent`]; returns the bytes written.
pub fn write(o: &ObjObject, roots: &[String], path: &Path) -> Result<Vec<u8>> {
    let bytes = emit(o)?;
    check_round_trip(o, &bytes)?;
    check_idempotent(o, &bytes, roots)?;
    std::fs::write(path, &bytes)?;
    Ok(bytes)
}

/// The global and weak symbols the trim `o` defines: `--undefined` roots that keep every kept
/// section live under `--gc-sections` (each kept section is reachable from a root's section).
pub fn roots(o: &ObjObject) -> impl Iterator<Item = &str> {
    o.symbols
        .iter()
        .filter(|s| matches!(s.bind, SymBind::Global | SymBind::Weak))
        .filter(|s| matches!(s.sec, SymSection::Sec(_)))
        .map(|s| s.raw_name.as_str())
}

/// Fail if the `ld.lld --print-gc-sections` output `lld_out` removes any section of the emitted
/// trims `paths`: the linked image must contain the whole keep set, not a subset of it.
pub fn check_none_collected(lld_out: &str, paths: &[&std::path::Path]) -> Result<()> {
    let dropped: Vec<&str> = lld_out
        .lines()
        .filter_map(|l| l.trim().strip_prefix("removing unused section "))
        .filter(|s| {
            paths
                .iter()
                .any(|p| s.starts_with(&format!("{}:(", p.display())))
        })
        .collect();
    ensure!(
        dropped.is_empty(),
        "--gc-sections removed kept sections of a trimmed sysroot object:\n  {}",
        dropped.join("\n  ")
    );
    Ok(())
}

/// SHA-256 of the kept sections of `trim`, one `<elf index>\t<name>\n` line each, in order.
pub fn keep_set_digest(trim: &ObjObject) -> String {
    let lines: String = trim
        .sections
        .iter()
        .map(|s| format!("{}\t{}\n", s.elf_index, s.name))
        .collect();
    crate::link::sha256(lines.as_bytes())
}

/// The definitions of hooked externs in the `ld.lld --trace-symbol` output `lld_out` that come
/// from neither an object in `objects` nor a member of an archive in `archives` (the extern
/// stubs and the C runtime), as `<file>: <name>` lines.
pub fn disallowed_definers(lld_out: &str, objects: &[&Path], archives: &[&Path]) -> Vec<String> {
    let allowed = |file: &str| {
        objects.iter().any(|p| file == p.display().to_string())
            || archives.iter().any(|p| {
                file.strip_prefix(&p.display().to_string())
                    .is_some_and(|m| m.starts_with('(') && m.ends_with(')'))
            })
    };
    lld_out
        .lines()
        .filter_map(|l| l.trim().split_once(": definition of "))
        .filter(|(file, _)| !allowed(file))
        .map(|(file, sym)| format!("{file}: {sym}"))
        .collect()
}

/// The flagged-name symbols (see [`crate::verify::is_forbidden_name`]) of `trims` that are pure
/// aliases in the linked `exe`: defined in a kept section that also holds a root, at the same
/// offset as a non-flagged defined symbol at least as large, with the section's linked bytes equal
/// to the trim's outside relocation fields.
pub fn exempt_aliases(exe: &[u8], trims: &[(&ObjObject, &[String])]) -> Result<Vec<String>> {
    let elf = object::File::parse(exe)?;
    let addr_of = |raw: &str| {
        elf.symbols()
            .find(|s| s.name() == Ok(raw) && s.is_definition())
            .map(|s| s.address())
    };
    let mut out = Vec::new();
    for (o, roots) in trims {
        let defined = |s: &&ObjSymbol| {
            matches!(s.sec, SymSection::Sec(_)) && matches!(s.kind, SymKind::Func | SymKind::Object)
        };
        for (j, sec) in o.sections.iter().enumerate() {
            let here: Vec<&ObjSymbol> = o
                .symbols
                .iter()
                .filter(defined)
                .filter(|s| s.sec == SymSection::Sec(j))
                .collect();
            let is_root = here.iter().any(|s| {
                s.bind != SymBind::Local && roots.iter().any(|r| *r == s.raw_name || *r == s.name)
            });
            if !is_root {
                continue;
            }
            for a in here
                .iter()
                .filter(|s| crate::verify::is_forbidden_name(&s.raw_name))
            {
                let owner = here.iter().find(|s| {
                    !crate::verify::is_forbidden_name(&s.raw_name)
                        && s.value == a.value
                        && s.size >= a.size
                });
                let Some(owner) = owner else { continue };
                // The section's linked base, from the owner's address in the executable.
                let Some(base) = addr_of(&owner.raw_name).map(|x| x - owner.value) else {
                    continue;
                };
                if addr_of(&a.raw_name) != Some(base + a.value) {
                    continue;
                }
                let Some(linked) = read_at(&elf, base, sec.bytes.len() as u64) else {
                    continue;
                };
                let mask = crate::census::reloc_mask(sec);
                let same = linked
                    .iter()
                    .zip(&sec.bytes)
                    .zip(&mask)
                    .all(|((x, y), m)| *m || x == y);
                if same {
                    out.push(a.raw_name.clone());
                }
            }
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

/// The `n` bytes of `elf` at address `a`, from the one section holding them.
fn read_at<'d>(elf: &object::File<'d>, a: u64, n: u64) -> Option<&'d [u8]> {
    elf.sections().find_map(|s| {
        let off = a.checked_sub(s.address())?;
        (s.address() != 0 && off + n <= s.size())
            .then(|| s.data().ok())
            .flatten()
            .and_then(|d| d.get(off as usize..(off + n) as usize))
    })
}
