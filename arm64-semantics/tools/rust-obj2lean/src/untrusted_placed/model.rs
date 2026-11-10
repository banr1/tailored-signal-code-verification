// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Build the `Arm64.Obj.PlacedLib` of a library from its relocatable objects (`[OUTSIDE TCB]`).
//!
//! # Layout rules (what stock `ld.lld` does without a linker script)
//! - Every non-empty executable input section (`.text*`) of the library objects goes into the
//!   output `.text` in input order (objects in load order, sections in section-header order), each
//!   at the next offset aligned to its `sh_addralign`, gaps filled with zero bytes (lld's fill for
//!   executable sections on AArch64). The block is that concatenation; its alignment is the largest
//!   input-section alignment, so offsets relative to the block are the same for every block base
//!   aligned to it.
//! - Data input sections (`.rodata*`, `.data*`, `.bss*`) become one data object each; `SHF_MERGE`
//!   sections are split into pieces (strings at each NUL terminator, constants every `sh_entsize`
//!   bytes), one data object per piece, as lld deduplicates pieces independently. Only data objects
//!   that some relocation reaches (transitively from the text) are emitted: an unreferenced object
//!   constrains nothing the library does.
//!
//! # Naming
//! Block symbols are the defining `STT_FUNC` symbols (demangled names), plus `"<obj>:<section>+<off>"`
//! names synthesized for relocation targets that are not function starts. Data objects are named by
//! their covering `STT_OBJECT` symbol, else `"<obj>:<section>"` (`"<obj>:<section>+<off>"` for
//! merge pieces), with the per-build hash of anonymous `.Lanon.<hash>.<n>` sections removed.
//! Externs keep their raw (linker) names.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use anyhow::{Context, Result, bail, ensure};
use object::elf;

use crate::trusted_common::{
    ObjObject, ObjSection, ObjSymbol, RelocKind, RelocType, SecKind, SymBind, SymKind, SymSection,
};
use crate::trusted_extractor::demangle_rust_symbol;

/// One relocation (`Arm64.Obj.RelocEntry` with `localSym = false`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PReloc {
    pub off: u64,
    pub kind: RelocKind,
    pub sym: String,
    pub addend: i64,
}

/// `Arm64.Obj.CodeBlock`.
#[derive(Clone, Debug, Default)]
pub struct PBlock {
    pub code: Vec<u8>,
    pub align: u64,
    pub symbols: Vec<(String, u64)>,
    pub relocs: Vec<PReloc>,
    pub externs: Vec<String>,
    /// `weakRefs`: the externs that every object referencing them leaves undefined `STB_WEAK`.
    pub weak_refs: Vec<String>,
}

/// `Arm64.Obj.SymDataInfo`, plus provenance.
#[derive(Clone, Debug, Default)]
pub struct PData {
    pub sym: String,
    pub align: u64,
    pub read_only: bool,
    pub is_tls: bool,
    pub bytes: Vec<u8>,
    pub zero_tail: u64,
    pub relocs: Vec<PReloc>,
    /// `(object index, section index, offset in section)` of the object's first byte.
    pub origin: (usize, usize, u64),
    /// Raw `.symtab` names of symbols defined at the object's first byte (for the witness).
    pub raw_names: Vec<String>,
    /// Demangled names of the same symbols, hashes removed (for the witness).
    pub demangled_names: Vec<String>,
}

/// One text input section placed in the block.
#[derive(Clone, Debug)]
pub struct PTextSec {
    pub obj: usize,
    pub sec: usize,
    pub off: u64,
    pub size: u64,
    /// `"<obj>:<section>"` (display name).
    pub label: String,
}

/// `Arm64.Obj.PlacedLib`, plus the census facts the generator learnt on the way.
#[derive(Clone, Debug, Default)]
pub struct PLib {
    pub name: String,
    pub text: PBlock,
    pub data: Vec<PData>,
    pub tls: Vec<PData>,
    pub exports: Vec<String>,
    pub text_secs: Vec<PTextSec>,
    /// Data pieces/sections that no relocation reaches (not emitted).
    pub unreferenced_data: Vec<String>,
    /// Raw names of block symbols (for matching against a linked ELF's `.symtab`).
    pub block_raw: BTreeMap<String, String>,
}

/// `Arm64.Obj.MultiPlacedLib`: one independently placed `CodeBlock` per `.text.<fn>` section
/// (or per `STT_FUNC` symbol slice) and per-symbol `SymDataInfo` entries.
#[derive(Clone, Debug, Default)]
pub struct PMultiLib {
    pub name: String,
    pub blocks: Vec<PBlock>,
    pub data: Vec<PData>,
    pub tls: Vec<PData>,
    pub exports: Vec<String>,
    pub text_secs: Vec<PTextSec>,
    /// Data pieces/sections that no relocation reaches (not emitted).
    pub unreferenced_data: Vec<String>,
    /// Raw names of block symbols (for matching against a linked ELF's `.symtab`).
    pub block_raw: BTreeMap<String, String>,
    /// `exportSyms`: `(export, raw .symtab name)` for each export whose raw name differs.
    pub export_syms: Vec<(String, String)>,
}

impl PMultiLib {
    /// `MultiPlacedLib.elfSym`: the raw `.symtab` name of export `e` (its `export_syms` entry,
    /// or `e` itself).
    pub fn elf_sym<'a>(&'a self, e: &'a str) -> &'a str {
        self.export_syms
            .iter()
            .find(|(x, _)| x == e)
            .map_or(e, |(_, raw)| raw.as_str())
    }

    /// Look up symbol `sym` across `self.blocks`, returning `(block_idx, offset_in_block)`.
    pub fn lookup_block_sym(&self, sym: &str) -> Option<(usize, u64)> {
        self.blocks
            .iter()
            .enumerate()
            .find_map(|(i, b)| b.lookup(sym).map(|off| (i, off)))
    }
}

impl PBlock {
    pub fn lookup(&self, sym: &str) -> Option<u64> {
        self.symbols.iter().find(|(n, _)| n == sym).map(|(_, o)| *o)
    }
}

const SHF_ALLOC: u64 = elf::SHF_ALLOC as u64;
const SHF_WRITE: u64 = elf::SHF_WRITE as u64;
const SHF_EXEC: u64 = elf::SHF_EXECINSTR as u64;
const SHF_MERGE: u64 = elf::SHF_MERGE as u64;
const SHF_STRINGS: u64 = elf::SHF_STRINGS as u64;
const SHF_GROUP: u64 = elf::SHF_GROUP as u64;

/// Remove the per-build hash of an anonymous constant section name
/// (`.rodata..Lanon.<hex>.<n>` -> `.rodata..Lanon.<n>`).
pub fn strip_anon_hash(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut rest = name;
    while let Some(i) = rest.find(".Lanon.") {
        out.push_str(&rest[..i + 7]);
        rest = &rest[i + 7..];
        let hex_len = rest.chars().take_while(|c| c.is_ascii_hexdigit()).count();
        if hex_len >= 16 && rest[hex_len..].starts_with('.') {
            rest = &rest[hex_len + 1..];
        }
    }
    out.push_str(rest);
    out
}

/// Human-readable section name: prefix kept, a mangled Rust symbol suffix demangled
/// (`.text._RNv..` -> `.text.my_lib::f`), anonymous hashes removed.
pub fn display_section_name(name: &str) -> String {
    for prefix in [
        ".text.",
        ".rodata.",
        ".data.rel.ro.",
        ".data.",
        ".bss.",
        ".tdata.",
        ".tbss.",
    ] {
        if let Some(rest) = name.strip_prefix(prefix)
            && (rest.starts_with("_R") || rest.starts_with("_ZN"))
        {
            return format!("{prefix}{}", demangle_rust_symbol(rest));
        }
    }
    strip_anon_hash(name)
}

/// Demangled name with any `::h<hash>` legacy suffix and anonymous hash removed.
pub fn stable_demangled(raw: &str) -> String {
    strip_anon_hash(&demangle_rust_symbol(raw))
}

/// Pieces `(start, len)` of an `SHF_MERGE` section: NUL-terminated strings (entsize 1) or
/// `entsize`-byte constants.
pub fn merge_pieces(sec: &ObjSection) -> Result<Vec<(u64, u64)>> {
    let ent = sec.entsize.max(1);
    ensure!(
        sec.size % ent == 0,
        "merge section {} size {} is not a multiple of entsize {ent}",
        sec.name,
        sec.size
    );
    let mut out = Vec::new();
    if sec.sh_flags & SHF_STRINGS != 0 {
        let mut start = 0u64;
        let mut i = 0u64;
        while i < sec.size {
            let chunk = &sec.bytes[i as usize..(i + ent) as usize];
            i += ent;
            if chunk.iter().all(|b| *b == 0) {
                out.push((start, i - start));
                start = i;
            }
        }
        ensure!(
            start == sec.size,
            "string merge section {} is not NUL-terminated",
            sec.name
        );
    } else {
        let mut i = 0;
        while i < sec.size {
            out.push((i, ent));
            i += ent;
        }
    }
    Ok(out)
}

/// What a data section of the library contributes: its candidate data objects.
#[derive(Clone, Debug)]
struct DataEntry {
    name: String,
    start: u64,
    len: u64,
}

/// Where a relocation target lands.
enum Target {
    Block(String, i64),
    Data(usize, usize, usize, i64),
    Extern(String, i64),
}

struct Ctx<'a> {
    objs: &'a [ObjObject],
    /// `(obj, sec)` -> block offset of a text section.
    text_off: BTreeMap<(usize, usize), u64>,
    /// `(obj, sec)` -> entries of a data section (one entry, or the merge pieces).
    data_entries: BTreeMap<(usize, usize), Vec<DataEntry>>,
    /// `(obj, sec, off)` -> block symbol name at that offset (first name wins).
    fn_at: BTreeMap<(usize, usize, u64), String>,
    /// raw name -> `(obj, sym index)` of every non-local defined symbol.
    globals: BTreeMap<String, (usize, usize)>,
    /// Synthesized block symbols.
    synth: BTreeMap<(usize, usize, u64), String>,
    taken: BTreeSet<String>,
}

fn sec_kind(s: &ObjSection) -> Option<SecKind> {
    SecKind::classify(&s.name, s.sh_type, s.sh_flags & !SHF_GROUP)
}

fn is_text(s: &ObjSection) -> bool {
    s.sh_flags & SHF_ALLOC != 0 && s.sh_flags & SHF_EXEC != 0
}

impl Ctx<'_> {
    fn unique(&mut self, base: String, obj: &str) -> String {
        let mut name = base.clone();
        if self.taken.contains(&name) {
            name = format!("{base} [{obj}]");
        }
        let mut k = 2;
        while self.taken.contains(&name) {
            name = format!("{base} [{obj}#{k}]");
            k += 1;
        }
        self.taken.insert(name.clone());
        name
    }

    /// Resolve symbol `si` of object `oi` with addend `addend` to a target.
    fn resolve(&mut self, oi: usize, si: usize, addend: i64, depth: u32) -> Result<Target> {
        let o = &self.objs[oi];
        let s = o
            .symbols
            .get(si)
            .with_context(|| format!("{}: bad symbol index {si}", o.name))?;
        match s.sec {
            SymSection::Undef => {
                ensure!(
                    depth == 0,
                    "{}: symbol {} resolves cyclically",
                    o.name,
                    s.raw_name
                );
                if let Some(&(oj, sj)) = self.globals.get(&s.raw_name) {
                    return self.resolve(oj, sj, addend, depth + 1);
                }
                ensure!(
                    !s.raw_name.is_empty(),
                    "{}: undefined unnamed symbol",
                    o.name
                );
                let ext_name = if s.name.starts_with("examples::") {
                    s.name.clone()
                } else {
                    s.raw_name.clone()
                };
                Ok(Target::Extern(ext_name, addend))
            }
            SymSection::Sec(sec) => {
                let is_section_sym = s.kind == SymKind::Section;
                if self.text_off.contains_key(&(oi, sec)) {
                    // A function symbol targets itself; anything else targets an offset.
                    if !is_section_sym && let Some(n) = self.fn_at.get(&(oi, sec, s.value)) {
                        return Ok(Target::Block(n.clone(), addend));
                    }
                    let t = s.value as i64 + if is_section_sym { addend } else { 0 };
                    let rem = if is_section_sym { 0 } else { addend };
                    ensure!(t >= 0, "{}: negative text target", o.name);
                    let t = t as u64;
                    let name = match self.fn_at.get(&(oi, sec, t)) {
                        Some(n) => n.clone(),
                        None => match self.synth.get(&(oi, sec, t)) {
                            Some(n) => n.clone(),
                            None => {
                                let base = format!(
                                    "{}:{}+{t:#x}",
                                    o.name,
                                    display_section_name(&o.sections[sec].name)
                                );
                                let n = self.unique(base, &o.name.clone());
                                self.synth.insert((oi, sec, t), n.clone());
                                n
                            }
                        },
                    };
                    return Ok(Target::Block(name, rem));
                }
                if let Some(entries) = self.data_entries.get(&(oi, sec)) {
                    let sec_ref = &o.sections[sec];
                    let merge = sec_ref.sh_flags & SHF_MERGE != 0;
                    // lld: a section symbol's offset includes the addend for merge or multi-entry
                    // sections; other symbols select the piece by their own value.
                    let sel = if (merge || entries.len() > 1) && is_section_sym {
                        s.value as i64 + addend
                    } else {
                        s.value as i64
                    };
                    ensure!(sel >= 0, "{}: negative data target", o.name);
                    let sel = sel as u64;
                    let idx = entries
                        .iter()
                        .position(|e| e.start <= sel && sel < e.start + e.len.max(1))
                        .or_else(|| (sel == sec_ref.size).then_some(entries.len() - 1))
                        .with_context(|| {
                            format!("{}: target {sel:#x} not in {}", o.name, sec_ref.name)
                        })?;
                    let start = entries[idx].start as i64;
                    let rel = s.value as i64 + addend - start;
                    return Ok(Target::Data(oi, sec, idx, rel));
                }
                if matches!(
                    sec_kind(&o.sections[sec]),
                    Some(SecKind::Tdata | SecKind::Tbss)
                ) {
                    if !is_section_sym && !s.raw_name.is_empty() {
                        return Ok(Target::Extern(s.raw_name.clone(), addend));
                    }
                    let off = s.value as i64 + addend;
                    ensure!(off >= 0, "{}: negative TLS target", o.name);
                    if let Some(ts) = o.symbols.iter().find(|sym| {
                        sym.sec == SymSection::Sec(sec)
                            && sym.kind == SymKind::Tls
                            && sym.value == off as u64
                            && !sym.raw_name.is_empty()
                    }) {
                        return Ok(Target::Extern(ts.raw_name.clone(), 0));
                    }
                    return Ok(Target::Extern(
                        format!("{}:{}", o.name, display_section_name(&o.sections[sec].name)),
                        off,
                    ));
                }
                bail!(
                    "{}: relocation target {} is in unsupported section {}",
                    o.name,
                    s.name,
                    o.sections[sec].name
                )
            }
            _ => bail!(
                "{}: relocation target {} is absolute/common (unsupported)",
                o.name,
                s.raw_name
            ),
        }
    }
}

/// Build the placed library `name` from `objs` (the library's objects in link order), with
/// exported functions `exports` (raw `.symtab` names of block functions).
pub fn build_placed_lib(name: &str, objs: &[ObjObject], exports: &[String]) -> Result<PLib> {
    build_placed_lib_inner(name, objs, exports, false)
}

fn split_data_entries_by_symbol(o: &ObjObject, si: usize, s: &ObjSection) -> Vec<DataEntry> {
    let starts: BTreeSet<u64> = o
        .symbols
        .iter()
        .filter(|sym| {
            matches!(sym.kind, SymKind::Object | SymKind::Tls)
                && sym.sec == SymSection::Sec(si)
                && !sym.raw_name.is_empty()
                && sym.size > 0
                && sym.value < s.size
        })
        .map(|sym| sym.value)
        .collect();
    if starts.len() >= 2 && *starts.first().unwrap() == 0 {
        let pts: Vec<u64> = starts.into_iter().collect();
        pts.iter()
            .enumerate()
            .map(|(idx, &start)| {
                let next = pts.get(idx + 1).copied().unwrap_or(s.size);
                let len = o
                    .symbols
                    .iter()
                    .filter(|sym| {
                        matches!(sym.kind, SymKind::Object | SymKind::Tls)
                            && sym.sec == SymSection::Sec(si)
                            && !sym.raw_name.is_empty()
                            && sym.value == start
                            && sym.size > 0
                            && start + sym.size <= next
                    })
                    .map(|sym| sym.size)
                    .max()
                    .unwrap_or(next - start);
                DataEntry {
                    name: String::new(),
                    start,
                    len,
                }
            })
            .collect()
    } else {
        vec![DataEntry {
            name: String::new(),
            start: 0,
            len: s.size,
        }]
    }
}

fn build_placed_lib_inner(
    name: &str,
    objs: &[ObjObject],
    exports: &[String],
    split_data_syms: bool,
) -> Result<PLib> {
    let mut ctx = Ctx {
        objs,
        text_off: BTreeMap::new(),
        data_entries: BTreeMap::new(),
        fn_at: BTreeMap::new(),
        globals: BTreeMap::new(),
        synth: BTreeMap::new(),
        taken: BTreeSet::new(),
    };
    // 1. Classify sections and lay out the text block.
    let mut text_secs = Vec::new();
    let mut code: Vec<u8> = Vec::new();
    let mut align = 4u64;
    for (oi, o) in objs.iter().enumerate() {
        for (si, s) in o.sections.iter().enumerate() {
            if s.sh_flags & SHF_ALLOC == 0 || s.name == ".eh_frame" {
                continue;
            }
            if is_text(s) {
                ensure!(
                    sec_kind(s) == Some(SecKind::Text),
                    "{}: unsupported executable section {}",
                    o.name,
                    s.name
                );
                if s.size == 0 {
                    continue;
                }
                let a = s.align.max(1);
                ensure!(
                    a.is_power_of_two(),
                    "{}: bad alignment of {}",
                    o.name,
                    s.name
                );
                align = align.max(a);
                let off = code.len() as u64;
                let off = off.div_ceil(a) * a;
                code.resize(off as usize, 0);
                ensure!(
                    s.bytes.len() as u64 == s.size,
                    "{}: short section {}",
                    o.name,
                    s.name
                );
                code.extend_from_slice(&s.bytes);
                ctx.text_off.insert((oi, si), off);
                text_secs.push(PTextSec {
                    obj: oi,
                    sec: si,
                    off,
                    size: s.size,
                    label: format!("{}:{}", o.name, display_section_name(&s.name)),
                });
                continue;
            }
            match sec_kind(s) {
                Some(
                    SecKind::Rodata
                    | SecKind::Data
                    | SecKind::Bss
                    | SecKind::Tdata
                    | SecKind::Tbss,
                ) => {}
                _ => bail!("{}: unsupported allocated section {}", o.name, s.name),
            }
            // `.init_array` / `.fini_array` hold constructor / destructor pointers (`abs64`
            // relocations to text): plain data for the placed model, which emits them only
            // when the library's text references them.
            if !matches!(
                s.sh_type,
                elf::SHT_PROGBITS | elf::SHT_NOBITS | elf::SHT_INIT_ARRAY | elf::SHT_FINI_ARRAY
            ) {
                bail!("{}: unsupported data section type of {}", o.name, s.name);
            }
            if s.size == 0 {
                continue;
            }
            let entries = if s.sh_flags & SHF_MERGE != 0 {
                ensure!(
                    s.relocs.is_empty(),
                    "{}: relocations in merge section {}",
                    o.name,
                    s.name
                );
                merge_pieces(s)?
                    .into_iter()
                    .map(|(start, len)| DataEntry {
                        name: String::new(),
                        start,
                        len,
                    })
                    .collect()
            } else if split_data_syms
                || matches!(sec_kind(s), Some(SecKind::Tdata | SecKind::Tbss))
            {
                split_data_entries_by_symbol(o, si, s)
            } else {
                vec![DataEntry {
                    name: String::new(),
                    start: 0,
                    len: s.size,
                }]
            };
            ctx.data_entries.insert((oi, si), entries);
        }
    }
    ensure!(!code.is_empty(), "library {name} has no text");
    ensure!(
        code.len() % 4 == 0,
        "library {name}: text length is not a multiple of 4"
    );

    // 2. Block symbols and globals.
    let mut symbols: Vec<(String, u64)> = Vec::new();
    let mut block_raw = BTreeMap::new();
    for (oi, o) in objs.iter().enumerate() {
        for (si, s) in o.symbols.iter().enumerate() {
            if let SymSection::Sec(sec) = s.sec
                && s.bind != SymBind::Local
                && !s.raw_name.is_empty()
                && (ctx.text_off.contains_key(&(oi, sec))
                    || ctx.data_entries.contains_key(&(oi, sec))
                    || matches!(
                        sec_kind(&o.sections[sec]),
                        Some(SecKind::Tdata | SecKind::Tbss)
                    ))
            {
                ensure!(
                    ctx.globals.insert(s.raw_name.clone(), (oi, si)).is_none(),
                    "symbol {} is defined twice in library {name}",
                    s.raw_name
                );
            }
        }
    }
    for (oi, o) in objs.iter().enumerate() {
        let mut fns: Vec<&ObjSymbol> = o
            .symbols
            .iter()
            .filter(|s| s.kind == SymKind::Func && !s.raw_name.is_empty())
            .filter(
                |s| matches!(s.sec, SymSection::Sec(sec) if ctx.text_off.contains_key(&(oi, sec))),
            )
            .collect();
        // Globals first, so that they keep their plain names.
        fns.sort_by_key(|s| s.bind == SymBind::Local);
        for s in fns {
            let SymSection::Sec(sec) = s.sec else {
                unreachable!()
            };
            let base = ctx.text_off[&(oi, sec)];
            ensure!(
                s.value % 4 == 0,
                "{}: misaligned function {}",
                o.name,
                s.name
            );
            let n = ctx.unique(s.name.clone(), &o.name);
            ctx.fn_at
                .entry((oi, sec, s.value))
                .or_insert_with(|| n.clone());
            block_raw.insert(n.clone(), s.raw_name.clone());
            symbols.push((n, base + s.value));
        }
    }

    // 3. Data object names.
    let keys: Vec<(usize, usize)> = ctx.data_entries.keys().copied().collect();
    for (oi, si) in keys {
        let o = &objs[oi];
        let sec = &o.sections[si];
        let merge = sec.sh_flags & SHF_MERGE != 0;
        let n_entries = ctx.data_entries[&(oi, si)].len();
        for k in 0..n_entries {
            let (start, len) = {
                let e = &ctx.data_entries[&(oi, si)][k];
                (e.start, e.len)
            };
            let covering: Vec<&ObjSymbol> = o
                .symbols
                .iter()
                .filter(|s| {
                    matches!(s.kind, SymKind::Object | SymKind::Tls)
                        && s.sec == SymSection::Sec(si)
                        && s.value == start
                        && s.size == len
                        && !s.raw_name.is_empty()
                })
                .collect();
            let base = if let Some(s) = covering.iter().find(|s| s.bind != SymBind::Local) {
                s.name.clone()
            } else if let Some(s) = covering.first() {
                s.name.clone()
            } else if merge {
                format!("{}:{}+{start:#x}", o.name, display_section_name(&sec.name))
            } else {
                format!("{}:{}", o.name, display_section_name(&sec.name))
            };
            let n = ctx.unique(base, &o.name.clone());
            ctx.data_entries.get_mut(&(oi, si)).unwrap()[k].name = n;
        }
    }

    // 4. Text relocations.
    let mut relocs = Vec::new();
    let mut externs = BTreeSet::new();
    let mut needed: VecDeque<(usize, usize, usize)> = VecDeque::new();
    for ts in &text_secs {
        let o = &objs[ts.obj];
        let s = &o.sections[ts.sec];
        for r in &s.relocs {
            if r.rtype == RelocType::None {
                continue;
            }
            let kind = RelocKind::from_reloc_type(r.rtype).with_context(|| {
                format!(
                    "{}: unsupported relocation {:?} in {}",
                    o.name, r.rtype, s.name
                )
            })?;
            ensure!(
                !matches!(
                    kind,
                    RelocKind::Abs64 | RelocKind::Abs32 | RelocKind::Prel32
                ),
                "{}: data relocation {:?} in text section {}",
                o.name,
                r.rtype,
                s.name
            );
            let (sym, addend) = match ctx.resolve(ts.obj, r.sym, r.addend, 0)? {
                Target::Block(n, a) => (n, a),
                Target::Data(oi, si, k, a) => {
                    needed.push_back((oi, si, k));
                    (ctx.data_entries[&(oi, si)][k].name.clone(), a)
                }
                Target::Extern(n, a) => {
                    if matches!(kind, RelocKind::Call26 | RelocKind::Jump26) {
                        externs.insert(n.clone());
                    }
                    (n, a)
                }
            };
            relocs.push(PReloc {
                off: ts.off + r.offset,
                kind,
                sym,
                addend,
            });
        }
    }
    relocs.sort_by_key(|r| r.off);

    // 5. Data objects reachable from the text.
    let mut emitted: BTreeMap<(usize, usize, usize), PData> = BTreeMap::new();
    while let Some(key) = needed.pop_front() {
        if emitted.contains_key(&key) {
            continue;
        }
        let (oi, si, k) = key;
        let o = &objs[oi];
        let sec = &o.sections[si];
        let e = ctx.data_entries[&(oi, si)][k].clone();
        let nobits = sec.sh_type == elf::SHT_NOBITS;
        let mut drelocs = Vec::new();
        if !nobits {
            for r in &sec.relocs {
                if r.rtype == RelocType::None || r.offset < e.start || r.offset >= e.start + e.len {
                    continue;
                }
                let kind = RelocKind::from_reloc_type(r.rtype).with_context(|| {
                    format!(
                        "{}: unsupported relocation {:?} in {}",
                        o.name, r.rtype, sec.name
                    )
                })?;
                ensure!(
                    matches!(
                        kind,
                        RelocKind::Abs64 | RelocKind::Abs32 | RelocKind::Prel32
                    ),
                    "{}: code relocation {:?} in data section {}",
                    o.name,
                    r.rtype,
                    sec.name
                );
                let (sym, addend) = match ctx.resolve(oi, r.sym, r.addend, 0)? {
                    Target::Block(n, a) => (n, a),
                    Target::Data(oj, sj, kj, a) => {
                        needed.push_back((oj, sj, kj));
                        (ctx.data_entries[&(oj, sj)][kj].name.clone(), a)
                    }
                    Target::Extern(n, a) => (n, a),
                };
                drelocs.push(PReloc {
                    off: r.offset - e.start,
                    kind,
                    sym,
                    addend,
                });
            }
        }
        let syms_here: Vec<&ObjSymbol> = o
            .symbols
            .iter()
            .filter(|s| {
                s.sec == SymSection::Sec(si)
                    && s.value == e.start
                    && matches!(s.kind, SymKind::Object | SymKind::Tls | SymKind::Notype)
                    && !s.raw_name.is_empty()
                    && !s.raw_name.starts_with('$')
            })
            .collect();
        let align = if sec.sh_flags & SHF_MERGE != 0 || e.start == 0 {
            sec.align.max(1)
        } else {
            (1u64 << e.start.trailing_zeros()).min(sec.align.max(1)).max(1)
        };
        let is_tls = matches!(sec_kind(sec), Some(SecKind::Tdata | SecKind::Tbss));
        emitted.insert(
            key,
            PData {
                sym: e.name.clone(),
                align,
                read_only: sec.sh_flags & SHF_WRITE == 0,
                is_tls,
                bytes: if nobits {
                    vec![]
                } else {
                    sec.bytes[e.start as usize..(e.start + e.len) as usize].to_vec()
                },
                zero_tail: if nobits { e.len } else { 0 },
                relocs: drelocs,
                origin: (oi, si, e.start),
                raw_names: syms_here.iter().map(|s| s.raw_name.clone()).collect(),
                demangled_names: syms_here
                    .iter()
                    .map(|s| stable_demangled(&s.raw_name))
                    .collect(),
            },
        );
    }
    let mut unreferenced_data = Vec::new();
    for (&(oi, si), entries) in &ctx.data_entries {
        for (k, e) in entries.iter().enumerate() {
            if !emitted.contains_key(&(oi, si, k)) {
                unreferenced_data.push(e.name.clone());
            }
        }
    }

    // 6. Synthesized block symbols, then exports.
    for (&(oi, sec, off), n) in &ctx.synth {
        symbols.push((n.clone(), ctx.text_off[&(oi, sec)] + off));
    }
    ensure!(
        symbols.iter().all(|(_, off)| off % 4 == 0),
        "library {name}: misaligned block symbol"
    );
    for e in exports {
        let Some((n, raw)) = block_raw.iter().find(|(n, raw)| *raw == e || *n == e) else {
            bail!("export {e} of {name} is not a function defined in its text");
        };
        ensure!(n == e, "export {e} of {name} is mangled (block name {n})");
        let &(oi, si) = ctx
            .globals
            .get(raw)
            .with_context(|| format!("export {e} is not global"))?;
        ensure!(
            objs[oi].symbols[si].kind == SymKind::Func,
            "export {e} of {name} is not STT_FUNC"
        );
    }
    let externs: Vec<String> = externs.into_iter().collect();
    let weak_refs = weak_undef_refs(objs, &externs);
    for x in &externs {
        ensure!(
            !symbols.iter().any(|(n, _)| n == x),
            "extern {x} of {name} collides with a block symbol"
        );
    }
    let (tls, data): (Vec<PData>, Vec<PData>) =
        emitted.into_values().partition(|d| d.is_tls);
    Ok(PLib {
        name: name.to_string(),
        text: PBlock {
            code,
            align,
            symbols,
            relocs,
            externs,
            weak_refs,
        },
        data,
        tls,
        exports: exports.to_vec(),
        text_secs,
        unreferenced_data,
        block_raw,
    })
}

/// `exportSyms` of a multi-block library: `(export, raw .symtab name)` for every export whose raw
/// name differs from its (demangled) block name. Fails unless `rustc_demangle` maps each raw name
/// back to its export name (`{:#}`, as the extractor names block symbols), so the recorded mapping
/// is differentially checked against the compiler's own mangling.
pub(super) fn export_syms(
    name: &str,
    exports: &[String],
    block_raw: &BTreeMap<String, String>,
) -> Result<Vec<(String, String)>> {
    let mut out = Vec::new();
    for e in exports {
        let raw = block_raw
            .get(e)
            .with_context(|| format!("export {e} of {name} has no raw symbol name"))?;
        let dm = demangle_rust_symbol(raw);
        ensure!(
            dm == *e,
            "export {e} of {name}: raw symbol {raw} demangles to {dm}"
        );
        if raw != e {
            out.push((e.clone(), raw.clone()));
        }
    }
    Ok(out)
}

/// The externs (by extern name, as `Ctx::resolve` names them) that the objects reference only as
/// undefined `STB_WEAK` symbols: a static link may leave them undefined (AAELF64 §5.7.11.2).
pub(super) fn weak_undef_refs(objs: &[ObjObject], externs: &[String]) -> Vec<String> {
    let mut weak = BTreeSet::new();
    let mut strong = BTreeSet::new();
    for o in objs {
        for s in &o.symbols {
            if s.sec != SymSection::Undef || s.raw_name.is_empty() {
                continue;
            }
            let n = if s.name.starts_with("examples::") {
                &s.name
            } else {
                &s.raw_name
            };
            if s.bind == SymBind::Weak {
                weak.insert(n.clone());
            } else {
                strong.insert(n.clone());
            }
        }
    }
    externs
        .iter()
        .filter(|x| weak.contains(*x) && !strong.contains(*x))
        .cloned()
        .collect()
}

/// Build the multi-block placed library `name` from `objs`, emitting one [`PBlock`] per
/// `.text.<fn>` input section (or per `STT_FUNC` symbol slice inside a multi-function `.text`
/// section) and per-symbol [`PData`] entries reachable from `exports`.
pub fn build_multi_placed_lib(
    name: &str,
    objs: &[ObjObject],
    exports: &[String],
) -> Result<PMultiLib> {
    Ok(build_multi_placed_lib_bounded(name, objs, exports, &[])?.0)
}

/// [`build_multi_placed_lib`] with an extern boundary: the reachability search from `exports`
/// stops at the functions named in `boundary` (demangled block names or raw `.symtab` names), so
/// their blocks, and everything reachable only through them, are left out. Every relocation to a
/// boundary function then targets its raw `.symtab` name and is an ordinary extern (a hook for
/// `CALL26` / `JUMP26`), resolved from the stock-linked ELF like any other undefined symbol.
///
/// Fails closed when a boundary name is an export, is not a function defined in the library, is
/// listed twice, or shares its block with a reachable symbol that is not itself a boundary name,
/// or when its raw name collides with a symbol that stays in the library. Returns the library and
/// the raw names of the boundary functions, in `boundary` order.
pub fn build_multi_placed_lib_bounded(
    name: &str,
    objs: &[ObjObject],
    exports: &[String],
    boundary: &[String],
) -> Result<(PMultiLib, Vec<String>)> {
    let lib = build_placed_lib_inner(name, objs, exports, true)?;
    // Boundary entries as (block name, raw `.symtab` name).
    let mut bnd: BTreeMap<String, String> = BTreeMap::new();
    let mut bnd_raw: Vec<String> = Vec::new();
    for b in boundary {
        let Some((n, raw)) = lib
            .block_raw
            .iter()
            .find(|(n, raw)| *raw == b || *n == b)
        else {
            bail!("extern_boundary {b} of {name} is not a function defined in its text");
        };
        ensure!(
            !exports.iter().any(|e| e == n || e == raw),
            "extern_boundary {b} of {name} is an export"
        );
        ensure!(
            bnd.insert(n.clone(), raw.clone()).is_none(),
            "extern_boundary {b} of {name} is listed twice"
        );
        bnd_raw.push(raw.clone());
    }
    let mut all_blocks = Vec::new();
    let mut all_text_secs = Vec::new();
    for ts in &lib.text_secs {
        let o = &objs[ts.obj];
        let sec = &o.sections[ts.sec];
        let starts: BTreeSet<u64> = o
            .symbols
            .iter()
            .filter(|s| {
                s.kind == SymKind::Func
                    && s.sec == SymSection::Sec(ts.sec)
                    && !s.raw_name.is_empty()
                    && s.value < ts.size
            })
            .map(|s| s.value)
            .collect();
        let slices: Vec<(u64, u64)> = if starts.len() >= 2 && *starts.first().unwrap() == 0 {
            let pts: Vec<u64> = starts.into_iter().collect();
            pts.iter()
                .enumerate()
                .map(|(idx, &st)| {
                    let end = pts.get(idx + 1).copied().unwrap_or(ts.size);
                    (ts.off + st, ts.off + end)
                })
                .collect()
        } else {
            vec![(ts.off, ts.off + ts.size)]
        };
        for (b_start, b_end) in slices {
            let code = lib.text.code[b_start as usize..b_end as usize].to_vec();
            let rel_off = b_start - ts.off;
            let align = if rel_off == 0 {
                sec.align.max(1)
            } else {
                (1u64 << rel_off.trailing_zeros()).min(sec.align.max(1)).max(4)
            };
            let symbols: Vec<(String, u64)> = lib
                .text
                .symbols
                .iter()
                .filter(|(_, off)| b_start <= *off && *off < b_end)
                .map(|(n, off)| (n.clone(), *off - b_start))
                .collect();
            let mut relocs: Vec<PReloc> = lib
                .text
                .relocs
                .iter()
                .filter(|r| b_start <= r.off && r.off < b_end)
                .map(|r| PReloc {
                    off: r.off - b_start,
                    kind: r.kind,
                    sym: r.sym.clone(),
                    addend: r.addend,
                })
                .collect();
            relocs.sort_by_key(|r| r.off);
            let label = if rel_off == 0 && b_end - b_start == ts.size {
                ts.label.clone()
            } else if let Some((fn_name, _)) = symbols.iter().find(|(_, off)| *off == 0) {
                format!("{} ({fn_name})", ts.label)
            } else {
                format!("{}+{rel_off:#x}", ts.label)
            };
            all_text_secs.push(PTextSec {
                obj: ts.obj,
                sec: ts.sec,
                off: b_start,
                size: b_end - b_start,
                label,
            });
            all_blocks.push(PBlock {
                code,
                align,
                symbols,
                relocs,
                externs: Vec::new(),
                weak_refs: Vec::new(),
            });
        }
    }

    // Prune blocks and data entries to the transitive reachability cone of `exports`.
    let mut sym_to_block: BTreeMap<String, usize> = BTreeMap::new();
    for (bi, b) in all_blocks.iter().enumerate() {
        for (n, _) in &b.symbols {
            sym_to_block.insert(n.clone(), bi);
        }
    }
    let mut sym_to_data: BTreeMap<String, usize> = BTreeMap::new();
    for (di, d) in lib.data.iter().enumerate() {
        sym_to_data.insert(d.sym.clone(), di);
    }
    let mut reach_blocks: BTreeSet<usize> = BTreeSet::new();
    let mut reach_data: BTreeSet<usize> = BTreeSet::new();
    let bnd_blocks: BTreeSet<usize> = bnd.keys().filter_map(|n| sym_to_block.get(n).copied()).collect();
    let mut queue: VecDeque<String> = exports.iter().cloned().collect();
    while let Some(sym) = queue.pop_front() {
        if let Some(&bi) = sym_to_block.get(&sym)
            && bnd_blocks.contains(&bi)
        {
            ensure!(
                bnd.contains_key(&sym),
                "{sym} of {name} is reachable but shares its block with an extern_boundary function"
            );
            continue;
        }
        if let Some(&bi) = sym_to_block.get(&sym)
            && reach_blocks.insert(bi)
        {
            for r in &all_blocks[bi].relocs {
                queue.push_back(r.sym.clone());
            }
        }
        if let Some(&di) = sym_to_data.get(&sym)
            && reach_data.insert(di)
        {
            for r in &lib.data[di].relocs {
                queue.push_back(r.sym.clone());
            }
        }
    }

    let mut blocks = Vec::new();
    let mut split_text_secs = Vec::new();
    for (bi, (b, ts)) in all_blocks.into_iter().zip(all_text_secs).enumerate() {
        if reach_blocks.contains(&bi) {
            blocks.push(b);
            split_text_secs.push(ts);
        }
    }
    let mut data = Vec::new();
    let mut unreferenced_data = lib.unreferenced_data;
    for (di, d) in lib.data.into_iter().enumerate() {
        if reach_data.contains(&di) {
            data.push(d);
        } else {
            unreferenced_data.push(d.sym);
        }
    }
    // Relocations to a boundary function target its raw `.symtab` name, which must not name
    // anything that stays in the library.
    if !bnd.is_empty() {
        let kept: BTreeSet<&str> = blocks
            .iter()
            .flat_map(|b| b.symbols.iter().map(|(n, _)| n.as_str()))
            .chain(data.iter().map(|d| d.sym.as_str()))
            .collect();
        for (n, raw) in &bnd {
            ensure!(
                !kept.contains(raw.as_str()),
                "extern_boundary {n} of {name}: raw name {raw} collides with a library symbol"
            );
        }
        // Only direct branches can leave the library through a hook; any other reference to a
        // boundary function (an address taken in code or data) has no extern meaning.
        for r in blocks.iter().flat_map(|b| b.relocs.iter()) {
            ensure!(
                !bnd.contains_key(&r.sym) || matches!(r.kind, RelocKind::Call26 | RelocKind::Jump26),
                "extern_boundary {} of {name} is referenced by a non-branch relocation",
                r.sym
            );
        }
        for d in &data {
            if let Some(r) = d.relocs.iter().find(|r| bnd.contains_key(&r.sym)) {
                bail!("extern_boundary {} of {name} is referenced from data {}", r.sym, d.sym);
            }
        }
        let rename = |s: &mut String| {
            if let Some(raw) = bnd.get(s.as_str()) {
                *s = raw.clone();
            }
        };
        for b in &mut blocks {
            b.relocs.iter_mut().for_each(|r| rename(&mut r.sym));
        }
        for d in &mut data {
            d.relocs.iter_mut().for_each(|r| rename(&mut r.sym));
        }
    }

    // Every block shares the library-wide external branch target list (excluding internal block
    // symbols) so `MultiPlacedLib.blockProgram mpl i H` exposes identical hook tables across blocks.
    let all_block_syms: BTreeSet<String> = blocks
        .iter()
        .flat_map(|b| b.symbols.iter().map(|(n, _)| n.clone()))
        .collect();
    let lib_externs: Vec<String> = blocks
        .iter()
        .flat_map(|b| b.relocs.iter())
        .filter(|r| matches!(r.kind, RelocKind::Call26 | RelocKind::Jump26))
        .filter(|r| !all_block_syms.contains(&r.sym))
        .map(|r| r.sym.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let lib_weak_refs: Vec<String> = lib
        .text
        .weak_refs
        .iter()
        .filter(|w| lib_externs.contains(w))
        .cloned()
        .collect();
    for b in &mut blocks {
        b.externs = lib_externs.clone();
        b.weak_refs = lib_weak_refs.clone();
    }
    let block_raw: BTreeMap<String, String> = lib
        .block_raw
        .into_iter()
        .filter(|(n, _)| all_block_syms.contains(n))
        .collect();
    let export_syms = export_syms(&lib.name, &lib.exports, &block_raw)?;

    let mlib = PMultiLib {
        name: lib.name,
        blocks,
        data,
        tls: lib.tls,
        exports: lib.exports,
        text_secs: split_text_secs,
        unreferenced_data,
        block_raw,
        export_syms,
    };
    Ok((mlib, bnd_raw))
}
