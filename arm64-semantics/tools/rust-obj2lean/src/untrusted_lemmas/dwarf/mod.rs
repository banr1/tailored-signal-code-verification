// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! DWARF Reader for Relocatable AArch64 Objects (`untrusted_lemmas::dwarf`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (read-only advisor: DWARF never reaches a trusted `Obj`
//!   definition; it only annotates `*Index.json`, `symexec` output and the `layout`
//!   subcommand. A bug here can only produce a wrong *hint*).
//! - **Purpose:** Reads `.debug_info` / `.debug_line` / `.debug_loc(lists)` / `.debug_ranges`
//!   of one relocatable ELF object with `gimli`, applying its `.rela.debug_*` relocations
//!   (addresses in an allocated section `S` become the synthetic address `(S << 32) + offset`, so
//!   every function's PCs stay section-relative), and extracts:
//!   1. function signatures (`DW_TAG_subprogram` + `DW_TAG_formal_parameter`: names, types,
//!      sizes, entry locations, optimized-out parameters),
//!   2. struct/union layouts (`DW_TAG_member`: byte/bit offsets and sizes, nested aggregates),
//!   3. function-relative line tables with inlined-call chains (`DW_TAG_inlined_subroutine`),
//!   4. variable location lists (`DW_AT_location`, `.debug_loc` / `.debug_loclists`).
//!
//! # Key Types & Functions
//! - [`read_elf_dwarf`] → [`DwarfObject`] ([`FoundFunction`]s + layouts keyed by name).
//! - [`reachable_layouts`]: layouts referenced by a set of functions (for `*Index.json`).
//! - Submodules: [`companion`] (the `-g` companion build of C objects mapped onto the trusted
//!   `-g0` objects), [`cli`] (`layout` subcommand).
//!
//! # When to Read This File
//! - Read this file when a DWARF construct is rendered wrongly (types, locations, bitfields);
//!   read `companion.rs` for how DWARF is attached to the exported image.

pub mod cli;
pub mod companion;
#[cfg(test)]
mod tests;
#[cfg(test)]
pub(crate) use tests::SAMPLE_C;

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use anyhow::{Context, Result, anyhow};
use gimli::{AttributeValue, DwAt, DwTag, Reader, constants as dw};
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SectionIndex, SymbolSection};

pub use super::index_schema::{
    DwarfFunctionInfo, DwarfLineEntry, DwarfMember, DwarfParam, DwarfTypeLayout, DwarfVarLocation,
    DwarfVariable,
};

/// Synthetic address of `offset` in allocated ELF section `sec` (`sec >= 1`, so never 0).
fn synth(sec: usize, offset: u64) -> u64 {
    ((sec as u64) << 32) | (offset & 0xffff_ffff)
}

fn synth_section(addr: u64) -> usize {
    (addr >> 32) as usize
}

/// Relocated values of one debug section, keyed by the offset of the relocated field.
#[derive(Clone, Debug, Default)]
struct RelocMap(Rc<HashMap<usize, u64>>);

impl gimli::read::Relocate<usize> for RelocMap {
    fn relocate_address(&self, offset: usize, value: u64) -> gimli::Result<u64> {
        Ok(self.0.get(&offset).copied().unwrap_or(value))
    }

    fn relocate_offset(&self, offset: usize, value: usize) -> gimli::Result<usize> {
        Ok(self.0.get(&offset).map_or(value, |v| *v as usize))
    }
}

type Slice<'a> = gimli::EndianSlice<'a, gimli::RunTimeEndian>;
type R<'a> = gimli::RelocateReader<Slice<'a>, RelocMap>;

/// A function found in DWARF, located by its ELF section and offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundFunction {
    /// Name of the ELF section holding the function (e.g. `.text.sum_list`).
    pub section: String,
    /// Offset of the function's entry in `section`.
    pub section_offset: u64,
    /// Size of the function's first range in bytes.
    pub size: u64,
    /// Raw (mangled) name of the `STT_FUNC` symbol at that address, if any.
    pub symbol: Option<String>,
    pub info: DwarfFunctionInfo,
}

/// Everything extracted from one object's DWARF.
#[derive(Clone, Debug, Default)]
pub struct DwarfObject {
    pub functions: Vec<FoundFunction>,
    /// Struct/union layouts keyed by [`DwarfTypeLayout::name`].
    pub layouts: BTreeMap<String, DwarfTypeLayout>,
    /// Every source file named by a line table (headers included), deduplicated.
    pub files: BTreeSet<String>,
}

impl DwarfObject {
    /// Merge `other` into `self` (first definition of a layout key wins).
    pub fn merge(&mut self, other: DwarfObject) {
        self.functions.extend(other.functions);
        for (k, v) in other.layouts {
            self.layouts.entry(k).or_insert(v);
        }
        self.files.extend(other.files);
    }
}

fn is_alloc(sec: &object::Section<'_, '_>) -> bool {
    match sec.flags() {
        object::SectionFlags::Elf { sh_flags } => sh_flags & u64::from(object::elf::SHF_ALLOC) != 0,
        _ => false,
    }
}

/// Read the DWARF of the relocatable ELF object `elf` (empty result if it has none).
pub fn read_elf_dwarf(elf: &[u8]) -> Result<DwarfObject> {
    let file = object::File::parse(elf).context("not an object file")?;
    let endian = if file.is_little_endian() {
        gimli::RunTimeEndian::Little
    } else {
        gimli::RunTimeEndian::Big
    };
    // Section data and relocations of every `.debug_*` section.
    let mut data: HashMap<String, (Cow<'_, [u8]>, RelocMap)> = HashMap::new();
    for sec in file.sections() {
        let Ok(name) = sec.name() else { continue };
        if !name.starts_with(".debug_") {
            continue;
        }
        let bytes = sec.uncompressed_data().unwrap_or(Cow::Borrowed(&[]));
        let mut relocs = HashMap::new();
        for (off, rel) in sec.relocations() {
            let (target_sec, sym_value) = match rel.target() {
                RelocationTarget::Symbol(si) => {
                    let Ok(sym) = file.symbol_by_index(si) else {
                        continue;
                    };
                    match sym.section() {
                        SymbolSection::Section(s) => (Some(s), sym.address()),
                        _ => (None, sym.address()),
                    }
                }
                RelocationTarget::Section(s) => (Some(s), 0),
                _ => continue,
            };
            let base = match target_sec.and_then(|s| file.section_by_index(s).ok()) {
                Some(t) if is_alloc(&t) => synth(t.index().0, sym_value),
                _ => sym_value,
            };
            let mut value = base.wrapping_add(rel.addend() as u64);
            if rel.has_implicit_addend() {
                let o = off as usize;
                let n = (rel.size() / 8) as usize;
                if let Some(b) = bytes.get(o..o + n) {
                    let mut buf = [0u8; 8];
                    buf[..n].copy_from_slice(b);
                    value = value.wrapping_add(u64::from_le_bytes(buf));
                }
            }
            relocs.insert(off as usize, value);
        }
        data.insert(name.to_string(), (bytes, RelocMap(Rc::new(relocs))));
    }
    if !data.contains_key(".debug_info") {
        return Ok(DwarfObject::default());
    }
    let dwarf = gimli::Dwarf::load(|id| -> gimli::Result<R<'_>> {
        let (bytes, rel) = data
            .get(id.name())
            .map(|(b, r)| (b.as_ref(), r.clone()))
            .unwrap_or((&[][..], RelocMap::default()));
        Ok(gimli::RelocateReader::new(
            gimli::EndianSlice::new(bytes, endian),
            rel,
        ))
    })
    .map_err(|e| anyhow!("cannot load DWARF: {e}"))?;

    // Function symbols by (section index, offset).
    let mut func_syms: HashMap<(usize, u64), String> = HashMap::new();
    for sym in file.symbols() {
        if sym.kind() != object::SymbolKind::Text {
            continue;
        }
        if let (SymbolSection::Section(s), Ok(name)) = (sym.section(), sym.name()) {
            func_syms
                .entry((s.0, sym.address()))
                .or_insert_with(|| name.to_string());
        }
    }
    let section_name = |idx: usize| -> String {
        file.section_by_index(SectionIndex(idx))
            .ok()
            .and_then(|s| s.name().ok().map(str::to_string))
            .unwrap_or_default()
    };

    let mut out = DwarfObject::default();
    let mut units = dwarf.units();
    while let Some(header) = units
        .next()
        .map_err(|e| anyhow!("DWARF unit header: {e}"))?
    {
        let unit = dwarf.unit(header).map_err(|e| anyhow!("DWARF unit: {e}"))?;
        let cu = UnitCtx::new(&dwarf, &unit).map_err(|e| anyhow!("DWARF DIEs: {e}"))?;
        out.files.extend(cu.files.values().cloned());
        cu.collect_layouts(&mut out.layouts);
        for f in cu.collect_functions() {
            let sec = synth_section(f.low);
            out.functions.push(FoundFunction {
                section: section_name(sec),
                section_offset: f.low & 0xffff_ffff,
                size: f.high.saturating_sub(f.low),
                symbol: func_syms.get(&(sec, f.low & 0xffff_ffff)).cloned(),
                info: f.info,
            });
        }
    }
    Ok(out)
}

/// One DIE of a unit, flattened (attributes cloned, tree as parent/children indices).
struct Die<Rd: Reader> {
    tag: DwTag,
    parent: Option<usize>,
    children: Vec<usize>,
    attrs: Vec<(DwAt, AttributeValue<Rd>)>,
}

/// A subprogram with code: synthetic `[low, high)` (first range) and its DWARF view.
struct FnFound {
    low: u64,
    high: u64,
    info: DwarfFunctionInfo,
}

/// Inlined subroutine instance within a function (for line-row chains).
struct Inlined {
    ranges: Vec<(u64, u64)>,
    depth: usize,
    text: String,
}

struct UnitCtx<'d, Rd: Reader<Offset = usize>> {
    dwarf: &'d gimli::Dwarf<Rd>,
    unit: &'d gimli::Unit<Rd>,
    dies: Vec<Die<Rd>>,
    by_off: HashMap<usize, usize>,
    language: String,
    is_c: bool,
    /// File index → path (as numbered by `DW_AT_decl_file` / line rows).
    files: BTreeMap<u64, String>,
    /// Line rows `(synthetic address, file index, line)`, sorted by address.
    rows: Vec<(u64, u64, u64)>,
}

const MAX_DEPTH: usize = 12;

impl<'d, Rd: Reader<Offset = usize>> UnitCtx<'d, Rd> {
    fn new(dwarf: &'d gimli::Dwarf<Rd>, unit: &'d gimli::Unit<Rd>) -> gimli::Result<Self> {
        let mut dies: Vec<Die<Rd>> = Vec::new();
        let mut by_off = HashMap::new();
        let mut stack: Vec<usize> = Vec::new();
        let mut depth: isize = 0;
        let mut cursor = unit.entries();
        while let Some((delta, entry)) = cursor.next_dfs()? {
            depth += delta;
            stack.truncate(depth.max(0) as usize);
            let parent = stack.last().copied();
            let idx = dies.len();
            let mut attrs = Vec::new();
            let mut it = entry.attrs();
            while let Some(a) = it.next()? {
                attrs.push((a.name(), a.value()));
            }
            dies.push(Die {
                tag: entry.tag(),
                parent,
                children: Vec::new(),
                attrs,
            });
            if let Some(p) = parent {
                dies[p].children.push(idx);
            }
            by_off.insert(entry.offset().0, idx);
            stack.push(idx);
        }
        let mut ctx = UnitCtx {
            dwarf,
            unit,
            dies,
            by_off,
            language: String::new(),
            is_c: true,
            files: BTreeMap::new(),
            rows: Vec::new(),
        };
        if let Some(AttributeValue::Language(l)) = ctx.attr(0, dw::DW_AT_language) {
            let s = l.static_string().unwrap_or("DW_LANG_unknown");
            ctx.language = s.trim_start_matches("DW_LANG_").to_string();
            ctx.is_c = !matches!(l, dw::DW_LANG_Rust);
        }
        if let Some(program) = unit.line_program.clone() {
            let header = program.header().clone();
            let n = header.file_names().len() as u64;
            let first = if header.version() >= 5 { 0 } else { 1 };
            for i in first..first + n {
                if let Some(f) = header.file(i) {
                    ctx.files.insert(i, ctx.render_file(&header, f));
                }
            }
            let mut rows = program.rows();
            while let Some((_, row)) = rows.next_row()? {
                if row.end_sequence() {
                    continue;
                }
                if let Some(line) = row.line() {
                    ctx.rows.push((row.address(), row.file_index(), line.get()));
                }
            }
            ctx.rows.sort_by_key(|r| r.0);
        }
        Ok(ctx)
    }

    fn string(&self, v: AttributeValue<Rd>) -> Option<String> {
        let r = self.dwarf.attr_string(self.unit, v).ok()?;
        r.to_string_lossy().ok().map(|s| s.into_owned())
    }

    fn render_file(
        &self,
        header: &gimli::LineProgramHeader<Rd>,
        file: &gimli::FileEntry<Rd>,
    ) -> String {
        let name = self.string(file.path_name()).unwrap_or_default();
        if name.starts_with('/') {
            return name;
        }
        let mut dir = file
            .directory(header)
            .and_then(|d| self.string(d))
            .unwrap_or_default();
        if !dir.starts_with('/')
            && let Some(cd) = self
                .unit
                .comp_dir
                .as_ref()
                .and_then(|c| c.to_string_lossy().ok())
        {
            dir = join_path(&cd, &dir);
        }
        join_path(&dir, &name)
    }

    fn attr(&self, idx: usize, at: DwAt) -> Option<AttributeValue<Rd>> {
        self.dies[idx]
            .attrs
            .iter()
            .find(|(n, _)| *n == at)
            .map(|(_, v)| v.clone())
    }

    /// Target DIE index of a same-unit reference attribute.
    fn ref_attr(&self, idx: usize, at: DwAt) -> Option<usize> {
        match self.attr(idx, at)? {
            AttributeValue::UnitRef(o) => self.by_off.get(&o.0).copied(),
            _ => None,
        }
    }

    /// `at` on `idx`, else on its `DW_AT_abstract_origin` / `DW_AT_specification` chain.
    fn attr_follow(&self, idx: usize, at: DwAt) -> Option<AttributeValue<Rd>> {
        let mut cur = idx;
        for _ in 0..4 {
            if let Some(v) = self.attr(cur, at) {
                return Some(v);
            }
            cur = self
                .ref_attr(cur, dw::DW_AT_abstract_origin)
                .or_else(|| self.ref_attr(cur, dw::DW_AT_specification))?;
        }
        None
    }

    fn name(&self, idx: usize) -> Option<String> {
        self.attr_follow(idx, dw::DW_AT_name)
            .and_then(|v| self.string(v))
    }

    fn udata(&self, idx: usize, at: DwAt) -> Option<u64> {
        self.attr_follow(idx, at).and_then(|v| v.udata_value())
    }

    fn decl(&self, idx: usize) -> (String, u64) {
        let file = match self.attr_follow(idx, dw::DW_AT_decl_file) {
            Some(AttributeValue::FileIndex(i)) => self.files.get(&i).cloned().unwrap_or_default(),
            Some(v) => v
                .udata_value()
                .and_then(|i| self.files.get(&i).cloned())
                .unwrap_or_default(),
            None => String::new(),
        };
        (file, self.udata(idx, dw::DW_AT_decl_line).unwrap_or(0))
    }

    fn type_of(&self, idx: usize) -> Option<usize> {
        match self.attr_follow(idx, dw::DW_AT_type)? {
            AttributeValue::UnitRef(o) => self.by_off.get(&o.0).copied(),
            _ => None,
        }
    }

    /// Rust: `a::b::Name` from enclosing `DW_TAG_namespace` DIEs.
    fn qualified(&self, idx: usize, name: &str) -> String {
        if self.is_c {
            return name.to_string();
        }
        let mut parts = vec![name.to_string()];
        let mut cur = self.dies[idx].parent;
        while let Some(p) = cur {
            let tag = self.dies[p].tag;
            if (tag == dw::DW_TAG_namespace
                || tag == dw::DW_TAG_structure_type
                || tag == dw::DW_TAG_union_type)
                && let Some(n) = self.name(p)
            {
                parts.push(n);
            }
            cur = self.dies[p].parent;
        }
        parts.reverse();
        parts.join("::")
    }

    /// Layout key of an aggregate DIE (`struct foo`, `union <anon@f.c:3>`, Rust path).
    fn aggregate_key(&self, idx: usize) -> String {
        let kind = match self.dies[idx].tag {
            dw::DW_TAG_union_type => "union",
            dw::DW_TAG_class_type => "class",
            dw::DW_TAG_enumeration_type => "enum",
            _ => "struct",
        };
        match self.name(idx) {
            Some(n) if self.is_c => format!("{kind} {n}"),
            Some(n) => self.qualified(idx, &n),
            None => {
                let (f, l) = self.decl(idx);
                let base = f.rsplit('/').next().unwrap_or(&f).to_string();
                format!("{kind} <anon@{base}:{l}>")
            }
        }
    }

    fn is_aggregate(tag: DwTag) -> bool {
        matches!(
            tag,
            dw::DW_TAG_structure_type | dw::DW_TAG_union_type | dw::DW_TAG_class_type
        )
    }

    /// Strip typedefs and cv-qualifiers.
    fn strip(&self, mut idx: usize) -> usize {
        for _ in 0..MAX_DEPTH {
            match self.dies[idx].tag {
                dw::DW_TAG_typedef
                | dw::DW_TAG_const_type
                | dw::DW_TAG_volatile_type
                | dw::DW_TAG_restrict_type
                | dw::DW_TAG_atomic_type => match self.type_of(idx) {
                    Some(t) => idx = t,
                    None => return idx,
                },
                _ => return idx,
            }
        }
        idx
    }

    /// Layout key of the aggregate type `ty` resolves to (through typedefs / cv).
    fn aggregate_of(&self, ty: usize) -> Option<String> {
        let s = self.strip(ty);
        Self::is_aggregate(self.dies[s].tag).then(|| self.aggregate_key(s))
    }

    /// Layout key of the aggregate a pointer type `ty` points to.
    fn pointee_of(&self, ty: usize) -> Option<String> {
        let s = self.strip(ty);
        if !matches!(
            self.dies[s].tag,
            dw::DW_TAG_pointer_type | dw::DW_TAG_reference_type | dw::DW_TAG_rvalue_reference_type
        ) {
            return None;
        }
        self.aggregate_of(self.type_of(s)?)
    }

    /// Render a type as C (or Rust, from its DWARF names).
    fn type_name(&self, ty: Option<usize>, depth: usize) -> String {
        let Some(idx) = ty else {
            return "void".into();
        };
        if depth > MAX_DEPTH {
            return "...".into();
        }
        let die = &self.dies[idx];
        let inner = || self.type_name(self.type_of(idx), depth + 1);
        match die.tag {
            dw::DW_TAG_base_type | dw::DW_TAG_typedef | dw::DW_TAG_unspecified_type => {
                self.name(idx).unwrap_or_else(|| "?".into())
            }
            t if Self::is_aggregate(t) || t == dw::DW_TAG_enumeration_type => {
                self.aggregate_key(idx)
            }
            dw::DW_TAG_const_type => format!("const {}", inner()),
            dw::DW_TAG_volatile_type => format!("volatile {}", inner()),
            dw::DW_TAG_atomic_type => format!("_Atomic {}", inner()),
            dw::DW_TAG_restrict_type => format!("{} restrict", inner()),
            dw::DW_TAG_pointer_type
            | dw::DW_TAG_reference_type
            | dw::DW_TAG_rvalue_reference_type => {
                if let Some(n) = self.name(idx) {
                    return n;
                }
                match self.type_of(idx) {
                    Some(t) if self.dies[t].tag == dw::DW_TAG_subroutine_type => {
                        self.fn_type_name(t, depth + 1, "(*)")
                    }
                    t => format!("{} *", self.type_name(t, depth + 1)),
                }
            }
            dw::DW_TAG_array_type => {
                let mut dims = String::new();
                for &c in &die.children {
                    if self.dies[c].tag != dw::DW_TAG_subrange_type {
                        continue;
                    }
                    match self.array_count(c) {
                        Some(n) => dims.push_str(&format!("[{n}]")),
                        None => dims.push_str("[]"),
                    }
                }
                format!("{}{dims}", inner())
            }
            dw::DW_TAG_subroutine_type => self.fn_type_name(idx, depth, ""),
            _ => self.name(idx).unwrap_or_else(|| format!("<{}>", die.tag)),
        }
    }

    fn fn_type_name(&self, idx: usize, depth: usize, declarator: &str) -> String {
        let args: Vec<String> = self.dies[idx]
            .children
            .iter()
            .filter(|&&c| self.dies[c].tag == dw::DW_TAG_formal_parameter)
            .map(|&c| self.type_name(self.type_of(c), depth + 1))
            .collect();
        format!(
            "{} {declarator}({})",
            self.type_name(self.type_of(idx), depth + 1),
            args.join(", ")
        )
    }

    fn array_count(&self, subrange: usize) -> Option<u64> {
        if let Some(n) = self.udata(subrange, dw::DW_AT_count) {
            return Some(n);
        }
        let ub = self.attr(subrange, dw::DW_AT_upper_bound)?;
        let ub = ub
            .udata_value()
            .or_else(|| ub.sdata_value().map(|s| s as u64))?;
        // An upper bound of -1 encodes a flexible array member.
        (ub != u64::MAX).then(|| ub + 1 - self.udata(subrange, dw::DW_AT_lower_bound).unwrap_or(0))
    }

    fn type_size(&self, ty: Option<usize>, depth: usize) -> Option<u64> {
        let idx = ty?;
        if depth > MAX_DEPTH {
            return None;
        }
        if let Some(n) = self.udata(idx, dw::DW_AT_byte_size) {
            return Some(n);
        }
        match self.dies[idx].tag {
            dw::DW_TAG_pointer_type
            | dw::DW_TAG_reference_type
            | dw::DW_TAG_rvalue_reference_type => Some(8),
            dw::DW_TAG_array_type => {
                let mut n = self.type_size(self.type_of(idx), depth + 1)?;
                for &c in &self.dies[idx].children {
                    if self.dies[c].tag == dw::DW_TAG_subrange_type {
                        n = n.saturating_mul(self.array_count(c).unwrap_or(0));
                    }
                }
                Some(n)
            }
            dw::DW_TAG_typedef
            | dw::DW_TAG_const_type
            | dw::DW_TAG_volatile_type
            | dw::DW_TAG_restrict_type
            | dw::DW_TAG_atomic_type => self.type_size(self.type_of(idx), depth + 1),
            _ => None,
        }
    }

    fn type_align(&self, ty: Option<usize>, depth: usize) -> u64 {
        let Some(idx) = ty else { return 1 };
        if depth > MAX_DEPTH {
            return 1;
        }
        if let Some(a) = self.udata(idx, dw::DW_AT_alignment) {
            return a.max(1);
        }
        let s = self.strip(idx);
        if s != idx {
            return self.type_align(Some(s), depth + 1);
        }
        match self.dies[s].tag {
            t if Self::is_aggregate(t) => self.dies[s]
                .children
                .iter()
                .filter(|&&c| self.dies[c].tag == dw::DW_TAG_member)
                .map(|&c| self.type_align(self.type_of(c), depth + 1))
                .max()
                .unwrap_or(1),
            dw::DW_TAG_array_type => self.type_align(self.type_of(s), depth + 1),
            _ => self.type_size(Some(s), depth + 1).unwrap_or(1).clamp(1, 16),
        }
    }

    fn collect_layouts(&self, out: &mut BTreeMap<String, DwarfTypeLayout>) {
        let mut typedefs: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (i, d) in self.dies.iter().enumerate() {
            if d.tag == dw::DW_TAG_typedef
                && let (Some(n), Some(t)) = (self.name(i), self.type_of(i))
                && let Some(k) = self.aggregate_of(t)
            {
                typedefs.entry(k).or_default().push(n);
            }
        }
        for (i, d) in self.dies.iter().enumerate() {
            if !Self::is_aggregate(d.tag) || self.attr(i, dw::DW_AT_declaration).is_some() {
                continue;
            }
            let Some(byte_size) = self.udata(i, dw::DW_AT_byte_size) else {
                continue;
            };
            let key = self.aggregate_key(i);
            if out.contains_key(&key) {
                continue;
            }
            let (decl_file, decl_line) = self.decl(i);
            let mut tds = typedefs.get(&key).cloned().unwrap_or_default();
            tds.sort();
            tds.dedup();
            out.insert(
                key.clone(),
                DwarfTypeLayout {
                    name: key,
                    kind: match d.tag {
                        dw::DW_TAG_union_type => "union".into(),
                        dw::DW_TAG_class_type => "class".into(),
                        _ => "struct".into(),
                    },
                    byte_size,
                    alignment: self.type_align(Some(i), 0),
                    decl_file,
                    decl_line,
                    typedefs: tds,
                    members: self.members(i),
                },
            );
        }
    }

    fn members(&self, agg: usize) -> Vec<DwarfMember> {
        let mut out = Vec::new();
        for &c in &self.dies[agg].children {
            if self.dies[c].tag != dw::DW_TAG_member || self.attr(c, dw::DW_AT_external).is_some() {
                continue;
            }
            let ty = self.type_of(c);
            let type_size = self.type_size(ty, 0).unwrap_or(0);
            let loc = match self.attr(c, dw::DW_AT_data_member_location) {
                Some(AttributeValue::Exprloc(e)) => plus_uconst(e, self.unit.encoding()),
                Some(v) => v.udata_value(),
                None => None,
            };
            let bit_size = self.udata(c, dw::DW_AT_bit_size);
            let (byte_offset, byte_size, bit_offset) = match bit_size {
                Some(bits) => {
                    // DWARF 4+: `DW_AT_data_bit_offset` from the start of the aggregate;
                    // DWARF 2/3: `DW_AT_bit_offset` counted from the MSB of the storage unit.
                    let abs = if let Some(dbo) = self.udata(c, dw::DW_AT_data_bit_offset) {
                        dbo
                    } else {
                        let storage = self.udata(c, dw::DW_AT_byte_size).unwrap_or(type_size);
                        let msb = self.udata(c, dw::DW_AT_bit_offset).unwrap_or(0);
                        loc.unwrap_or(0) * 8 + (storage * 8).saturating_sub(msb + bits)
                    };
                    let bo = abs % 8;
                    (abs / 8, (bo + bits).div_ceil(8), Some(bo))
                }
                None => (loc.unwrap_or(0), type_size, None),
            };
            let stripped = ty.map(|t| self.strip(t));
            let (array_elem_size, array_elem_aggregate) = match stripped {
                Some(s) if self.dies[s].tag == dw::DW_TAG_array_type => {
                    let elem = self.type_of(s);
                    (
                        self.type_size(elem, 0),
                        elem.and_then(|e| self.aggregate_of(e)),
                    )
                }
                _ => (None, None),
            };
            out.push(DwarfMember {
                name: self.name(c).unwrap_or_default(),
                byte_offset,
                byte_size,
                bit_offset,
                bit_size,
                c_type: self.type_name(ty, 0),
                aggregate: ty.and_then(|t| self.aggregate_of(t)),
                pointee: ty.and_then(|t| self.pointee_of(t)),
                array_elem_size,
                array_elem_aggregate,
            });
        }
        out
    }

    /// Synthetic `[low, high)` ranges of a DIE with code.
    fn ranges(&self, idx: usize) -> Vec<(u64, u64)> {
        let mut out = Vec::new();
        if let Some(lo) = self.attr(idx, dw::DW_AT_low_pc)
            && let Ok(Some(low)) = self.dwarf.attr_address(self.unit, lo)
        {
            let high = match self.attr(idx, dw::DW_AT_high_pc) {
                Some(AttributeValue::Udata(n)) => Some(low + n),
                Some(v) => self.dwarf.attr_address(self.unit, v).ok().flatten(),
                None => None,
            };
            if let Some(h) = high {
                out.push((low, h));
            }
        }
        if let Some(r) = self.attr(idx, dw::DW_AT_ranges)
            && let Ok(Some(mut it)) = self.dwarf.attr_ranges(self.unit, r)
        {
            while let Ok(Some(range)) = it.next() {
                if range.end > range.begin {
                    out.push((range.begin, range.end));
                }
            }
        }
        out
    }

    /// Location list of a variable as function-relative ranges within `[low, high)`.
    fn locations(
        &self,
        idx: usize,
        low: u64,
        high: u64,
        frame_base: &str,
    ) -> Option<Vec<DwarfVarLocation>> {
        let v = self.attr(idx, dw::DW_AT_location)?;
        let enc = self.unit.encoding();
        let mut out = Vec::new();
        if let AttributeValue::Exprloc(e) = &v {
            out.push(DwarfVarLocation {
                start: 0,
                end: high - low,
                location: render_expr(e.clone(), enc, frame_base),
            });
            return Some(out);
        }
        let mut it = self.dwarf.attr_locations(self.unit, v).ok()??;
        while let Ok(Some(entry)) = it.next() {
            let (b, e) = (entry.range.begin, entry.range.end);
            if synth_section(b) != synth_section(low) || e <= low || b >= high {
                continue;
            }
            out.push(DwarfVarLocation {
                start: b.max(low) - low,
                end: e.min(high) - low,
                location: render_expr(entry.data, enc, frame_base),
            });
        }
        Some(out)
    }

    fn collect_functions(&self) -> Vec<FnFound> {
        let mut out = Vec::new();
        for (i, d) in self.dies.iter().enumerate() {
            if d.tag != dw::DW_TAG_subprogram {
                continue;
            }
            let ranges = self.ranges(i);
            let Some(&(low, high)) = ranges.iter().min_by_key(|r| r.0) else {
                continue;
            };
            out.push(FnFound {
                low,
                high,
                info: self.function_info(i, low, high),
            });
        }
        out
    }

    fn frame_base(&self, idx: usize) -> String {
        match self.attr(idx, dw::DW_AT_frame_base) {
            Some(AttributeValue::Exprloc(e)) => render_expr(e, self.unit.encoding(), "fb"),
            _ => "fb".into(),
        }
    }

    fn function_info(&self, f: usize, low: u64, high: u64) -> DwarfFunctionInfo {
        let (decl_file, decl_line) = self.decl(f);
        let fb = self.frame_base(f);
        let mut params = Vec::new();
        let mut variables = Vec::new();
        let mut inlined: Vec<Inlined> = Vec::new();
        for &c in &self.dies[f].children {
            if self.dies[c].tag != dw::DW_TAG_formal_parameter {
                continue;
            }
            let ty = self.type_of(c);
            let locs = self.locations(c, low, high, &fb);
            let entry_location = locs.as_ref().and_then(|ls| {
                ls.iter()
                    .find(|l| l.start == 0 && l.end > 0)
                    .map(|l| l.location.clone())
            });
            params.push(DwarfParam {
                name: self.name(c).unwrap_or_default(),
                c_type: self.type_name(ty, 0),
                byte_size: self.type_size(ty, 0),
                entry_location,
                optimized_out: locs.as_ref().is_none_or(Vec::is_empty),
                pointee: ty.and_then(|t| self.pointee_of(t)),
            });
        }
        self.walk_scope(f, low, high, &fb, "", 0, &mut variables, &mut inlined);
        DwarfFunctionInfo {
            name: self.name(f).unwrap_or_default(),
            decl_file,
            decl_line,
            return_type: self.type_name(self.type_of(f), 0),
            params,
            external: self.attr_follow(f, dw::DW_AT_external).is_some(),
            language: self.language.clone(),
            lines: self.line_rows(low, high, &inlined),
            variables,
            exact: false,
        }
    }

    /// Collect variables of a scope (function, lexical block, inlined subroutine).
    #[allow(clippy::too_many_arguments)]
    fn walk_scope(
        &self,
        scope: usize,
        low: u64,
        high: u64,
        fb: &str,
        inlined_from: &str,
        depth: usize,
        vars: &mut Vec<DwarfVariable>,
        inlined: &mut Vec<Inlined>,
    ) {
        if depth > MAX_DEPTH {
            return;
        }
        for &c in &self.dies[scope].children {
            match self.dies[c].tag {
                dw::DW_TAG_formal_parameter | dw::DW_TAG_variable => {
                    let Some(locations) = self.locations(c, low, high, fb) else {
                        continue;
                    };
                    if locations.is_empty() {
                        continue;
                    }
                    let kind = if self.dies[c].tag == dw::DW_TAG_formal_parameter {
                        "param"
                    } else {
                        "local"
                    };
                    vars.push(DwarfVariable {
                        name: self.name(c).unwrap_or_default(),
                        c_type: self.type_name(self.type_of(c), 0),
                        kind: kind.into(),
                        inlined_from: inlined_from.to_string(),
                        locations,
                    });
                }
                dw::DW_TAG_lexical_block => {
                    self.walk_scope(c, low, high, fb, inlined_from, depth + 1, vars, inlined);
                }
                dw::DW_TAG_inlined_subroutine => {
                    let callee = self.name(c).unwrap_or_else(|| "?".into());
                    let call_file = match self.attr(c, dw::DW_AT_call_file) {
                        Some(AttributeValue::FileIndex(i)) => self.files.get(&i).cloned(),
                        Some(v) => v.udata_value().and_then(|i| self.files.get(&i).cloned()),
                        None => None,
                    }
                    .unwrap_or_default();
                    let call_line = self.udata(c, dw::DW_AT_call_line).unwrap_or(0);
                    inlined.push(Inlined {
                        ranges: self.ranges(c),
                        depth,
                        text: format!("{callee} ({call_file}:{call_line})"),
                    });
                    self.walk_scope(c, low, high, fb, &callee, depth + 1, vars, inlined);
                }
                _ => {}
            }
        }
    }

    fn line_rows(&self, low: u64, high: u64, inlined: &[Inlined]) -> Vec<DwarfLineEntry> {
        let start = self.rows.partition_point(|r| r.0 < low);
        let mut out: Vec<DwarfLineEntry> = Vec::new();
        for &(addr, file, line) in self.rows[start..].iter().take_while(|r| r.0 < high) {
            let offset = addr - low;
            let mut chain: Vec<&Inlined> = inlined
                .iter()
                .filter(|i| i.ranges.iter().any(|&(b, e)| b <= addr && addr < e))
                .collect();
            chain.sort_by_key(|i| std::cmp::Reverse(i.depth));
            let entry = DwarfLineEntry {
                offset,
                file: self.files.get(&file).cloned().unwrap_or_default(),
                line,
                inlined: chain.iter().map(|i| i.text.clone()).collect(),
            };
            // Keep the last row at an address (the one that applies to the instruction).
            match out.last_mut() {
                Some(last) if last.offset == offset => *last = entry,
                Some(last)
                    if last.file == entry.file
                        && last.line == entry.line
                        && last.inlined == entry.inlined => {}
                _ => out.push(entry),
            }
        }
        out
    }
}

/// Join `dir` and `name` (absolute `name` wins) and lexically drop `.` / resolve `..`.
fn join_path(dir: &str, name: &str) -> String {
    let joined = if name.starts_with('/') || dir.is_empty() {
        name.to_string()
    } else if name.is_empty() {
        dir.to_string()
    } else {
        format!("{dir}/{name}")
    };
    let mut parts: Vec<&str> = Vec::new();
    for c in joined.split('/') {
        match c {
            "" | "." => {}
            ".." if parts.last().is_some_and(|p| *p != "..") => {
                parts.pop();
            }
            _ => parts.push(c),
        }
    }
    let body = parts.join("/");
    if joined.starts_with('/') {
        format!("/{body}")
    } else {
        body
    }
}

/// `DW_OP_plus_uconst N` (old-style `DW_AT_data_member_location`) → `N`.
fn plus_uconst<Rd: Reader>(e: gimli::Expression<Rd>, enc: gimli::Encoding) -> Option<u64> {
    let mut ops = e.operations(enc);
    match ops.next().ok()?? {
        gimli::Operation::PlusConstant { value } => Some(value),
        gimli::Operation::UnsignedConstant { value } => Some(value),
        _ => None,
    }
}

/// AArch64 DWARF register name (`x0`..`x30`, `sp`, `v0`..`v31`).
pub fn dwarf_reg_name(r: u16) -> String {
    match r {
        0..=30 => format!("x{r}"),
        31 => "sp".into(),
        64..=95 => format!("v{}", r - 64),
        _ => format!("r{r}"),
    }
}

fn fmt_off(base: &str, off: i64) -> String {
    match off {
        0 => base.to_string(),
        o if o < 0 => format!("{base}-{:#x}", o.unsigned_abs()),
        o => format!("{base}+{o:#x}"),
    }
}

/// Render a DWARF location expression compactly:
/// `x19` (in register), `[sp+0x4]` (in memory), `= sp+0x8` / `= 0x0` (value),
/// `x0@entry` (entry value), pieces joined with ` | `.
pub fn render_expr<Rd: Reader>(e: gimli::Expression<Rd>, enc: gimli::Encoding, fb: &str) -> String {
    let mut pieces: Vec<String> = Vec::new();
    let mut stack: Vec<String> = Vec::new();
    let mut is_value = false;
    let mut reg_loc: Option<String> = None;
    let mut ops = e.operations(enc);
    let flush = |stack: &mut Vec<String>, reg: &mut Option<String>, val: &mut bool| {
        let s = if let Some(r) = reg.take() {
            r
        } else if let Some(top) = stack.pop() {
            if *val {
                format!("= {top}")
            } else {
                format!("[{top}]")
            }
        } else {
            "?".into()
        };
        stack.clear();
        *val = false;
        s
    };
    loop {
        let op = match ops.next() {
            Ok(Some(op)) => op,
            Ok(None) => break,
            Err(_) => return "<bad expr>".into(),
        };
        use gimli::Operation as Op;
        match op {
            Op::Register { register } => reg_loc = Some(dwarf_reg_name(register.0)),
            Op::RegisterOffset {
                register, offset, ..
            } => {
                stack.push(fmt_off(&dwarf_reg_name(register.0), offset));
            }
            Op::FrameOffset { offset } => stack.push(fmt_off(fb, offset)),
            Op::CallFrameCFA => stack.push("cfa".into()),
            Op::UnsignedConstant { value } => stack.push(format!("{value:#x}")),
            Op::SignedConstant { value } => stack.push(format!("{value}")),
            Op::PlusConstant { value } => {
                if let Some(t) = stack.pop() {
                    stack.push(format!("{t}+{value:#x}"));
                }
            }
            Op::Plus | Op::Minus | Op::Mul | Op::And | Op::Or | Op::Shl | Op::Shr => {
                let sym = match op {
                    Op::Plus => "+",
                    Op::Minus => "-",
                    Op::Mul => "*",
                    Op::And => "&",
                    Op::Or => "|",
                    Op::Shl => "<<",
                    _ => ">>",
                };
                if let (Some(b), Some(a)) = (stack.pop(), stack.pop()) {
                    stack.push(format!("({a}{sym}{b})"));
                }
            }
            Op::Deref { .. } => {
                if let Some(t) = stack.pop() {
                    stack.push(format!("*({t})"));
                }
            }
            Op::StackValue => is_value = true,
            Op::EntryValue { expression } => {
                let inner = render_expr(gimli::Expression(expression), enc, fb);
                stack.push(format!("{inner}@entry"));
            }
            Op::ImplicitValue { .. } => stack.push("<implicit>".into()),
            Op::ImplicitPointer { .. } => stack.push("<implicit-ptr>".into()),
            Op::Address { address } => stack.push(format!("{address:#x}")),
            Op::Piece { size_in_bits, .. } => {
                let s = flush(&mut stack, &mut reg_loc, &mut is_value);
                pieces.push(format!("{s}:{}B", size_in_bits / 8));
            }
            _ => stack.push("<expr>".into()),
        }
    }
    if !pieces.is_empty() {
        if reg_loc.is_some() || !stack.is_empty() {
            pieces.push(flush(&mut stack, &mut reg_loc, &mut is_value));
        }
        return pieces.join(" | ");
    }
    if let Some(r) = reg_loc {
        return r;
    }
    match stack.pop() {
        // `DW_OP_entry_value(DW_OP_regN), DW_OP_stack_value` is the entry value itself.
        Some(t) if t.ends_with("@entry") => t,
        Some(t) if is_value => format!("= {t}"),
        Some(t) => format!("[{t}]"),
        None => "<empty>".into(),
    }
}

/// Layouts reachable from `functions`: parameter/variable aggregates and pointees, their nested
/// member aggregates (transitively) and member pointees up to `pointer_depth` hops.
pub fn reachable_layouts<'a>(
    functions: impl IntoIterator<Item = &'a DwarfFunctionInfo>,
    layouts: &BTreeMap<String, DwarfTypeLayout>,
    pointer_depth: usize,
) -> Vec<DwarfTypeLayout> {
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut work: Vec<(String, usize)> = Vec::new();
    for f in functions {
        for p in &f.params {
            if let Some(k) = &p.pointee {
                work.push((k.clone(), 0));
            }
        }
    }
    while let Some((k, d)) = work.pop() {
        if seen.get(&k).is_some_and(|&old| old <= d) {
            continue;
        }
        seen.insert(k.clone(), d);
        let Some(l) = layouts.get(&k) else { continue };
        for m in &l.members {
            for agg in m.aggregate.iter().chain(&m.array_elem_aggregate) {
                work.push((agg.clone(), d));
            }
            if let Some(p) = &m.pointee
                && d < pointer_depth
            {
                work.push((p.clone(), d + 1));
            }
        }
    }
    seen.keys()
        .filter_map(|k| layouts.get(k).cloned())
        .collect()
}
