// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Legacy Static Linker (`untrusted_legacy_linker`) — `[OUTSIDE TCB]` (deprecated).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (deprecated legacy `Arm64.Obj.LinkedImage` linker kept only
//!   behind `--legacy-linked-image` for external downstream consumers migrating to `PlacedLib` /
//!   `MultiPlacedLib`; zero engine targets or theorems depend on it).
//! - **Purpose:** Lays out sections from offset 0 (text + 4-byte zero extern stubs, followed by
//!   either interleaved page-aligned rodata/data + bss + extern data objects and 8-byte-aligned
//!   GOT ([`DataLayout::Interleaved`], the default) or page-separated rodata, page-separated
//!   writable data + bss + extern data objects, and page-separated 8-byte-aligned GOT
//!   ([`DataLayout::PageSeparated`]), plus an initial-exec TLS block),
//!   patches base-independent relocations (`CALL26`, `JUMP26`, `CONDBR19`, `ADR_PREL_*`, `ADD_ABS_LO12_NC`,
//!   `LDST*_ABS_LO12_NC`, `PREL32`/`PREL64`/`PLT32`, `TLSIE_*`) at base 0, and records load-time
//!   `ABS64`/`ABS32` data relocations and GOT slots for `Arm64.Obj.LinkedImage.load`.
//!
//! # Key Types & Functions
//! - [`LinkedImage`], [`LinkedSymbol`], [`StubEntry`], [`DataReloc`], [`GotEntry`], [`ObjectSlice`]:
//!   Base-independent linked image representation mirroring `Arm64/Legacy/Object/LinkedImage.lean`.
//! - [`DataLayout`], [`link`], [`link_with_perturb`], [`link_with_layout`]: Links [`ObjObject`]s
//!   and [`ExternDecl`]s into a [`LinkedImage`].
//! - [`render_image`], [`render_obj_module`], [`emit_obj_lean_module`]: Renders [`LinkedImage`]
//!   and `ObjectInfo` definitions as Lean 4 source (`<ObjName>Obj.lean` + `.code.bin`/`.data.bin`).
//!
//! # When to Read This File
//! - Read this file only when maintaining legacy `--legacy-linked-image` output before physical
//!   deletion.

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use anyhow::{Result, anyhow, bail};

pub use crate::trusted_common::RelocKind;
use crate::trusted_common::{
    ExternDecl, ExternKind, Extraction, ObjModuleMeta, ObjObject, RelocType, SecKind, SymBind,
    SymKind, SymSection, lean_string_lit,
};
use crate::trusted_extractor::doc_safe;

/// `Arm64.Obj.pageSize`: the loader requires the base to be a multiple of it.
pub const PAGE_SIZE: u64 = 4096;

fn align_up(n: u64, a: u64) -> u64 {
    if a <= 1 { n } else { n.div_ceil(a) * a }
}

/// `Arm64.Obj.DataReloc`: the loader writes the `width`-byte little-endian encoding of
/// `base + target` at offset `off` of the data region.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DataReloc {
    pub off: u64,
    pub width: u64,
    pub target: u64,
}

/// A function recorded in an `ObjectInfo`: its symbol, and its bytes `code[off, off + size)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnInfo {
    pub name: String,
    pub off: u64,
    pub size: u64,
}

/// A function recorded in `ObjectInfo.call_fns`: its symbol, its bytes `code[off, off + size)`,
/// and its direct branch relocations `(offset_in_fn, target_sym)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallFnInfo {
    pub name: String,
    pub off: u64,
    pub size: u64,
    pub calls: Vec<(u64, String)>,
}

/// `Arm64.Obj.RelocEntry`: one relocation at byte offset `off` within a function or data symbol,
/// targeting `sym + addend`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelocEntry {
    pub off: u64,
    pub kind: RelocKind,
    pub sym: String,
    pub addend: i64,
    pub local_sym: bool,
}

/// `Arm64.Obj.SymCodeInfo`: a function recorded in `ObjectInfo.reloc_fns`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymCodeInfo {
    pub sym: String,
    pub off: u64,
    pub size: u64,
    /// Unperturbed (`perturb_bytes = 0`) linked bytes of the function (`Obj.SymCodeInfo.code`).
    pub code: Vec<u8>,
    /// Little-endian 32-bit instruction words of `code` (`words.len() * 4 == size`).
    pub words: Vec<u32>,
    pub relocs: Vec<RelocEntry>,
}

/// `Arm64.Obj.SymDataInfo`: a data symbol recorded in `ObjectInfo.data_syms`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymDataInfo {
    pub sym: String,
    pub align: u64,
    pub read_only: bool,
    pub off: u64,
    pub bytes_len: u64,
    pub zero_tail: u64,
    pub relocs: Vec<RelocEntry>,
}

/// `Arm64.Obj.ObjectInfo`: link-independent facts about one input object (`fns`, `call_fns`,
/// `reloc_fns`, and `data_syms`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectInfo {
    pub name: String,
    pub fns: Vec<FnInfo>,
    pub call_fns: Vec<CallFnInfo>,
    pub reloc_fns: Vec<SymCodeInfo>,
    pub data_syms: Vec<SymDataInfo>,
}

/// `Arm64.Obj.GotEntry`: a GOT slot holds `base + off` (`Addr`) or the base-independent
/// thread-pointer offset `v` of an extern TLS variable (`TpOff`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GotEntry {
    Addr(u64),
    TpOff(u64),
}

impl GotEntry {
    /// The value of the slot when the image is loaded at `base` (`GotEntry.value`).
    pub fn value(self, base: u64) -> u64 {
        match self {
            GotEntry::Addr(off) => base.wrapping_add(off),
            GotEntry::TpOff(v) => v,
        }
    }
}

/// `Arm64.Obj.LinkedImage` (see the module docs).
#[derive(Clone, Debug)]
pub struct LinkedImage {
    pub code: Vec<u8>,
    pub data_off: u64,
    /// rodata and data sections (not bss).
    pub data: Vec<u8>,
    /// Number of bss zero bytes after `data`.
    pub bss: u64,
    pub ro_data: Vec<(u64, u64)>,
    pub extern_data: Vec<(String, u64, u64)>,
    pub got_off: u64,
    pub got: Vec<GotEntry>,
    pub relocs: Vec<DataReloc>,
    pub symbols: Vec<(String, u64)>,
    pub obj_symbols: Vec<(String, Vec<(String, u64)>)>,
    pub stubs: Vec<(String, u64)>,
    pub objects: Vec<ObjectInfo>,
    /// Offset of every loaded section (`sec_off[i][j]` for section `j` of object `i`).
    /// Not part of the Lean image; used to locate symbols when generating lemmas.
    pub sec_off: Vec<Vec<Option<u64>>>,
    /// Offset of each extern TLS variable from the thread pointer. Not part of the Lean image
    /// (only the GOT slots holding these offsets are).
    pub extern_tls: Vec<(String, u64)>,
}

impl LinkedImage {
    pub fn data_end(&self) -> u64 {
        self.data_off + self.data.len() as u64 + self.bss
    }
}

/// Relocations allowed in text sections (all base-independent, see the module docs).
fn is_code(t: RelocType) -> bool {
    matches!(
        t,
        RelocType::Call26
            | RelocType::Jump26
            | RelocType::AdrPrelLo21
            | RelocType::AdrPrelPgHi21
            | RelocType::AdrPrelPgHi21Nc
            | RelocType::AddAbsLo12Nc
            | RelocType::Ldst8AbsLo12Nc
            | RelocType::Ldst16AbsLo12Nc
            | RelocType::Ldst32AbsLo12Nc
            | RelocType::Ldst64AbsLo12Nc
            | RelocType::Ldst128AbsLo12Nc
            | RelocType::Condbr19
            | RelocType::LdPrelLo19
            | RelocType::Tstbr14
            | RelocType::AdrGotPage
            | RelocType::Ld64GotLo12Nc
            | RelocType::TlsieAdrGottprelPage21
            | RelocType::TlsieLd64GottprelLo12Nc
            | RelocType::None
    )
}

/// Relocations allowed in rodata and data sections.
fn is_data(t: RelocType) -> bool {
    matches!(
        t,
        RelocType::Abs64
            | RelocType::Abs32
            | RelocType::Prel64
            | RelocType::Prel32
            | RelocType::Plt32
            | RelocType::None
    )
}

/// Relocations whose target is a GOT slot holding the symbol's address.
pub fn is_got(t: RelocType) -> bool {
    matches!(t, RelocType::AdrGotPage | RelocType::Ld64GotLo12Nc)
}

/// The supported TLS relocations (initial-exec): their target is a GOT slot holding the
/// symbol's offset from the thread pointer.
pub fn is_tls_ie(t: RelocType) -> bool {
    matches!(
        t,
        RelocType::TlsieAdrGottprelPage21 | RelocType::TlsieLd64GottprelLo12Nc
    )
}

fn check_align_ok(a: u64) -> bool {
    a <= PAGE_SIZE && PAGE_SIZE % a.max(1) == 0
}

/// Reject inputs using features the linker does not support.
fn check_supported(objs: &[ObjObject]) -> Result<()> {
    for o in objs {
        // Groups with no extracted members (e.g. trimmed away) do not affect the image.
        if let Some(g) = o.groups.iter().find(|g| !g.sections.is_empty()) {
            bail!(
                "unsupported (comdat): {}: section group `{}` (COMDAT={}) is not yet supported",
                o.name,
                g.signature,
                g.is_comdat
            );
        }
        for s in &o.sections {
            if (s.sh_flags & (object::elf::SHF_GROUP as u64)) != 0 {
                bail!(
                    "unsupported (comdat): {}: section `{}` has SHF_GROUP",
                    o.name,
                    s.name
                );
            }
            if s.is_rel {
                bail!(
                    "unsupported (rel_implicit_addend): {}: section `{}` uses SHT_REL relocations without explicit addends",
                    o.name,
                    s.name
                );
            }
            if (s.sh_flags & (object::elf::SHF_TLS as u64)) != 0 {
                bail!(
                    "unsupported (tls): {}: TLS section `{}` (SHF_TLS) is not yet supported",
                    o.name,
                    s.name
                );
            }
            for r in &s.relocs {
                if r.rtype.is_tls() && !is_tls_ie(r.rtype) {
                    bail!(
                        "unsupported (tls): {}: TLS relocation `{}` in section `{}` is not yet supported",
                        o.name,
                        r.rtype.lean_ctor(),
                        s.name
                    );
                }
            }
        }
        for sym in &o.symbols {
            if sym.kind == SymKind::Tls && sym.sec != SymSection::Undef {
                bail!(
                    "unsupported (tls): {}: TLS symbol definition `{}` (STT_TLS) is not yet supported",
                    o.name,
                    sym.name
                );
            }
            if sym.kind == SymKind::GnuIfunc {
                bail!(
                    "unsupported (ifunc): {}: IFUNC symbol `{}` (STT_GNU_IFUNC) is not yet supported",
                    o.name,
                    sym.name
                );
            }
            if sym.kind == SymKind::Common || sym.sec == SymSection::Common {
                bail!(
                    "unsupported (common_symbol): {}: common symbol `{}` (SHN_COMMON) is not yet supported",
                    o.name,
                    sym.name
                );
            }
        }
    }
    Ok(())
}

/// Check the well-formedness of the inputs.
fn check_inputs(objs: &[ObjObject], externs: &[ExternDecl]) -> Result<()> {
    check_supported(objs)?;
    let mut obj_names = HashSet::new();
    for o in objs {
        if !obj_names.insert(o.name.as_str()) {
            bail!("duplicate object name {}", o.name);
        }
        for s in &o.sections {
            if (s.sh_flags & (object::elf::SHF_ALLOC as u64)) != 0
                && s.name != ".eh_frame"
                && s.kind().is_none()
            {
                bail!(
                    "{}: unsupported allocated section `{}` (type={:#x}, flags={:#x})",
                    o.name,
                    s.name,
                    s.sh_type,
                    s.sh_flags
                );
            }
            let nobits = s.is_nobits();
            if nobits && !(s.bytes.is_empty() && s.relocs.is_empty()) {
                bail!(
                    "{}: NOBITS section {} has contents or relocations",
                    o.name,
                    s.name
                );
            }
            if !nobits && s.bytes.len() as u64 != s.size {
                bail!("{}: section {} has wrong length", o.name, s.name);
            }
            if !check_align_ok(s.align) {
                bail!(
                    "{}: section {} has unsupported alignment {}",
                    o.name,
                    s.name,
                    s.align
                );
            }
        }
    }
    let mut seen = HashSet::new();
    for o in objs {
        for s in &o.symbols {
            if s.bind == SymBind::Global
                && matches!(s.sec, SymSection::Sec(_))
                && !seen.insert(s.name.as_str())
            {
                bail!("duplicate global definition of {}", s.name);
            }
        }
    }
    for x in externs {
        if !check_align_ok(x.align) {
            bail!("extern {} has unsupported alignment {}", x.name, x.align);
        }
    }
    Ok(())
}

/// Place the sections of `objs` whose kind satisfies `p`, from offset `cur`.
fn place_secs(
    p: impl Fn(SecKind) -> bool,
    objs: &[ObjObject],
    sec_off: &mut [Vec<Option<u64>>],
    mut cur: u64,
) -> u64 {
    for (o, offs) in objs.iter().zip(sec_off.iter_mut()) {
        for (s, off) in o.sections.iter().zip(offs.iter_mut()) {
            if s.kind().is_some_and(&p) {
                let at = align_up(cur, s.align);
                cur = at + s.size;
                *off = Some(at);
            }
        }
    }
    cur
}

/// Place the externs of kind `kind`, from offset `cur`.
fn place_externs(
    externs: &[ExternDecl],
    kind: ExternKind,
    mut cur: u64,
) -> (Vec<(String, u64, u64)>, u64) {
    let mut out = Vec::new();
    for x in externs.iter().filter(|x| x.kind == kind) {
        let (size, align) = match kind {
            ExternKind::Func => (4, 4),
            _ => (x.size, x.align),
        };
        let at = align_up(cur, align);
        cur = at + size;
        out.push((x.name.clone(), at, size));
    }
    (out, cur)
}

/// Whether `x` fits in an `n`-bit two's-complement immediate.
fn fits_signed(n: u32, x: u64) -> bool {
    let v = x as i64 as i128;
    let lim = 1i128 << (n - 1);
    -lim <= v && v < lim
}

/// Replace bits `[lo, lo + w)` of `insn` by the low `w` bits of `v`.
fn set_bits(insn: u32, lo: u32, w: u32, v: u64) -> u32 {
    let mask: u32 = (((1u64 << w) - 1) as u32) << lo;
    (insn & !mask) | (((v as u32) << lo) & mask)
}

/// Patch instruction `insn` at place `p` for a code relocation of type `ty` with target `t`.
pub fn patch_code(ty: RelocType, insn: u32, t: u64, p: u64) -> Result<u32> {
    let page = |x: u64| x & !0xfff;
    let delta = t.wrapping_sub(p);
    let page_delta = page(t).wrapping_sub(page(p));
    let lo12 = t & 0xfff;
    let lo = |k: u32| -> Result<u32> {
        if lo12 % (1 << k) == 0 {
            Ok(set_bits(insn, 10, 12, lo12 >> k))
        } else {
            bail!("misaligned lo12 for {}-byte access", 1u32 << k)
        }
    };
    match ty {
        RelocType::None => Ok(insn),
        RelocType::Call26 | RelocType::Jump26 => {
            if delta % 4 == 0 && fits_signed(28, delta) {
                Ok(set_bits(insn, 0, 26, delta >> 2))
            } else {
                bail!("branch target misaligned or out of range")
            }
        }
        RelocType::Condbr19 | RelocType::LdPrelLo19 => {
            if delta % 4 == 0 && fits_signed(21, delta) {
                Ok(set_bits(insn, 5, 19, delta >> 2))
            } else {
                bail!("CONDBR19/LD_PREL_LO19 target misaligned or out of range")
            }
        }
        RelocType::Tstbr14 => {
            if delta % 4 == 0 && fits_signed(16, delta) {
                Ok(set_bits(insn, 5, 14, delta >> 2))
            } else {
                bail!("TSTBR14 target misaligned or out of range")
            }
        }
        RelocType::AdrPrelLo21 => {
            if fits_signed(21, delta) {
                Ok(set_bits(set_bits(insn, 29, 2, delta), 5, 19, delta >> 2))
            } else {
                bail!("ADR_PREL_LO21 target out of range")
            }
        }
        RelocType::AdrPrelPgHi21 | RelocType::AdrGotPage | RelocType::TlsieAdrGottprelPage21 => {
            if fits_signed(33, page_delta) {
                Ok(set_bits(
                    set_bits(insn, 29, 2, page_delta >> 12),
                    5,
                    19,
                    page_delta >> 14,
                ))
            } else {
                bail!("ADRP target out of range")
            }
        }
        RelocType::AdrPrelPgHi21Nc => Ok(set_bits(
            set_bits(insn, 29, 2, page_delta >> 12),
            5,
            19,
            page_delta >> 14,
        )),
        RelocType::AddAbsLo12Nc | RelocType::Ldst8AbsLo12Nc => lo(0),
        RelocType::Ldst16AbsLo12Nc => lo(1),
        RelocType::Ldst32AbsLo12Nc => lo(2),
        RelocType::Ldst64AbsLo12Nc
        | RelocType::Ld64GotLo12Nc
        | RelocType::TlsieLd64GottprelLo12Nc => lo(3),
        RelocType::Ldst128AbsLo12Nc => lo(4),
        _ => bail!("relocation type {ty:?} not allowed in code"),
    }
}

/// Byte width patched by a relocation of type `t` in a section of kind `kind`.
fn reloc_width(kind: SecKind, t: RelocType) -> u64 {
    match (kind, t) {
        (_, RelocType::None) => 0,
        (SecKind::Text, _) => 4,
        (_, RelocType::Prel32 | RelocType::Plt32 | RelocType::Abs32) => 4,
        _ => 8,
    }
}

fn add_signed_off(off: u64, addend: i64) -> Option<u64> {
    let t = (off as i128) + (addend as i128);
    if (0..(1i128 << 64)).contains(&t) {
        Some(t as u64)
    } else {
        None
    }
}

fn code_reloc_in_range(kind: RelocKind, place_off: u64, target_off: u64) -> bool {
    let d = target_off.wrapping_sub(place_off) as i64;
    match kind {
        RelocKind::Call26 | RelocKind::Jump26 => {
            target_off.wrapping_sub(place_off) % 4 == 0
                && (-(1i64 << 27)..(1i64 << 27)).contains(&d)
        }
        RelocKind::AdrpHi21 | RelocKind::AdrGotPage | RelocKind::TlsieAdrGottprelPage21 => {
            let pg = (target_off & !0xfff).wrapping_sub(place_off & !0xfff) as i64;
            (-(1i64 << 32)..(1i64 << 32)).contains(&pg)
        }
        RelocKind::AdrpHi21Nc | RelocKind::AddLo12 | RelocKind::Ldst8Lo12 => true,
        RelocKind::Ldst16Lo12 => target_off & 1 == 0,
        RelocKind::Ldst32Lo12 => target_off & 3 == 0,
        RelocKind::Ldst64Lo12
        | RelocKind::Ld64GotLo12Nc
        | RelocKind::TlsieLd64GottprelLo12Nc => target_off & 7 == 0,
        RelocKind::Ldst128Lo12 => target_off & 15 == 0,
        RelocKind::Condbr19 | RelocKind::LdPrelLo19 => {
            target_off.wrapping_sub(place_off) % 4 == 0
                && (-(1i64 << 20)..(1i64 << 20)).contains(&d)
        }
        RelocKind::Tstbr14 => {
            target_off.wrapping_sub(place_off) % 4 == 0
                && (-(1i64 << 15)..(1i64 << 15)).contains(&d)
        }
        RelocKind::AdrPrelLo21 => (-(1i64 << 20)..(1i64 << 20)).contains(&d),
        RelocKind::Prel32 => (-(1i64 << 31)..(1i64 << 31)).contains(&d),
        RelocKind::Abs64 | RelocKind::Abs32 => false,
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn build_reloc_entry(
    o: &ObjObject,
    offs: &[Option<u64>],
    r: &crate::trusted_common::ObjReloc,
    rel_off: u64,
    actual_target: u64,
    unique_obj_sym_off: &HashMap<&str, u64>,
    first_sym_off: &HashMap<&str, u64>,
    first_stub_off: &HashMap<&str, u64>,
    first_ext_data_off: &HashMap<&str, u64>,
) -> Option<RelocEntry> {
    if is_got(r.rtype) || is_tls_ie(r.rtype) {
        return None;
    }
    let kind = RelocKind::from_reloc_type(r.rtype)?;
    let resolve_reloc_target = |sym: &str, addend: i64, local_sym: bool| -> Option<u64> {
        let local_lookup = unique_obj_sym_off.get(sym).copied();
        let base = if local_sym {
            local_lookup
        } else {
            local_lookup
                .or_else(|| first_sym_off.get(sym).copied())
                .or_else(|| first_stub_off.get(sym).copied())
                .or_else(|| first_ext_data_off.get(sym).copied())
        }?;
        add_signed_off(base, addend)
    };
    let ts = o.symbols.get(r.sym)?;
    let preferred_local = ts.bind == SymBind::Local && matches!(ts.sec, SymSection::Sec(_));
    if resolve_reloc_target(&ts.name, r.addend, preferred_local) == Some(actual_target) {
        return Some(RelocEntry {
            off: rel_off,
            kind,
            sym: ts.name.clone(),
            addend: r.addend,
            local_sym: preferred_local,
        });
    }
    let SymSection::Sec(ti) = ts.sec else {
        return None;
    };
    let sec_base = offs.get(ti).copied().flatten()?;
    let mut best: Option<((u8, u64), RelocEntry)> = None;
    for cs in &o.symbols {
        if cs.sec != SymSection::Sec(ti) || !matches!(cs.kind, SymKind::Func | SymKind::Object) {
            continue;
        }
        let cand_off = sec_base + cs.value;
        let Ok(cand_addend) = i64::try_from((actual_target as i128) - (cand_off as i128)) else {
            continue;
        };
        let local_sym = cs.bind == SymBind::Local;
        if resolve_reloc_target(&cs.name, cand_addend, local_sym) != Some(actual_target) {
            continue;
        }
        let rank = if cand_off <= actual_target && actual_target < cand_off + cs.size.max(1) {
            (0, actual_target - cand_off)
        } else if cand_off <= actual_target {
            (1, actual_target - cand_off)
        } else {
            (2, cand_addend.unsigned_abs())
        };
        if best.as_ref().is_none_or(|(b_rank, _)| rank < *b_rank) {
            best = Some((
                rank,
                RelocEntry {
                    off: rel_off,
                    kind,
                    sym: cs.name.clone(),
                    addend: cand_addend,
                    local_sym,
                },
            ));
        }
    }
    best.map(|(_, e)| e)
}

/// A resolved relocation of a section: offset in the section, type, and target offset
/// (the symbol's offset plus addend, or the GOT slot's offset for GOT relocations).
struct Fixup {
    offset: u64,
    rtype: RelocType,
    target: u64,
}

/// ARM64 `NOP` (`0xd503201f`), used to pad the leading `.text` shift under `--perturb-layout`.
pub const ARM64_NOP_WORD: u32 = 0xd503_201f;

/// Data and GOT placement policy for [`link_with_layout`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DataLayout {
    /// Default layout: `.rodata` and `.data` sections are placed in input order starting at
    /// `data_start`, followed by `.bss`, external data objects, and the GOT at
    /// `align_up(xd_end, 8)`. Every `.rodata` section (including empty ones) is recorded in
    /// `li.ro_data` without inter-section padding ranges.
    #[default]
    Interleaved,
    /// Permission-separated 4 KiB page layout (`perturb_bytes = p`, `sub_page = p % PAGE_SIZE`):
    /// - `.rodata` starts at `data_start = data_off` (`+ sub_page` when `p > 0`) and ends at
    ///   `ro_end`.
    /// - If the image has non-empty `.rodata` and writable bytes (non-empty `.data`/`.bss` or an
    ///   `ExternKind::Object`), writable sections start on a fresh page
    ///   `rw_off = align_up(ro_end, PAGE_SIZE)` at `rw_start = rw_off + sub_page` in order `.data`,
    ///   then `.bss`, then extern data.
    /// - Every byte of `[data_off, rw_off)` outside `.rodata` is zero and is recorded in
    ///   `li.ro_data` so `Obj.Image.dataPerm` assigns `Perm.ro` across the read-only ELF pages
    ///   while keeping `[rw_off, rw_start)` at `Perm.rw`.
    /// - If the image has writable bytes, `got_off = align_up(xd_end, PAGE_SIZE) + (align_up(sub_page, 8) % PAGE_SIZE)`.
    /// - Zero-size `.rodata` sections are omitted from `li.ro_data`.
    PageSeparated,
}

/// Link `objs` with the extern declarations `externs` using [`DataLayout::Interleaved`].
pub fn link(objs: &[ObjObject], externs: &[ExternDecl]) -> Result<LinkedImage> {
    link_with_layout(objs, externs, 0, DataLayout::Interleaved)
}

/// Link `objs` with the extern declarations `externs` using [`DataLayout::Interleaved`],
/// deterministically shifting `.text` and `.rodata`/`.data`/`.bss` section placements by
/// `perturb_bytes` (must be a multiple of 4). See [`link_with_layout`] for layout options.
pub fn link_with_perturb(
    objs: &[ObjObject],
    externs: &[ExternDecl],
    perturb_bytes: u64,
) -> Result<LinkedImage> {
    link_with_layout(objs, externs, perturb_bytes, DataLayout::Interleaved)
}

/// Link `objs` with the extern declarations `externs` under `layout` (default
/// [`DataLayout::Interleaved`]), deterministically shifting `.text` and `.rodata`/`.data`/`.bss`
/// section placements by `perturb_bytes` (must be a multiple of 4).
///
/// When `perturb_bytes > 0`:
/// - `.text` sections are placed starting at offset `perturb_bytes` (with leading 4-byte words
///   filled with [`ARM64_NOP_WORD`]);
/// - `.rodata`/`.data`/`.bss` sections are shifted by `perturb_bytes` (keeping `data_off`
///   page-aligned as required by `Arm64.Obj.LinkedImage.wellFormed` and prepending zero padding
///   to `data` when `perturb_bytes % PAGE_SIZE != 0`);
/// - under [`DataLayout::Interleaved`] (the default), `.rodata` and `.data` are placed in input
///   order and `got_off = align_up(xd_end, 8)`; under [`DataLayout::PageSeparated`], non-empty
///   `.rodata`, writable `.data`/`.bss`/extern-data, and the GOT occupy separate 4 KiB page
///   ranges with `[data_off, rw_off)` covered in `li.ro_data`;
/// - each `SymCodeInfo` in `ObjectInfo.reloc_fns` retains its unperturbed (`perturb_bytes = 0`)
///   instruction words (`code` and `words`) and function-relative `relocs`, while `li.code`
///   receives the relocated instruction words for the perturbed layout.
pub fn link_with_layout(
    objs: &[ObjObject],
    externs: &[ExternDecl],
    perturb_bytes: u64,
    layout: DataLayout,
) -> Result<LinkedImage> {
    if perturb_bytes % 4 != 0 {
        bail!("layout perturbation byte count ({perturb_bytes}) must be a multiple of 4");
    }
    check_inputs(objs, externs)?;
    let base_li = if perturb_bytes > 0 {
        Some(link_with_layout(objs, externs, 0, layout)?)
    } else {
        None
    };

    // Layout.
    let mut sec_off: Vec<Vec<Option<u64>>> =
        objs.iter().map(|o| vec![None; o.sections.len()]).collect();
    let text_end = place_secs(|k| k == SecKind::Text, objs, &mut sec_off, perturb_bytes);
    let (stubs3, code_end) = place_externs(externs, ExternKind::Func, align_up(text_end, 4));
    let stubs: Vec<(String, u64)> = stubs3.into_iter().map(|(n, o, _)| (n, o)).collect();
    let (data_off, data_bytes_end, data_end, extern_data, got_off, page_sep_rw_off) = match layout {
        DataLayout::Interleaved => {
            let has_data_or_bss = objs.iter().any(|o| {
                o.sections.iter().any(|s| {
                    matches!(
                        s.kind(),
                        Some(SecKind::Rodata | SecKind::Data | SecKind::Bss)
                    )
                })
            });
            let (data_off, data_start) = match &base_li {
                Some(b) if has_data_or_bss => {
                    let min_data_start = b
                        .data_off
                        .checked_add(perturb_bytes)
                        .ok_or_else(|| anyhow!("layout perturbation byte count overflows u64"))?;
                    let d_off = align_up(code_end, PAGE_SIZE).max(min_data_start & !(PAGE_SIZE - 1));
                    (d_off, d_off + (perturb_bytes % PAGE_SIZE))
                }
                _ => {
                    let d_off = align_up(code_end, PAGE_SIZE);
                    (d_off, d_off)
                }
            };
            let data_bytes_end = place_secs(
                |k| matches!(k, SecKind::Rodata | SecKind::Data),
                objs,
                &mut sec_off,
                data_start,
            );
            let data_end = place_secs(|k| k == SecKind::Bss, objs, &mut sec_off, data_bytes_end);
            let (extern_data, xd_end) = place_externs(externs, ExternKind::Object, data_end);
            let got_off = align_up(xd_end, 8);
            (data_off, data_bytes_end, data_end, extern_data, got_off, None)
        }
        DataLayout::PageSeparated => {
            let has_rodata = objs.iter().any(|o| {
                o.sections
                    .iter()
                    .any(|s| s.kind() == Some(SecKind::Rodata) && s.size > 0)
            });
            let has_writable = objs.iter().any(|o| {
                o.sections
                    .iter()
                    .any(|s| matches!(s.kind(), Some(SecKind::Data | SecKind::Bss)) && s.size > 0)
            }) || externs.iter().any(|x| x.kind == ExternKind::Object);
            let has_data_or_bss = has_rodata
                || has_writable
                || objs.iter().any(|o| {
                    o.sections.iter().any(|s| {
                        matches!(
                            s.kind(),
                            Some(SecKind::Rodata | SecKind::Data | SecKind::Bss)
                        )
                    })
                });
            let sub_page = perturb_bytes % PAGE_SIZE;
            let (data_off, data_start) = match &base_li {
                Some(b) if has_data_or_bss => {
                    let min_data_start = b
                        .data_off
                        .checked_add(perturb_bytes)
                        .ok_or_else(|| anyhow!("layout perturbation byte count overflows u64"))?;
                    let d_off = align_up(code_end, PAGE_SIZE).max(min_data_start & !(PAGE_SIZE - 1));
                    (d_off, d_off + sub_page)
                }
                _ => {
                    let d_off = align_up(code_end, PAGE_SIZE);
                    (d_off, d_off)
                }
            };
            let placed_ro_end = place_secs(|k| k == SecKind::Rodata, objs, &mut sec_off, data_start);
            let ro_end = if has_rodata {
                placed_ro_end
            } else {
                data_start
            };
            let (rw_off, rw_start) = if !has_rodata {
                (data_off, data_start)
            } else if has_writable {
                let rw_off = align_up(ro_end, PAGE_SIZE);
                (rw_off, rw_off + sub_page)
            } else {
                (ro_end, ro_end)
            };
            let (data_bytes_end, data_end) = if has_writable {
                let d_bytes_end = place_secs(|k| k == SecKind::Data, objs, &mut sec_off, rw_start);
                let d_end = place_secs(|k| k == SecKind::Bss, objs, &mut sec_off, d_bytes_end);
                (d_bytes_end, d_end)
            } else {
                place_secs(|k| k == SecKind::Data, objs, &mut sec_off, rw_start);
                place_secs(|k| k == SecKind::Bss, objs, &mut sec_off, rw_start);
                (rw_start, rw_start)
            };
            let (extern_data, xd_end) = place_externs(externs, ExternKind::Object, data_end);
            let got_shift = align_up(sub_page, 8) % PAGE_SIZE;
            let got_off = if has_writable {
                align_up(xd_end, PAGE_SIZE) + got_shift
            } else if has_rodata {
                align_up(xd_end, 8)
            } else {
                align_up(xd_end, 8) + got_shift
            };
            (
                data_off,
                data_bytes_end,
                data_end,
                extern_data,
                got_off,
                has_rodata.then_some(rw_off),
            )
        }
    };
    // Extern TLS variables: one TLS block, placed after the 16-byte thread control block as
    // AArch64 TLS variant 1 specifies for an executable (so variable `x` at offset `o` in the
    // block is at `tp + align_up(16, block_align) + o`).
    let (tls3, _) = place_externs(externs, ExternKind::Tls, 0);
    let tls_align = externs
        .iter()
        .filter(|x| x.kind == ExternKind::Tls)
        .map(|x| x.align)
        .fold(1, u64::max);
    let tp_off = align_up(16, tls_align);
    let extern_tls: Vec<(String, u64)> =
        tls3.into_iter().map(|(n, o, _)| (n, tp_off + o)).collect();
    let tls_externs: HashMap<&str, u64> =
        extern_tls.iter().map(|(n, o)| (n.as_str(), *o)).collect();

    // Global symbols: strong definitions take precedence over weak ones.
    let mut globals: HashMap<&str, u64> = HashMap::new();
    for want in [SymBind::Global, SymBind::Weak] {
        for (o, offs) in objs.iter().zip(&sec_off) {
            for s in &o.symbols {
                if s.bind != want {
                    continue;
                }
                if let SymSection::Sec(i) = s.sec
                    && let Some(off) = offs.get(i).copied().flatten()
                {
                    globals.entry(s.name.as_str()).or_insert(off + s.value);
                }
            }
        }
    }
    let mut mem_externs: HashMap<&str, u64> = HashMap::new();
    for (n, o) in &stubs {
        mem_externs.entry(n.as_str()).or_insert(*o);
    }
    for (n, o, _) in &extern_data {
        mem_externs.entry(n.as_str()).or_insert(*o);
    }
    for x in externs {
        if globals.contains_key(x.name.as_str()) {
            bail!("extern {} is also defined", x.name);
        }
    }

    // Symbol resolution.
    let resolve = |o: &ObjObject, offs: &[Option<u64>], idx: usize| -> Result<u64> {
        let s = o
            .symbols
            .get(idx)
            .ok_or_else(|| anyhow!("{}: bad symbol index {idx}", o.name))?;
        match s.sec {
            SymSection::Sec(i) => {
                if s.bind != SymBind::Local
                    && let Some(off) = globals.get(s.name.as_str())
                {
                    return Ok(*off);
                }
                match offs.get(i).copied().flatten() {
                    Some(off) => Ok(off + s.value),
                    None => bail!(
                        "{}: symbol {} is in a section that is not loaded",
                        o.name,
                        s.name
                    ),
                }
            }
            SymSection::Abs => bail!(
                "{}: relocation against absolute symbol {} is not supported",
                o.name,
                s.name
            ),
            SymSection::Common => bail!(
                "unsupported (common_symbol): {}: relocation against common symbol {}",
                o.name,
                s.name
            ),
            SymSection::Other => bail!(
                "{}: relocation against unsupported symbol {}",
                o.name,
                s.name
            ),
            SymSection::Undef => globals
                .get(s.name.as_str())
                .or_else(|| mem_externs.get(s.name.as_str()))
                .copied()
                .ok_or_else(|| anyhow!("{}: undefined symbol {}", o.name, s.name)),
        }
    };

    // Resolve the relocations of every loaded section; GOT slots are allocated in order of
    // first use.
    let mut got: Vec<GotEntry> = Vec::new();
    let mut got_index: HashMap<GotEntry, u64> = HashMap::new();
    let mut got_slot = |e: GotEntry| -> u64 {
        *got_index.entry(e).or_insert_with(|| {
            got.push(e);
            got.len() as u64 - 1
        })
    };
    let mut secs: Vec<(SecKind, u64, &[u8], u64, Vec<Fixup>)> = Vec::new();
    for (o, offs) in objs.iter().zip(&sec_off) {
        for (s, off) in o.sections.iter().zip(offs) {
            let Some(off) = *off else { continue };
            let Some(kind) = s.kind() else {
                bail!("{}: loaded section {} has no kind", o.name, s.name)
            };
            let mut fixups = Vec::with_capacity(s.relocs.len());
            for r in &s.relocs {
                let ok = match kind {
                    SecKind::Text => is_code(r.rtype),
                    SecKind::Rodata | SecKind::Data => is_data(r.rtype),
                    _ => false,
                };
                if !ok {
                    bail!(
                        "{}: relocation {:?} not allowed in a {:?} section ({})",
                        o.name,
                        r.rtype,
                        kind,
                        s.name
                    );
                }
                if r.rtype == RelocType::None {
                    continue;
                }
                let target = if is_tls_ie(r.rtype) {
                    let s = o
                        .symbols
                        .get(r.sym)
                        .ok_or_else(|| anyhow!("{}: bad symbol index {}", o.name, r.sym))?;
                    let tp = match (s.sec, tls_externs.get(s.name.as_str())) {
                        (SymSection::Undef, Some(tp)) => *tp,
                        _ => bail!(
                            "unsupported (tls): {}: TLS relocation against {}, which is not an extern TLS variable",
                            o.name,
                            s.name
                        ),
                    };
                    got_off + 8 * got_slot(GotEntry::TpOff(tp.wrapping_add(r.addend as u64)))
                } else {
                    let t = resolve(o, offs, r.sym)?.wrapping_add(r.addend as u64);
                    if is_got(r.rtype) {
                        got_off + 8 * got_slot(GotEntry::Addr(t))
                    } else {
                        t
                    }
                };
                fixups.push(Fixup {
                    offset: r.offset,
                    rtype: r.rtype,
                    target,
                });
            }
            fixups.sort_by_key(|f| f.offset);
            let mut next = 0u64;
            for f in &fixups {
                if f.offset < next {
                    bail!(
                        "{}: overlapping relocations at {:#x} in section {}",
                        o.name,
                        f.offset,
                        s.name
                    );
                }
                next = f.offset.saturating_add(reloc_width(kind, f.rtype));
                if next > s.size {
                    bail!(
                        "{}: relocation at {:#x} past the end of section {}",
                        o.name,
                        f.offset,
                        s.name
                    );
                }
            }
            secs.push((kind, off, &s.bytes, s.size, fixups));
        }
    }

    // Code at base 0 (with leading/inter-section padding filled with NOPs when perturbed),
    // then zero stubs.
    let mut code = vec![0u8; code_end as usize];
    if perturb_bytes > 0 {
        let nop_end = align_up(text_end, 4) as usize;
        for chunk in code[..nop_end].chunks_exact_mut(4) {
            chunk.copy_from_slice(&ARM64_NOP_WORD.to_le_bytes());
        }
    }
    // Data (without bss) at base 0; absolute addresses become `DataReloc`s.
    let mut data = vec![0u8; (data_bytes_end - data_off) as usize];
    let mut relocs = Vec::new();
    let mut ro_data = Vec::new();
    for (kind, off, bytes, size, fixups) in &secs {
        match kind {
            SecKind::Text => {
                let at = *off as usize;
                code[at..at + bytes.len()].copy_from_slice(bytes);
                for f in fixups {
                    let o = at + f.offset as usize;
                    let w = u32::from_le_bytes(code[o..o + 4].try_into().unwrap());
                    let w = patch_code(f.rtype, w, f.target, off + f.offset)?;
                    code[o..o + 4].copy_from_slice(&w.to_le_bytes());
                }
            }
            SecKind::Rodata | SecKind::Data => {
                match layout {
                    DataLayout::Interleaved => {
                        if *kind == SecKind::Rodata {
                            ro_data.push((*off, *size));
                        }
                    }
                    DataLayout::PageSeparated => {
                        if *kind == SecKind::Rodata && *size > 0 {
                            ro_data.push((*off, *size));
                        }
                    }
                }
                let at = (off - data_off) as usize;
                data[at..at + bytes.len()].copy_from_slice(bytes);
                for f in fixups {
                    let o = at + f.offset as usize;
                    let place = off + f.offset;
                    match f.rtype {
                        RelocType::Abs64 | RelocType::Abs32 => relocs.push(DataReloc {
                            off: o as u64,
                            width: reloc_width(*kind, f.rtype),
                            target: f.target,
                        }),
                        RelocType::Prel64 => {
                            let v = f.target.wrapping_sub(place);
                            data[o..o + 8].copy_from_slice(&v.to_le_bytes());
                        }
                        RelocType::Prel32 | RelocType::Plt32 => {
                            let v = f.target.wrapping_sub(place);
                            if !(-(1i64 << 31)..(1i64 << 32)).contains(&(v as i64)) {
                                bail!("PREL32 out of range at {place:#x}");
                            }
                            data[o..o + 4].copy_from_slice(&v.to_le_bytes()[..4]);
                        }
                        t => bail!("relocation type {t:?} not allowed in data"),
                    }
                }
            }
            _ => {}
        }
    }
    if let Some(rw_off) = page_sep_rw_off {
        // Cover zero-filled padding inside the read-only prefix `[data_off, rw_off)` so `dataPerm`
        // assigns `Perm.ro` to every byte mapped `r--` in the ELF while keeping `[rw_off, rw_start)`
        // at `Perm.rw` on the `rw-` page.
        let mut sorted_ro = ro_data.clone();
        sorted_ro.sort_by_key(|&(o, _)| o);
        let mut cur = data_off;
        for (o, n) in sorted_ro {
            if cur < o {
                ro_data.push((cur, o - cur));
            }
            cur = cur.max(o + n);
        }
        if cur < rw_off {
            ro_data.push((cur, rw_off - cur));
        }
    }

    // Symbols: defined function and object symbols in loaded sections, per object. A
    // non-local symbol is only listed for the object whose definition was selected.
    let mut obj_symbols = Vec::with_capacity(objs.len());
    for (o, offs) in objs.iter().zip(&sec_off) {
        let mut syms = Vec::new();
        for s in &o.symbols {
            if !matches!(s.kind, SymKind::Func | SymKind::Object) {
                continue;
            }
            let SymSection::Sec(i) = s.sec else { continue };
            let Some(off) = offs.get(i).copied().flatten() else {
                continue;
            };
            let at = off + s.value;
            if s.bind != SymBind::Local && globals.get(s.name.as_str()) != Some(&at) {
                continue;
            }
            syms.push((s.name.clone(), at));
        }
        syms.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        obj_symbols.push((o.name.clone(), syms));
    }
    let symbols: Vec<(String, u64)> = obj_symbols
        .iter()
        .flat_map(|(_, syms)| syms.iter().cloned())
        .collect();

    // Object infos: exported functions in relocation-free text sections (`fns`), or in text
    // sections whose relocations are only direct branches to external symbols (`call_fns`), at
    // a 4-aligned offset, listed exactly once in the object's symbols and resolved by `symbols`.
    let mut first_sym_off: HashMap<&str, u64> = HashMap::new();
    for (n, o) in &symbols {
        first_sym_off.entry(n.as_str()).or_insert(*o);
    }
    let mut first_stub_off: HashMap<&str, u64> = HashMap::new();
    for (n, o) in &stubs {
        first_stub_off.entry(n.as_str()).or_insert(*o);
    }
    let mut first_ext_data_off: HashMap<&str, u64> = HashMap::new();
    for (n, o, _) in &extern_data {
        first_ext_data_off.entry(n.as_str()).or_insert(*o);
    }
    let mut objects = Vec::with_capacity(objs.len());
    for (obj_idx, ((o, offs), (_, syms))) in objs
        .iter()
        .zip(&sec_off)
        .zip(&obj_symbols)
        .enumerate()
    {
        let mut count: HashMap<&str, usize> = HashMap::new();
        for (n, _) in syms {
            *count.entry(n.as_str()).or_default() += 1;
        }
        let mut unique_obj_sym_off: HashMap<&str, u64> = HashMap::new();
        for (n, off) in syms {
            if count.get(n.as_str()) == Some(&1) {
                unique_obj_sym_off.insert(n.as_str(), *off);
            }
        }
        let mut fns: Vec<FnInfo> = Vec::new();
        let mut call_fns: Vec<CallFnInfo> = Vec::new();
        let mut reloc_fns: Vec<SymCodeInfo> = Vec::new();
        let mut data_syms: Vec<SymDataInfo> = Vec::new();
        let mut seen = HashSet::new();
        for s in &o.symbols {
            if s.kind != SymKind::Func || s.bind == SymBind::Local || s.size == 0 {
                continue;
            }
            let SymSection::Sec(i) = s.sec else { continue };
            let (Some(sec), Some(off)) = (o.sections.get(i), offs.get(i).copied().flatten())
            else {
                continue;
            };
            let at = off + s.value;
            if sec.kind() != Some(SecKind::Text)
                || at % 4 != 0
                || s.value + s.size > sec.size
                || count.get(s.name.as_str()) != Some(&1)
                || globals.get(s.name.as_str()) != Some(&at)
                || first_sym_off.get(s.name.as_str()) != Some(&at)
                || !seen.insert(s.name.as_str())
            {
                continue;
            }
            if sec.relocs.is_empty() {
                fns.push(FnInfo {
                    name: s.name.clone(),
                    off: at,
                    size: s.size,
                });
            } else if s.value == 0 && s.size == sec.size && s.size % 4 == 0 {
                let mut calls = Vec::with_capacity(sec.relocs.len());
                let mut reloc_offs = HashSet::new();
                let mut ok = true;
                for r in &sec.relocs {
                    if !matches!(r.rtype, RelocType::Call26 | RelocType::Jump26)
                        || r.addend != 0
                        || r.offset % 4 != 0
                        || r.offset + 4 > s.size
                        || !reloc_offs.insert(r.offset)
                    {
                        ok = false;
                        break;
                    }
                    let Some(ts) = o.symbols.get(r.sym) else {
                        ok = false;
                        break;
                    };
                    let resolved = first_sym_off
                        .get(ts.name.as_str())
                        .or_else(|| first_stub_off.get(ts.name.as_str()))
                        .copied();
                    if ts.sec != SymSection::Undef || resolved.is_none() {
                        ok = false;
                        break;
                    }
                    calls.push((r.offset, ts.name.clone()));
                }
                if ok {
                    call_fns.push(CallFnInfo {
                        name: s.name.clone(),
                        off: at,
                        size: s.size,
                        calls,
                    });
                }
            }
        }
        let fn_names: HashSet<&str> = fns.iter().map(|f| f.name.as_str()).collect();
        let mut seen_reloc_fn = HashSet::new();
        for s in &o.symbols {
            if s.kind != SymKind::Func || s.size == 0 || s.size % 4 != 0 {
                continue;
            }
            let SymSection::Sec(i) = s.sec else { continue };
            let (Some(sec), Some(off)) = (o.sections.get(i), offs.get(i).copied().flatten())
            else {
                continue;
            };
            let at = off + s.value;
            if sec.kind() != Some(SecKind::Text)
                || at % 4 != 0
                || s.value % 4 != 0
                || s.value + s.size > sec.size
                || count.get(s.name.as_str()) != Some(&1)
                || first_sym_off.get(s.name.as_str()) != Some(&at)
                || (s.bind != SymBind::Local && globals.get(s.name.as_str()) != Some(&at))
                || fn_names.contains(s.name.as_str())
                || stubs.iter().any(|(_, st)| at <= *st && *st < at + s.size)
                || !seen_reloc_fn.insert(s.name.as_str())
            {
                continue;
            }
            let mut fn_relocs = Vec::new();
            let mut reloc_offs = HashSet::new();
            let mut ok = true;
            for r in &sec.relocs {
                if r.rtype == RelocType::None {
                    continue;
                }
                if r.offset + 4 <= s.value || r.offset >= s.value + s.size {
                    continue;
                }
                if r.offset < s.value || r.offset + 4 > s.value + s.size {
                    ok = false;
                    break;
                }
                let roff = r.offset - s.value;
                if roff % 4 != 0 || !reloc_offs.insert(roff) {
                    ok = false;
                    break;
                }
                let Ok(base_t) = resolve(o, offs, r.sym) else {
                    ok = false;
                    break;
                };
                let actual_t = base_t.wrapping_add(r.addend as u64);
                let Some(entry) = build_reloc_entry(
                    o,
                    offs,
                    r,
                    roff,
                    actual_t,
                    &unique_obj_sym_off,
                    &first_sym_off,
                    &first_stub_off,
                    &first_ext_data_off,
                ) else {
                    ok = false;
                    break;
                };
                if !code_reloc_in_range(entry.kind, at + roff, actual_t) {
                    ok = false;
                    break;
                }
                fn_relocs.push(entry);
            }
            if ok {
                let fn_code = match &base_li {
                    Some(b) => {
                        let base_sec_off = b.sec_off[obj_idx][i].expect("loaded in base_li");
                        let base_at = (base_sec_off + s.value) as usize;
                        b.code[base_at..base_at + s.size as usize].to_vec()
                    }
                    None => code[at as usize..(at + s.size) as usize].to_vec(),
                };
                let fn_words = fn_code
                    .chunks_exact(4)
                    .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
                    .collect();
                reloc_fns.push(SymCodeInfo {
                    sym: s.name.clone(),
                    off: at,
                    size: s.size,
                    code: fn_code,
                    words: fn_words,
                    relocs: fn_relocs,
                });
            }
        }
        let mut seen_data_sym = HashSet::new();
        for s in &o.symbols {
            if s.kind != SymKind::Object || s.size == 0 {
                continue;
            }
            let SymSection::Sec(i) = s.sec else { continue };
            let (Some(sec), Some(off)) = (o.sections.get(i), offs.get(i).copied().flatten())
            else {
                continue;
            };
            let Some(sec_kind @ (SecKind::Rodata | SecKind::Data | SecKind::Bss)) = sec.kind()
            else {
                continue;
            };
            let at = off + s.value;
            if at < data_off
                || s.value + s.size > sec.size
                || count.get(s.name.as_str()) != Some(&1)
                || first_sym_off.get(s.name.as_str()) != Some(&at)
                || (s.bind != SymBind::Local && globals.get(s.name.as_str()) != Some(&at))
                || !seen_data_sym.insert(s.name.as_str())
            {
                continue;
            }
            let align = (1u64 << at.trailing_zeros().min(63)).min(sec.align.max(1));
            let (read_only, bytes_len, zero_tail) = match sec_kind {
                SecKind::Rodata => (true, s.size, 0),
                SecKind::Data => (false, s.size, 0),
                SecKind::Bss => (false, 0, s.size),
                _ => unreachable!(),
            };
            let rel_off = at - data_off;
            if (bytes_len > 0 && rel_off + bytes_len > data.len() as u64)
                || rel_off + bytes_len + zero_tail > data.len() as u64 + (data_end - data_bytes_end)
            {
                continue;
            }
            let mut d_relocs = Vec::new();
            let mut expected_data_relocs = Vec::new();
            let mut ok = true;
            for r in &sec.relocs {
                if r.rtype == RelocType::None {
                    continue;
                }
                let w = reloc_width(sec_kind, r.rtype);
                if r.offset + w <= s.value || r.offset >= s.value + s.size {
                    continue;
                }
                if sec_kind == SecKind::Bss || r.offset < s.value || r.offset + w > s.value + s.size
                {
                    ok = false;
                    break;
                }
                let roff = r.offset - s.value;
                let Ok(base_t) = resolve(o, offs, r.sym) else {
                    ok = false;
                    break;
                };
                let actual_t = base_t.wrapping_add(r.addend as u64);
                let Some(entry) = build_reloc_entry(
                    o,
                    offs,
                    r,
                    roff,
                    actual_t,
                    &unique_obj_sym_off,
                    &first_sym_off,
                    &first_stub_off,
                    &first_ext_data_off,
                ) else {
                    ok = false;
                    break;
                };
                match entry.kind {
                    RelocKind::Abs64 => expected_data_relocs.push(DataReloc {
                        off: rel_off + roff,
                        width: 8,
                        target: actual_t,
                    }),
                    RelocKind::Abs32 => expected_data_relocs.push(DataReloc {
                        off: rel_off + roff,
                        width: 4,
                        target: actual_t,
                    }),
                    RelocKind::Prel32 => {
                        let d = actual_t.wrapping_sub(at + roff) as i64;
                        if !(-(1i64 << 31)..(1i64 << 31)).contains(&d) {
                            ok = false;
                            break;
                        }
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
                d_relocs.push(entry);
            }
            let total_len = bytes_len + zero_tail;
            let window_relocs: Vec<DataReloc> = relocs
                .iter()
                .copied()
                .filter(|lr| !(lr.off + lr.width <= rel_off || rel_off + total_len <= lr.off))
                .collect();
            if ok && window_relocs == expected_data_relocs {
                data_syms.push(SymDataInfo {
                    sym: s.name.clone(),
                    align,
                    read_only,
                    off: at,
                    bytes_len,
                    zero_tail,
                    relocs: d_relocs,
                });
            }
        }
        objects.push(ObjectInfo {
            name: o.name.clone(),
            fns,
            call_fns,
            reloc_fns,
            data_syms,
        });
    }

    let li = LinkedImage {
        code,
        data_off,
        data,
        bss: data_end - data_bytes_end,
        ro_data,
        extern_data,
        got_off,
        got,
        relocs,
        symbols,
        obj_symbols,
        stubs,
        objects,
        sec_off,
        extern_tls,
    };
    check_well_formed(&li)?;
    Ok(li)
}

/// The checks of `Arm64.Obj.LinkedImage.wellFormed`, so that a malformed image is reported
/// here rather than making every `Obj.Loads` hypothesis unsatisfiable.
fn check_well_formed(li: &LinkedImage) -> Result<()> {
    let code_len = li.code.len() as u64;
    let data_len = li.data.len() as u64;
    let ok = code_len <= li.data_off
        && li.data_off % PAGE_SIZE == 0
        && li.data_end() <= li.got_off
        && li.got_off % 8 == 0
        && li
            .ro_data
            .iter()
            .all(|&(o, n)| li.data_off <= o && o + n <= li.data_end())
        && li
            .extern_data
            .iter()
            .all(|(_, o, n)| li.data_end() <= *o && o + n <= li.got_off)
        && li
            .relocs
            .iter()
            .all(|r| (r.width == 8 || r.width == 4) && r.off + r.width <= data_len)
        && li.stubs.iter().all(|(_, s)| s + 4 <= code_len);
    if !ok {
        bail!("internal error: the linked image is malformed");
    }
    for o in &li.objects {
        for f in &o.fns {
            if f.off % 4 != 0
                || f.off + f.size > code_len
                || li.stubs.iter().any(|(_, s)| f.off <= *s && *s < f.off + f.size)
            {
                bail!(
                    "internal error: function {} of {} is not honoured",
                    f.name,
                    o.name
                );
            }
        }
        for f in &o.call_fns {
            if f.off % 4 != 0
                || f.size % 4 != 0
                || f.off + f.size > code_len
                || li.stubs.iter().any(|(_, s)| f.off <= *s && *s < f.off + f.size)
            {
                bail!(
                    "internal error: call function {} of {} is not honoured",
                    f.name,
                    o.name
                );
            }
        }
        for f in &o.reloc_fns {
            if f.off % 4 != 0
                || f.size % 4 != 0
                || f.code.len() as u64 != f.size
                || f.words.len() * 4 != f.code.len()
                || f.off + f.size > code_len
                || li.stubs.iter().any(|(_, s)| f.off <= *s && *s < f.off + f.size)
                || f.relocs.iter().any(|r| r.off % 4 != 0 || r.off + 4 > f.size)
            {
                bail!(
                    "internal error: relocated function {} of {} is not honoured",
                    f.sym,
                    o.name
                );
            }
        }
        for d in &o.data_syms {
            let total_len = d.bytes_len + d.zero_tail;
            if d.align == 0
                || d.off % d.align != 0
                || d.off < li.data_off
                || (d.bytes_len > 0 && d.off - li.data_off + d.bytes_len > data_len)
                || d.off - li.data_off + total_len > data_len + li.bss
            {
                bail!(
                    "internal error: data symbol {} of {} is not honoured",
                    d.sym,
                    o.name
                );
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lean rendering of the linked image
// ---------------------------------------------------------------------------

fn render_reloc_entry(r: &RelocEntry) -> String {
    let mut parts = vec![
        format!("off := {}", r.off),
        format!("kind := {}", r.kind.lean_name()),
        format!("sym := {}", lean_string_lit(&r.sym)),
    ];
    if r.addend != 0 {
        parts.push(format!("addend := {}", r.addend));
    }
    if r.local_sym {
        parts.push("localSym := true".to_string());
    }
    format!("{{ {} }}", parts.join(", "))
}

fn file_name(p: &std::path::Path) -> String {
    p.file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .into_owned()
}

fn push_list(lines: &mut Vec<String>, field: &str, items: Vec<String>) {
    if items.is_empty() {
        lines.push(format!("  {field} := []"));
        return;
    }
    lines.push(format!("  {field} := ["));
    let n = items.len();
    for (i, it) in items.into_iter().enumerate() {
        let sep = if i + 1 < n { "," } else { "]" };
        lines.push(format!("    {it}{sep}"));
    }
}

fn pairs(xs: &[(String, u64)]) -> Vec<String> {
    xs.iter()
        .map(|(n, o)| format!("({}, {o})", lean_string_lit(n)))
        .collect()
}

/// Lean definitions of the `ObjectInfo` of each object and of the `LinkedImage` of `meta`.
/// Byte contents are read with `include_bytes%` from `meta.code_bin_file()` and
/// `meta.data_bin_file()`, whose contents are `li.code` and `li.data`.
pub fn render_image(meta: &ObjModuleMeta, li: &LinkedImage) -> Vec<String> {
    let code_bin = lean_string_lit(&file_name(&meta.code_bin_file()));
    let data_bin = lean_string_lit(&file_name(&meta.data_bin_file()));
    let n = li.objects.len();
    let mut l = Vec::new();
    for o in &li.objects {
        let def = meta.obj_def_name_for(&o.name, n);
        l.push(format!(
            "/-- The relocation-free exported functions of object `{}`. -/",
            o.name.replace("-/", "- /")
        ));
        l.push(format!("noncomputable def {def} : Obj.ObjectInfo where"));
        l.push(format!("  name := {}", lean_string_lit(&o.name)));
        push_list(
            &mut l,
            "fns",
            o.fns
                .iter()
                .map(|f| {
                    format!(
                        "({}, include_bytes% {code_bin} {} {})",
                        lean_string_lit(&f.name),
                        f.off,
                        f.size
                    )
                })
                .collect(),
        );
        if !o.call_fns.is_empty() {
            push_list(
                &mut l,
                "callFns",
                o.call_fns
                    .iter()
                    .map(|f| {
                        let calls = f
                            .calls
                            .iter()
                            .map(|(roff, sym)| format!("({roff}, {})", lean_string_lit(sym)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "({}, include_bytes% {code_bin} {} {}, [{calls}])",
                            lean_string_lit(&f.name),
                            f.off,
                            f.size
                        )
                    })
                    .collect(),
            );
        }
        if !o.reloc_fns.is_empty() {
            push_list(
                &mut l,
                "relocFns",
                o.reloc_fns
                    .iter()
                    .map(|f| {
                        let rels = f
                            .relocs
                            .iter()
                            .map(render_reloc_entry)
                            .collect::<Vec<_>>()
                            .join(", ");
                        let live_slice = &li.code[f.off as usize..(f.off + f.size) as usize];
                        let code_expr = if f.code.as_slice() == live_slice {
                            format!("include_bytes% {code_bin} {} {}", f.off, f.size)
                        } else {
                            let bytes = f
                                .code
                                .iter()
                                .map(|b| format!("{b:#04x}#8"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            format!("[{bytes}]")
                        };
                        format!(
                            "{{ sym := {}, code := {code_expr}, relocs := [{rels}] }}",
                            lean_string_lit(&f.sym),
                        )
                    })
                    .collect(),
            );
        }
        if !o.data_syms.is_empty() {
            push_list(
                &mut l,
                "dataSyms",
                o.data_syms
                    .iter()
                    .map(|d| {
                        let rels = d
                            .relocs
                            .iter()
                            .map(render_reloc_entry)
                            .collect::<Vec<_>>()
                            .join(", ");
                        let bytes_expr = if d.bytes_len == 0 {
                            "[]".to_string()
                        } else {
                            format!(
                                "include_bytes% {data_bin} {} {}",
                                d.off - li.data_off,
                                d.bytes_len
                            )
                        };
                        format!(
                            "{{ sym := {}, align := {}, readOnly := {}, bytes := {bytes_expr}, zeroTail := {}, relocs := [{rels}] }}",
                            lean_string_lit(&d.sym),
                            d.align,
                            d.read_only,
                            d.zero_tail
                        )
                    })
                    .collect(),
            );
        }
        l.push(String::new());
    }
    l.push(format!(
        "/-- The linked image of {}. -/",
        meta.title.replace("-/", "- /")
    ));
    l.push(format!(
        "noncomputable def {} : Obj.LinkedImage where",
        meta.image_def_name()
    ));
    l.push(format!(
        "  code := include_bytes% {code_bin} 0 {}",
        li.code.len()
    ));
    l.push(format!("  dataOff := {:#x}", li.data_off));
    l.push(format!(
        "  data := include_bytes% {data_bin} 0 {}",
        li.data.len()
    ));
    l.push(format!("  bss := {}", li.bss));
    push_list(
        &mut l,
        "roData",
        li.ro_data
            .iter()
            .map(|(o, n)| format!("({o:#x}, {n})"))
            .collect(),
    );
    push_list(
        &mut l,
        "externData",
        li.extern_data
            .iter()
            .map(|(x, o, n)| format!("({}, {o:#x}, {n})", lean_string_lit(x)))
            .collect(),
    );
    l.push(format!("  gotOff := {:#x}", li.got_off));
    push_list(
        &mut l,
        "got",
        li.got
            .iter()
            .map(|e| match e {
                GotEntry::Addr(off) => format!(".addr {off:#x}"),
                GotEntry::TpOff(v) => format!(".tpoff {v:#x}"),
            })
            .collect(),
    );
    push_list(
        &mut l,
        "relocs",
        li.relocs
            .iter()
            .map(|r| {
                format!(
                    "{{ off := {:#x}, width := {}, target := {:#x} }}",
                    r.off, r.width, r.target
                )
            })
            .collect(),
    );
    push_list(&mut l, "symbols", pairs(&li.symbols));
    push_list(
        &mut l,
        "objSymbols",
        li.obj_symbols
            .iter()
            .map(|(o, syms)| {
                if syms.is_empty() {
                    format!("({}, [])", lean_string_lit(o))
                } else {
                    format!("({}, [{}])", lean_string_lit(o), pairs(syms).join(", "))
                }
            })
            .collect(),
    );
    push_list(&mut l, "stubs", pairs(&li.stubs));
    push_list(
        &mut l,
        "objects",
        li.objects
            .iter()
            .map(|o| meta.obj_def_name_for(&o.name, n))
            .collect(),
    );
    l.push(String::new());
    l
}

/// Render the legacy Lean module defining the linked image `li` of the objects of `meta`
/// (see [`render_image`]).
pub fn render_obj_module(meta: &ObjModuleMeta, ex: &Extraction, li: &LinkedImage) -> String {
    let mut lines = Vec::new();
    if !meta.license_header.is_empty() {
        lines.push("/-".to_string());
        lines.extend(meta.license_header.iter().map(|l| doc_safe(l)));
        lines.push("-/".to_string());
    }
    lines.extend([
        "module".to_string(),
        String::new(),
        "public import Arm64".to_string(),
        "public import Arm64.Legacy".to_string(),
        "public import Arm64.Trusted.Surface.IncludeBytes".to_string(),
        String::new(),
        format!("/-! # Linked Image ({})", doc_safe(&meta.title)),
        String::new(),
        "Generated by `rust-obj2lean`, which `lake build` runs before compiling this library."
            .into(),
        "DO NOT EDIT MANUALLY and do not commit it: this file is a gitignored build product,"
            .into(),
        "regenerated from the Rust sources on every build. The objects below were linked by the"
            .into(),
        "legacy Rust linker (`tools/rust-obj2lean/src/untrusted_legacy_linker/`); code and data bytes are"
            .into(),
        "read from the `.code.bin` and `.data.bin` files next to this file.".into(),
        String::new(),
        "## Provenance".into(),
        String::new(),
    ]);
    for (k, v) in &ex.provenance {
        lines.push(format!("* **{}**: {}", doc_safe(k), doc_safe(v)));
    }
    if !ex.externs.is_empty() {
        lines.extend([String::new(), "## Externs".into(), String::new()]);
        for x in &ex.externs {
            lines.push(format!(
                "* `{}` ({}, {} bytes): {}",
                doc_safe(&x.name).replace('`', "'"),
                x.kind.as_str(),
                x.size,
                doc_safe(&x.origin)
            ));
        }
    }
    lines.extend([
        "-/".into(),
        String::new(),
        "@[expose] public section".into(),
        String::new(),
        format!("namespace {}", meta.namespace_prefix),
        String::new(),
        "open Arm64".into(),
        String::new(),
        "set_option maxHeartbeats 10000000".into(),
        "set_option maxRecDepth 2000000".into(),
        String::new(),
    ]);
    lines.extend(render_image(meta, li));
    lines.extend([format!("end {}", meta.namespace_prefix), String::new()]);
    lines.join("\n")
}

/// Emit the legacy `<ObjName>Obj.lean` source and its `.code.bin` and `.data.bin` binary
/// sidecars: `((obj_file, lean_src), (code_bin_file, code_bytes), (data_bin_file, data_bytes))`.
pub fn emit_obj_lean_module(
    meta: &ObjModuleMeta,
    ex: &Extraction,
    li: &LinkedImage,
) -> ((PathBuf, String), (PathBuf, Vec<u8>), (PathBuf, Vec<u8>)) {
    (
        (meta.obj_file.clone(), render_obj_module(meta, ex, li)),
        (meta.code_bin_file(), li.code.clone()),
        (meta.data_bin_file(), li.data.clone()),
    )
}

#[cfg(test)]
mod tests;
