// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Placement witness extraction from a stock-linked ELF (`[OUTSIDE TCB]`).
//!
//! Given a placed library (`model::PLib`) and the bytes of a static executable that links it,
//! reads off an `Arm64.Obj.Placement`:
//! - `base`: from the unique global `STT_FUNC` `.symtab` entry of an export, minus its block
//!   offset (all exports must agree);
//! - `ρ`: the address of every non-block symbol a relocation or data object uses, decoded from the
//!   relocated instruction fields in the ELF (branch / `ADR` / imm19 / imm14 immediates give the
//!   target directly, an `ADRP` page plus a `:lo12:` field of the same symbol give it jointly), then
//!   from relocated data words, then from the ELF `.symtab` (local symbols included, matched by
//!   stable demangled name and size) and finally by a unique aligned search for the object's bytes;
//! - `relax`: the relaxable `ADRP`+`ADD` pairs whose `ADRP` site holds `NOP` in the ELF;
//! - `b2b`: the branches to a block `B` whose ELF word branches to that `B`'s target instead.
//!
//! The result is then re-checked in full with the mirror of the Lean definitions (`patch`):
//! `Placeable`, every patched text and data byte against the ELF's `PT_LOAD` image (as
//! `ElfImage.parse` builds it, with the required permissions), and the export `.symtab` entries.
//! Any disagreement is an error (fail closed); the kernel re-checks the emitted witness anyway.

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context, Result, bail, ensure};

use super::model::{PLib, PMultiLib, PReloc, stable_demangled};
use super::patch::{NOP, PMultiPlacement, PPlacement, is_add_imm64, is_adrp, page_of};
use crate::trusted_common::RelocKind;

/// `Perm` of a `PT_LOAD` segment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Perm {
    pub r: bool,
    pub w: bool,
    pub x: bool,
}

/// One `Snapshot.Region` built by `ElfImage.parse`.
#[derive(Clone, Debug)]
pub struct Region {
    pub start: u64,
    pub perm: Perm,
    pub bytes: Vec<u8>,
}

/// One `.symtab` entry.
#[derive(Clone, Debug)]
pub struct ElfSym {
    pub name: String,
    pub value: u64,
    pub size: u64,
    /// `st_info & 0xf`.
    pub kind: u8,
    pub shndx: u16,
    /// Index `≥ sh_info` (the part `ElfImage.parse` reads).
    pub global_part: bool,
}

/// The parts of `ElfImage` the witness needs.
#[derive(Clone, Debug)]
pub struct Elf {
    pub regions: Vec<Region>,
    pub syms: Vec<ElfSym>,
}

fn u16_at(b: &[u8], o: usize) -> u64 {
    b.get(o..o + 2)
        .map_or(0, |s| u16::from_le_bytes([s[0], s[1]]) as u64)
}
fn u32_at(b: &[u8], o: usize) -> u64 {
    b.get(o..o + 4)
        .map_or(0, |s| u32::from_le_bytes(s.try_into().unwrap()) as u64)
}
fn u64_at(b: &[u8], o: usize) -> u64 {
    b.get(o..o + 8)
        .map_or(0, |s| u64::from_le_bytes(s.try_into().unwrap()))
}

const PAGE: u64 = 0x1000;

impl Elf {
    /// Parse like `ElfImage.parse` (regions and `.symtab`; header checks reduced to what the
    /// witness relies on).
    pub fn parse(b: &[u8]) -> Result<Elf> {
        ensure!(b.len() >= 64 && &b[..4] == b"\x7fELF", "not an ELF file");
        ensure!(b[4] == 2 && b[5] == 1, "not ELF64 little-endian");
        ensure!(u16_at(b, 16) == 2, "not ET_EXEC");
        ensure!(u16_at(b, 18) == 183, "not EM_AARCH64");
        let phoff = u64_at(b, 32) as usize;
        let shoff = u64_at(b, 40) as usize;
        let phnum = u16_at(b, 56) as usize;
        let shnum = u16_at(b, 60) as usize;
        let mut regions: Vec<Region> = Vec::new();
        for i in 0..phnum {
            let ph = phoff + 56 * i;
            if u32_at(b, ph) != 1 {
                continue;
            }
            let flags = u32_at(b, ph + 4);
            let off = u64_at(b, ph + 8);
            let vaddr = u64_at(b, ph + 16);
            let filesz = u64_at(b, ph + 32);
            let memsz = u64_at(b, ph + 40);
            if memsz == 0 {
                continue;
            }
            ensure!(
                off + filesz <= b.len() as u64 && filesz <= memsz,
                "bad PT_LOAD"
            );
            let perm = Perm {
                r: flags & 4 != 0,
                w: flags & 2 != 0,
                x: flags & 1 != 0,
            };
            let page_start = vaddr & !(PAGE - 1);
            let lead = vaddr - page_start;
            let page_end = (vaddr + memsz).div_ceil(PAGE) * PAGE;
            let size = page_end - page_start;
            let bytes = if filesz == memsz {
                let fs = (off - lead) as usize;
                let avail = (size as usize).min(b.len() - fs);
                let mut v = b[fs..fs + avail].to_vec();
                v.resize(size as usize, 0);
                v
            } else if filesz > 0 {
                let fs = (off - lead) as usize;
                let fl = (off + filesz) as usize - fs;
                let mut v = b[fs..fs + fl].to_vec();
                v.resize(v.len() + (page_end - (vaddr + filesz)) as usize, 0);
                v
            } else {
                vec![0; size as usize]
            };
            let r = Region {
                start: page_start,
                perm,
                bytes,
            };
            // `insertRegionSorted`.
            let pos = regions
                .iter()
                .position(|x| r.start <= x.start)
                .unwrap_or(regions.len());
            regions.insert(pos, r);
        }
        for w in regions.windows(2) {
            ensure!(
                w[0].start + w[0].bytes.len() as u64 <= w[1].start,
                "overlapping PT_LOAD regions"
            );
        }
        // `.symtab` (first `SHT_SYMTAB`).
        let mut syms = Vec::new();
        for i in 0..shnum {
            let sh = shoff + 64 * i;
            if u32_at(b, sh + 4) != 2 {
                continue;
            }
            let (so, ss, link, info) = (
                u64_at(b, sh + 24) as usize,
                u64_at(b, sh + 32) as usize,
                u32_at(b, sh + 40) as usize,
                u32_at(b, sh + 44) as usize,
            );
            let str_sh = shoff + 64 * link;
            let (stro, strs) = (
                u64_at(b, str_sh + 24) as usize,
                u64_at(b, str_sh + 32) as usize,
            );
            let strtab = b.get(stro..stro + strs).context("bad .strtab")?;
            for k in 0..ss / 24 {
                let e = so + 24 * k;
                let name_off = u32_at(b, e) as usize;
                let name = strtab
                    .get(name_off..)
                    .and_then(|s| s.split(|c| *c == 0).next())
                    .map(|s| String::from_utf8_lossy(s).into_owned())
                    .unwrap_or_default();
                syms.push(ElfSym {
                    name,
                    value: u64_at(b, e + 8),
                    size: u64_at(b, e + 16),
                    kind: (b[e + 4] & 0xf),
                    shndx: u16_at(b, e + 6) as u16,
                    global_part: k >= info,
                });
            }
            break;
        }
        Ok(Elf { regions, syms })
    }

    /// `Snapshot.cellAt`: `(perm, byte)` at `addr` from the first region containing it.
    pub fn cell_at(&self, addr: u64) -> Option<(Perm, u8)> {
        self.regions.iter().find_map(|r| {
            let d = addr.wrapping_sub(r.start);
            (d < r.bytes.len() as u64).then(|| (r.perm, r.bytes[d as usize]))
        })
    }

    fn read(&self, addr: u64, n: usize) -> Option<Vec<u8>> {
        (0..n as u64)
            .map(|i| self.cell_at(addr.wrapping_add(i)).map(|c| c.1))
            .collect()
    }

    fn word(&self, addr: u64) -> Option<u32> {
        self.read(addr, 4)
            .map(|v| u32::from_le_bytes(v.try_into().unwrap()))
    }

    /// `ElfImage.symbols`: defined `STT_FUNC` entries of the global part with a name.
    pub fn image_symbols(&self) -> impl Iterator<Item = &ElfSym> {
        self.syms
            .iter()
            .filter(|s| s.global_part && s.kind == 2 && s.shndx != 0 && !s.name.is_empty())
    }
}

fn sext(v: u64, bits: u32) -> i64 {
    ((v << (64 - bits)) as i64) >> (64 - bits)
}

/// Decoded immediate of a relocated instruction word.
enum Field {
    /// Full target address.
    Exact(u64),
    /// `ADRP`: the target's page.
    Page(u64),
    /// `:lo12:` field: `(target & 0xfff) >> scale`.
    Lo12(u32, u64),
}

fn decode(kind: RelocKind, w: u32, place: u64) -> Option<Field> {
    use RelocKind::*;
    let w = w as u64;
    Some(match kind {
        Call26 | Jump26 => Field::Exact(place.wrapping_add((sext(w & 0x3ff_ffff, 26) << 2) as u64)),
        AdrpHi21 | AdrpHi21Nc | AdrGotPage | TlsieAdrGottprelPage21 => {
            let imm = (((w >> 5) & 0x7ffff) << 2) | ((w >> 29) & 3);
            Field::Page(page_of(place).wrapping_add((sext(imm, 21) << 12) as u64))
        }
        AdrPrelLo21 => {
            let imm = (((w >> 5) & 0x7ffff) << 2) | ((w >> 29) & 3);
            Field::Exact(place.wrapping_add(sext(imm, 21) as u64))
        }
        AddLo12 | Ldst8Lo12 => Field::Lo12(0, (w >> 10) & 0xfff),
        Ldst16Lo12 => Field::Lo12(1, (w >> 10) & 0xfff),
        Ldst32Lo12 => Field::Lo12(2, (w >> 10) & 0xfff),
        Ldst64Lo12 | Ld64GotLo12Nc | TlsieLd64GottprelLo12Nc => Field::Lo12(3, (w >> 10) & 0xfff),
        Ldst128Lo12 => Field::Lo12(4, (w >> 10) & 0xfff),
        Condbr19 | LdPrelLo19 => {
            Field::Exact(place.wrapping_add((sext((w >> 5) & 0x7ffff, 19) << 2) as u64))
        }
        Tstbr14 => Field::Exact(place.wrapping_add((sext((w >> 5) & 0x3fff, 14) << 2) as u64)),
        TlsleAddTprelLo12 => Field::Exact((w >> 10) & 0xfff),
        Prel32
        | Abs64
        | Abs32
        | TlsdescAdrPage21
        | TlsdescLd64Lo12
        | TlsdescAddLo12
        | TlsdescCall
        | TlsleAddTprelHi12
        | TlsleAddTprelLo12Nc
        | TlsleLdst8TprelLo12Nc
        | TlsleLdst16TprelLo12Nc
        | TlsleLdst32TprelLo12Nc
        | TlsleLdst64TprelLo12Nc
        | TlsleLdst128TprelLo12Nc
        | TlsleMovwTprelG1
        | TlsleMovwTprelG1Nc
        | TlsleMovwTprelG0
        | TlsleMovwTprelG0Nc => return None,
    })
}

#[derive(Default)]
struct Constraints {
    exact: BTreeMap<String, u64>,
    pages: BTreeMap<String, Vec<(i64, u64)>>,
    lo12s: BTreeMap<String, Vec<(i64, u32, u64)>>,
    tls_hi16: BTreeMap<String, Vec<(i64, u64)>>,
    tls_lo16: BTreeMap<String, Vec<(i64, u64)>>,
}

impl Constraints {
    fn set(&mut self, sym: &str, v: u64, what: &str) -> Result<()> {
        if let Some(old) = self.exact.insert(sym.to_string(), v) {
            ensure!(old == v, "{what}: {sym} at both {old:#x} and {v:#x}");
        }
        Ok(())
    }
}

/// Extract the placement of `lib` in the ELF file `elf_bytes`, and check it.
pub fn extract(lib: &PLib, elf_bytes: &[u8]) -> Result<PPlacement> {
    extract_from(lib, &Elf::parse(elf_bytes)?)
}

/// `extract` for an already parsed ELF.
pub fn extract_from(lib: &PLib, elf: &Elf) -> Result<PPlacement> {
    let blk = &lib.text;
    // 1. Base, from the exports.
    let mut base = None;
    for e in &lib.exports {
        let off = blk
            .lookup(e)
            .with_context(|| format!("export {e} is not a block symbol"))?;
        let hits: Vec<&ElfSym> = elf.image_symbols().filter(|s| &s.name == e).collect();
        let [s] = hits.as_slice() else {
            bail!(
                "export {e} has {} global STT_FUNC .symtab entries, expected 1",
                hits.len()
            );
        };
        let b = s.value.wrapping_sub(off);
        if let Some(b0) = base {
            ensure!(
                b0 == b,
                "exports disagree on the block base ({b0:#x} vs {b:#x})"
            );
        }
        base = Some(b);
    }
    let base = base.context("library has no exports")?;
    let mut pl = PPlacement {
        base,
        ..Default::default()
    };

    // 2. Text: relaxation, branch-to-branch, and symbol constraints.
    let mut cs = Constraints::default();
    for r in &blk.relocs {
        let place = base.wrapping_add(r.off);
        let w = elf
            .word(place)
            .with_context(|| format!("relocation site {:#x} is not mapped", r.off))?;
        if (blk.relaxable_at(r.off) || blk.got_pair_at(r.off)) && w == NOP {
            pl.relax.insert(r.off);
            continue;
        }
        if blk.got_pair_at(r.off)
            && w != NOP
            && elf.word(place.wrapping_add(4)).is_some_and(is_add_imm64)
        {
            pl.relax.insert(r.off + 4);
        }
        if blk.tlsie_relaxable_at(r.off) {
            if r.kind == RelocKind::TlsieAdrGottprelPage21 && (w & 0xffe0_0000) == 0xd2a0_0000 {
                pl.relax.insert(r.off);
                cs.tls_hi16
                    .entry(r.sym.clone())
                    .or_default()
                    .push((r.addend, ((w >> 5) & 0xffff) as u64));
                continue;
            }
            if r.kind == RelocKind::TlsieLd64GottprelLo12Nc && (w & 0xffe0_0000) == 0xf280_0000 {
                pl.relax.insert(r.off);
                cs.tls_lo16
                    .entry(r.sym.clone())
                    .or_default()
                    .push((r.addend, ((w >> 5) & 0xffff) as u64));
                continue;
            }
        }
        let relaxed_adr = r.off >= 4
            && (blk.relaxable_at(r.off - 4) || blk.got_pair_at(r.off - 4))
            && pl.relax.contains(&(r.off - 4));
        let relaxed_got_add = r.off >= 4
            && blk.got_pair_at(r.off - 4)
            && !pl.relax.contains(&(r.off - 4))
            && pl.relax.contains(&r.off);
        let field = if relaxed_adr {
            decode(RelocKind::AdrPrelLo21, w, place)
        } else if relaxed_got_add {
            decode(RelocKind::AddLo12, w, place)
        } else {
            if matches!(
                r.kind,
                RelocKind::AdrpHi21
                    | RelocKind::AdrpHi21Nc
                    | RelocKind::AdrGotPage
                    | RelocKind::TlsieAdrGottprelPage21
            ) {
                ensure!(
                    is_adrp(w),
                    "site {:#x}: expected ADRP, found {w:#010x}",
                    r.off
                );
            }
            decode(r.kind, w, place)
        };
        let Some(field) = field else { continue };
        // A branch to a weak reference that lands on the next instruction: left undefined.
        if blk.weak_refs.contains(&r.sym)
            && matches!(r.kind, RelocKind::Call26 | RelocKind::Jump26)
            && matches!(field, Field::Exact(t) if t == place.wrapping_add(4))
        {
            pl.undef_weak.insert(r.sym.clone());
            continue;
        }
        let blk_addr = blk.lookup(&r.sym).map(|o| base.wrapping_add(o));
        match field {
            Field::Exact(t) => {
                if let Some(a) = blk_addr {
                    let expect = a.wrapping_add(r.addend as u64);
                    if t != expect {
                        let r2 = blk.b2b_next(r).with_context(|| {
                            format!(
                                "site {:#x} ({:?} to {}): ELF target {t:#x}, expected {expect:#x}",
                                r.off, r.kind, r.sym
                            )
                        })?;
                        pl.b2b.insert(r.off);
                        constrain_exact(&mut cs, blk, base, r2, t)?;
                    }
                } else {
                    cs.set(&r.sym, t.wrapping_sub(r.addend as u64), "text")?;
                }
            }
            Field::Page(p) => {
                if blk_addr.is_none() {
                    cs.pages
                        .entry(r.sym.clone())
                        .or_default()
                        .push((r.addend, p));
                }
            }
            Field::Lo12(scale, v) => {
                if blk_addr.is_none() {
                    cs.lo12s
                        .entry(r.sym.clone())
                        .or_default()
                        .push((r.addend, scale, v));
                }
            }
        }
    }
    // ADRP page + lo12 field -> exact.
    let pages_all = std::mem::take(&mut cs.pages);
    for (sym, pages) in &pages_all {
        if cs.exact.contains_key(sym) {
            continue;
        }
        let lo = cs
            .lo12s
            .get(sym)
            .with_context(|| format!("{sym}: ADRP page without a :lo12: use"))?;
        let (ap, page) = pages[0];
        let (al, scale, v) = lo[0];
        // sym + ap ∈ [page, page + 4096); (sym + al) & 0xfff = v << scale.
        let lo_bits = (v << scale) & 0xfff;
        let start = page.wrapping_sub(ap as u64);
        let want = lo_bits.wrapping_sub(al as u64) & 0xfff;
        let mut s = (start & !0xfff) | want;
        if s < start {
            s = s.wrapping_add(0x1000);
        }
        cs.set(sym, s, "adrp+lo12")?;
    }
    let tls_syms: BTreeSet<String> = cs
        .tls_hi16
        .keys()
        .chain(cs.tls_lo16.keys())
        .cloned()
        .collect();
    for sym in &tls_syms {
        if cs.exact.contains_key(sym) {
            continue;
        }
        let hi_entries = cs.tls_hi16.get(sym).map_or(&[][..], |v| v.as_slice());
        let lo_entries = cs.tls_lo16.get(sym).map_or(&[][..], |v| v.as_slice());
        let (addend, hi16, lo16) = match (hi_entries.first(), lo_entries.first()) {
            (Some(&(ah, hi)), Some(&(_, lo))) => {
                let lo_match = lo_entries
                    .iter()
                    .find(|&&(al, _)| al == ah)
                    .map(|&(_, l)| l)
                    .unwrap_or(lo);
                (ah, hi, lo_match)
            }
            (Some(&(ah, hi)), None) => (ah, hi, 0),
            (None, Some(&(al, lo))) => (al, 0, lo),
            (None, None) => continue,
        };
        let t = (hi16 << 16) | lo16;
        cs.set(sym, t.wrapping_sub(addend as u64), "tlsie->tlsle")?;
    }
    for (sym, v) in &cs.exact {
        pl.rho.insert(sym.clone(), *v);
    }

    // 3. Data objects: relocated words, then .symtab names, then byte search.
    let block_syms: BTreeSet<&str> = blk.symbols.iter().map(|(n, _)| n.as_str()).collect();
    loop {
        let mut changed = false;
        for d in &lib.data {
            let Some(&addr) = pl.rho.get(&d.sym) else {
                continue;
            };
            for r in &d.relocs {
                if block_syms.contains(r.sym.as_str()) || pl.rho.contains_key(&r.sym) {
                    continue;
                }
                let at = addr.wrapping_add(r.off);
                let t = match r.kind {
                    RelocKind::Abs64 => elf
                        .read(at, 8)
                        .map(|v| u64::from_le_bytes(v.try_into().unwrap())),
                    RelocKind::Abs32 => elf
                        .read(at, 4)
                        .map(|v| u32::from_le_bytes(v.try_into().unwrap()) as u64),
                    RelocKind::Prel32 => elf.read(at, 4).map(|v| {
                        at.wrapping_add(i32::from_le_bytes(v.try_into().unwrap()) as i64 as u64)
                    }),
                    _ => None,
                };
                if let Some(t) = t {
                    pl.rho
                        .insert(r.sym.clone(), t.wrapping_sub(r.addend as u64));
                    changed = true;
                }
            }
        }
        if changed {
            continue;
        }
        // Fallbacks for one data object at a time, then re-run the relocation pass.
        let Some(d) = lib.data.iter().find(|d| !pl.rho.contains_key(&d.sym)) else {
            break;
        };
        let size = d.bytes.len() as u64 + d.zero_tail;
        let by_name: BTreeSet<u64> = elf
            .syms
            .iter()
            .filter(|s| s.shndx != 0 && s.kind != 2 && s.size == size)
            .filter(|s| {
                d.raw_names.contains(&s.name)
                    || d.demangled_names.contains(&stable_demangled(&s.name))
            })
            .map(|s| s.value)
            .collect();
        let addr = if by_name.len() == 1 {
            *by_name.iter().next().unwrap()
        } else {
            search_bytes(elf, &d.bytes, d.align, d.read_only)
                .with_context(|| format!("cannot locate data object {} in the ELF", d.sym))?
        };
        pl.rho.insert(d.sym.clone(), addr);
    }
    // Every referenced non-block symbol and extern must be placed.
    let refs = blk
        .relocs
        .iter()
        .chain(lib.data.iter().flat_map(|d| d.relocs.iter()))
        .map(|r| r.sym.as_str())
        .chain(blk.externs.iter().map(String::as_str));
    for s in refs {
        ensure!(
            block_syms.contains(s) || pl.rho.contains_key(s),
            "no address for {s}"
        );
    }

    check(lib, &pl, elf)?;
    Ok(pl)
}

fn constrain_exact(
    cs: &mut Constraints,
    blk: &super::model::PBlock,
    base: u64,
    r: &PReloc,
    t: u64,
) -> Result<()> {
    match blk.lookup(&r.sym) {
        Some(o) => {
            let expect = base.wrapping_add(o).wrapping_add(r.addend as u64);
            ensure!(
                t == expect,
                "branch-to-branch target {t:#x}, expected {expect:#x}"
            );
            Ok(())
        }
        None => cs.set(&r.sym, t.wrapping_sub(r.addend as u64), "branch-to-branch"),
    }
}

/// The unique `align`-aligned address of `needle` in the ELF's readable (`read_only`) or exactly
/// read-write regions.
fn search_bytes(elf: &Elf, needle: &[u8], align: u64, read_only: bool) -> Result<u64> {
    ensure!(!needle.is_empty(), "no bytes to search for");
    let mut hits = Vec::new();
    for r in &elf.regions {
        let ok = if read_only {
            r.perm.r
        } else {
            r.perm
                == Perm {
                    r: true,
                    w: true,
                    x: false,
                }
        };
        if !ok || r.bytes.len() < needle.len() {
            continue;
        }
        let mut i = 0u64;
        while i + needle.len() as u64 <= r.bytes.len() as u64 {
            let a = r.start + i;
            if a % align == 0 && &r.bytes[i as usize..i as usize + needle.len()] == needle {
                hits.push(a);
            }
            i += 1;
        }
    }
    match hits.as_slice() {
        [a] => Ok(*a),
        _ => bail!("{} aligned occurrences, expected 1", hits.len()),
    }
}

/// Check `Placeable` and `InElf` of `lib` under `pl` for the ELF `elf`.
pub fn check(lib: &PLib, pl: &PPlacement, elf: &Elf) -> Result<()> {
    lib.check_placeable(pl)
        .context("placement is not Placeable")?;
    let rx = Perm {
        r: true,
        w: false,
        x: true,
    };
    let rw = Perm {
        r: true,
        w: true,
        x: false,
    };
    let text = lib.text.patched(pl);
    for (i, b) in text.iter().enumerate() {
        let a = pl.base.wrapping_add(i as u64);
        let (p, v) = elf
            .cell_at(a)
            .with_context(|| format!("text byte {i:#x} at {a:#x} is not mapped"))?;
        ensure!(p == rx, "text byte {i:#x} at {a:#x} is not r-x");
        ensure!(
            v == *b,
            "text word at {:#x} (block offset {:#x}): ELF {:#010x}, model {:#010x}",
            a & !3,
            i & !3,
            elf.word(a & !3).unwrap_or(0),
            lib.text.patched_word(pl, (i & !3) as u64)
        );
    }
    for (k, d) in lib.data.iter().enumerate() {
        let addr = pl.rho(&d.sym);
        for (i, b) in lib.patched_data(pl, k).iter().enumerate() {
            let a = addr.wrapping_add(i as u64);
            let (p, v) = elf
                .cell_at(a)
                .with_context(|| format!("{} byte {i} at {a:#x} is not mapped", d.sym))?;
            ensure!(
                if d.read_only { p.r } else { p == rw },
                "{} byte {i} at {a:#x} has the wrong permission",
                d.sym
            );
            ensure!(
                v == *b,
                "{} byte {i} at {a:#x}: ELF {v:#04x}, model {b:#04x}",
                d.sym
            );
        }
    }
    for e in &lib.exports {
        let off = lib
            .text
            .lookup(e)
            .with_context(|| format!("export {e} not in block"))?;
        let hits: Vec<u64> = elf
            .image_symbols()
            .filter(|s| &s.name == e)
            .map(|s| s.value)
            .collect();
        ensure!(
            hits == [pl.base.wrapping_add(off)],
            "export {e}: .symtab entries {hits:x?}, expected [{:#x}]",
            pl.base.wrapping_add(off)
        );
    }
    Ok(())
}

/// Extract the multi-block placement of `lib` in `elf_bytes`, and check it.
pub fn extract_multi(lib: &PMultiLib, elf_bytes: &[u8]) -> Result<PMultiPlacement> {
    extract_multi_from(lib, &Elf::parse(elf_bytes)?)
}

fn record_sym_addr(
    lib: &PMultiLib,
    bases: &mut [Option<u64>],
    rho: &mut BTreeMap<String, u64>,
    sym: &str,
    addr: u64,
    what: &str,
) -> Result<bool> {
    if let Some((bi, off)) = lib.lookup_block_sym(sym) {
        let b = addr.wrapping_sub(off);
        if let Some(old) = bases[bi] {
            ensure!(old == b, "{what}: block {bi} ({sym}) at both {old:#x} and {b:#x}");
            Ok(false)
        } else {
            bases[bi] = Some(b);
            Ok(true)
        }
    } else if let Some(old) = rho.insert(sym.to_string(), addr) {
        ensure!(old == addr, "{what}: {sym} at both {old:#x} and {addr:#x}");
        Ok(false)
    } else {
        Ok(true)
    }
}

/// Check the `[placed] extern_boundary` functions (raw `.symtab` names) of a multi-block
/// library against a witness ELF: each has exactly one global defined `STT_FUNC` entry, and the
/// placement maps it, when it is an extern of the library, to that entry's address.
pub fn check_extern_boundary(raw: &[String], mpl: &PMultiPlacement, elf: &Elf) -> Result<()> {
    for b in raw {
        let hits: Vec<&ElfSym> = elf.image_symbols().filter(|s| &s.name == b).collect();
        let [s] = hits.as_slice() else {
            bail!(
                "extern_boundary {b} has {} global STT_FUNC .symtab entries, expected 1",
                hits.len()
            );
        };
        if let Some(&a) = mpl.rho.get(b) {
            ensure!(
                a == s.value,
                "extern_boundary {b} is placed at {a:#x} but its .symtab entry is {:#x}",
                s.value
            );
        }
    }
    Ok(())
}

/// `extract_multi` for an already parsed ELF.
pub fn extract_multi_from(lib: &PMultiLib, elf: &Elf) -> Result<PMultiPlacement> {
    let nb = lib.blocks.len();
    let mut bases: Vec<Option<u64>> = vec![None; nb];
    let mut relax: Vec<BTreeSet<u64>> = vec![BTreeSet::new(); nb];
    let mut b2b: Vec<BTreeSet<u64>> = vec![BTreeSet::new(); nb];
    let mut rho: BTreeMap<String, u64> = BTreeMap::new();
    let mut undef_weak: BTreeSet<String> = BTreeSet::new();
    for e in &lib.exports {
        let (bi, off) = lib
            .lookup_block_sym(e)
            .with_context(|| format!("export {e} is not a block symbol"))?;
        let elf_name = lib.elf_sym(e);
        let hits: Vec<&ElfSym> = elf.image_symbols().filter(|s| s.name == elf_name).collect();
        let [s] = hits.as_slice() else {
            bail!(
                "export {e} has {} global STT_FUNC .symtab entries, expected 1",
                hits.len()
            );
        };
        record_sym_addr(lib, &mut bases, &mut rho, e, s.value, "export")?;
        debug_assert_eq!(bases[bi], Some(s.value.wrapping_sub(off)));
    }
    let mut scanned = vec![false; nb];
    let mut cs = Constraints::default();
    loop {
        let mut changed = false;
        for bi in 0..nb {
            let Some(base) = bases[bi] else { continue };
            if scanned[bi] {
                continue;
            }
            scanned[bi] = true;
            changed = true;
            let blk = &lib.blocks[bi];
            for r in &blk.relocs {
                let place = base.wrapping_add(r.off);
                let w = elf.word(place).with_context(|| {
                    format!("block {bi} relocation site {:#x} is not mapped", r.off)
                })?;
                if (blk.relaxable_at(r.off) || blk.got_pair_at(r.off)) && w == NOP {
                    relax[bi].insert(r.off);
                    continue;
                }
                if blk.got_pair_at(r.off)
                    && w != NOP
                    && elf.word(place.wrapping_add(4)).is_some_and(is_add_imm64)
                {
                    relax[bi].insert(r.off + 4);
                }
                if blk.tlsie_relaxable_at(r.off) {
                    if r.kind == RelocKind::TlsieAdrGottprelPage21
                        && (w & 0xffe0_0000) == 0xd2a0_0000
                    {
                        relax[bi].insert(r.off);
                        cs.tls_hi16
                            .entry(r.sym.clone())
                            .or_default()
                            .push((r.addend, ((w >> 5) & 0xffff) as u64));
                        continue;
                    }
                    if r.kind == RelocKind::TlsieLd64GottprelLo12Nc
                        && (w & 0xffe0_0000) == 0xf280_0000
                    {
                        relax[bi].insert(r.off);
                        cs.tls_lo16
                            .entry(r.sym.clone())
                            .or_default()
                            .push((r.addend, ((w >> 5) & 0xffff) as u64));
                        continue;
                    }
                }
                let relaxed_adr = r.off >= 4
                    && (blk.relaxable_at(r.off - 4) || blk.got_pair_at(r.off - 4))
                    && relax[bi].contains(&(r.off - 4));
                let relaxed_got_add = r.off >= 4
                    && blk.got_pair_at(r.off - 4)
                    && !relax[bi].contains(&(r.off - 4))
                    && relax[bi].contains(&r.off);
                let field = if relaxed_adr {
                    decode(RelocKind::AdrPrelLo21, w, place)
                } else if relaxed_got_add {
                    decode(RelocKind::AddLo12, w, place)
                } else {
                    if matches!(
                        r.kind,
                        RelocKind::AdrpHi21
                            | RelocKind::AdrpHi21Nc
                            | RelocKind::AdrGotPage
                            | RelocKind::TlsieAdrGottprelPage21
                    ) {
                        ensure!(
                            is_adrp(w),
                            "block {bi} site {:#x}: expected ADRP, found {w:#010x}",
                            r.off
                        );
                    }
                    decode(r.kind, w, place)
                };
                let Some(field) = field else { continue };
                // A branch to a weak reference that lands on the next instruction: left undefined.
                if blk.weak_refs.contains(&r.sym)
                    && matches!(r.kind, RelocKind::Call26 | RelocKind::Jump26)
                    && matches!(field, Field::Exact(t) if t == place.wrapping_add(4))
                {
                    undef_weak.insert(r.sym.clone());
                    continue;
                }
                let blk_addr = blk.lookup(&r.sym).map(|o| base.wrapping_add(o));
                match field {
                    Field::Exact(t) => {
                        if let Some(a) = blk_addr {
                            let expect = a.wrapping_add(r.addend as u64);
                            if t != expect {
                                let r2 = blk.b2b_next(r).with_context(|| {
                                    format!(
                                        "block {bi} site {:#x} ({:?} to {}): ELF target {t:#x}, expected {expect:#x}",
                                        r.off, r.kind, r.sym
                                    )
                                })?;
                                b2b[bi].insert(r.off);
                                constrain_exact(&mut cs, blk, base, r2, t)?;
                            }
                        } else {
                            cs.set(&r.sym, t.wrapping_sub(r.addend as u64), "text")?;
                        }
                    }
                    Field::Page(p) if blk_addr.is_none() => {
                        cs.pages.entry(r.sym.clone()).or_default().push((r.addend, p));
                    }
                    Field::Lo12(scale, v) if blk_addr.is_none() => {
                        cs.lo12s
                            .entry(r.sym.clone())
                            .or_default()
                            .push((r.addend, scale, v));
                    }
                    _ => {}
                }
            }
        }
        let page_syms: Vec<String> = cs.pages.keys().cloned().collect();
        for sym in page_syms {
            if cs.exact.contains_key(&sym) {
                continue;
            }
            if let Some(lo) = cs.lo12s.get(&sym) {
                let (ap, page) = cs.pages[&sym][0];
                let (al, scale, v) = lo[0];
                let lo_bits = (v << scale) & 0xfff;
                let start = page.wrapping_sub(ap as u64);
                let want = lo_bits.wrapping_sub(al as u64) & 0xfff;
                let mut s = (start & !0xfff) | want;
                if s < start {
                    s = s.wrapping_add(0x1000);
                }
                cs.set(&sym, s, "adrp+lo12")?;
            }
        }
        let tls_syms: BTreeSet<String> = cs
            .tls_hi16
            .keys()
            .chain(cs.tls_lo16.keys())
            .cloned()
            .collect();
        for sym in &tls_syms {
            if cs.exact.contains_key(sym) {
                continue;
            }
            let hi_entries = cs.tls_hi16.get(sym).map_or(&[][..], |v| v.as_slice());
            let lo_entries = cs.tls_lo16.get(sym).map_or(&[][..], |v| v.as_slice());
            let (addend, hi16, lo16) = match (hi_entries.first(), lo_entries.first()) {
                (Some(&(ah, hi)), Some(&(_, lo))) => {
                    let lo_match = lo_entries
                        .iter()
                        .find(|&&(al, _)| al == ah)
                        .map(|&(_, l)| l)
                        .unwrap_or(lo);
                    (ah, hi, lo_match)
                }
                (Some(&(ah, hi)), None) => (ah, hi, 0),
                (None, Some(&(al, lo))) => (al, 0, lo),
                (None, None) => continue,
            };
            let t = (hi16 << 16) | lo16;
            cs.set(sym, t.wrapping_sub(addend as u64), "tlsie->tlsle")?;
        }
        let exact_now: Vec<(String, u64)> = cs.exact.iter().map(|(k, v)| (k.clone(), *v)).collect();
        for (sym, v) in exact_now {
            if record_sym_addr(lib, &mut bases, &mut rho, &sym, v, "text")? {
                changed = true;
            }
        }
        for d in &lib.data {
            let Some(&addr) = rho.get(&d.sym) else {
                continue;
            };
            for r in &d.relocs {
                let at = addr.wrapping_add(r.off);
                let t = match r.kind {
                    RelocKind::Abs64 => elf
                        .read(at, 8)
                        .map(|v| u64::from_le_bytes(v.try_into().unwrap())),
                    RelocKind::Abs32 => elf
                        .read(at, 4)
                        .map(|v| u32::from_le_bytes(v.try_into().unwrap()) as u64),
                    RelocKind::Prel32 => elf.read(at, 4).map(|v| {
                        at.wrapping_add(i32::from_le_bytes(v.try_into().unwrap()) as i64 as u64)
                    }),
                    _ => None,
                };
                if let Some(t) = t
                    && record_sym_addr(
                        lib,
                        &mut bases,
                        &mut rho,
                        &r.sym,
                        t.wrapping_sub(r.addend as u64),
                        "data",
                    )?
                {
                    changed = true;
                }
            }
        }
        if changed {
            continue;
        }
        if let Some(bi) = bases.iter().position(Option::is_none) {
            let blk = &lib.blocks[bi];
            let sz = blk.code.len() as u64;
            let mut found = BTreeSet::new();
            for (sym, off) in &blk.symbols {
                let raw = lib.block_raw.get(sym).map_or(sym.as_str(), String::as_str);
                for s in &elf.syms {
                    if s.shndx != 0
                        && s.kind == 2
                        && (s.name == raw || stable_demangled(&s.name) == *sym)
                        && (s.size == 0 || *off + s.size <= sz)
                    {
                        found.insert(s.value.wrapping_sub(*off));
                    }
                }
            }
            let found_vec: Vec<_> = found.into_iter().collect();
            let [b] = found_vec.as_slice() else {
                bail!("cannot locate code block {bi} in the ELF");
            };
            bases[bi] = Some(*b);
            continue;
        }
        let Some(d) = lib.data.iter().find(|d| !rho.contains_key(&d.sym)) else {
            break;
        };
        let size = d.bytes.len() as u64 + d.zero_tail;
        let by_name: BTreeSet<u64> = elf
            .syms
            .iter()
            .filter(|s| s.shndx != 0 && s.kind != 2 && s.size == size)
            .filter(|s| {
                d.raw_names.contains(&s.name)
                    || d.demangled_names.contains(&stable_demangled(&s.name))
            })
            .map(|s| s.value)
            .collect();
        let addr = if by_name.len() == 1 {
            *by_name.iter().next().unwrap()
        } else {
            search_bytes(elf, &d.bytes, d.align, d.read_only)
                .with_context(|| format!("cannot locate data object {} in the ELF", d.sym))?
        };
        rho.insert(d.sym.clone(), addr);
    }
    let bases: Vec<u64> = bases
        .into_iter()
        .enumerate()
        .map(|(i, b)| b.with_context(|| format!("missing base for block {i}")))
        .collect::<Result<_>>()?;
    for (sym, _) in &cs.pages {
        ensure!(
            lib.lookup_block_sym(sym).is_some() || rho.contains_key(sym),
            "{sym}: ADRP page without a :lo12: use"
        );
    }
    let refs = lib
        .blocks
        .iter()
        .flat_map(|b| b.relocs.iter())
        .chain(lib.data.iter().flat_map(|d| d.relocs.iter()))
        .map(|r| r.sym.as_str())
        .chain(
            lib.blocks
                .iter()
                .flat_map(|b| b.externs.iter().map(String::as_str)),
        );
    for s in refs {
        ensure!(
            lib.lookup_block_sym(s).is_some() || rho.contains_key(s),
            "no address for {s}"
        );
    }
    let mpl = PMultiPlacement {
        bases,
        rho,
        relax,
        b2b,
        undef_weak,
    };
    check_multi(lib, &mpl, elf)?;
    Ok(mpl)
}

/// The externs of `lib` (deduplicated across blocks, sorted) split by whether `elf`'s
/// `ElfImage.symbols` view has exactly one entry with that name, whose value is the placed address
/// `lib.resolve(mpl, e)`. The first list is what `Obj.Interned.externSymtab_of` can prove; the
/// second pairs each other extern with the reason it is left out (not a global defined
/// `STT_FUNC`, e.g. a data object or a linker-synthesized symbol; a duplicate name; or a value
/// that differs from the placed address).
pub fn extern_symtab_split(
    lib: &PMultiLib,
    mpl: &PMultiPlacement,
    elf: &Elf,
) -> (Vec<String>, Vec<(String, String)>) {
    let externs: BTreeSet<&str> = lib
        .blocks
        .iter()
        .flat_map(|b| b.externs.iter().map(String::as_str))
        .collect();
    let mut ok = Vec::new();
    let mut skipped = Vec::new();
    for e in externs {
        let hits: Vec<&ElfSym> = elf.image_symbols().filter(|s| s.name == e).collect();
        let addr = lib.resolve(mpl, e);
        match hits.as_slice() {
            [s] if s.value == addr => ok.push(e.to_string()),
            [s] => skipped.push((
                e.to_string(),
                format!(".symtab value {:#x} differs from the placed address {addr:#x}", s.value),
            )),
            [] => skipped.push((e.to_string(), "no global defined STT_FUNC entry".into())),
            _ => skipped.push((
                e.to_string(),
                format!("{} global defined STT_FUNC entries", hits.len()),
            )),
        }
    }
    (ok, skipped)
}

/// Reorder the code blocks of `lib` (and its per-block `text_secs`) by increasing base under
/// `mpl`, and permute `mpl`'s per-block `bases`, `relax` and `b2b` to match. The sort is stable,
/// so a library whose blocks are already in address order is left unchanged. Returns whether
/// any block moved.
///
/// With the blocks in address order, the kernel checks block disjointness with the linear
/// `Obj.sortedRangesB` walk instead of the quadratic pairwise fallback of
/// `Obj.Interned.multiPlaceableB`. Object load order is not always address order: the linker may
/// place some input sections out of order.
pub fn sort_multi_blocks_by_base(lib: &mut PMultiLib, mpl: &mut PMultiPlacement) -> bool {
    fn permute<T>(v: &mut Vec<T>, perm: &[usize]) {
        let mut old: Vec<Option<T>> = std::mem::take(v).into_iter().map(Some).collect();
        *v = perm
            .iter()
            .map(|&i| old[i].take().expect("permutation index used twice"))
            .collect();
    }
    let n = lib.blocks.len();
    let mut perm: Vec<usize> = (0..n).collect();
    perm.sort_by_key(|&i| mpl.bases[i]);
    if perm.iter().enumerate().all(|(k, &i)| k == i) {
        return false;
    }
    permute(&mut lib.blocks, &perm);
    if lib.text_secs.len() == n {
        permute(&mut lib.text_secs, &perm);
    }
    permute(&mut mpl.bases, &perm);
    permute(&mut mpl.relax, &perm);
    permute(&mut mpl.b2b, &perm);
    true
}

/// Check `Placeable` and `InElf` of `lib` under `mpl` for the ELF `elf`.
pub fn check_multi(lib: &PMultiLib, mpl: &PMultiPlacement, elf: &Elf) -> Result<()> {
    lib.check_placeable(mpl)
        .context("multi-placement is not Placeable")?;
    let rx = Perm {
        r: true,
        w: false,
        x: true,
    };
    let rw = Perm {
        r: true,
        w: true,
        x: false,
    };
    for (bi, blk) in lib.blocks.iter().enumerate() {
        let bp = lib.block_placement(mpl, bi);
        let text = blk.patched(&bp);
        for (i, b) in text.iter().enumerate() {
            let a = bp.base.wrapping_add(i as u64);
            let (p, v) = elf
                .cell_at(a)
                .with_context(|| format!("block {bi} byte {i:#x} at {a:#x} is not mapped"))?;
            ensure!(p == rx, "block {bi} byte {i:#x} at {a:#x} is not r-x");
            ensure!(
                v == *b,
                "block {bi} word at {:#x} (offset {:#x}): ELF {:#010x}, model {:#010x}",
                a & !3,
                i & !3,
                elf.word(a & !3).unwrap_or(0),
                blk.patched_word(&bp, (i & !3) as u64)
            );
        }
    }
    for (k, d) in lib.data.iter().enumerate() {
        let addr = mpl.rho(&d.sym);
        for (i, b) in lib.patched_data(mpl, k).iter().enumerate() {
            let a = addr.wrapping_add(i as u64);
            let (p, v) = elf
                .cell_at(a)
                .with_context(|| format!("{} byte {i} at {a:#x} is not mapped", d.sym))?;
            ensure!(
                if d.read_only { p.r } else { p == rw },
                "{} byte {i} at {a:#x} has the wrong permission",
                d.sym
            );
            ensure!(
                v == *b,
                "{} byte {i} at {a:#x}: ELF {v:#04x}, model {b:#04x}",
                d.sym
            );
        }
    }
    for e in &lib.exports {
        let (bi, off) = lib
            .lookup_block_sym(e)
            .with_context(|| format!("export {e} not in any block"))?;
        let elf_name = lib.elf_sym(e);
        let hits: Vec<u64> = elf
            .image_symbols()
            .filter(|s| s.name == elf_name)
            .map(|s| s.value)
            .collect();
        let expected = mpl.bases[bi].wrapping_add(off);
        ensure!(
            hits == [expected],
            "export {e}: .symtab entries {hits:x?}, expected [{expected:#x}]"
        );
    }
    Ok(())
}

fn is_tls_reloc_kind(k: RelocKind) -> bool {
    matches!(
        k,
        RelocKind::TlsdescAdrPage21
            | RelocKind::TlsdescLd64Lo12
            | RelocKind::TlsdescAddLo12
            | RelocKind::TlsdescCall
            | RelocKind::TlsleAddTprelHi12
            | RelocKind::TlsleAddTprelLo12
            | RelocKind::TlsleAddTprelLo12Nc
            | RelocKind::TlsleLdst8TprelLo12Nc
            | RelocKind::TlsleLdst16TprelLo12Nc
            | RelocKind::TlsleLdst32TprelLo12Nc
            | RelocKind::TlsleLdst64TprelLo12Nc
            | RelocKind::TlsleLdst128TprelLo12Nc
            | RelocKind::TlsleMovwTprelG1
            | RelocKind::TlsleMovwTprelG1Nc
            | RelocKind::TlsleMovwTprelG0
            | RelocKind::TlsleMovwTprelG0Nc
    )
}

/// Synthesize a canonical valid [`PPlacement`] for `lib` without needing a linked ELF.
///
/// Places `.text` at an aligned `base >= 0x10_0000`, assigns any thread-local symbols small
/// 16-byte-aligned TP offsets, assigns each extern symbol a distinct 64-byte-aligned slot after
/// `.text`, and places each data object at a disjoint aligned address after the externs.
/// Re-checks `lib.check_placeable(&pl)` and extern-address distinctness before returning.
pub fn synthesize_placement(lib: &PLib) -> Result<PPlacement> {
    let text_align = lib.text.align.max(PAGE);
    let base = 0x10_0000u64.div_ceil(text_align) * text_align;
    let text_end = base.saturating_add(lib.text.code.len() as u64);

    let block_syms: BTreeSet<&str> = lib.text.symbols.iter().map(|(s, _)| s.as_str()).collect();
    let data_syms: BTreeSet<&str> = lib.data.iter().map(|d| d.sym.as_str()).collect();

    let mut addend_bounds: BTreeMap<String, (i64, i64)> = BTreeMap::new();
    let mut tls_syms: BTreeSet<String> = lib.tls.iter().map(|t| t.sym.clone()).collect();
    let mut other_syms: BTreeSet<String> = lib.text.externs.iter().cloned().collect();

    for r in lib
        .text
        .relocs
        .iter()
        .chain(lib.data.iter().flat_map(|d| d.relocs.iter()))
    {
        let entry = addend_bounds.entry(r.sym.clone()).or_insert((0, 0));
        entry.0 = entry.0.min(r.addend);
        entry.1 = entry.1.max(r.addend);
        if !block_syms.contains(r.sym.as_str()) && !data_syms.contains(r.sym.as_str()) {
            if is_tls_reloc_kind(r.kind) {
                tls_syms.insert(r.sym.clone());
            } else {
                other_syms.insert(r.sym.clone());
            }
        }
    }

    let mut rho: BTreeMap<String, u64> = BTreeMap::new();

    // 1. Thread-local symbols need small non-negative TP offsets (e.g. `< 4096` for `tprel_lo12`).
    let mut tp_cursor = 0x10u64;
    for sym in &tls_syms {
        if block_syms.contains(sym.as_str()) || data_syms.contains(sym.as_str()) {
            continue;
        }
        let (min_add, max_add) = addend_bounds.get(sym).copied().unwrap_or((0, 0));
        if min_add < 0 {
            let need = (-min_add) as u64 + 0x10;
            if tp_cursor < need {
                tp_cursor = need;
            }
        }
        tp_cursor = tp_cursor.div_ceil(16) * 16;
        rho.insert(sym.clone(), tp_cursor);
        let span = (max_add.max(0) as u64).saturating_add(16).div_ceil(16) * 16;
        tp_cursor = tp_cursor.saturating_add(span.max(16));
    }

    // 2. Externs and any other undefined non-block, non-data symbols get distinct 64-byte slots
    // strictly after `[base, base + text.code.len())`.
    let mut cursor = text_end.saturating_add(64).div_ceil(PAGE) * PAGE;
    for sym in &other_syms {
        if block_syms.contains(sym.as_str())
            || data_syms.contains(sym.as_str())
            || rho.contains_key(sym)
        {
            continue;
        }
        let (min_add, max_add) = addend_bounds.get(sym).copied().unwrap_or((0, 0));
        if min_add < 0 {
            let need = text_end.saturating_add((-min_add) as u64).saturating_add(64);
            if cursor < need {
                cursor = need;
            }
        }
        cursor = cursor.div_ceil(64) * 64;
        rho.insert(sym.clone(), cursor);
        let span = (max_add.max(0) as u64).saturating_add(64).div_ceil(64) * 64;
        cursor = cursor.saturating_add(span.max(64));
    }

    // 3. Data objects get disjoint aligned regions after the extern table.
    cursor = cursor.div_ceil(PAGE) * PAGE;
    for d in &lib.data {
        let align = d.align.max(1);
        let eff_align = if align % 64 == 0 { align } else { align * 64 };
        let (min_add, max_add) = addend_bounds.get(&d.sym).copied().unwrap_or((0, 0));
        if min_add < 0 {
            cursor = cursor.saturating_add((-min_add) as u64);
        }
        cursor = cursor.div_ceil(eff_align) * eff_align;
        rho.insert(d.sym.clone(), cursor);
        let obj_len = (d.bytes.len() as u64).saturating_add(d.zero_tail);
        let rel_len = (max_add.max(0) as u64).saturating_add(64);
        let span = obj_len.max(rel_len).max(64);
        cursor = cursor.saturating_add(span);
    }

    let pl = PPlacement {
        undef_weak: Default::default(),
        base,
        rho,
        relax: BTreeSet::new(),
        b2b: BTreeSet::new(),
    };
    lib.check_placeable(&pl)
        .context("synthesized placement is not Placeable")?;
    let mut seen_extern_addrs = BTreeSet::new();
    for ext in &lib.text.externs {
        let addr = pl.rho(ext);
        ensure!(
            seen_extern_addrs.insert(addr),
            "synthesized placement assigned duplicate address {addr:#x} to extern {ext}"
        );
    }
    Ok(pl)
}
