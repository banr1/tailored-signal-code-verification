// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Relocation-site census of a stock-linked executable (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — a measurement tool. It reports how far an executable
//!   produced by an ordinary `ld.lld` link (see [`crate::stock`]) is from "every library word is
//!   the relocation template patched with the final symbol addresses", so that a layout-generic
//!   proof knows which alternative templates (linker relaxations, thunks) it has to admit.
//! - **Purpose:** [`census`] locates every allocated input section of the library objects in the
//!   executable (by symbol anchors from `.symtab`, then by masked content search, with
//!   `SHF_MERGE` sections split into pieces), resolves every relocation target to an address, and
//!   classifies each relocation site:
//!   - `exact`: the executable word equals `patch_code(template, target)` (code) or the
//!     expected `S + A` / `S + A - P` value (data);
//!   - `adrpAddToNopAdr`: lld's `adrp xN, sym; add xN, xN, :lo12:sym` → `nop; adr xN, sym`;
//!   - `gotToAdrpAdd` / `gotToNopAdr`: `adrp xN, :got:sym; ldr xN, [xN, :got_lo12:sym]` →
//!     `adrp; add` or `nop; adr`; `gotUnrelaxed`: the pair loads a GOT slot holding the target;
//!   - `branchViaThunk`: a `b`/`bl` reaches a linker-inserted range-extension thunk whose target is
//!     the symbol; `branchToBranch`: lld's `--branch-to-branch` (default at `-O2`) retargeted a
//!     `b`/`bl` whose target is itself an unconditional `b` to that `b`'s destination (followed
//!     transitively); `weakUndefBranch`: a branch to an undefined weak symbol, relocated to
//!     `P + 4`;
//!   - `unresolved`: the target address could not be determined (reported, never counted as a
//!     match); `unsupported`: a relocation type this census does not evaluate;
//!   - `unmatched`: the word matches none of the above — the critical number.
//!
//!   It also reports function survival after `--gc-sections`, `.symtab` visibility, identical
//!   code folding, GOT and thunk usage, merged-string placement, `.eh_frame` presence, and
//!   whether the library's code and data are contiguous.
//!
//! # Key Types & Functions
//! - [`census`]: the whole report as JSON. [`Class`]: site classes. [`relax`]: the relaxed
//!   instruction forms. [`thunk_target`]: range-extension thunk decoding.
//!
//! # When to Read This File
//! - Read this file to interpret `census.json` or to add a relaxation form.

use crate::stock::StockImage;
use anyhow::{Context, Result};
use object::read::elf::{ElfFile64, SectionHeader};
use object::{Endianness, Object, ObjectSection, ObjectSymbol, SectionFlags, SymbolFlags};
use rust_obj2lean::trusted_common::{
    ObjObject, ObjSection, RelocType, SymBind, SymKind, SymSection,
};
use rust_obj2lean::untrusted_legacy_linker::{self, patch_code};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, HashSet};

const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;
const SHF_MERGE: u64 = 0x10;
const SHF_STRINGS: u64 = 0x20;
const SHT_NOBITS: u32 = 8;
const STT_FUNC: u8 = 2;
const MAX_CANDIDATES: usize = 16;
const MAX_SAMPLES: usize = 50;
const MAX_EXAMPLES: usize = 3;

/// Relaxed AArch64 instruction forms produced by `ld.lld`.
pub mod relax {
    /// `nop`.
    pub const NOP: u32 = 0xd503_201f;

    fn sext(v: u64, bits: u32) -> i64 {
        ((v << (64 - bits)) as i64) >> (64 - bits)
    }

    /// `adr x<rd>, target` at `p`, if `target` is within ±1 MiB.
    pub fn adr(rd: u32, target: u64, p: u64) -> Option<u32> {
        let d = target.wrapping_sub(p) as i64;
        if !(-(1 << 20)..(1 << 20)).contains(&d) {
            return None;
        }
        let d = d as u64;
        Some(0x1000_0000 | (((d & 3) as u32) << 29) | ((((d >> 2) & 0x7ffff) as u32) << 5) | rd)
    }

    /// `rd` field (bits 0..5).
    pub fn rd(w: u32) -> u32 {
        w & 0x1f
    }

    /// `rn` field (bits 5..10).
    pub fn rn(w: u32) -> u32 {
        (w >> 5) & 0x1f
    }

    /// The `add x<rd>, x<rn>, #0` lld writes in place of a GOT `ldr x<rd>, [x<rn>, #imm]`
    /// before patching the low 12 bits.
    pub fn ldr_to_add(ldr: u32) -> u32 {
        0x9100_0000 | (rn(ldr) << 5) | rd(ldr)
    }

    /// Target page of an `adrp` at `p`.
    pub fn adrp_page(w: u32, p: u64) -> Option<u64> {
        if w & 0x9f00_0000 != 0x9000_0000 {
            return None;
        }
        let imm = (((w >> 5) & 0x7ffff) as u64) << 2 | ((w >> 29) & 3) as u64;
        Some((p & !0xfff).wrapping_add((sext(imm, 21) << 12) as u64))
    }

    /// Unsigned scaled offset of a 64-bit `ldr x<rt>, [x<rn>, #imm]`.
    pub fn ldr64_imm(w: u32) -> Option<u64> {
        (w & 0xffc0_0000 == 0xf940_0000).then_some((((w >> 10) & 0xfff) as u64) << 3)
    }

    /// Target of a `b`/`bl` at `p` (`None` if `w` is neither).
    pub fn branch_target(w: u32, p: u64) -> Option<u64> {
        if w & 0x7c00_0000 != 0x1400_0000 {
            return None;
        }
        Some(p.wrapping_add((sext((w & 0x03ff_ffff) as u64, 26) << 2) as u64))
    }
}

/// Final target of a linker range-extension thunk starting at `a`: `ldr x16, #8; br x16;
/// .quad T` (absolute) or `adrp x16, T; add x16, x16, :lo12:T; br x16` (page-relative).
pub fn thunk_target(word: impl Fn(u64) -> Option<u32>, a: u64) -> Option<u64> {
    const LDR_X16_8: u32 = 0x5800_0050;
    const BR_X16: u32 = 0xd61f_0200;
    let (w0, w1) = (word(a)?, word(a + 4)?);
    if w0 == LDR_X16_8 && w1 == BR_X16 {
        let lo = word(a + 8)? as u64;
        let hi = word(a + 12)? as u64;
        return Some(lo | (hi << 32));
    }
    if relax::rd(w0) == 16 && w1 & 0xffc0_03ff == 0x9100_0210 && word(a + 8)? == BR_X16 {
        let page = relax::adrp_page(w0, a)?;
        return Some(page + ((w1 >> 10) & 0xfff) as u64);
    }
    None
}

/// Classification of one relocation site (see the module docs).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Class {
    Exact,
    AdrpAddToNopAdr,
    GotToAdrpAdd,
    GotToNopAdr,
    GotUnrelaxed,
    BranchViaThunk,
    BranchToBranch,
    WeakUndefBranch,
    Unresolved,
    Unsupported,
    Unmatched,
}

impl Class {
    fn key(self) -> &'static str {
        match self {
            Class::Exact => "exact",
            Class::AdrpAddToNopAdr => "adrpAddToNopAdr",
            Class::GotToAdrpAdd => "gotToAdrpAdd",
            Class::GotToNopAdr => "gotToNopAdr",
            Class::GotUnrelaxed => "gotUnrelaxed",
            Class::BranchViaThunk => "branchViaThunk",
            Class::BranchToBranch => "branchToBranch",
            Class::WeakUndefBranch => "weakUndefBranch",
            Class::Unresolved => "unresolved",
            Class::Unsupported => "unsupported",
            Class::Unmatched => "unmatched",
        }
    }
}

struct OutSec {
    name: String,
    addr: u64,
    size: u64,
    flags: u64,
    nobits: bool,
    data: Vec<u8>,
}

struct OutSym {
    name: String,
    addr: u64,
    size: u64,
    typ: u8,
    global: bool,
}

/// The parts of the executable the census needs.
struct Elf {
    secs: Vec<OutSec>,
    syms: Vec<OutSym>,
    by_name: HashMap<String, Vec<usize>>,
}

impl Elf {
    fn parse(bytes: &[u8]) -> Result<Elf> {
        let elf = ElfFile64::<Endianness>::parse(bytes).context("cannot parse the executable")?;
        let e = elf.endian();
        let mut secs = Vec::new();
        for s in elf.sections() {
            let flags = match s.flags() {
                SectionFlags::Elf { sh_flags } => sh_flags,
                _ => 0,
            };
            if flags & SHF_ALLOC == 0 {
                continue;
            }
            let nobits = s.elf_section_header().sh_type(e) == SHT_NOBITS;
            secs.push(OutSec {
                name: s.name().unwrap_or("").to_string(),
                addr: s.address(),
                size: s.size(),
                flags,
                nobits,
                data: if nobits {
                    Vec::new()
                } else {
                    s.data()?.to_vec()
                },
            });
        }
        let mut syms = Vec::new();
        let mut by_name: HashMap<String, Vec<usize>> = HashMap::new();
        for s in elf.symbols() {
            if s.is_undefined() {
                continue;
            }
            let SymbolFlags::Elf { st_info, .. } = s.flags() else {
                continue;
            };
            let name = s.name().unwrap_or("").to_string();
            if name.is_empty() {
                continue;
            }
            by_name.entry(name.clone()).or_default().push(syms.len());
            syms.push(OutSym {
                name,
                addr: s.address(),
                size: s.size(),
                typ: st_info & 0xf,
                global: st_info >> 4 != 0,
            });
        }
        Ok(Elf {
            secs,
            syms,
            by_name,
        })
    }

    fn sec_at(&self, a: u64) -> Option<&OutSec> {
        self.secs
            .iter()
            .find(|s| s.size > 0 && s.addr <= a && a < s.addr + s.size)
    }

    fn bytes(&self, a: u64, n: u64) -> Option<&[u8]> {
        let s = self.sec_at(a)?;
        if s.nobits || a + n > s.addr + s.size {
            return None;
        }
        let o = (a - s.addr) as usize;
        Some(&s.data[o..o + n as usize])
    }

    fn word(&self, a: u64) -> Option<u32> {
        self.bytes(a, 4)
            .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
    }

    fn u64_at(&self, a: u64) -> Option<u64> {
        self.bytes(a, 8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
    }

    /// Addresses of the defined symbols named `name`, globals first.
    fn addrs(&self, name: &str, globals_only: bool) -> Vec<u64> {
        let Some(ix) = self.by_name.get(name) else {
            return Vec::new();
        };
        let mut v: Vec<u64> = ix
            .iter()
            .filter(|&&i| self.syms[i].global)
            .map(|&i| self.syms[i].addr)
            .collect();
        if v.is_empty() && !globals_only {
            v = ix.iter().map(|&i| self.syms[i].addr).collect();
        }
        v.sort();
        v.dedup();
        v
    }
}

/// Where the bytes of one input section ended up.
#[derive(Clone, Default)]
enum Place {
    #[default]
    Unplaced,
    Bases {
        bases: Vec<u64>,
        anchored: bool,
        mismatches: usize,
    },
    Pieces(Vec<Piece>),
}

#[derive(Clone)]
struct Piece {
    off: u64,
    len: u64,
    addrs: Vec<u64>,
    /// Some occurrence is only a suffix of a longer string (tail merge).
    tail: bool,
}

fn is_exec(s: &ObjSection) -> bool {
    s.sh_flags & SHF_EXECINSTR != 0
}

fn is_merge(s: &ObjSection) -> bool {
    s.sh_flags & SHF_MERGE != 0
}

fn is_nobits(s: &ObjSection) -> bool {
    s.sh_type == SHT_NOBITS
}

fn width(exec: bool, t: RelocType) -> u64 {
    match t {
        RelocType::None => 0,
        _ if exec => 4,
        RelocType::Abs16 | RelocType::Prel16 => 2,
        RelocType::Abs32 | RelocType::Prel32 | RelocType::Plt32 => 4,
        _ => 8,
    }
}

/// `true` for every byte a relocation patches.
pub(crate) fn reloc_mask(s: &ObjSection) -> Vec<bool> {
    let mut m = vec![false; s.bytes.len()];
    for r in &s.relocs {
        let w = width(is_exec(s), r.rtype);
        for b in r.offset..(r.offset + w).min(s.bytes.len() as u64) {
            m[b as usize] = true;
        }
    }
    m
}

fn find_all(hay: &[u8], needle: &[u8]) -> Vec<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return Vec::new();
    }
    let mut v = Vec::new();
    let mut i = 0;
    while i + needle.len() <= hay.len() {
        match hay[i..=hay.len() - needle.len()]
            .iter()
            .position(|&b| b == needle[0])
        {
            None => break,
            Some(k) => {
                let at = i + k;
                if &hay[at..at + needle.len()] == needle {
                    v.push(at);
                }
                i = at + 1;
            }
        }
    }
    v
}

/// Possible target addresses of a relocation.
enum Tgt {
    Addrs(Vec<u64>),
    WeakZero(u64),
    Unknown(String),
}

struct Lib<'a> {
    image: usize,
    obj: &'a ObjObject,
}

struct Census<'a> {
    elf: Elf,
    libs: Vec<Lib<'a>>,
    place: Vec<Vec<Place>>,
    masks: Vec<Vec<Vec<bool>>>,
}

impl<'a> Census<'a> {
    fn mismatches(&self, li: usize, j: usize, base: u64) -> Option<usize> {
        let s = &self.libs[li].obj.sections[j];
        if is_nobits(s) {
            let o = self.elf.sec_at(base)?;
            return (o.flags & SHF_WRITE != 0
                && o.flags & SHF_EXECINSTR == 0
                && base + s.size <= o.addr + o.size)
                .then_some(0);
        }
        let b = self.elf.bytes(base, s.size)?;
        let m = &self.masks[li][j];
        Some(
            s.bytes
                .iter()
                .zip(b)
                .zip(m)
                .filter(|((x, y), k)| !**k && x != y)
                .count(),
        )
    }

    /// Placement from symbols defined in the section that also appear in `.symtab`.
    fn anchor_pass(&mut self) {
        for li in 0..self.libs.len() {
            let o = self.libs[li].obj;
            let mut cands: BTreeMap<usize, HashSet<u64>> = BTreeMap::new();
            for sym in &o.symbols {
                let SymSection::Sec(j) = sym.sec else {
                    continue;
                };
                if !matches!(sym.kind, SymKind::Func | SymKind::Object | SymKind::Notype)
                    || sym.raw_name.is_empty()
                    || sym.raw_name.starts_with('$')
                    || sym.raw_name.starts_with(".L")
                    || is_merge(&o.sections[j])
                {
                    continue;
                }
                for a in self.elf.addrs(&sym.raw_name, false) {
                    cands
                        .entry(j)
                        .or_default()
                        .insert(a.wrapping_sub(sym.value));
                }
            }
            for (j, cs) in cands {
                let mut scored: Vec<(usize, u64)> = cs
                    .into_iter()
                    .filter_map(|b| self.mismatches(li, j, b).map(|m| (m, b)))
                    .collect();
                scored.sort();
                let Some(&(best, _)) = scored.first() else {
                    continue;
                };
                // A wrong anchor (a same-named symbol elsewhere) almost never matches; keep a
                // best candidate with a few mismatches so the mismatching bytes get reported.
                if best * 8 > o.sections[j].size as usize {
                    continue;
                }
                let bases: Vec<u64> = scored
                    .iter()
                    .filter(|(m, _)| *m == best)
                    .map(|(_, b)| *b)
                    .take(MAX_CANDIDATES)
                    .collect();
                self.place[li][j] = Place::Bases {
                    bases,
                    anchored: true,
                    mismatches: best,
                };
            }
        }
    }

    /// Whether no relocation site of code section `j` placed at `base` is `unmatched`.
    fn sites_match(&self, li: usize, j: usize, base: u64) -> bool {
        let s = &self.libs[li].obj.sections[j];
        s.relocs.iter().enumerate().all(|(ri, r)| {
            let (ts, weak) = match self.targets(li, r.sym, r.addend) {
                Tgt::Addrs(v) => (v, false),
                Tgt::WeakZero(z) => (vec![z], true),
                Tgt::Unknown(_) => return true,
            };
            classify_text(self, s, ri, base + r.offset, &ts, weak).0 != Class::Unmatched
        })
    }

    /// The bytes of section `j` the executable must contain, `None` where unknown.
    fn expected(&self, li: usize, j: usize) -> Vec<Option<u8>> {
        let s = &self.libs[li].obj.sections[j];
        let m = &self.masks[li][j];
        let mut v: Vec<Option<u8>> = s
            .bytes
            .iter()
            .zip(m)
            .map(|(b, k)| (!*k).then_some(*b))
            .collect();
        if is_exec(s) {
            return v;
        }
        // Absolute data relocations whose target is already unique fill in their bytes.
        for r in &s.relocs {
            let w = width(false, r.rtype) as usize;
            let val = match (r.rtype, self.targets(li, r.sym, r.addend)) {
                (RelocType::Abs64, Tgt::Addrs(t)) if t.len() == 1 => t[0],
                (RelocType::Abs64, Tgt::WeakZero(z)) => z,
                _ => continue,
            };
            for (k, b) in val.to_le_bytes().iter().take(w).enumerate() {
                if let Some(slot) = v.get_mut(r.offset as usize + k) {
                    *slot = Some(*b);
                }
            }
        }
        v
    }

    /// Whether section `j` defines a named function or object symbol. The link keeps `.symtab`
    /// (locals included), so such a section that the anchor pass could not place was discarded;
    /// searching for its bytes would only find an identical sibling (e.g. a same-shaped wrapper).
    fn defines_named_symbol(&self, li: usize, j: usize) -> bool {
        self.libs[li].obj.symbols.iter().any(|sym| {
            matches!(sym.sec, SymSection::Sec(k) if k == j)
                && matches!(sym.kind, SymKind::Func | SymKind::Object)
                && !sym.raw_name.is_empty()
                && !sym.raw_name.starts_with('$')
                && !sym.raw_name.starts_with(".L")
        })
    }

    /// Placement of the remaining non-merge sections by masked content search.
    fn content_pass(&mut self) -> usize {
        let mut placed = 0;
        for li in 0..self.libs.len() {
            let o = self.libs[li].obj;
            for (j, s) in o.sections.iter().enumerate() {
                if !matches!(self.place[li][j], Place::Unplaced)
                    || is_merge(s)
                    || is_nobits(s)
                    || s.size == 0
                    || self.defines_named_symbol(li, j)
                {
                    continue;
                }
                let exp = self.expected(li, j);
                // Longest run of known bytes as the needle.
                let (mut best, mut cur) = ((0usize, 0usize), (0usize, 0usize));
                for (k, b) in exp.iter().enumerate() {
                    if b.is_some() {
                        if cur.1 == 0 {
                            cur.0 = k;
                        }
                        cur.1 += 1;
                        if cur.1 > best.1 {
                            best = cur;
                        }
                    } else {
                        cur.1 = 0;
                    }
                }
                if best.1 < 4 && best.1 < exp.len() {
                    continue;
                }
                let needle: Vec<u8> = exp[best.0..best.0 + best.1]
                    .iter()
                    .map(|b| b.unwrap())
                    .collect();
                let want_exec = is_exec(s);
                let mut bases = Vec::new();
                for os in &self.elf.secs {
                    if os.nobits || (os.flags & SHF_EXECINSTR != 0) != want_exec {
                        continue;
                    }
                    for hit in find_all(&os.data, &needle) {
                        let base = (os.addr + hit as u64).wrapping_sub(best.0 as u64);
                        if !base.is_multiple_of(s.align.max(1)) || base < os.addr {
                            continue;
                        }
                        let ok = self.elf.bytes(base, s.size).is_some_and(|b| {
                            b.iter().zip(&exp).all(|(x, y)| y.is_none_or(|y| *x == y))
                        });
                        if ok {
                            bases.push(base);
                        }
                        if bases.len() > MAX_CANDIDATES {
                            break;
                        }
                    }
                }
                // Code found by content must also match at every relocation site whose target is
                // known (short functions are otherwise found at unrelated copies).
                if want_exec {
                    bases.retain(|&b| self.sites_match(li, j, b));
                }
                if !bases.is_empty() {
                    bases.truncate(MAX_CANDIDATES);
                    self.place[li][j] = Place::Bases {
                        bases,
                        anchored: false,
                        mismatches: 0,
                    };
                    placed += 1;
                }
            }
        }
        placed
    }

    /// Placement of `SHF_MERGE` sections piece by piece.
    fn merge_pass(&mut self) {
        for li in 0..self.libs.len() {
            let o = self.libs[li].obj;
            for (j, s) in o.sections.iter().enumerate() {
                if !is_merge(s) || is_nobits(s) {
                    continue;
                }
                let mut pieces = Vec::new();
                let mut off = 0usize;
                while off < s.bytes.len() {
                    let len = if s.sh_flags & SHF_STRINGS != 0 {
                        let ent = s.entsize.max(1) as usize;
                        let mut k = off;
                        while k + ent <= s.bytes.len()
                            && s.bytes[k..k + ent].iter().any(|&b| b != 0)
                        {
                            k += ent;
                        }
                        (k + ent).min(s.bytes.len()) - off
                    } else {
                        (s.entsize.max(1) as usize).min(s.bytes.len() - off)
                    };
                    let needle = &s.bytes[off..off + len];
                    let mut addrs = Vec::new();
                    let mut tail = false;
                    for os in &self.elf.secs {
                        if os.nobits || os.flags & SHF_EXECINSTR != 0 {
                            continue;
                        }
                        for hit in find_all(&os.data, needle) {
                            let a = os.addr + hit as u64;
                            let starts = hit == 0 || os.data[hit - 1] == 0;
                            if s.sh_flags & SHF_STRINGS != 0 && !starts {
                                tail = true;
                            }
                            addrs.push(a);
                            if addrs.len() > MAX_CANDIDATES {
                                break;
                            }
                        }
                    }
                    pieces.push(Piece {
                        off: off as u64,
                        len: len as u64,
                        addrs,
                        tail,
                    });
                    off += len;
                }
                self.place[li][j] = Place::Pieces(pieces);
            }
        }
    }

    fn targets(&self, li: usize, sym_ix: usize, addend: i64) -> Tgt {
        let o = self.libs[li].obj;
        let Some(sym) = o.symbols.get(sym_ix) else {
            return Tgt::Unknown(format!("bad symbol index {sym_ix}"));
        };
        let a = addend as u64;
        let by_name = |globals_only: bool| -> Tgt {
            let v = self.elf.addrs(&sym.raw_name, globals_only);
            if v.is_empty() {
                if sym.bind == SymBind::Weak && sym.sec == SymSection::Undef {
                    Tgt::WeakZero(a)
                } else {
                    Tgt::Unknown(format!("no .symtab entry for `{}`", sym.name))
                }
            } else {
                Tgt::Addrs(v.into_iter().map(|x| x.wrapping_add(a)).collect())
            }
        };
        match sym.sec {
            SymSection::Sec(j) => match &self.place[li][j] {
                Place::Bases { bases, .. } => Tgt::Addrs(
                    bases
                        .iter()
                        .map(|b| b.wrapping_add(sym.value).wrapping_add(a))
                        .collect(),
                ),
                Place::Pieces(ps) => {
                    let (off, rest) = if sym.kind == SymKind::Section {
                        (sym.value.wrapping_add(a), 0)
                    } else {
                        (sym.value, a)
                    };
                    match ps.iter().find(|p| p.off <= off && off < p.off + p.len) {
                        Some(p) if !p.addrs.is_empty() => Tgt::Addrs(
                            p.addrs
                                .iter()
                                .map(|x| x.wrapping_add(off - p.off).wrapping_add(rest))
                                .collect(),
                        ),
                        _ => Tgt::Unknown(format!(
                            "merge piece at {}+{off:#x} not found",
                            o.sections[j].name
                        )),
                    }
                }
                Place::Unplaced => {
                    if sym.kind != SymKind::Section && !sym.raw_name.is_empty() {
                        by_name(false)
                    } else {
                        Tgt::Unknown(format!("section {} not located", o.sections[j].name))
                    }
                }
            },
            SymSection::Undef => {
                // A definition in another object of the same image wins (its `.symtab` entry may
                // be local or missing).
                let im = self.libs[li].image;
                let mut v = Vec::new();
                for (lk, l) in self.libs.iter().enumerate() {
                    if l.image != im {
                        continue;
                    }
                    for (si, d) in l.obj.symbols.iter().enumerate() {
                        if d.raw_name == sym.raw_name
                            && d.bind != SymBind::Local
                            && matches!(d.sec, SymSection::Sec(_))
                            && let Tgt::Addrs(a) = self.targets(lk, si, addend)
                        {
                            v.extend(a);
                        }
                    }
                }
                if v.is_empty() {
                    by_name(false)
                } else {
                    Tgt::Addrs(v)
                }
            }
            SymSection::Abs => Tgt::Addrs(vec![sym.value.wrapping_add(a)]),
            _ => by_name(false),
        }
    }

    fn func_at(&self, li: usize, j: usize, off: u64) -> String {
        self.libs[li]
            .obj
            .symbols
            .iter()
            .find(|s| {
                s.sec == SymSection::Sec(j)
                    && s.kind == SymKind::Func
                    && s.value <= off
                    && off < s.value + s.size.max(1)
            })
            .map_or_else(String::new, |s| s.name.clone())
    }
}

fn orig_word(s: &ObjSection, off: u64) -> u32 {
    let o = off as usize;
    u32::from_le_bytes(s.bytes[o..o + 4].try_into().unwrap())
}

fn is_adrp_type(t: RelocType) -> bool {
    matches!(t, RelocType::AdrPrelPgHi21 | RelocType::AdrPrelPgHi21Nc)
}

/// Classify a relocation site in a code section at address `p`.
fn classify_text(
    c: &Census,
    s: &ObjSection,
    ri: usize,
    p: u64,
    ts: &[u64],
    weak: bool,
) -> (Class, Vec<u32>) {
    let r = &s.relocs[ri];
    let e = &c.elf;
    let Some(w) = e.word(p) else {
        return (Class::Unmatched, vec![]);
    };
    let orig = orig_word(s, r.offset);
    let is_got = matches!(r.rtype, RelocType::AdrGotPage | RelocType::Ld64GotLo12Nc);
    if !is_got
        && ts
            .iter()
            .any(|&t| patch_code(r.rtype, orig, t, p).ok() == Some(w))
    {
        return (Class::Exact, vec![w]);
    }
    // The other half of an `adrp` + lo12 pair, as lld pairs them: adjacent in the relocation
    // list, at consecutive words, against the same symbol and addend.
    let next = s
        .relocs
        .get(ri + 1)
        .filter(|n| n.offset == r.offset + 4 && n.sym == r.sym && n.addend == r.addend);
    let prev = ri
        .checked_sub(1)
        .map(|k| &s.relocs[k])
        .filter(|q| q.offset + 4 == r.offset && q.sym == r.sym && q.addend == r.addend);
    // (adrp-site address, adrp template, lo12 template, lo12 is GOT ldr)
    let pair = match r.rtype {
        t if is_adrp_type(t) => next
            .filter(|n| n.rtype == RelocType::AddAbsLo12Nc)
            .map(|n| (p, orig, orig_word(s, n.offset), false)),
        RelocType::AddAbsLo12Nc => prev
            .filter(|q| is_adrp_type(q.rtype))
            .map(|q| (p - 4, orig_word(s, q.offset), orig, false)),
        RelocType::AdrGotPage => next
            .filter(|n| n.rtype == RelocType::Ld64GotLo12Nc)
            .map(|n| (p, orig, orig_word(s, n.offset), true)),
        RelocType::Ld64GotLo12Nc => prev
            .filter(|q| q.rtype == RelocType::AdrGotPage)
            .map(|q| (p - 4, orig_word(s, q.offset), orig, true)),
        _ => None,
    };
    if let Some((pa, t0, t1, got)) = pair {
        let (Some(w0), Some(w1)) = (e.word(pa), e.word(pa + 4)) else {
            return (Class::Unmatched, vec![]);
        };
        for &t in ts {
            if w0 == relax::NOP && relax::adr(relax::rd(t1), t, pa + 4) == Some(w1) {
                let k = if got {
                    Class::GotToNopAdr
                } else {
                    Class::AdrpAddToNopAdr
                };
                return (k, vec![w0, w1]);
            }
            if got
                && patch_code(RelocType::AdrPrelPgHi21, t0, t, pa).ok() == Some(w0)
                && patch_code(RelocType::AddAbsLo12Nc, relax::ldr_to_add(t1), t, pa + 4).ok()
                    == Some(w1)
            {
                return (Class::GotToAdrpAdd, vec![w0, w1]);
            }
            if got && let (Some(page), Some(imm)) = (relax::adrp_page(w0, pa), relax::ldr64_imm(w1))
            {
                let slot = page + imm;
                if e.u64_at(slot) == Some(t)
                    && patch_code(RelocType::AdrGotPage, t0, slot, pa).ok() == Some(w0)
                    && patch_code(RelocType::Ld64GotLo12Nc, t1, slot, pa + 4).ok() == Some(w1)
                {
                    return (Class::GotUnrelaxed, vec![w0, w1]);
                }
            }
        }
    }
    if matches!(r.rtype, RelocType::Call26 | RelocType::Jump26) {
        if weak && patch_code(r.rtype, orig, p + 4, p).ok() == Some(w) {
            return (Class::WeakUndefBranch, vec![w]);
        }
        if let Some(d) = relax::branch_target(w, p)
            && (w ^ orig) & 0xfc00_0000 == 0
        {
            if thunk_target(|a| e.word(a), d).is_some_and(|t| ts.contains(&t)) {
                return (Class::BranchViaThunk, vec![w]);
            }
            for &t in ts {
                let mut cur = t;
                for _ in 0..8 {
                    match e.word(cur) {
                        Some(bw) if bw & 0xfc00_0000 == 0x1400_0000 => {
                            cur = relax::branch_target(bw, cur).unwrap_or(cur);
                            if cur == d {
                                return (Class::BranchToBranch, vec![w]);
                            }
                        }
                        _ => break,
                    }
                }
            }
        }
    }
    (Class::Unmatched, vec![w])
}

/// Classify a relocation site in a data section at address `p`.
fn classify_data(c: &Census, t: RelocType, p: u64, ts: &[u64]) -> Class {
    let w = width(false, t);
    let Some(actual) = c.elf.bytes(p, w) else {
        return Class::Unmatched;
    };
    let ok = ts.iter().any(|&tv| {
        let v = match t {
            RelocType::Abs64 | RelocType::Abs32 | RelocType::Abs16 => tv,
            RelocType::Prel64 | RelocType::Prel32 | RelocType::Plt32 | RelocType::Prel16 => {
                tv.wrapping_sub(p)
            }
            _ => return false,
        };
        v.to_le_bytes()[..w as usize] == *actual
    });
    match t {
        RelocType::Abs64
        | RelocType::Abs32
        | RelocType::Abs16
        | RelocType::Prel64
        | RelocType::Prel32
        | RelocType::Plt32
        | RelocType::Prel16 => {
            if ok {
                Class::Exact
            } else {
                Class::Unmatched
            }
        }
        _ => Class::Unsupported,
    }
}

/// Compare the library's text in the executable with the text region `untrusted_legacy_linker` lays out
/// for the same objects: per-section offset deltas, the fill of the gaps between sections, and
/// the non-relocated bytes of the whole region.
fn trusted_layout(c: &Census, k: usize, im: &StockImage) -> Value {
    let layout = if im.page_separate_data {
        untrusted_legacy_linker::DataLayout::PageSeparated
    } else {
        untrusted_legacy_linker::DataLayout::Interleaved
    };
    let li_img =
        match untrusted_legacy_linker::link_with_layout(&im.objects, &im.externs, 0, layout) {
            Ok(x) => x,
            Err(e) => return json!({"error": format!("{e:#}")}),
        };
    let lis: Vec<usize> = (0..c.libs.len())
        .filter(|&li| c.libs[li].image == k)
        .collect();
    let text_end = li_img
        .stubs
        .iter()
        .map(|s| s.1)
        .min()
        .unwrap_or(li_img.code.len() as u64);
    // Region mask: relocated words of every text section at its trusted offset.
    let mut mask = vec![false; li_img.code.len()];
    let mut secs = Vec::new(); // (trusted off, size, placed base)
    let mut deltas: BTreeMap<i64, usize> = BTreeMap::new();
    let mut gcd = Vec::new();
    for (oi, &li) in lis.iter().enumerate() {
        let o = c.libs[li].obj;
        for (j, s) in o.sections.iter().enumerate() {
            let Some(Some(off)) = li_img.sec_off.get(oi).and_then(|v| v.get(j)).copied() else {
                continue;
            };
            if !is_exec(s) {
                continue;
            }
            for (b, m) in c.masks[li][j].iter().enumerate() {
                if *m {
                    mask[off as usize + b] = true;
                }
            }
            match &c.place[li][j] {
                Place::Bases { bases, .. } if bases.len() == 1 => {
                    *deltas.entry(bases[0] as i64 - off as i64).or_default() += 1;
                    secs.push((off, s.size, Some(bases[0])));
                }
                Place::Bases { bases, .. } => {
                    secs.push((off, s.size, None));
                    gcd.push(format!("{} (ambiguous: {} bases)", s.name, bases.len()));
                }
                _ => {
                    secs.push((off, s.size, None));
                    if s.size > 0 {
                        gcd.push(format!("{} ({} B)", s.name, s.size));
                    }
                }
            }
        }
    }
    let uniform = deltas.len() == 1 && gcd.is_empty();
    let mut region = Value::Null;
    if let Some((&delta, _)) = deltas.iter().max_by_key(|(_, n)| **n) {
        // Compare `[0, text_end)` of the trusted code with the executable at `delta`.
        let (mut diff, mut gap_zero, mut gap_trap, mut gap_other) =
            (0usize, 0usize, 0usize, 0usize);
        let mut samples = Vec::new();
        let in_sec = |b: u64| secs.iter().any(|&(o, n, _)| o <= b && b < o + n);
        for b in 0..text_end {
            let a = (b as i64 + delta) as u64;
            let Some(x) = c.elf.bytes(a, 1) else {
                diff += 1;
                continue;
            };
            let (x, t) = (x[0], li_img.code[b as usize]);
            if !in_sec(b) {
                match x {
                    0 => gap_zero += 1,
                    0xd4 => gap_trap += 1,
                    _ => gap_other += 1,
                }
                continue;
            }
            if !mask[b as usize] && x != t {
                diff += 1;
                if samples.len() < 10 {
                    samples.push(json!({"off": hex(b), "addr": hex(a), "trusted": t, "elf": x}));
                }
            }
        }
        region = json!({
            "delta": hex(delta as u64), "textEnd": hex(text_end),
            "nonRelocByteDiffsInSections": diff, "diffSamples": samples,
            "gapBytesInExecutable": {"zero": gap_zero, "trap0xd4": gap_trap, "other": gap_other},
        });
    }
    json!({
        "textSections": secs.len(),
        "deltaHistogram": Value::Object(deltas.iter().map(|(d, n)| (format!("{:#x}", *d as u64), json!(n))).collect()),
        "sameIntraBlockOffsets": uniform,
        "missingOrAmbiguousSections": gcd,
        "trustedPadding": "zero",
        "region": region,
    })
}

fn hex(v: u64) -> String {
    format!("{v:#x}")
}

fn words(v: &[u32]) -> Vec<String> {
    v.iter().map(|w| format!("{w:#010x}")).collect()
}

/// Relocation counts by type in the `.eh_frame` of a raw `.o` (not part of the extraction).
fn eh_frame_relocs(elf_bytes: &[u8]) -> (u64, usize) {
    let Ok(f) = object::File::parse(elf_bytes) else {
        return (0, 0);
    };
    f.sections()
        .filter(|s| s.name() == Ok(".eh_frame"))
        .fold((0, 0), |(sz, n), s| {
            (sz + s.size(), n + s.relocations().count())
        })
}

/// The census of `elf_bytes` (a stock link of `images`) as JSON.
pub fn census(elf_bytes: &[u8], images: &[StockImage]) -> Result<Value> {
    let elf = Elf::parse(elf_bytes)?;
    let libs: Vec<Lib> = images
        .iter()
        .enumerate()
        .flat_map(|(k, im)| im.objects.iter().map(move |obj| Lib { image: k, obj }))
        .collect();
    let place = libs
        .iter()
        .map(|l| vec![Place::Unplaced; l.obj.sections.len()])
        .collect();
    let masks = libs
        .iter()
        .map(|l| l.obj.sections.iter().map(reloc_mask).collect())
        .collect();
    let mut c = Census {
        elf,
        libs,
        place,
        masks,
    };
    c.anchor_pass();
    c.merge_pass();
    for _ in 0..4 {
        if c.content_pass() == 0 {
            break;
        }
    }

    let thunks: Vec<(String, u64, Option<u64>)> = c
        .elf
        .syms
        .iter()
        .filter(|s| s.name.starts_with("__AArch64") && s.name.contains("Thunk"))
        .map(|s| {
            (
                s.name.clone(),
                s.addr,
                thunk_target(|a| c.elf.word(a), s.addr),
            )
        })
        .collect();
    let mut out_images = Vec::new();
    for (k, im) in images.iter().enumerate() {
        let lis: Vec<usize> = (0..c.libs.len())
            .filter(|&li| c.libs[li].image == k)
            .collect();
        let mut classes: BTreeMap<Class, usize> = BTreeMap::new();
        let mut data_classes: BTreeMap<Class, usize> = BTreeMap::new();
        let mut examples: BTreeMap<Class, Vec<Value>> = BTreeMap::new();
        let mut unmatched = Vec::new();
        let mut unresolved = Vec::new();
        let mut ambiguous_matches = 0usize;
        let mut reloc_counts: BTreeMap<String, [usize; 4]> = BTreeMap::new();
        let mut objects_json = Vec::new();
        let mut text_ranges: Vec<(u64, u64)> = Vec::new();
        let mut data_ranges: Vec<(u64, u64)> = Vec::new();
        let mut text_out: BTreeMap<String, usize> = BTreeMap::new();
        let mut data_out: BTreeMap<String, usize> = BTreeMap::new();
        let mut lib_names: HashSet<String> = HashSet::new();
        let mut byte_mismatch_samples = Vec::new();
        let mut text_bases: HashMap<u64, Vec<String>> = HashMap::new();
        for &li in &lis {
            let o = c.libs[li].obj;
            lib_names.extend(o.symbols.iter().map(|s| s.raw_name.clone()));
            let mut sec_stats = [0usize; 6]; // placed, anchored, content, merge, gc, nonreloc-mismatch secs
            let mut merge = [0usize; 5]; // pieces, unique, ambiguous, missing, tail
            for (j, s) in o.sections.iter().enumerate() {
                let live = !matches!(c.place[li][j], Place::Unplaced);
                for r in &s.relocs {
                    let e = reloc_counts.entry(format!("{:?}", r.rtype)).or_default();
                    let col = usize::from(!is_exec(s)) * 2;
                    e[col] += 1;
                    if live {
                        e[col + 1] += 1;
                    }
                }
                match &c.place[li][j] {
                    Place::Unplaced => sec_stats[4] += 1,
                    Place::Bases {
                        bases,
                        anchored,
                        mismatches,
                    } => {
                        sec_stats[0] += 1;
                        sec_stats[if *anchored { 1 } else { 2 }] += 1;
                        if *mismatches > 0 {
                            sec_stats[5] += 1;
                            if byte_mismatch_samples.len() < MAX_SAMPLES {
                                byte_mismatch_samples.push(json!({
                                    "object": o.name, "section": s.name,
                                    "base": hex(bases[0]), "mismatchedBytes": mismatches,
                                }));
                            }
                        }
                        let b = bases[0];
                        let os = c.elf.sec_at(b).map_or("?".to_string(), |x| x.name.clone());
                        if s.size > 0 {
                            if is_exec(s) {
                                text_ranges.push((b, b + s.size));
                                *text_out.entry(os).or_default() += 1;
                                text_bases
                                    .entry(b)
                                    .or_default()
                                    .push(format!("{}:{}", o.name, s.name));
                            } else {
                                data_ranges.push((b, b + s.size));
                                *data_out.entry(os).or_default() += 1;
                            }
                        }
                    }
                    Place::Pieces(ps) => {
                        sec_stats[0] += 1;
                        sec_stats[3] += 1;
                        for p in ps {
                            merge[0] += 1;
                            match p.addrs.len() {
                                0 => merge[3] += 1,
                                1 => merge[1] += 1,
                                _ => merge[2] += 1,
                            }
                            if p.tail {
                                merge[4] += 1;
                            }
                            if let Some(&a) = p.addrs.iter().min() {
                                data_ranges.push((a, a + p.len));
                                let os =
                                    c.elf.sec_at(a).map_or("?".to_string(), |x| x.name.clone());
                                *data_out.entry(os).or_default() += 1;
                            }
                        }
                    }
                }
                // Sites.
                let Place::Bases { bases, .. } = &c.place[li][j] else {
                    continue;
                };
                for (ri, r) in s.relocs.iter().enumerate() {
                    if r.rtype == RelocType::None {
                        continue;
                    }
                    let tg = c.targets(li, r.sym, r.addend);
                    let (ts, weak) = match &tg {
                        Tgt::Addrs(v) => (v.clone(), false),
                        Tgt::WeakZero(z) => (vec![*z], true),
                        Tgt::Unknown(why) => {
                            if is_exec(s) {
                                *classes.entry(Class::Unresolved).or_default() += 1;
                            } else {
                                *data_classes.entry(Class::Unresolved).or_default() += 1;
                            }
                            if unresolved.len() < MAX_SAMPLES {
                                unresolved.push(json!({
                                    "object": o.name, "section": s.name,
                                    "offset": hex(r.offset), "type": format!("{:?}", r.rtype),
                                    "symbol": o.symbols.get(r.sym).map(|x| x.name.clone()),
                                    "reason": why,
                                }));
                            }
                            continue;
                        }
                    };
                    let sym_name = o.symbols.get(r.sym).map(|x| x.name.clone());
                    if is_exec(s) {
                        let (cl, ws, b) = bases
                            .iter()
                            .map(|&b| {
                                let (cl, ws) = classify_text(&c, s, ri, b + r.offset, &ts, weak);
                                (cl, ws, b)
                            })
                            .min_by_key(|x| x.0)
                            .expect("placed sections have a base");
                        let p = b + r.offset;
                        if cl != Class::Unmatched && (ts.len() > 1 || bases.len() > 1) {
                            ambiguous_matches += 1;
                        }
                        *classes.entry(cl).or_default() += 1;
                        let sample = || {
                            let tmpl_off = if ws.len() == 2
                                && !is_adrp_type(r.rtype)
                                && r.rtype != RelocType::AdrGotPage
                            {
                                r.offset - 4
                            } else {
                                r.offset
                            };
                            let tmpl: Vec<u32> = (0..ws.len().max(1) as u64)
                                .map(|k| orig_word(s, tmpl_off + 4 * k))
                                .collect();
                            json!({
                                "object": o.name, "section": s.name,
                                "function": c.func_at(li, j, r.offset),
                                "offset": hex(r.offset), "site": hex(p),
                                "type": format!("{:?}", r.rtype), "symbol": sym_name,
                                "addend": r.addend,
                                "targets": ts.iter().map(|t| hex(*t)).collect::<Vec<_>>(),
                                "pairAddr": hex(b + tmpl_off),
                                "templateWords": words(&tmpl),
                                "elfWords": words(&ws),
                            })
                        };
                        match cl {
                            Class::Exact => {}
                            Class::Unmatched => {
                                if unmatched.len() < MAX_SAMPLES {
                                    unmatched.push(sample());
                                }
                            }
                            _ => {
                                let ex = examples.entry(cl).or_default();
                                let first_of_pair = is_adrp_type(r.rtype)
                                    || r.rtype == RelocType::AdrGotPage
                                    || ws.len() < 2;
                                if ex.len() < MAX_EXAMPLES && first_of_pair {
                                    ex.push(sample());
                                }
                            }
                        }
                    } else {
                        let cl = bases
                            .iter()
                            .map(|b| classify_data(&c, r.rtype, b + r.offset, &ts))
                            .min()
                            .unwrap_or(Class::Unmatched);
                        if cl == Class::Exact && (ts.len() > 1 || bases.len() > 1) {
                            ambiguous_matches += 1;
                        }
                        *data_classes.entry(cl).or_default() += 1;
                        if cl == Class::Unmatched && unmatched.len() < MAX_SAMPLES {
                            let p = bases[0] + r.offset;
                            unmatched.push(json!({
                                "object": o.name, "section": s.name,
                                "offset": hex(r.offset), "site": hex(p),
                                "type": format!("{:?}", r.rtype), "symbol": sym_name,
                                "addend": r.addend,
                                "targets": ts.iter().map(|t| hex(*t)).collect::<Vec<_>>(),
                                "elfBytes": c.elf.bytes(p, width(false, r.rtype))
                                    .map(|b| b.iter().map(|x| format!("{x:02x}")).collect::<String>()),
                            }));
                        }
                    }
                }
            }
            // Functions.
            let funcs: Vec<_> = o
                .symbols
                .iter()
                .filter(|s| s.kind == SymKind::Func && matches!(s.sec, SymSection::Sec(_)))
                .collect();
            let mut fstats = [0usize; 5]; // defined, live, gc, visible-global, live-local
            let mut gc_names = Vec::new();
            for f in &funcs {
                let SymSection::Sec(j) = f.sec else { continue };
                fstats[0] += 1;
                match &c.place[li][j] {
                    Place::Bases { bases, .. } => {
                        fstats[1] += 1;
                        let addr = bases[0] + f.value;
                        let visible = c.elf.by_name.get(&f.raw_name).is_some_and(|ix| {
                            ix.iter().any(|&i| {
                                let es = &c.elf.syms[i];
                                es.global && es.typ == STT_FUNC && es.addr == addr
                            })
                        });
                        if visible {
                            fstats[3] += 1;
                        } else if f.bind == SymBind::Local {
                            fstats[4] += 1;
                        }
                    }
                    _ => {
                        fstats[2] += 1;
                        if gc_names.len() < 40 {
                            gc_names.push(f.name.clone());
                        }
                    }
                }
            }
            let multi_func_secs = (0..o.sections.len())
                .filter(|&j| {
                    is_exec(&o.sections[j])
                        && funcs.iter().filter(|f| f.sec == SymSection::Sec(j)).count() > 1
                })
                .count();
            // The file actually linked (a trimmed sysroot object's `elf_bytes` are the whole member).
            let path = &im.paths[li - lis[0]];
            let linked =
                std::fs::read(path).with_context(|| format!("reading {}", path.display()))?;
            let (eh_size, eh_relocs) = eh_frame_relocs(&linked);
            objects_json.push(json!({
                "name": o.name,
                "functions": {
                    "defined": fstats[0], "surviving": fstats[1], "gcd": fstats[2],
                    "visibleGlobalInSymtab": fstats[3], "survivingLocalOnly": fstats[4],
                    "textSectionsWithSeveralFunctions": multi_func_secs,
                    "gcdNames": gc_names,
                },
                "sections": {
                    "alloc": o.sections.len(), "placed": sec_stats[0], "byAnchor": sec_stats[1],
                    "byContent": sec_stats[2], "mergePieces": sec_stats[3], "gcdOrUnlocated": sec_stats[4],
                    "withNonRelocByteMismatch": sec_stats[5],
                    "unplacedNames": o.sections.iter().enumerate()
                        .filter(|(j, _)| matches!(c.place[li][*j], Place::Unplaced))
                        .map(|(_, s)| format!("{} ({} B)", s.name, s.size))
                        .take(40).collect::<Vec<_>>(),
                },
                "mergeSections": {
                    "pieces": merge[0], "unique": merge[1], "ambiguous": merge[2],
                    "notFound": merge[3], "tailMerged": merge[4],
                },
                "ehFrame": {"bytes": eh_size, "relocs": eh_relocs},
            }));
        }
        let range_json = |rs: &mut Vec<(u64, u64)>, exec: bool| -> Value {
            if rs.is_empty() {
                return Value::Null;
            }
            rs.sort();
            let (lo, hi) = (rs[0].0, rs.iter().map(|r| r.1).max().unwrap());
            let mut covered = 0u64;
            let mut end = lo;
            for &(a, b) in rs.iter() {
                if b > end {
                    covered += b - a.max(end);
                    end = b;
                }
            }
            let foreign: Vec<Value> = c
                .elf
                .syms
                .iter()
                .filter(|s| {
                    s.addr >= lo
                        && s.addr < hi
                        && (!exec || s.typ == STT_FUNC)
                        && s.typ != 0
                        && !lib_names.contains(&s.name)
                        && !rs.iter().any(|&(a, b)| a <= s.addr && s.addr < b)
                })
                .map(|s| json!({"name": s.name, "addr": hex(s.addr), "size": s.size}))
                .take(20)
                .collect();
            json!({
                "lo": hex(lo), "hi": hex(hi), "span": hi - lo, "libraryBytes": covered,
                "gapBytes": (hi - lo) - covered, "foreignSymbolsInGaps": foreign,
                "contiguous": foreign.is_empty(),
            })
        };
        let icf_folds: Vec<Value> = text_bases
            .iter()
            .filter(|(_, v)| v.len() > 1)
            .map(|(b, v)| json!({"addr": hex(*b), "sections": v}))
            .collect();
        let class_json = |m: &BTreeMap<Class, usize>| -> Value {
            Value::Object(
                m.iter()
                    .map(|(k, v)| (k.key().to_string(), json!(v)))
                    .collect(),
            )
        };
        let total_text: usize = classes.values().sum();
        let total_data: usize = data_classes.values().sum();
        out_images.push(json!({
            "config": im.config.display().to_string(),
            "objects": objects_json,
            "relocCounts": Value::Object(reloc_counts.into_iter().map(|(k, v)| (k, json!({
                "text": v[0], "textLive": v[1], "data": v[2], "dataLive": v[3],
            }))).collect()),
            "textSites": {"total": total_text, "byClass": class_json(&classes)},
            "dataSites": {"total": total_data, "byClass": class_json(&data_classes)},
            "matchedOnlyUpToAmbiguousPlacement": ambiguous_matches,
            "relaxationExamples": Value::Object(examples.into_iter()
                .map(|(k, v)| (k.key().to_string(), Value::Array(v))).collect()),
            "unmatchedSamples": unmatched,
            "unresolvedSamples": unresolved,
            "nonRelocByteMismatchSamples": byte_mismatch_samples,
            "icfFolds": icf_folds,
            "text": range_json(&mut text_ranges, true),
            "data": range_json(&mut data_ranges, false),
            "textOutputSections": text_out,
            "trustedLinkerTextLayout": trusted_layout(&c, k, im),
            "dataOutputSections": data_out,
        }));
    }
    let sec_size = |n: &str| {
        c.elf
            .secs
            .iter()
            .filter(|s| s.name == n)
            .map(|s| s.size)
            .sum::<u64>()
    };
    let got_slots: Vec<Value> = c
        .elf
        .secs
        .iter()
        .filter(|s| s.name == ".got" || s.name == ".got.plt")
        .flat_map(|s| {
            (0..s.size / 8)
                .map(move |k| s.addr + 8 * k)
                .collect::<Vec<_>>()
        })
        .map(|a| {
            let v = c.elf.u64_at(a).unwrap_or(0);
            let name = c
                .elf
                .syms
                .iter()
                .find(|s| s.addr == v && s.typ != 0 && v != 0)
                .map(|s| s.name.clone());
            json!({"slot": hex(a), "value": hex(v), "symbol": name})
        })
        .take(40)
        .collect();
    Ok(json!({
        "images": out_images,
        "executable": {
            "outputSections": c.elf.secs.iter().map(|s| json!({
                "name": s.name, "addr": hex(s.addr), "size": s.size,
            })).collect::<Vec<_>>(),
            "got": {"bytes": sec_size(".got"), "gotPltBytes": sec_size(".got.plt"), "slots": got_slots},
            "plt": {"pltBytes": sec_size(".plt"), "ipltBytes": sec_size(".iplt")},
            "thunks": thunks.iter().map(|(n, a, t)| json!({
                "name": n, "addr": hex(*a), "target": t.map(hex),
            })).collect::<Vec<_>>(),
            "ehFrameBytes": sec_size(".eh_frame"),
            "ehFrameHdrBytes": sec_size(".eh_frame_hdr"),
        },
    }))
}

#[cfg(test)]
mod tests {
    use super::relax::{NOP, adr, adrp_page, branch_target, ldr_to_add, ldr64_imm};
    use super::thunk_target;
    use std::collections::HashMap;

    #[test]
    fn adr_encodes_forward_and_backward_offsets() {
        // `adr x0, .+0x100`, `adr x8, .-4`, `adr x3, .+1` (immlo = 1).
        assert_eq!(adr(0, 0x1100, 0x1000), Some(0x1000_0800));
        assert_eq!(adr(8, 0x0ffc, 0x1000), Some(0x10ff_ffe8));
        assert_eq!(adr(3, 0x1001, 0x1000), Some(0x3000_0003));
        // The relaxed `nop; adr x0, crc_table` lld emitted in a stock link (word from the ELF).
        assert_eq!(adr(0, 0x2005bc, 0x212f20), Some(0x10f6_b4e0));
    }

    #[test]
    fn adr_rejects_targets_out_of_range() {
        assert_eq!(adr(0, 0x10_0000 + 0x1000, 0x1000), None);
        assert_eq!(
            adr(0, 0x0f_ffff + 0x1000, 0x1000).map(|w| w & 0x1f),
            Some(0)
        );
        assert_eq!(adr(0, 0x1000u64.wrapping_sub(0x10_0001), 0x1000), None);
        assert!(adr(0, 0x1000u64.wrapping_sub(0x10_0000), 0x1000).is_some());
    }

    #[test]
    fn adrp_page_and_ldr_offsets() {
        // `adrp x0, .+0x1000` and `adrp x0, .-0x1000` from a non-page-aligned pc.
        assert_eq!(adrp_page(0xb000_0000, 0x4123), Some(0x5000));
        assert_eq!(adrp_page(0xf0ff_ffe0, 0x4123), Some(0x3000));
        assert_eq!(adrp_page(NOP, 0x4123), None);
        // `ldr x1, [x2, #16]`; a 32-bit `ldr w1, [x2, #16]` is not a GOT load.
        assert_eq!(ldr64_imm(0xf940_0841), Some(16));
        assert_eq!(ldr64_imm(0xb940_1041), None);
        assert_eq!(ldr_to_add(0xf940_0841), 0x9100_0041);
    }

    #[test]
    fn branch_targets() {
        assert_eq!(branch_target(0x9400_0004, 0x1000), Some(0x1010)); // bl .+16
        assert_eq!(branch_target(0x17ff_ffff, 0x1000), Some(0x0ffc)); // b .-4
        assert_eq!(branch_target(NOP, 0x1000), None);
        assert_eq!(branch_target(0x5400_0040, 0x1000), None); // b.eq is not b/bl
    }

    fn mem(words: &[(u64, u32)]) -> impl Fn(u64) -> Option<u32> {
        let m: HashMap<u64, u32> = words.iter().copied().collect();
        move |a| m.get(&a).copied()
    }

    #[test]
    fn thunk_targets() {
        // Absolute: `ldr x16, #8; br x16; .quad 0x1_2345_6780`.
        let abs = mem(&[
            (0x100, 0x5800_0050),
            (0x104, 0xd61f_0200),
            (0x108, 0x2345_6780),
            (0x10c, 0x1),
        ]);
        assert_eq!(thunk_target(&abs, 0x100), Some(0x1_2345_6780));
        // Page-relative: `adrp x16, .+0x2000; add x16, x16, #0x10; br x16`.
        let rel = mem(&[
            (0x100, 0x9000_0010),
            (0x104, 0x9100_4210),
            (0x108, 0xd61f_0200),
        ]);
        assert_eq!(rel(0x100).and_then(|w| adrp_page(w, 0x100)), Some(0));
        let rel = mem(&[
            (0x100, 0xd000_0010),
            (0x104, 0x9100_4210),
            (0x108, 0xd61f_0200),
        ]);
        assert_eq!(thunk_target(&rel, 0x100), Some(0x2010));
        // Not a thunk: a different register, or no `br x16`.
        let other = mem(&[
            (0x100, 0xd000_0011),
            (0x104, 0x9100_4231),
            (0x108, 0xd61f_0220),
        ]);
        assert_eq!(thunk_target(&other, 0x100), None);
        let short = mem(&[(0x100, 0x5800_0050), (0x104, NOP)]);
        assert_eq!(thunk_target(&short, 0x100), None);
    }
}
