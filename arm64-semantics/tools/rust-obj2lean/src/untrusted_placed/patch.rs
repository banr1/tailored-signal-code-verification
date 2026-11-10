// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Rust mirror of the trusted Lean patch function and `Placeable` (`[OUTSIDE TCB]`).
//!
//! Mirrors `Arm64.Obj.CodeBlock.patchedWord` / `patched`, `PlacedLib.patchedData` and the
//! `CodeBlock.Placeable` / `PlacedLib.Placeable` conditions of `Arm64/Trusted/Object/Placed.lean`
//! (and the word patchers of `Arm64/Trusted/Object/Reloc.lean`), so that a witness is
//! checked before it is emitted. Disagreement with the Lean definitions only costs completeness:
//! the kernel re-checks everything.

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Result, bail, ensure};

use super::model::{PBlock, PLib, PMultiLib, PReloc};
use crate::trusted_common::RelocKind;

/// `Arm64.Obj.Placement` (`ρ` defaults to 0 off its domain, as the emitted lookup does).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PPlacement {
    pub base: u64,
    pub rho: BTreeMap<String, u64>,
    pub relax: BTreeSet<u64>,
    pub b2b: BTreeSet<u64>,
    /// `undefWeak`: weak references the linker left undefined.
    pub undef_weak: BTreeSet<String>,
}

impl PPlacement {
    pub fn rho(&self, s: &str) -> u64 {
        self.rho.get(s).copied().unwrap_or(0)
    }
}

/// `Arm64.Obj.MultiPlacement` (`bases[i]` per block, `ρ` for non-block symbols, per-block `relax`
/// and `b2b`, and `undefWeak`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PMultiPlacement {
    pub bases: Vec<u64>,
    pub rho: BTreeMap<String, u64>,
    pub relax: Vec<BTreeSet<u64>>,
    pub b2b: Vec<BTreeSet<u64>>,
    pub undef_weak: BTreeSet<String>,
}

impl PMultiPlacement {
    pub fn rho(&self, s: &str) -> u64 {
        self.rho.get(s).copied().unwrap_or(0)
    }
}

pub const NOP: u32 = 0xd503_201f;

pub fn is_adrp(w: u32) -> bool {
    w & 0x9f00_0000 == 0x9000_0000
}
pub fn is_add_imm64(w: u32) -> bool {
    w & 0xffc0_0000 == 0x9100_0000
}
pub fn is_ldr64_unsigned(w: u32) -> bool {
    w & 0xffc0_0000 == 0xf940_0000
}
pub fn is_b(w: u32) -> bool {
    w & 0xfc00_0000 == 0x1400_0000
}
pub fn adr_template(rd: u32) -> u32 {
    0x1000_0000 | (rd & 0x1f)
}
pub fn page_of(x: u64) -> u64 {
    x & !0xfff
}

pub fn branch_word(w: u32, place: u64, target: u64) -> u32 {
    (w & 0xfc00_0000) | ((target.wrapping_sub(place) >> 2) as u32 & 0x03ff_ffff)
}
pub fn adrp_word(w: u32, place: u64, target: u64) -> u32 {
    let pg = page_of(target).wrapping_sub(page_of(place));
    (w & 0x9f00_001f) | ((((pg >> 12) as u32) & 0x3) << 29) | ((((pg >> 14) as u32) & 0x7ffff) << 5)
}
pub fn adr_word(w: u32, place: u64, target: u64) -> u32 {
    let d = target.wrapping_sub(place);
    (w & 0x9f00_001f) | (((d as u32) & 0x3) << 29) | ((((d >> 2) as u32) & 0x7ffff) << 5)
}
pub fn lo12_word(scale: u32, w: u32, target: u64) -> u32 {
    (w & 0xffc0_03ff) | (((((target & 0xfff) >> scale) as u32) & 0xfff) << 10)
}
pub fn ldr_to_add_word(w: u32, target: u64) -> u32 {
    lo12_word(0, (w & 0x0000_03ff) | 0x9100_0000, target)
}
pub fn tlsie_movz_word(w: u32, tpoff: u64) -> u32 {
    let hi16 = ((tpoff >> 16) as u32) & 0xffff;
    0xd2a0_0000 | (hi16 << 5) | (w & 0x1f)
}
pub fn tlsie_movk_word(w: u32, tpoff: u64) -> u32 {
    let lo16 = (tpoff as u32) & 0xffff;
    0xf280_0000 | (lo16 << 5) | (w & 0x1f)
}
pub fn tls_ie_in_range(tpoff: u64) -> bool {
    tpoff < (1u64 << 32)
}
pub fn imm19_word(w: u32, place: u64, target: u64) -> u32 {
    let d = target.wrapping_sub(place);
    (w & 0xff00_001f) | ((((d >> 2) as u32) & 0x7ffff) << 5)
}
pub fn tstbr14_word(w: u32, place: u64, target: u64) -> u32 {
    let d = target.wrapping_sub(place);
    (w & 0xfff8_001f) | ((((d >> 2) as u32) & 0x3fff) << 5)
}

/// `tlsdescAdrPage21Word`: `movz x0, #((tprel >> 16) & 0xffff), lsl #16`.
pub fn tlsdesc_adr_page21_word(target: u64) -> u32 {
    0xd2a0_0000 | ((((target >> 16) as u32) & 0xffff) << 5)
}
/// `tlsdescLd64Lo12Word`: `movk x0, #(tprel & 0xffff)`.
pub fn tlsdesc_ld64_lo12_word(target: u64) -> u32 {
    0xf280_0000 | (((target as u32) & 0xffff) << 5)
}
/// `tprelHi12Word`: patches `imm12` (`bits [21:10]`) with `(tprel >> 12) & 0xfff`.
pub fn tprel_hi12_word(w: u32, target: u64) -> u32 {
    (w & 0xffc0_03ff) | ((((target >> 12) as u32) & 0xfff) << 10)
}
/// `movwSignedWord`: patches signed `MOVZ`/`MOVN` with `(tprel >> shift) & 0xffff` (or `~tprel` for negative).
pub fn movw_signed_word(shift: u32, w: u32, target: u64) -> u32 {
    if (target as i64) >= 0 {
        let imm16 = ((target >> shift) as u32) & 0xffff;
        (w & 0x7fe0_001f) | 0xd280_0000 | (imm16 << 5)
    } else {
        let inv = !target;
        let imm16 = ((inv >> shift) as u32) & 0xffff;
        (w & 0x3fe0_001f) | 0x9280_0000 | (imm16 << 5)
    }
}
/// `movwNcWord`: patches `imm16` (`bits [20:5]`) of `MOVK` with `(tprel >> shift) & 0xffff`.
pub fn movw_nc_word(shift: u32, w: u32, target: u64) -> u32 {
    (w & 0xffe0_001f) | ((((target >> shift) as u32) & 0xffff) << 5)
}
/// `tlsBaseOffset`: `alignUp(16, max(1, maxTlsAlign))`.
pub fn tls_base_offset(max_tls_align: u64) -> u64 {
    let a = max_tls_align.max(1);
    15u64.wrapping_add(a) / a * a
}

/// `patchRelocWord`.
pub fn patch_reloc_word(kind: RelocKind, w: u32, place: u64, target: u64) -> u32 {
    use RelocKind::*;
    match kind {
        Call26 | Jump26 => branch_word(w, place, target),
        AdrpHi21 | AdrpHi21Nc | AdrGotPage | TlsieAdrGottprelPage21 => adrp_word(w, place, target),
        AddLo12 | Ldst8Lo12 | TlsleAddTprelLo12 | TlsleAddTprelLo12Nc | TlsleLdst8TprelLo12Nc => {
            lo12_word(0, w, target)
        }
        Ldst16Lo12 | TlsleLdst16TprelLo12Nc => lo12_word(1, w, target),
        Ldst32Lo12 | TlsleLdst32TprelLo12Nc => lo12_word(2, w, target),
        Ldst64Lo12 | Ld64GotLo12Nc | TlsieLd64GottprelLo12Nc | TlsleLdst64TprelLo12Nc => {
            lo12_word(3, w, target)
        }
        Ldst128Lo12 | TlsleLdst128TprelLo12Nc => lo12_word(4, w, target),
        Condbr19 | LdPrelLo19 => imm19_word(w, place, target),
        Tstbr14 => tstbr14_word(w, place, target),
        AdrPrelLo21 => adr_word(w, place, target),
        Prel32 => target.wrapping_sub(place) as u32,
        TlsdescAdrPage21 => tlsdesc_adr_page21_word(target),
        TlsdescLd64Lo12 => tlsdesc_ld64_lo12_word(target),
        TlsdescAddLo12 | TlsdescCall => NOP,
        TlsleAddTprelHi12 => tprel_hi12_word(w, target),
        TlsleMovwTprelG1 => movw_signed_word(16, w, target),
        TlsleMovwTprelG1Nc => movw_nc_word(16, w, target),
        TlsleMovwTprelG0 => movw_signed_word(0, w, target),
        TlsleMovwTprelG0Nc => movw_nc_word(0, w, target),
        Abs64 | Abs32 => w,
    }
}

fn in_signed(d: u64, lo: i64, hi: i64) -> bool {
    let d = d as i64;
    lo <= d && d < hi
}

/// `CodeRelocInRange`.
pub fn code_reloc_in_range(kind: RelocKind, place: u64, target: u64) -> bool {
    use RelocKind::*;
    let d = target.wrapping_sub(place);
    let lo12 = |s: u32| target & ((1u64 << s) - 1) == 0;
    match kind {
        Call26 | Jump26 => d % 4 == 0 && in_signed(d, -(1 << 27), 1 << 27),
        AdrpHi21 | AdrGotPage | TlsieAdrGottprelPage21 => in_signed(
            page_of(target).wrapping_sub(page_of(place)),
            -(1 << 32),
            1 << 32,
        ),
        AdrpHi21Nc | AddLo12 | Ldst8Lo12 | TlsleAddTprelLo12Nc | TlsleLdst8TprelLo12Nc
        | TlsleMovwTprelG1Nc | TlsleMovwTprelG0Nc => true,
        Ldst16Lo12 | TlsleLdst16TprelLo12Nc => lo12(1),
        Ldst32Lo12 | TlsleLdst32TprelLo12Nc => lo12(2),
        Ldst64Lo12 | Ld64GotLo12Nc | TlsieLd64GottprelLo12Nc | TlsleLdst64TprelLo12Nc => lo12(3),
        Ldst128Lo12 | TlsleLdst128TprelLo12Nc => lo12(4),
        Condbr19 | LdPrelLo19 => d % 4 == 0 && in_signed(d, -(1 << 20), 1 << 20),
        Tstbr14 => d % 4 == 0 && in_signed(d, -(1 << 15), 1 << 15),
        AdrPrelLo21 => in_signed(d, -(1 << 20), 1 << 20),
        Prel32 => in_signed(d, -(1 << 31), 1 << 31),
        TlsdescAdrPage21 | TlsdescLd64Lo12 | TlsdescAddLo12 | TlsdescCall => {
            in_signed(target, 0, 1 << 32)
        }
        TlsleAddTprelHi12 => in_signed(target, 0, 1 << 24),
        TlsleAddTprelLo12 => in_signed(target, 0, 1 << 12),
        TlsleMovwTprelG1 => in_signed(target, -(1 << 32), 1 << 32),
        TlsleMovwTprelG0 => in_signed(target, -(1 << 16), 1 << 16),
        Abs64 | Abs32 => false,
    }
}

/// `addSignedAddr`.
pub fn add_signed(a: u64, addend: i64) -> u64 {
    a.wrapping_add(addend as u64)
}

impl PBlock {
    /// `wordAt` (bytes past the end read as zero).
    pub fn word_at(&self, off: u64) -> u32 {
        let mut b = [0u8; 4];
        for (i, x) in b.iter_mut().enumerate() {
            *x = self.code.get(off as usize + i).copied().unwrap_or(0);
        }
        u32::from_le_bytes(b)
    }

    /// `relocAt?` (first match).
    pub fn reloc_at(&self, off: u64) -> Option<&PReloc> {
        self.relocs.iter().find(|r| r.off == off)
    }

    /// `resolve`.
    pub fn resolve(&self, pl: &PPlacement, sym: &str) -> u64 {
        match self.lookup(sym) {
            Some(off) => pl.base.wrapping_add(off),
            None => pl.rho(sym),
        }
    }

    /// `target`.
    pub fn target(&self, pl: &PPlacement, r: &PReloc) -> u64 {
        add_signed(self.resolve(pl, &r.sym), r.addend)
    }

    /// `relaxableAt`.
    pub fn relaxable_at(&self, off: u64) -> bool {
        let (Some(r1), Some(r2)) = (self.reloc_at(off), self.reloc_at(off + 4)) else {
            return false;
        };
        let (w1, w2) = (self.word_at(off), self.word_at(off + 4));
        r1.kind == RelocKind::AdrpHi21
            && r2.kind == RelocKind::AddLo12
            && r1.sym == r2.sym
            && r1.addend == r2.addend
            && is_adrp(w1)
            && is_add_imm64(w2)
            && (w1 & 0x1f) != 0x1f
            && w1 & 0x1f == w2 & 0x1f
            && (w2 >> 5) & 0x1f == w1 & 0x1f
    }

    /// `gotPairAt`.
    pub fn got_pair_at(&self, off: u64) -> bool {
        let (Some(r1), Some(r2)) = (self.reloc_at(off), self.reloc_at(off + 4)) else {
            return false;
        };
        let (w1, w2) = (self.word_at(off), self.word_at(off + 4));
        r1.kind == RelocKind::AdrGotPage
            && r2.kind == RelocKind::Ld64GotLo12Nc
            && r1.sym == r2.sym
            && r1.addend == 0
            && r2.addend == 0
            && is_adrp(w1)
            && is_ldr64_unsigned(w2)
            && (w1 & 0x1f) != 0x1f
            && w1 & 0x1f == w2 & 0x1f
            && (w2 >> 5) & 0x1f == w1 & 0x1f
    }

    /// `gotRelaxedToAdrAt`.
    pub fn got_relaxed_to_adr_at(&self, pl: &PPlacement, off: u64) -> bool {
        self.got_pair_at(off) && pl.relax.contains(&off)
    }

    /// `gotRelaxedToAddAt`.
    pub fn got_relaxed_to_add_at(&self, pl: &PPlacement, off: u64) -> bool {
        self.got_pair_at(off) && !pl.relax.contains(&off) && pl.relax.contains(&(off + 4))
    }

    /// `tlsieRelaxableAt`.
    pub fn tlsie_relaxable_at(&self, off: u64) -> bool {
        let Some(r) = self.reloc_at(off) else {
            return false;
        };
        let w = self.word_at(off);
        match r.kind {
            RelocKind::TlsieAdrGottprelPage21 => is_adrp(w),
            RelocKind::TlsieLd64GottprelLo12Nc => {
                is_ldr64_unsigned(w) && ((w >> 5) & 0x1f) == (w & 0x1f)
            }
            _ => false,
        }
    }

    /// `tlsieRelaxedAt`.
    pub fn tlsie_relaxed_at(&self, pl: &PPlacement, off: u64) -> bool {
        self.tlsie_relaxable_at(off) && pl.relax.contains(&off)
    }

    /// `b2bNext?`.
    pub fn b2b_next(&self, r: &PReloc) -> Option<&PReloc> {
        if !matches!(r.kind, RelocKind::Call26 | RelocKind::Jump26) {
            return None;
        }
        let sym_off = self.lookup(&r.sym)?;
        let t = sym_off as i128 + r.addend as i128;
        if t < 0 {
            return None;
        }
        let t = t as u64;
        let r2 = self.reloc_at(t)?;
        (r2.kind == RelocKind::Jump26 && is_b(self.word_at(t))).then_some(r2)
    }

    /// `relocTarget`.
    pub fn reloc_target(&self, pl: &PPlacement, off: u64, r: &PReloc) -> u64 {
        match if pl.b2b.contains(&off) {
            self.b2b_next(r)
        } else {
            None
        } {
            Some(r2) => self.target(pl, r2),
            None => self.target(pl, r),
        }
    }

    /// `relaxedAt`.
    pub fn relaxed_at(&self, pl: &PPlacement, off: u64) -> bool {
        self.relaxable_at(off) && pl.relax.contains(&off)
    }

    /// `undefWeakBranch`.
    pub fn undef_weak_branch(&self, pl: &PPlacement, r: &PReloc) -> bool {
        self.weak_refs.contains(&r.sym)
            && matches!(r.kind, RelocKind::Call26 | RelocKind::Jump26)
            && pl.undef_weak.contains(&r.sym)
    }

    /// `patchGotOrTlsIeRelaxed`.
    pub fn patch_got_or_tlsie_relaxed(&self, pl: &PPlacement, off: u64, r: &PReloc, w: u32) -> u32 {
        let place = pl.base.wrapping_add(off);
        let t = self.target(pl, r);
        if self.got_relaxed_to_adr_at(pl, off) {
            NOP
        } else if off >= 4 && self.got_relaxed_to_adr_at(pl, off - 4) {
            adr_word(adr_template(w), place, t)
        } else if self.got_relaxed_to_add_at(pl, off) {
            adrp_word(w, place, t)
        } else if off >= 4 && self.got_relaxed_to_add_at(pl, off - 4) {
            ldr_to_add_word(w, t)
        } else if r.kind == RelocKind::TlsieAdrGottprelPage21 {
            tlsie_movz_word(w, t)
        } else {
            tlsie_movk_word(w, t)
        }
    }

    /// `patchedWord`.
    pub fn patched_word(&self, pl: &PPlacement, off: u64) -> u32 {
        let w = self.word_at(off);
        let Some(r) = self.reloc_at(off) else {
            return w;
        };
        let place = pl.base.wrapping_add(off);
        if self.relaxed_at(pl, off) {
            NOP
        } else if off >= 4 && self.relaxed_at(pl, off - 4) {
            adr_word(adr_template(w), place, self.target(pl, r))
        } else if r.kind.is_got_or_tls_ie()
            && (self.got_relaxed_to_adr_at(pl, off)
                || (off >= 4 && self.got_relaxed_to_adr_at(pl, off - 4))
                || self.got_relaxed_to_add_at(pl, off)
                || (off >= 4 && self.got_relaxed_to_add_at(pl, off - 4))
                || self.tlsie_relaxed_at(pl, off))
        {
            self.patch_got_or_tlsie_relaxed(pl, off, r, w)
        } else if self.undef_weak_branch(pl, r) {
            patch_reloc_word(r.kind, w, place, place.wrapping_add(4))
        } else {
            patch_reloc_word(r.kind, w, place, self.reloc_target(pl, off, r))
        }
    }

    /// `patched`.
    pub fn patched(&self, pl: &PPlacement) -> Vec<u8> {
        let n = self.code.len() as u64 / 4;
        (0..n)
            .flat_map(|j| self.patched_word(pl, 4 * j).to_le_bytes())
            .collect()
    }

    /// `CodeBlock.Placeable`, with the first violated condition as the error.
    pub fn check_placeable(&self, pl: &PPlacement) -> Result<()> {
        let len = self.code.len() as u64;
        ensure!(self.align > 0 && self.align % 4 == 0, "align_pos");
        ensure!(pl.base % self.align == 0, "base_aligned");
        ensure!((pl.base as u128) + len as u128 <= 1u128 << 64, "no_wrap");
        ensure!(len % 4 == 0, "len_aligned");
        let mut seen = BTreeSet::new();
        for r in &self.relocs {
            ensure!(seen.insert(r.off), "relocs_nodup: {:#x}", r.off);
        }
        for r in &self.relocs {
            ensure!(
                r.off % 4 == 0 && r.off + 4 <= len,
                "relocs_ok: bounds at {:#x}",
                r.off
            );
            let place = pl.base.wrapping_add(r.off);
            let t = self.reloc_target(pl, r.off, r);
            let ok = if self.got_relaxed_to_adr_at(pl, r.off) {
                true
            } else if r.off >= 4 && self.got_relaxed_to_adr_at(pl, r.off - 4) {
                code_reloc_in_range(RelocKind::AdrPrelLo21, place, self.target(pl, r))
            } else if self.got_relaxed_to_add_at(pl, r.off) {
                code_reloc_in_range(RelocKind::AdrpHi21, place, self.target(pl, r))
            } else if r.off >= 4 && self.got_relaxed_to_add_at(pl, r.off - 4) {
                code_reloc_in_range(RelocKind::AddLo12, place, self.target(pl, r))
            } else if self.tlsie_relaxed_at(pl, r.off) {
                tls_ie_in_range(self.target(pl, r))
            } else {
                code_reloc_in_range(r.kind, place, t)
            };
            ensure!(
                ok,
                "relocs_ok: {:?} at {:#x} to {} = {t:#x} out of range",
                r.kind,
                r.off,
                r.sym
            );
        }
        for &off in &pl.relax {
            if (self.relaxed_at(pl, off) || self.got_relaxed_to_adr_at(pl, off))
                && let Some(r) = self.reloc_at(off + 4)
            {
                let place = pl.base.wrapping_add(off + 4);
                ensure!(
                    code_reloc_in_range(RelocKind::AdrPrelLo21, place, self.target(pl, r)),
                    "relaxed_ok at {off:#x}"
                );
            }
        }
        for (s, o) in &self.symbols {
            ensure!(o % 4 == 0 && *o <= len, "symbols_ok: {s}");
        }
        for e in &self.externs {
            ensure!(
                self.lookup(e).is_none(),
                "externs_ok: {e} is a block symbol"
            );
            ensure!(
                pl.rho(e).wrapping_sub(pl.base) >= len,
                "externs_ok: {e} inside the block"
            );
        }
        Ok(())
    }
}

/// Width of a data relocation (`dataRelocWidth`).
pub fn data_reloc_width(k: RelocKind) -> u64 {
    match k {
        RelocKind::Abs64 => 8,
        RelocKind::Abs32 | RelocKind::Prel32 => 4,
        _ => 0,
    }
}

impl PLib {
    /// `PlacedLib.patchedData` (relocated bytes followed by the zero tail).
    pub fn patched_data(&self, pl: &PPlacement, k: usize) -> Vec<u8> {
        let d = &self.data[k];
        let addr = pl.rho(&d.sym);
        let mut bytes = d.bytes.clone();
        for r in &d.relocs {
            let t = add_signed(self.text.resolve(pl, &r.sym), r.addend);
            let (n, v) = match r.kind {
                RelocKind::Abs64 => (8, t),
                RelocKind::Abs32 => (4, t),
                RelocKind::Prel32 => (4, t.wrapping_sub(addr.wrapping_add(r.off))),
                _ => continue,
            };
            // `take off ++ bytesLE n v ++ drop (off + n)`.
            let off = r.off as usize;
            let mut out: Vec<u8> = bytes.iter().take(off).copied().collect();
            out.extend_from_slice(&v.to_le_bytes()[..n]);
            out.extend(bytes.iter().skip(off + n).copied());
            bytes = out;
        }
        bytes.extend(std::iter::repeat_n(0u8, d.zero_tail as usize));
        bytes
    }

    /// `PlacedLib.Placeable`.
    pub fn check_placeable(&self, pl: &PPlacement) -> Result<()> {
        self.text.check_placeable(pl)?;
        let mut seen = BTreeSet::new();
        for d in &self.data {
            ensure!(seen.insert(&d.sym), "data_nodup: {}", d.sym);
        }
        for d in &self.data {
            ensure!(
                self.text.lookup(&d.sym).is_none(),
                "data_ok: {} is a block symbol",
                d.sym
            );
            ensure!(d.align > 0, "data_ok: {} align", d.sym);
            let a = pl.rho(&d.sym);
            ensure!(a % d.align == 0, "data_ok: {} at {a:#x} misaligned", d.sym);
            ensure!(
                a as u128 + d.bytes.len() as u128 + d.zero_tail as u128 <= 1u128 << 64,
                "data_ok: {} wraps",
                d.sym
            );
            for r in &d.relocs {
                let w = data_reloc_width(r.kind);
                ensure!(
                    w > 0,
                    "data_relocs_ok: {} has code relocation {:?}",
                    d.sym,
                    r.kind
                );
                ensure!(
                    r.off + w <= d.bytes.len() as u64,
                    "data_relocs_ok: {} bounds",
                    d.sym
                );
                let t = add_signed(self.text.resolve(pl, &r.sym), r.addend);
                match r.kind {
                    RelocKind::Abs32 => {
                        let ti = t as i64 as i128;
                        ensure!(
                            -(1i128 << 31) <= ti && ti < 1i128 << 32,
                            "data_relocs_ok: abs32 in {} out of range",
                            d.sym
                        )
                    }
                    RelocKind::Prel32 => ensure!(
                        in_signed(t.wrapping_sub(a.wrapping_add(r.off)), -(1 << 31), 1 << 31),
                        "data_relocs_ok: prel32 in {} out of range",
                        d.sym
                    ),
                    RelocKind::Abs64 => {}
                    _ => bail!("unreachable"),
                }
            }
        }
        Ok(())
    }
}

impl PMultiLib {
    /// `MultiPlacedLib.resolve`.
    pub fn resolve(&self, mpl: &PMultiPlacement, sym: &str) -> u64 {
        if let Some((i, off)) = self.lookup_block_sym(sym) {
            mpl.bases.get(i).copied().unwrap_or(0).wrapping_add(off)
        } else {
            mpl.rho(sym)
        }
    }

    /// `MultiPlacedLib.blockPlacement`.
    pub fn block_placement(&self, mpl: &PMultiPlacement, i: usize) -> PPlacement {
        let mut rho = mpl.rho.clone();
        for (bi, b) in self.blocks.iter().enumerate() {
            let base = mpl.bases.get(bi).copied().unwrap_or(0);
            for (s, off) in &b.symbols {
                rho.insert(s.clone(), base.wrapping_add(*off));
            }
        }
        PPlacement {
            base: mpl.bases.get(i).copied().unwrap_or(0),
            rho,
            relax: mpl.relax.get(i).cloned().unwrap_or_default(),
            b2b: mpl.b2b.get(i).cloned().unwrap_or_default(),
            undef_weak: mpl.undef_weak.clone(),
        }
    }

    /// `MultiPlacedLib.patchedData`.
    pub fn patched_data(&self, mpl: &PMultiPlacement, k: usize) -> Vec<u8> {
        let d = &self.data[k];
        let addr = mpl.rho(&d.sym);
        let mut bytes = d.bytes.clone();
        for r in &d.relocs {
            let t = add_signed(self.resolve(mpl, &r.sym), r.addend);
            let (n, v) = match r.kind {
                RelocKind::Abs64 => (8, t),
                RelocKind::Abs32 => (4, t),
                RelocKind::Prel32 => (4, t.wrapping_sub(addr.wrapping_add(r.off))),
                _ => continue,
            };
            let off = r.off as usize;
            let mut out: Vec<u8> = bytes.iter().take(off).copied().collect();
            out.extend_from_slice(&v.to_le_bytes()[..n]);
            out.extend(bytes.iter().skip(off + n).copied());
            bytes = out;
        }
        bytes.extend(std::iter::repeat_n(0u8, d.zero_tail as usize));
        bytes
    }

    /// `MultiPlacedLib.Placeable`.
    pub fn check_placeable(&self, mpl: &PMultiPlacement) -> Result<()> {
        for (i, b) in self.blocks.iter().enumerate() {
            let bp = self.block_placement(mpl, i);
            b.check_placeable(&bp)
                .map_err(|e| anyhow::anyhow!("block {i}: {e}"))?;
        }
        for i in 0..self.blocks.len() {
            let b1 = mpl.bases.get(i).copied().unwrap_or(0) as u128;
            let n1 = self.blocks[i].code.len() as u128;
            for j in (i + 1)..self.blocks.len() {
                let b2 = mpl.bases.get(j).copied().unwrap_or(0) as u128;
                let n2 = self.blocks[j].code.len() as u128;
                ensure!(
                    b1 + n1 <= b2 || b2 + n2 <= b1,
                    "blocks_disjoint: block {i} [{b1:#x}..{:#x}) overlaps block {j} [{b2:#x}..{:#x})",
                    b1 + n1,
                    b2 + n2
                );
            }
        }
        let mut sym_seen = BTreeSet::new();
        for b in &self.blocks {
            for (s, _) in &b.symbols {
                ensure!(sym_seen.insert(s.as_str()), "symbols_nodup: {s}");
            }
        }
        let mut data_seen = BTreeSet::new();
        for d in &self.data {
            ensure!(data_seen.insert(d.sym.as_str()), "data_nodup: {}", d.sym);
        }
        for d in &self.data {
            ensure!(
                self.lookup_block_sym(&d.sym).is_none(),
                "data_ok: {} is a block symbol",
                d.sym
            );
            ensure!(d.align > 0, "data_ok: {} align", d.sym);
            let a = mpl.rho(&d.sym);
            ensure!(a % d.align == 0, "data_ok: {} at {a:#x} misaligned", d.sym);
            ensure!(
                a as u128 + d.bytes.len() as u128 + d.zero_tail as u128 <= 1u128 << 64,
                "data_ok: {} wraps",
                d.sym
            );
            for r in &d.relocs {
                let w = data_reloc_width(r.kind);
                ensure!(
                    w > 0,
                    "data_relocs_ok: {} has code relocation {:?}",
                    d.sym,
                    r.kind
                );
                ensure!(
                    r.off + w <= d.bytes.len() as u64,
                    "data_relocs_ok: {} bounds",
                    d.sym
                );
                let t = add_signed(self.resolve(mpl, &r.sym), r.addend);
                match r.kind {
                    RelocKind::Abs32 => {
                        let ti = t as i64 as i128;
                        ensure!(
                            -(1i128 << 31) <= ti && ti < 1i128 << 32,
                            "data_relocs_ok: abs32 in {} out of range",
                            d.sym
                        )
                    }
                    RelocKind::Prel32 => ensure!(
                        in_signed(t.wrapping_sub(a.wrapping_add(r.off)), -(1 << 31), 1 << 31),
                        "data_relocs_ok: prel32 in {} out of range",
                        d.sym
                    ),
                    RelocKind::Abs64 => {}
                    _ => bail!("unreachable"),
                }
            }
        }
        Ok(())
    }
}
