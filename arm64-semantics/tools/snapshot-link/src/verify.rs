// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Embedding checks for a linked executable (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — an early, readable failure when the link recipe drifts.
//!   Soundness does not depend on it: Lean proofs compare the *snapshot* bytes with the image.
//! - **Purpose:** For an executable linked by [`crate::link`], check for every image at its
//!   `base` (image `k > 0` uses `.img<k>.*` sections instead of `.img.*`) that
//!   - every code byte of the image is at `base + i` in `.img.text`, except that for branch stubs
//!     ([`StubMode::Branch`] or `--branch-stubs`) each stub word is `b <extern>` to the image that
//!     defines the extern or else to its definition outside every image ([`extern_symbols`]: a
//!     same-named symbol inside an image is never the target);
//!   - the image data sections (`.img.data` in interleaved mode, or `.img.rodata` concatenated
//!     with `.img.data` in page-separated mode) hold the image data with every `DataReloc`
//!     applied for `base` (exactly the bytes `Arm64.Obj.LinkedImage.load` produces), followed by
//!     `bss` zero bytes;
//!   - in interleaved mode, image code is in an `r-x` segment and image data/GOT are in
//!     non-executable segments; in page-separated mode (`page_separate_data`), code is in a
//!     `PF_R | PF_X` segment, read-only data and the GOT page are in `PF_R` segments with
//!     explicit file zero-fill (`p_filesz` covers every byte), writable data / bss / extern data
//!     are in `PF_R | PF_W` segments, no page mixes read-only and writable image bytes, and no
//!     two non-empty `PT_LOAD` segments share a 4 KiB page; in both modes no non-image section
//!     overlaps an image and no TLS sections lack `PT_TLS`;
//!   - every image symbol `(name, off)` is an ELF symbol `name` (without a ` [<object>]`
//!     suffix) at `base + off`;
//!   - no two images overlap.
//!
//! # Key Types & Functions
//! - [`check_images`], [`check_std_elf`] (flagged pure aliases exempted by
//!   [`check_std_elf_exempting`] / [`forbidden_symbols`]), [`ImageCheck`], [`extern_symbols`], [`Report`],
//!   [`relocated_data`], [`b_target`], [`encode_b`].
//!
//! # When to Read This File
//! - Read this file to see what the CI embedding test guarantees.

use crate::StubMode;
use crate::link::{PAGE, Stub, img_prefix};
use anyhow::{Context, Result, bail, ensure};
use object::elf::{
    EM_AARCH64, ET_EXEC, PF_R, PF_W, PF_X, PT_DYNAMIC, PT_GNU_EH_FRAME, PT_GNU_PROPERTY,
    PT_GNU_RELRO, PT_GNU_STACK, PT_INTERP, PT_LOAD, PT_NOTE, PT_NULL, PT_PHDR, PT_TLS, SHF_TLS,
};
use object::read::elf::{ElfFile64, FileHeader, ProgramHeader};
use object::{Endianness, Object, ObjectSection, ObjectSymbol, SectionFlags};
use rust_obj2lean::trusted_common::{ObjObject, SymBind, SymKind, SymSection};
use rust_obj2lean::untrusted_legacy_linker::LinkedImage;
use std::collections::{HashMap, HashSet};

/// Result of [`check_images`].
#[derive(Debug, Default)]
pub struct Report {
    pub code_bytes: usize,
    pub stub_words: usize,
    pub data_bytes: usize,
    pub relocs: usize,
    pub symbols: usize,
    pub stub_targets: HashMap<u64, u64>,
    pub errors: Vec<String>,
}

impl Report {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
    pub fn summary(&self) -> String {
        format!(
            "{} code bytes ({} stub words), {} data bytes ({} relocations), {} symbols checked",
            self.code_bytes, self.stub_words, self.data_bytes, self.relocs, self.symbols
        )
    }
    pub fn json(&self) -> serde_json::Value {
        serde_json::json!({
            "codeBytes": self.code_bytes, "stubWords": self.stub_words,
            "dataBytes": self.data_bytes, "relocs": self.relocs, "symbols": self.symbols,
            "errors": self.errors,
        })
    }
}

/// The image data with every relocation applied for `base`.
pub fn relocated_data(li: &LinkedImage, base: u64) -> Result<Vec<u8>> {
    let mut d = li.data.clone();
    for r in &li.relocs {
        let v = base.wrapping_add(r.target).to_le_bytes();
        let o = r.off as usize;
        let w = r.width as usize;
        if !(w == 4 || w == 8) || o + w > d.len() {
            bail!("unsupported DataReloc {r:?}");
        }
        d[o..o + w].copy_from_slice(&v[..w]);
    }
    Ok(d)
}

/// Target of the AArch64 `B` instruction `w` at `pc`, if `w` is one.
pub fn b_target(w: u32, pc: u64) -> Option<u64> {
    if w >> 26 != 0b000101 {
        return None;
    }
    let imm = (((w & 0x03ff_ffff) << 6) as i32 >> 6) as i64 * 4;
    Some(pc.wrapping_add(imm as u64))
}

/// Expected AArch64 unconditional branch word `B <target>` from `pc` (`0x1400_0000 | ((target - pc) >> 2 & 0x03ff_ffff)`),
/// returning `None` if `target - pc` is not 4-byte aligned or outside `[-128 MiB, +128 MiB - 4]`.
pub fn encode_b(pc: u64, target: u64) -> Option<u32> {
    let disp = (target.wrapping_sub(pc)) as i64;
    if disp % 4 != 0 || !(-0x0800_0000..0x0800_0000).contains(&disp) {
        return None;
    }
    let imm26 = ((disp >> 2) as u32) & 0x03ff_ffff;
    Some(0x1400_0000 | imm26)
}

fn section_bytes(elf: &ElfFile64<Endianness>, name: &str) -> Result<Option<(u64, u64, Vec<u8>)>> {
    match elf.section_by_name(name) {
        None => Ok(None),
        Some(s) => Ok(Some((
            s.address(),
            s.size(),
            s.uncompressed_data()?.into_owned(),
        ))),
    }
}

/// One image of a linked executable, for [`check_images`].
pub struct ImageCheck<'a> {
    /// Index of the image on the command line (names its sections, see [`img_prefix`]).
    pub tag: usize,
    pub objs: &'a [ObjObject],
    pub li: &'a LinkedImage,
    pub base: u64,
    /// [`crate::link::image_extent_with`] of `li`.
    pub extent: u64,
    pub stubs: &'a [Stub],
    /// Per stub (or empty): the address another image resolves it to; `None` means the stub
    /// must branch to the extern's definition outside every image ([`extern_symbols`]).
    pub targets: Vec<Option<u64>>,
    /// Whether this image uses the opt-in page-separated data layout.
    pub page_separate_data: bool,
}

/// Where an undefined reference from an image to each name resolves in `elf_bytes`, when no
/// image exports that name (`main`, native objects, and the C runtime): the address of the defined
/// code or data symbol with that name outside every image range `[start, end)` of `images`. A
/// global or weak definition wins; otherwise a single local address is taken (a static link turns
/// hidden runtime globals into local symbols); a name with several local addresses and no global
/// one is left out. Symbols inside an image, such as a same-named local function of another image,
/// are never candidates.
pub fn extern_symbols(elf_bytes: &[u8], images: &[(u64, u64)]) -> Result<HashMap<String, u64>> {
    use object::SymbolKind;
    let elf = ElfFile64::<Endianness>::parse(elf_bytes).context("cannot parse the executable")?;
    let in_image = |a: u64| images.iter().any(|&(s, e)| s <= a && a < e);
    let mut global: HashMap<String, u64> = HashMap::new();
    let mut local: HashMap<String, Vec<u64>> = HashMap::new();
    for s in elf.symbols() {
        let Ok(n) = s.name() else { continue };
        if n.is_empty()
            || s.is_undefined()
            || matches!(s.kind(), SymbolKind::File | SymbolKind::Section)
            || in_image(s.address())
        {
            continue;
        }
        if s.is_local() {
            let v = local.entry(n.to_string()).or_default();
            if !v.contains(&s.address()) {
                v.push(s.address());
            }
        } else {
            global.entry(n.to_string()).or_insert(s.address());
        }
    }
    for (n, v) in local {
        if let [a] = v[..] {
            global.entry(n).or_insert(a);
        }
    }
    Ok(global)
}

/// Single-image convenience wrapper around [`check_images`] for unit tests.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub fn check(
    elf_bytes: &[u8],
    objs: &[ObjObject],
    li: &LinkedImage,
    base: u64,
    stubs: &[Stub],
    mode: StubMode,
    branch_stubs: &[String],
    page_separate_data: bool,
) -> Result<Report> {
    check_images(
        elf_bytes,
        &[ImageCheck {
            tag: 0,
            objs,
            li,
            base,
            extent: crate::link::image_extent_with(li, page_separate_data),
            stubs,
            targets: Vec::new(),
            page_separate_data,
        }],
        mode,
        branch_stubs,
    )
}

/// Check that `elf_bytes` embeds every image of `images` at its base with global stub `mode` and
/// per-extern `branch_stubs`, and that images (and, in page-separated mode, all `PT_LOAD`
/// segments) are disjoint.
pub fn check_images(
    elf_bytes: &[u8],
    images: &[ImageCheck],
    mode: StubMode,
    branch_stubs: &[String],
) -> Result<Report> {
    let elf = ElfFile64::<Endianness>::parse(elf_bytes).context("cannot parse the executable")?;
    let mut r = Report::default();
    let mut syms: HashMap<&str, Vec<u64>> = HashMap::new();
    for s in elf.symbols() {
        if let Ok(n) = s.name()
            && !s.is_undefined()
        {
            syms.entry(n).or_default().push(s.address());
        }
    }
    let ranges: Vec<(u64, u64)> = images
        .iter()
        .map(|im| (im.base, im.base + im.extent))
        .collect();
    let externs = extern_symbols(elf_bytes, &ranges)?;
    let e = elf.endian();
    let phdrs = elf.elf_header().program_headers(e, elf.data())?;
    let rwx = PF_R | PF_W | PF_X;
    let seg_of = |a: u64| {
        phdrs.iter().find(|p| {
            p.p_type(e) == PT_LOAD && p.p_vaddr(e) <= a && a < p.p_vaddr(e) + p.p_memsz(e)
        })
    };
    let mut errs = Vec::new();
    for (i, a) in images.iter().enumerate() {
        for b in &images[i + 1..] {
            let (a0, a1, b0, b1) = (a.base, a.base + a.extent, b.base, b.base + b.extent);
            if a0 < b1 && b0 < a1 {
                errs.push(format!(
                    "image {} [{a0:#x}, {a1:#x}) overlaps image {} [{b0:#x}, {b1:#x})",
                    a.tag, b.tag
                ));
            }
        }
    }

    if images.iter().any(|im| im.page_separate_data) {
        // Check every pair of non-empty PT_LOAD segments is strictly page-disjoint (hence never
        // shares a 4 KiB page with another PT_LOAD segment of any flags).
        let mut page_owner: HashMap<u64, (usize, u32)> = HashMap::new();
        for (idx, p) in phdrs.iter().enumerate() {
            if p.p_type(e) != PT_LOAD || p.p_memsz(e) == 0 {
                continue;
            }
            let vaddr = p.p_vaddr(e);
            let memsz = p.p_memsz(e);
            let flags = p.p_flags(e) & rwx;
            let first_pg = vaddr & !(PAGE - 1);
            let end_pg = (vaddr + memsz + PAGE - 1) & !(PAGE - 1);
            let mut pg = first_pg;
            while pg < end_pg {
                if let Some(&(prev_idx, prev_flags)) = page_owner.get(&pg) {
                    errs.push(format!(
                        "PT_LOAD[{idx}] (flags {flags:#x}) overlaps page {pg:#x} of PT_LOAD[{prev_idx}] (flags {prev_flags:#x})"
                    ));
                    break;
                }
                page_owner.insert(pg, (idx, flags));
                pg += PAGE;
            }
        }
    }

    for im in images {
        let (li, base) = (im.li, im.base);
        let pfx = img_prefix(im.tag);
        // Errors name the image only when there are several.
        let who = if images.len() > 1 {
            format!("image {}: ", im.tag)
        } else {
            String::new()
        };
        let mut errs_im = Vec::new();

        // Code and stubs.
        let stub_at: HashMap<u64, (usize, &Stub)> = im
            .stubs
            .iter()
            .enumerate()
            .map(|(k, s)| (s.off, (k, s)))
            .collect();
        match section_bytes(&elf, &format!("{pfx}text"))? {
            None => errs_im.push(format!("no {pfx}text section")),
            Some((addr, _, bytes)) => {
                if addr != base || bytes.len() != li.code.len() {
                    errs_im.push(format!(
                        "{pfx}text at {addr:#x} with {} bytes, expected {base:#x} with {}",
                        bytes.len(),
                        li.code.len()
                    ));
                } else {
                    for off in (0..bytes.len()).step_by(4) {
                        let end = (off + 4).min(bytes.len());
                        let (ours, theirs) = (&li.code[off..end], &bytes[off..end]);
                        match stub_at.get(&(off as u64)).map(|&(k, s)| {
                            (
                                k,
                                s,
                                crate::link::effective_stub_mode(&s.raw, mode, branch_stubs),
                            )
                        }) {
                            Some((k, s, StubMode::Branch)) => {
                                if ours != [0, 0, 0, 0] {
                                    errs_im.push(format!(
                                        "stub {} at offset {off:#x}: expected zero image word, got {ours:02x?}",
                                        s.raw
                                    ));
                                }
                                let Ok(word_bytes): Result<[u8; 4], _> = theirs.try_into() else {
                                    errs_im.push(format!(
                                        "stub {} at offset {off:#x}: truncated word ({} bytes)",
                                        s.raw,
                                        theirs.len()
                                    ));
                                    continue;
                                };
                                let w = u32::from_le_bytes(word_bytes);
                                let pc = base + off as u64;
                                let want = match im.targets.get(k).copied().flatten() {
                                    Some(a) => Some(a),
                                    None => externs.get(s.raw.as_str()).copied(),
                                };
                                let expected_w = want.and_then(|t| encode_b(pc, t));
                                if want.is_none()
                                    || expected_w != Some(w)
                                    || b_target(w, pc) != want
                                {
                                    errs_im.push(format!(
                                        "stub {} at {pc:#x}: {w:#010x} is not `b` to {want:x?} (expected {expected_w:#010x?})",
                                        s.raw
                                    ));
                                } else if let Some(t) = want
                                    && im.tag == 0
                                {
                                    r.stub_targets.insert(s.off, t);
                                }
                                r.stub_words += 1;
                            }
                            other => {
                                if ours != theirs {
                                    errs_im.push(format!(
                                        "code differs at offset {off:#x}: image {ours:02x?}, ELF {theirs:02x?}"
                                    ));
                                }
                                r.stub_words += usize::from(other.is_some());
                                r.code_bytes += ours.len();
                            }
                        }
                    }
                }
            }
        }

        let data_addr = base + li.data_off;
        let got_addr = base + li.got_off;
        if im.page_separate_data {
            // Data (`{pfx}rodata ++ {pfx}data`) and bss.
            if !li.data.is_empty() {
                let want = relocated_data(li, base)?;
                let ro_sec = section_bytes(&elf, &format!("{pfx}rodata"))?;
                let rw_sec = section_bytes(&elf, &format!("{pfx}data"))?;
                let combined = match (ro_sec, rw_sec) {
                    (Some((ro_a, _, ro_b)), Some((rw_a, _, rw_b))) => {
                        if ro_a + ro_b.len() as u64 != rw_a {
                            errs_im.push(format!(
                                "{pfx}rodata [{ro_a:#x}, {:#x}) and {pfx}data [{rw_a:#x}, {:#x}) are not contiguous",
                                ro_a + ro_b.len() as u64,
                                rw_a + rw_b.len() as u64
                            ));
                        }
                        let mut v = ro_b;
                        v.extend_from_slice(&rw_b);
                        Some((ro_a, v))
                    }
                    (Some((ro_a, _, ro_b)), None) => Some((ro_a, ro_b)),
                    (None, Some((rw_a, _, rw_b))) => Some((rw_a, rw_b)),
                    (None, None) => None,
                };
                match combined {
                    Some((addr, bytes)) if addr == data_addr && bytes == want => {
                        r.data_bytes += bytes.len();
                        r.relocs += li.relocs.len();
                    }
                    Some((addr, bytes)) => {
                        let i = bytes.iter().zip(&want).position(|(a, b)| a != b);
                        errs_im.push(format!(
                            "{pfx}rodata/{pfx}data at {addr:#x} ({} bytes) differs from relocated image \
                             data at {data_addr:#x} ({} bytes); first difference at {i:x?}",
                            bytes.len(),
                            want.len()
                        ));
                    }
                    None => errs_im.push(format!("no {pfx}rodata or {pfx}data section")),
                }
            }
            if li.bss > 0 {
                match section_bytes(&elf, &format!("{pfx}bss"))? {
                    Some((addr, size, _)) if addr + size == base + li.data_end() => {}
                    other => errs_im.push(format!(
                        "{pfx}bss does not end at the image end: {:x?}",
                        other.map(|o| (o.0, o.1))
                    )),
                }
            }
            if !li.got.is_empty() {
                let want: Vec<u8> = li
                    .got
                    .iter()
                    .flat_map(|g| g.value(base).to_le_bytes())
                    .collect();
                match section_bytes(&elf, &format!("{pfx}got"))? {
                    Some((addr, _, bytes)) if addr == got_addr && bytes == want => {}
                    Some((addr, _, bytes)) => errs_im.push(format!(
                        "{pfx}got at {addr:#x} ({} bytes) differs from expected GOT at {got_addr:#x} ({} bytes)",
                        bytes.len(),
                        want.len()
                    )),
                    None => errs_im.push(format!("no {pfx}got section")),
                }
                for suffix in ["got.lead", "got.pad"] {
                    let pad_name = format!("{pfx}{suffix}");
                    if let Some((addr, size, bytes)) = section_bytes(&elf, &pad_name)?
                        && (bytes.len() as u64 != size || bytes.iter().any(|&b| b != 0))
                    {
                        errs_im.push(format!(
                            "{pad_name} at {addr:#x} ({size} bytes) is not explicitly zero-filled in the ELF file"
                        ));
                    }
                }
            }

            // Exact segment permissions, zero-fill coverage, zero mixed ro/rw pages.
            if !li.code.is_empty() {
                for off in [0u64, li.code.len() as u64 - 1] {
                    let a = base + off;
                    match seg_of(a) {
                        Some(p) if p.p_flags(e) & rwx == (PF_R | PF_X) => {}
                        _ => errs_im.push(format!(
                            "image code at {a:#x} is not in a PT_LOAD with exact flags PF_R | PF_X"
                        )),
                    }
                }
            }

            let is_ro_off =
                |off: u64| -> bool { li.ro_data.iter().any(|&(o, n)| o <= off && off < o + n) };
            let mut ro_pages: HashSet<u64> = HashSet::new();
            let mut rw_pages: HashSet<u64> = HashSet::new();
            let mut bad_ro: Option<(u64, Option<u32>)> = None;
            let mut bad_ro_filesz: Option<u64> = None;
            let mut bad_got: Option<(u64, Option<u32>)> = None;
            let mut bad_got_filesz: Option<u64> = None;
            let mut bad_rw: Option<(u64, Option<u32>)> = None;

            for &(o, n) in &li.ro_data {
                for off in o..o + n {
                    let a = base + off;
                    ro_pages.insert(a & !(PAGE - 1));
                    let flags = seg_of(a).map(|p| p.p_flags(e) & rwx);
                    if flags != Some(PF_R) && bad_ro.is_none() {
                        bad_ro = Some((a, flags));
                    }
                    if let Some(p) = seg_of(a)
                        && a >= p.p_vaddr(e) + p.p_filesz(e)
                        && bad_ro_filesz.is_none()
                    {
                        bad_ro_filesz = Some(a);
                    }
                }
            }
            if let Some((a, flags)) = bad_ro {
                errs_im.push(format!(
                    "ro_data byte at {a:#x} is not in a PF_R PT_LOAD (got flags {flags:x?})"
                ));
            }
            if let Some(a) = bad_ro_filesz {
                errs_im.push(format!(
                    "ro_data byte at {a:#x} is beyond p_filesz of its PT_LOAD (missing file zero-fill)"
                ));
            }

            for off in li.data_off..li.data_end() {
                if is_ro_off(off) {
                    continue;
                }
                let a = base + off;
                rw_pages.insert(a & !(PAGE - 1));
                let flags = seg_of(a).map(|p| p.p_flags(e) & rwx);
                if flags != Some(PF_R | PF_W) && bad_rw.is_none() {
                    bad_rw = Some((a, flags));
                }
            }
            for (_, o, sz) in &li.extern_data {
                for off in *o..*o + *sz {
                    let a = base + off;
                    rw_pages.insert(a & !(PAGE - 1));
                    let flags = seg_of(a).map(|p| p.p_flags(e) & rwx);
                    if flags != Some(PF_R | PF_W) && bad_rw.is_none() {
                        bad_rw = Some((a, flags));
                    }
                }
            }
            if let Some((a, flags)) = bad_rw {
                errs_im.push(format!(
                    "writable image byte at {a:#x} is not in a PF_R | PF_W PT_LOAD (got flags {flags:x?})"
                ));
            }

            if !li.got.is_empty() {
                let g_start = got_addr & !(PAGE - 1);
                let g_end = (got_addr + 8 * li.got.len() as u64 + PAGE - 1) & !(PAGE - 1);
                for a in g_start..g_end {
                    ro_pages.insert(a & !(PAGE - 1));
                    let flags = seg_of(a).map(|p| p.p_flags(e) & rwx);
                    if flags != Some(PF_R) && bad_got.is_none() {
                        bad_got = Some((a, flags));
                    }
                    if let Some(p) = seg_of(a)
                        && a >= p.p_vaddr(e) + p.p_filesz(e)
                        && bad_got_filesz.is_none()
                    {
                        bad_got_filesz = Some(a);
                    }
                }
            }
            if let Some((a, flags)) = bad_got {
                errs_im.push(format!(
                    "GOT byte at {a:#x} is not in a PF_R PT_LOAD (got flags {flags:x?})"
                ));
            }
            if let Some(a) = bad_got_filesz {
                errs_im.push(format!(
                    "GOT page byte at {a:#x} is beyond p_filesz of its PT_LOAD (missing file zero-fill)"
                ));
            }

            let mut mixed_pages: Vec<u64> = ro_pages.intersection(&rw_pages).copied().collect();
            mixed_pages.sort_unstable();
            if let Some(&pg) = mixed_pages.first() {
                errs_im.push(format!(
                    "image page {pg:#x} contains both read-only (ro_data/GOT) and writable (data/bss/extdata) bytes"
                ));
            }
        } else {
            // Default interleaved mode: `.img.data`, `.img.bss`, `.img.got`.
            if !li.data.is_empty() {
                let want = relocated_data(li, base)?;
                match section_bytes(&elf, &format!("{pfx}data"))? {
                    Some((addr, _, bytes)) if addr == data_addr && bytes == want => {
                        r.data_bytes += bytes.len();
                        r.relocs += li.relocs.len();
                    }
                    Some((addr, _, bytes)) => {
                        let i = bytes.iter().zip(&want).position(|(a, b)| a != b);
                        errs_im.push(format!(
                            "{pfx}data at {addr:#x} ({} bytes) differs from the relocated image data at \
                             {data_addr:#x} ({} bytes); first difference at {i:x?}",
                            bytes.len(),
                            want.len()
                        ));
                    }
                    None => errs_im.push(format!("no {pfx}data section")),
                }
            }
            if li.bss > 0 {
                match section_bytes(&elf, &format!("{pfx}bss"))? {
                    Some((addr, size, _)) if addr + size == base + li.data_end() => {}
                    other => errs_im.push(format!(
                        "{pfx}bss does not end at the image end: {:x?}",
                        other.map(|o| (o.0, o.1))
                    )),
                }
            }
            if !li.got.is_empty() {
                let want: Vec<u8> = li
                    .got
                    .iter()
                    .flat_map(|g| g.value(base).to_le_bytes())
                    .collect();
                match section_bytes(&elf, &format!("{pfx}got"))? {
                    Some((addr, _, bytes)) if addr == got_addr && bytes == want => {}
                    Some((addr, _, bytes)) => errs_im.push(format!(
                        "{pfx}got at {addr:#x} ({} bytes) differs from expected GOT at {got_addr:#x} ({} bytes)",
                        bytes.len(),
                        want.len()
                    )),
                    None => errs_im.push(format!("no {pfx}got section")),
                }
            }

            match seg_of(base) {
                Some(p) if p.p_flags(e) & (PF_W | PF_X) == PF_X => {}
                _ => errs_im.push(format!("image code at {base:#x} is not in an r-x PT_LOAD")),
            }
            if li.data_end() > li.data_off {
                match seg_of(data_addr) {
                    Some(p) if p.p_flags(e) & PF_X == 0 => {}
                    _ => errs_im.push(format!(
                        "image data at {data_addr:#x} is not in a non-executable PT_LOAD"
                    )),
                }
            }
            if !li.got.is_empty() {
                match seg_of(got_addr) {
                    Some(p) if p.p_flags(e) & PF_X == 0 => {}
                    _ => errs_im.push(format!(
                        "image GOT at {got_addr:#x} is not in a non-executable PT_LOAD"
                    )),
                }
            }
        }

        let img_end = base + im.extent;
        for s in elf.sections() {
            let name = s.name().unwrap_or("?");
            let (a, n) = (s.address(), s.size());
            if a != 0 && n > 0 && !name.starts_with(&pfx) && a < img_end && base < a + n {
                errs_im.push(format!(
                    "section {name} [{a:#x}, {:#x}) overlaps the image",
                    a + n
                ));
            }
        }

        // Symbols.
        for (o, offs) in im.objs.iter().zip(&li.sec_off) {
            for s in &o.symbols {
                if !matches!(s.kind, SymKind::Func | SymKind::Object) {
                    continue;
                }
                let SymSection::Sec(i) = s.sec else { continue };
                let Some(off) = offs.get(i).copied().flatten() else {
                    continue;
                };
                let at = off + s.value;
                let listed = li.symbols.iter().any(|(n, o)| *n == s.name && *o == at);
                if s.bind != SymBind::Local && !listed {
                    continue;
                }
                if s.bind == SymBind::Local
                    && s.raw_name.starts_with(".L")
                    && !syms.contains_key(s.raw_name.as_str())
                {
                    continue;
                }
                if syms
                    .get(s.raw_name.as_str())
                    .is_some_and(|v| v.contains(&(base + at)))
                {
                    r.symbols += 1;
                } else {
                    errs_im.push(format!(
                        "symbol {}: no ELF symbol at {:#x}",
                        s.name,
                        base + at
                    ));
                }
            }
        }
        errs.extend(errs_im.into_iter().map(|m| format!("{who}{m}")));
    }

    // TLS.
    let has_tls_phdr = phdrs.iter().any(|p| p.p_type(e) == PT_TLS);
    for s in elf.sections() {
        let name = s.name().unwrap_or("?");
        if let SectionFlags::Elf { sh_flags } = s.flags()
            && sh_flags & u64::from(SHF_TLS) != 0
            && s.size() > 0
            && !has_tls_phdr
        {
            errs.push(format!("TLS section {name} but no PT_TLS"));
        }
    }
    r.errors = errs;
    Ok(r)
}

/// Verify `Arm64.Process.ElfImage.parse` static-ELF invariants and the `panic = immediate-abort`
/// symbol-bloat audit on a linked Rust `std` executable.
pub fn check_std_elf(elf_bytes: &[u8]) -> Result<()> {
    check_std_elf_exempting(elf_bytes, &[])
}

/// [`check_std_elf`], with the flagged names in `exempt` allowed where they are pure aliases
/// (see [`forbidden_symbols`]).
pub fn check_std_elf_exempting(elf_bytes: &[u8], exempt: &[String]) -> Result<()> {
    const USER_SPACE_LIMIT: u64 = 1u64 << 48;
    const PT_AARCH64_MEMTAG_MTE: u32 = 0x7000_0002;

    let elf = ElfFile64::<Endianness>::parse(elf_bytes).context("cannot parse std ELF64 binary")?;
    let e = elf.endian();
    ensure!(
        e == Endianness::Little,
        "std ELF check failed: expected little-endian (ELFDATA2LSB), got {e:?}"
    );
    let hdr = elf.elf_header();
    ensure!(
        hdr.e_type(e) == ET_EXEC,
        "std ELF check failed: expected static ET_EXEC ({ET_EXEC}), got e_type={}",
        hdr.e_type(e)
    );
    ensure!(
        hdr.e_machine(e) == EM_AARCH64,
        "std ELF check failed: expected EM_AARCH64 ({EM_AARCH64}), got e_machine={}",
        hdr.e_machine(e)
    );
    ensure!(
        hdr.e_phentsize(e) == 56 && hdr.e_phnum(e) > 0,
        "std ELF check failed: invalid program header table (e_phentsize={}, e_phnum={})",
        hdr.e_phentsize(e),
        hdr.e_phnum(e)
    );
    let entry = hdr.e_entry(e);
    ensure!(
        entry != 0 && entry % 4 == 0,
        "std ELF check failed: invalid e_entry={entry:#x} (must be non-zero and 4-byte aligned)"
    );

    let phdrs = hdr.program_headers(e, elf.data())?;
    let mut load_regions: Vec<(usize, u64, u64, bool)> = Vec::new();
    let file_len = elf_bytes.len() as u64;

    for (idx, p) in phdrs.iter().enumerate() {
        let ptype = p.p_type(e);
        match ptype {
            PT_DYNAMIC => bail!("std ELF check failed: PT_DYNAMIC segment is forbidden"),
            PT_INTERP => bail!("std ELF check failed: PT_INTERP segment is forbidden"),
            PT_GNU_STACK => {
                ensure!(
                    p.p_flags(e) & PF_X == 0,
                    "std ELF check failed: executable PT_GNU_STACK segment is forbidden"
                );
            }
            PT_NULL
            | PT_NOTE
            | PT_PHDR
            | PT_TLS
            | PT_GNU_EH_FRAME
            | PT_GNU_RELRO
            | PT_GNU_PROPERTY
            | PT_AARCH64_MEMTAG_MTE => {}
            PT_LOAD => {
                let memsz = p.p_memsz(e);
                if memsz == 0 {
                    continue;
                }
                let vaddr = p.p_vaddr(e);
                let offset = p.p_offset(e);
                let filesz = p.p_filesz(e);
                let flags = p.p_flags(e);

                ensure!(
                    vaddr >= PAGE,
                    "std ELF check failed: PT_LOAD[{idx}] maps below {PAGE:#x} (p_vaddr={vaddr:#x})"
                );
                ensure!(
                    filesz <= memsz,
                    "std ELF check failed: PT_LOAD[{idx}] has p_filesz ({filesz:#x}) > p_memsz ({memsz:#x})"
                );
                ensure!(
                    offset
                        .checked_add(filesz)
                        .is_some_and(|end| end <= file_len),
                    "std ELF check failed: PT_LOAD[{idx}] file range [{offset:#x}, + {filesz:#x}) exceeds file length {file_len:#x}"
                );
                ensure!(
                    vaddr % PAGE == offset % PAGE,
                    "std ELF check failed: PT_LOAD[{idx}] p_vaddr ({vaddr:#x}) and p_offset ({offset:#x}) are not 4 KiB page-congruent"
                );
                let raw_end = vaddr.checked_add(memsz).ok_or_else(|| {
                    anyhow::anyhow!("std ELF check failed: PT_LOAD[{idx}] vaddr+memsz overflow")
                })?;
                let page_end = raw_end
                    .checked_add(PAGE - 1)
                    .map(|x| x & !(PAGE - 1))
                    .ok_or_else(|| {
                        anyhow::anyhow!("std ELF check failed: PT_LOAD[{idx}] page_end overflow")
                    })?;
                ensure!(
                    raw_end <= USER_SPACE_LIMIT && page_end <= USER_SPACE_LIMIT,
                    "std ELF check failed: PT_LOAD[{idx}] [{vaddr:#x}, {page_end:#x}) exceeds 48-bit user address space"
                );

                let r = flags & PF_R != 0;
                let w = flags & PF_W != 0;
                let x = flags & PF_X != 0;
                ensure!(
                    r || w || x,
                    "std ELF check failed: PT_LOAD[{idx}] has no R/W/X permissions"
                );
                ensure!(
                    !(w && x),
                    "std ELF check failed: PT_LOAD[{idx}] violates W^X (flags={flags:#x})"
                );
                if !w {
                    ensure!(
                        filesz == memsz,
                        "std ELF check failed: non-writable PT_LOAD[{idx}] has p_filesz ({filesz:#x}) != p_memsz ({memsz:#x})"
                    );
                }
                let page_start = vaddr & !(PAGE - 1);
                load_regions.push((idx, page_start, page_end, x));
            }
            other => bail!(
                "std ELF check failed: unsupported program header type {other:#x} at index {idx}"
            ),
        }
    }

    ensure!(
        !load_regions.is_empty(),
        "std ELF check failed: executable has no non-empty PT_LOAD segments"
    );
    load_regions.sort_by_key(|&(_, start, _, _)| start);
    for pair in load_regions.windows(2) {
        let (i0, s0, e0, _) = pair[0];
        let (i1, s1, e1, _) = pair[1];
        ensure!(
            e0 <= s1,
            "std ELF check failed: page-rounded PT_LOAD[{i0}] [{s0:#x}, {e0:#x}) overlaps PT_LOAD[{i1}] [{s1:#x}, {e1:#x})"
        );
    }
    ensure!(
        load_regions
            .iter()
            .any(|&(_, s, end, x)| x && s <= entry && entry + 4 <= end),
        "std ELF check failed: e_entry={entry:#x} does not lie inside an executable PT_LOAD segment"
    );

    let bad_syms = forbidden_symbols(&elf, exempt);
    if !bad_syms.is_empty() {
        bail!(
            "std ELF symbol audit failed: found unwind/backtrace symbols in .symtab: {}",
            bad_syms.join(", ")
        );
    }
    Ok(())
}

/// The forbidden unwind/backtrace symbol substrings of the symbol-bloat audit.
const FORBIDDEN_SYMS: &[&str] = &["gimli", "_Unwind_Backtrace", "sigaltstack"];

/// Whether `name` contains a [`FORBIDDEN_SYMS`] substring.
pub(crate) fn is_forbidden_name(name: &str) -> bool {
    FORBIDDEN_SYMS.iter().any(|pat| name.contains(pat))
}

/// The symbols of `obj` whose names contain a [`FORBIDDEN_SYMS`] substring, sorted and
/// deduplicated, except the names in `exempt` that are pure aliases here: a flagged function or
/// object at the same section and address as a non-flagged defined function or object at least
/// as large (identical code folded under several names, which links no bytes of its own). A
/// flagged symbol that is not in `exempt`, or that owns any byte outside such a symbol, is still
/// reported.
pub(crate) fn forbidden_symbols<'d>(obj: &impl Object<'d>, exempt: &[String]) -> Vec<String> {
    let owners: Vec<_> = obj
        .symbols()
        .filter(|s| {
            s.is_definition()
                && matches!(
                    s.kind(),
                    object::SymbolKind::Text | object::SymbolKind::Data
                )
                && s.name()
                    .is_ok_and(|n| !n.is_empty() && !n.starts_with('$') && !is_forbidden_name(n))
        })
        .map(|s| (s.section_index(), s.address(), s.size()))
        .collect();
    let mut bad: Vec<String> = obj
        .symbols()
        .filter(|s| s.name().is_ok_and(is_forbidden_name))
        .filter(|s| {
            let alias = s.name().is_ok_and(|n| exempt.iter().any(|e| e == n))
                && s.is_definition()
                && s.section_index().is_some()
                && matches!(
                    s.kind(),
                    object::SymbolKind::Text | object::SymbolKind::Data
                )
                && owners.iter().any(|&(sec, a, size)| {
                    sec == s.section_index() && a == s.address() && size >= s.size()
                });
            !alias
        })
        .map(|s| s.name().unwrap_or("?").to_string())
        .collect();
    bad.sort();
    bad.dedup();
    bad
}
