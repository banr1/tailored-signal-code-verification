// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! The link recipe (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — produces an executable; [`crate::verify`] checks it and
//!   the snapshot plus Lean proofs are what is trusted.
//! - **Purpose:** Extract and link the objects of a `translation.toml` with `rust-obj2lean`
//!   (the `Arm64.Obj.LinkedImage` the Lean proofs are about), then link the *same* `.o` files
//!   with `ld.lld` into a static non-PIE musl executable:
//!   1. extern references are renamed (`llvm-objcopy --redefine-sym`) to per-extern stub
//!      symbols; a generated stub object defines each one as a 4-byte word (`b <extern>` or
//!      zero, [`crate::StubMode`]) that the linker script pins at the image's stub offset;
//!   2. the musl startup objects and archives come from `zig cc -v` for a trivial `main` (when
//!      `--strip-runtime-debug` is passed — off by default so committed ELF fixtures keep their
//!      exact section-header layout — copies are staged with `llvm-objcopy --strip-debug` before
//!      linking so cold-cache `DW_AT_comp_dir` paths do not leave host-dependent `$d` values in
//!      `.symtab` or alter `inputs[].sha256` in `link.json`);
//!   3. a generated linker script pins every image section at `base + offset` in its own
//!      `PT_LOAD` segments — either the default 2-segment layout (`r-x` image code and
//!      `r--`/`rw-` image data) or, when `page_separate_data` / `--page-separate-data` is
//!      enabled, page-disjoint `PT_LOAD` segments (`r-x` code, `r--` read-only data, `rw-`
//!      writable data / bss / extern data, and `r--` GOT) — maps the ELF and program headers in
//!      the page below `base` (musl reads `AT_PHDR`), and places any native objects
//!      (`--native-objects` / `--musl-string`) and the C runtime after the image.
//!
//!   Several `translation.toml` files can be linked at once, each as its own image at its own
//!   page-aligned base ([`place_bases`], [`check_disjoint`]). Image `k > 0` uses suffixed
//!   names (`.img<k>.*` sections, `__snapstub<k>_*`, `img<i>i<k>.o`) so a one-image link is
//!   unchanged; an extern function of one image that another image exports branches to that
//!   definition ([`resolve_externs`]); the headers go in the page below the lowest image and
//!   the C runtime after the highest one.
//!
//! # Key Types & Functions
//! - [`run`], [`link_images`], [`link_std_images`], [`ImageDataLayout`], [`ImageLayoutKind`],
//!   [`linker_script_images`], [`linker_script_std_images`], [`resolve_externs`], [`place_bases`],
//!   [`effective_stub_mode`], [`validate_branch_stubs`], [`stub_asm`], [`musl_inputs`],
//!   [`stage_runtime_inputs`].
//!
//! # When to Read This File
//! - Read this file to see exactly how the executable is linked.

use crate::{Cli, StubMode, verify};
use anyhow::{Context, Result, bail, ensure};
use rust_obj2lean::trusted_common::{
    ExternDecl, ExternKind, ObjObject, SecKind, SymBind, SymKind, SymSection,
};
use rust_obj2lean::trusted_extractor::demangle_rust_symbol;
use rust_obj2lean::untrusted_driver::{self, Toolchain, config::load_config};
use rust_obj2lean::untrusted_legacy_linker::{self, GotEntry, LinkedImage};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

pub const PAGE: u64 = 0x1000;

/// Load address of the first image when no `--base` is given.
pub const DEFAULT_BASE: u64 = 0x40_0000;

/// One image section pinned by the linker script: input file, section name, image offset, size.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pinned {
    pub file: String,
    pub sec: String,
    pub off: u64,
    pub size: u64,
}

/// Byte bounds of one image's data and GOT regions relative to `base` for page-separated links,
/// derived from [`LinkedImage`] (or supplied directly in unit tests).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageDataLayout {
    /// Start of `li.data` (`li.data_off`, page-aligned).
    pub data_off: u64,
    /// End of the read-only prefix of `li.data` (`rw_off` when writable bytes follow rodata, else
    /// `ro_end`; equals `data_off` when there is no read-only image data).
    pub ro_end: u64,
    /// End of initialized `li.data` (`li.data_off + li.data.len()`).
    pub data_bytes_end: u64,
    /// End of `li.data` plus `li.bss` (`li.data_end()`).
    pub data_end: u64,
    /// `(li.got_off, 8 * li.got.len())` when `!li.got.is_empty()`.
    pub got: Option<(u64, u64)>,
}

impl ImageDataLayout {
    pub fn from_image(li: &LinkedImage) -> Self {
        let ro_end = li
            .ro_data
            .iter()
            .filter(|&&(_, n)| n > 0)
            .map(|&(o, n)| o + n)
            .max()
            .unwrap_or(li.data_off);
        let got = (!li.got.is_empty()).then_some((li.got_off, 8 * li.got.len() as u64));
        Self {
            data_off: li.data_off,
            ro_end,
            data_bytes_end: li.data_off + li.data.len() as u64,
            data_end: li.data_end(),
            got,
        }
    }
}

/// One extern stub: index, extern (raw) symbol name, image offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stub {
    pub raw: String,
    pub off: u64,
}

impl Stub {
    /// Symbol of stub `i` of the first image (`tag == 0`).
    #[cfg(test)]
    pub fn sym(i: usize) -> String {
        Self::sym_in(0, i)
    }

    /// Symbol of stub `i` of image `tag` (see [`img_prefix`]).
    pub fn sym_in(tag: usize, i: usize) -> String {
        format!("__snapstub{}_{i}", tag_suffix(tag))
    }
}

/// One extern data object: extern (raw) symbol name, image offset, byte size.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternData {
    pub raw: String,
    pub off: u64,
    pub size: u64,
}

impl ExternData {
    /// Symbol of extern data object `i` of the first image (`tag == 0`).
    #[cfg(test)]
    pub fn sym(i: usize) -> String {
        Self::sym_in(0, i)
    }

    /// Symbol of extern data object `i` of image `tag`.
    pub fn sym_in(tag: usize, i: usize) -> String {
        format!("__snapextdata{}_{i}", tag_suffix(tag))
    }
}

/// `""` for the first image (`tag == 0`), so a one-image link uses the unsuffixed names
/// (`.img.*`, `__snapgot`, `img<i>.o`); otherwise the decimal `tag`.
fn tag_suffix(tag: usize) -> String {
    if tag == 0 {
        String::new()
    } else {
        tag.to_string()
    }
}

/// Output-section prefix of image `tag`: `.img.` for the first image, `.img<tag>.` after it
/// (`.img.text`, `.img1.text`, ...). A section belongs to image `tag` iff its name starts with
/// this prefix.
pub fn img_prefix(tag: usize) -> String {
    format!(".img{}.", tag_suffix(tag))
}

/// Symbol of the GOT of image `tag`.
pub fn got_sym(tag: usize) -> String {
    format!("__snapgot{}", tag_suffix(tag))
}

/// Linker input file name of object `i` of image `tag`: `img<i>.o` for the first image and
/// `img<i>i<tag>.o` after it. No name is a suffix of another, so the linker-script pattern
/// `*<name>` matches exactly one input.
pub fn obj_file(tag: usize, i: usize) -> String {
    if tag == 0 {
        format!("img{i}.o")
    } else {
        format!("img{i}i{tag}.o")
    }
}

/// The image sections of `objs` of kinds `want`, in image-offset order, as `(file, section,
/// offset, size)`; `file(i)` names the input file of object `i`.
pub fn pinned_sections(
    objs: &[ObjObject],
    li: &LinkedImage,
    want: &[SecKind],
    file: impl Fn(usize) -> String,
) -> Result<Vec<Pinned>> {
    let mut out = Vec::new();
    for (i, (o, offs)) in objs.iter().zip(&li.sec_off).enumerate() {
        for (j, s) in o.sections.iter().enumerate() {
            let Some(k) = s.kind() else { continue };
            let Some(off) = offs.get(j).copied().flatten() else {
                continue;
            };
            if !want.contains(&k) || s.size == 0 {
                continue;
            }
            ensure!(
                o.sections.iter().filter(|t| t.name == s.name).count() == 1,
                "object {} has several sections named {}; cannot pin them by name",
                o.name,
                s.name
            );
            out.push(Pinned {
                file: file(i),
                sec: s.name.clone(),
                off,
                size: s.size,
            });
        }
    }
    out.sort_by_key(|p| p.off);
    Ok(out)
}

fn q(s: &str) -> String {
    format!("\"{s}\"")
}

/// Whether `branch_stubs` selects `raw` (matching either the raw symbol name or its demangled
/// Rust name).
pub fn matches_branch_stub(raw: &str, branch_stubs: &[String]) -> bool {
    if branch_stubs.iter().any(|s| s == raw) {
        return true;
    }
    let demangled = demangle_rust_symbol(raw);
    demangled != raw && branch_stubs.iter().any(|s| s == &demangled)
}

/// Effective stub emission mode for extern `raw` given global `mode` and `--branch-stubs`.
pub fn effective_stub_mode(raw: &str, mode: StubMode, branch_stubs: &[String]) -> StubMode {
    if matches_branch_stub(raw, branch_stubs) {
        return StubMode::Branch;
    }
    match mode {
        StubMode::Branch => StubMode::Branch,
        StubMode::Zero | StubMode::Mixed => StubMode::Zero,
    }
}

/// Assembly defining stub `i` of `stubs` as one word in section `.text.__snapstub_<i>`.
#[cfg(test)]
pub fn stub_asm(stubs: &[Stub], mode: StubMode) -> String {
    image_support_asm_in_with(0, stubs, &[], &[], mode, &[], false)
}

/// Assembly defining stub `i` of `stubs` with explicit per-extern `branch_stubs`.
#[cfg(test)]
pub fn stub_asm_with(stubs: &[Stub], mode: StubMode, branch_stubs: &[String]) -> String {
    image_support_asm_in_with(0, stubs, &[], &[], mode, branch_stubs, false)
}

/// Assembly defining extern function stubs, extern data objects, and GOT entries of the first
/// image in the default interleaved layout.
#[cfg(test)]
pub fn image_support_asm(
    stubs: &[Stub],
    ext_data: &[ExternData],
    got: &[u64],
    mode: StubMode,
) -> String {
    image_support_asm_in(0, stubs, ext_data, got, mode)
}

/// Assembly defining extern function stubs, extern data objects, and GOT entries of the first
/// image in the page-separated layout (`.data.__snapextdata_*` writable sections).
#[cfg(test)]
pub fn image_support_asm_pagesep(
    stubs: &[Stub],
    ext_data: &[ExternData],
    got: &[u64],
    mode: StubMode,
) -> String {
    image_support_asm_in_pagesep(0, stubs, ext_data, got, mode)
}

/// Assembly defining extern function stubs, extern data objects, and GOT entries of image `tag`
/// in the default interleaved layout.
#[cfg(test)]
pub fn image_support_asm_in(
    tag: usize,
    stubs: &[Stub],
    ext_data: &[ExternData],
    got: &[u64],
    mode: StubMode,
) -> String {
    image_support_asm_in_with(tag, stubs, ext_data, got, mode, &[], false)
}

/// Assembly defining extern function stubs, extern data objects, and GOT entries of image `tag`
/// in the page-separated layout.
#[cfg(test)]
pub fn image_support_asm_in_pagesep(
    tag: usize,
    stubs: &[Stub],
    ext_data: &[ExternData],
    got: &[u64],
    mode: StubMode,
) -> String {
    image_support_asm_in_with(tag, stubs, ext_data, got, mode, &[], true)
}

/// Assembly defining extern function stubs (with per-extern `branch_stubs`), extern data objects,
/// and GOT entries of image `tag`. A branch stub branches to `x.raw`, whichever object (another
/// image, `main`, native objects, or the C runtime) defines it. When `page_separate_data` is
/// enabled, extern data objects are emitted as writable `.data.<sym>` sections on `:imgdata`;
/// otherwise they use `.rodata.<sym>` on `:imgdata`.
pub fn image_support_asm_in_with(
    tag: usize,
    stubs: &[Stub],
    ext_data: &[ExternData],
    got: &[u64],
    mode: StubMode,
    branch_stubs: &[String],
    page_separate_data: bool,
) -> String {
    let mut s = String::new();
    for (i, x) in stubs.iter().enumerate() {
        let n = Stub::sym_in(tag, i);
        let body = match effective_stub_mode(&x.raw, mode, branch_stubs) {
            StubMode::Branch => format!("b {}", q(&x.raw)),
            StubMode::Zero | StubMode::Mixed => ".word 0".to_string(),
        };
        s += &format!(
            ".section .text.{n},\"ax\",@progbits\n.p2align 2\n.globl {n}\n.type {n},@function\n\
             {n}:\n{body}\n.size {n},4\n"
        );
    }
    for (i, d) in ext_data.iter().enumerate() {
        let n = ExternData::sym_in(tag, i);
        let sz = d.size;
        if page_separate_data {
            s += &format!(
                ".section .data.{n},\"aw\",@progbits\n.globl {n}\n.type {n},@object\n{n}:\n"
            );
        } else {
            s += &format!(
                ".section .rodata.{n},\"a\",@progbits\n.globl {n}\n.type {n},@object\n{n}:\n"
            );
        }
        if sz > 0 {
            s += &format!(".zero {sz}\n");
        }
        s += &format!(".size {n},{sz}\n");
    }
    if !got.is_empty() {
        let g = got_sym(tag);
        s += &format!(
            ".section .rodata.{g},\"a\",@progbits\n.p2align 3\n.globl {g}\n\
             .type {g},@object\n{g}:\n"
        );
        for &v in got {
            s += &format!(".quad {v:#x}\n");
        }
        s += &format!(".size {g},{}\n", 8 * got.len());
    }
    s
}

/// Linker script (default interleaved layout): the image (`text`, `stubs`, `data`, `bss`) pinned
/// at `base + offset`, the C runtime after it.
#[cfg(test)]
pub fn linker_script(
    base: u64,
    text: &[Pinned],
    stubs: &[Stub],
    data: &[Pinned],
    bss: &[Pinned],
) -> String {
    linker_script_full(base, text, stubs, data, bss, &[], None, false)
}

/// Linker script for one image (`tag == 0`) in the default interleaved layout, including optional
/// extern data and GOT sections in `:imgdata`.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub fn linker_script_full(
    base: u64,
    text: &[Pinned],
    stubs: &[Stub],
    data: &[Pinned],
    bss: &[Pinned],
    ext_data: &[ExternData],
    got_off: Option<u64>,
    gc_sections: bool,
) -> String {
    linker_script_images(
        &[ImageLayout {
            tag: 0,
            base,
            text,
            stubs,
            bss,
            ext_data,
            kind: ImageLayoutKind::Interleaved { data, got_off },
        }],
        gc_sections,
    )
}

/// Linker script helper for simple pure-rodata or pure-rw unit tests in the page-separated layout.
#[cfg(test)]
pub fn linker_script_pagesep(
    base: u64,
    text: &[Pinned],
    stubs: &[Stub],
    rodata: &[Pinned],
    bss: &[Pinned],
) -> String {
    let data_off = rodata
        .first()
        .or(bss.first())
        .map(|p| p.off & !(PAGE - 1))
        .unwrap_or(PAGE);
    let ro_raw_end = rodata.last().map(|p| p.off + p.size).unwrap_or(data_off);
    let ro_end = if !rodata.is_empty() && !bss.is_empty() {
        (ro_raw_end + PAGE - 1) & !(PAGE - 1)
    } else {
        ro_raw_end
    };
    let data_end = bss.last().map(|p| p.off + p.size).unwrap_or(ro_end);
    linker_script_full_pagesep(
        base,
        text,
        stubs,
        rodata,
        &[],
        bss,
        &[],
        ImageDataLayout {
            data_off,
            ro_end,
            data_bytes_end: ro_end,
            data_end,
            got: None,
        },
        false,
    )
}

/// Linker script for one image (`tag == 0`) in the page-separated layout, pinning image code
/// (`:imgtext`, `r-x`), read-only data (`:imgro`, `r--`), writable data + bss + extern data
/// (`:imgdata`, `rw-`), and GOT (`:imggot`, `r--`) on page-disjoint `PT_LOAD` segments with
/// explicit file zero-fill on `.img.rodata` and `.img.got`.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub fn linker_script_full_pagesep(
    base: u64,
    text: &[Pinned],
    stubs: &[Stub],
    rodata: &[Pinned],
    rw_data: &[Pinned],
    bss: &[Pinned],
    ext_data: &[ExternData],
    layout: ImageDataLayout,
    gc_sections: bool,
) -> String {
    linker_script_images(
        &[ImageLayout {
            tag: 0,
            base,
            text,
            stubs,
            bss,
            ext_data,
            kind: ImageLayoutKind::PageSeparated {
                rodata,
                rw_data,
                layout,
            },
        }],
        gc_sections,
    )
}

/// Layout variant for one image's non-code sections in [`linker_script_images`].
#[derive(Debug, Clone, Copy)]
pub enum ImageLayoutKind<'a> {
    /// Default 2-segment layout: combined `.rodata` + `.data`, `.bss`, extern data, and GOT on
    /// `:imgdata`.
    Interleaved {
        data: &'a [Pinned],
        got_off: Option<u64>,
    },
    /// Opt-in page-separated layout: `:imgro` (`r--`), `:imgdata` (`rw-`), and `:imggot` (`r--`)
    /// on page-disjoint `PT_LOAD` segments with explicit zero-fill.
    PageSeparated {
        rodata: &'a [Pinned],
        rw_data: &'a [Pinned],
        layout: ImageDataLayout,
    },
}

/// The pinned sections of one image for [`linker_script_images`].
#[derive(Debug, Clone, Copy)]
pub struct ImageLayout<'a> {
    /// Index of the image on the command line (names its sections, see [`img_prefix`]).
    pub tag: usize,
    pub base: u64,
    pub text: &'a [Pinned],
    pub stubs: &'a [Stub],
    pub bss: &'a [Pinned],
    pub ext_data: &'a [ExternData],
    pub kind: ImageLayoutKind<'a>,
}

fn image_script_block_interleaved(
    im: &ImageLayout,
    data: &[Pinned],
    got_off: Option<u64>,
    gc_sections: bool,
    explicit_flags: bool,
) -> (String, String) {
    let wrap = |pat: String| -> String {
        if gc_sections {
            format!("KEEP({pat})")
        } else {
            pat
        }
    };
    let (base, tag) = (im.base, im.tag);
    let pfx = img_prefix(tag);
    let sfx = tag_suffix(tag);
    let (pt_text, pt_data) = (format!("imgtext{sfx}"), format!("imgdata{sfx}"));
    let img_phdrs = if explicit_flags {
        format!("  {pt_text} PT_LOAD FLAGS(5);\n  {pt_data} PT_LOAD;\n")
    } else {
        format!("  {pt_text} PT_LOAD;\n  {pt_data} PT_LOAD;\n")
    };
    let place = |ps: &[Pinned]| -> String {
        ps.iter()
            .map(|p| {
                format!(
                    "    . = {:#x};\n    {}\n",
                    base + p.off,
                    wrap(format!("*{}({})", p.file, q(&p.sec)))
                )
            })
            .collect()
    };
    let stub_place: String = im
        .stubs
        .iter()
        .enumerate()
        .map(|(i, x)| {
            format!(
                "    . = {:#x};\n    {}\n",
                base + x.off,
                wrap(format!("*(.text.{})", Stub::sym_in(tag, i)))
            )
        })
        .collect();
    let (bss, ext_data) = (im.bss, im.ext_data);
    let data_start = data
        .first()
        .or(bss.first())
        .map(|p| base + p.off)
        .or_else(|| ext_data.first().map(|d| base + d.off))
        .or_else(|| got_off.map(|o| base + o));
    let mut data_part = match data_start {
        None => String::new(),
        Some(d) if ext_data.is_empty() && got_off.is_none() => format!(
            "  . = {d:#x};\n  {pfx}data : {{\n{}  }} :{pt_data}\n  {pfx}bss (NOLOAD) : {{\n{}  }} :{pt_data}\n",
            place(data),
            place(bss)
        ),
        Some(d) => {
            let mut s = format!(
                "  . = {d:#x};\n  {pfx}data : {{\n{}  }} :{pt_data}\n",
                place(data)
            );
            if !bss.is_empty() {
                s += &format!("  {pfx}bss (NOLOAD) : {{\n{}  }} :{pt_data}\n", place(bss));
            }
            s
        }
    };
    if !ext_data.is_empty() {
        let ext_place: String = ext_data
            .iter()
            .enumerate()
            .map(|(i, d)| {
                format!(
                    "    . = {:#x};\n    {}\n",
                    base + d.off,
                    wrap(format!("*(.rodata.{})", ExternData::sym_in(tag, i)))
                )
            })
            .collect();
        data_part += &format!("  {pfx}extdata : {{\n{ext_place}  }} :{pt_data}\n");
    }
    if let Some(goff) = got_off {
        let g = base + goff;
        data_part += &format!(
            "  . = {g:#x};\n  {pfx}got : {{\n    . = {g:#x};\n    {}\n  }} :{pt_data}\n",
            wrap(format!("*(.rodata.{})", got_sym(tag)))
        );
    }
    let block = format!(
        "  . = {base:#x};\n  {pfx}text : {{\n{}{stub_place}  }} :{pt_text} =0\n{data_part}",
        place(im.text)
    );
    (img_phdrs, block)
}

fn image_script_block_pagesep(
    im: &ImageLayout,
    rodata: &[Pinned],
    rw_data: &[Pinned],
    layout: ImageDataLayout,
    gc_sections: bool,
) -> (String, String) {
    let wrap = |pat: String| -> String {
        if gc_sections {
            format!("KEEP({pat})")
        } else {
            pat
        }
    };
    let zero_span = |start: u64, end: u64| -> String {
        if end - start == 1 {
            format!("    . = {start:#x};\n    BYTE(0);\n")
        } else {
            format!(
                "    . = {start:#x};\n    BYTE(0);\n    . = {:#x};\n    BYTE(0);\n",
                end - 1
            )
        }
    };
    let (base, tag) = (im.base, im.tag);
    let pfx = img_prefix(tag);
    let sfx = tag_suffix(tag);
    let (pt_text, pt_ro, pt_data, pt_got) = (
        format!("imgtext{sfx}"),
        format!("imgro{sfx}"),
        format!("imgdata{sfx}"),
        format!("imggot{sfx}"),
    );
    let place = |ps: &[Pinned]| -> String {
        ps.iter()
            .map(|p| {
                format!(
                    "    . = {:#x};\n    {}\n",
                    base + p.off,
                    wrap(format!("*{}({})", p.file, q(&p.sec)))
                )
            })
            .collect()
    };
    let stub_place: String = im
        .stubs
        .iter()
        .enumerate()
        .map(|(i, x)| {
            format!(
                "    . = {:#x};\n    {}\n",
                base + x.off,
                wrap(format!("*(.text.{})", Stub::sym_in(tag, i)))
            )
        })
        .collect();

    let has_ro = layout.ro_end > layout.data_off;
    let has_rw = layout.data_end > layout.ro_end || !im.ext_data.is_empty();
    let got_in_imgro = match layout.got {
        Some((goff, _)) => {
            has_ro && !has_rw && ((layout.ro_end - 1) & !(PAGE - 1)) == (goff & !(PAGE - 1))
        }
        None => false,
    };
    let has_got_seg = layout.got.is_some() && !got_in_imgro;

    let mut data_part = String::new();
    if has_ro {
        let ro_vma = base + layout.data_off;
        let ro_end_vma = base + layout.ro_end;
        let mut body = String::new();
        let after_ro = if rodata.is_empty() {
            body += &zero_span(ro_vma, ro_end_vma);
            ro_end_vma
        } else {
            if rodata[0].off > layout.data_off {
                body += &format!("    . = {ro_vma:#x};\n    BYTE(0);\n");
            }
            body += &place(rodata);
            let last = rodata.last().unwrap();
            base + last.off + last.size
        };
        if after_ro < ro_end_vma {
            body += &format!("    . = {:#x};\n    BYTE(0);\n", ro_end_vma - 1);
        }
        data_part += &format!("  . = {ro_vma:#x};\n  {pfx}rodata : {{\n{body}  }} :{pt_ro} =0\n");
        if got_in_imgro {
            let (goff, glen) = layout.got.unwrap();
            let g = base + goff;
            let g_end = g + glen;
            let g_page_end = (g_end + PAGE - 1) & !(PAGE - 1);
            data_part += &format!(
                "  . = {g:#x};\n  {pfx}got : {{\n    . = {g:#x};\n    {}\n  }} :{pt_ro} =0\n",
                wrap(format!("*(.rodata.{})", got_sym(tag)))
            );
            if g_end < g_page_end {
                data_part += &format!(
                    "  . = {g_end:#x};\n  {pfx}got.pad : {{\n{}  }} :{pt_ro} =0\n",
                    zero_span(g_end, g_page_end)
                );
            }
        }
    }

    if layout.data_bytes_end > layout.ro_end {
        let rw_vma = base + layout.ro_end;
        let rw_end_vma = base + layout.data_bytes_end;
        let mut body = String::new();
        let after_rw = if rw_data.is_empty() {
            body += &zero_span(rw_vma, rw_end_vma);
            rw_end_vma
        } else {
            if rw_data[0].off > layout.ro_end {
                body += &format!("    . = {rw_vma:#x};\n    BYTE(0);\n");
            }
            body += &place(rw_data);
            let last = rw_data.last().unwrap();
            base + last.off + last.size
        };
        if after_rw < rw_end_vma {
            body += &format!("    . = {:#x};\n    BYTE(0);\n", rw_end_vma - 1);
        }
        data_part += &format!("  . = {rw_vma:#x};\n  {pfx}data : {{\n{body}  }} :{pt_data} =0\n");
    }

    if layout.data_end > layout.data_bytes_end {
        let bss_vma = base + layout.data_bytes_end;
        let bss_end_vma = base + layout.data_end;
        let mut body = place(im.bss);
        let after_bss = im
            .bss
            .last()
            .map(|p| base + p.off + p.size)
            .unwrap_or(bss_vma);
        if after_bss < bss_end_vma {
            body += &format!("    . = {bss_end_vma:#x};\n");
        }
        data_part +=
            &format!("  . = {bss_vma:#x};\n  {pfx}bss (NOLOAD) : {{\n{body}  }} :{pt_data}\n");
    }

    if !im.ext_data.is_empty() {
        let ext_place: String = im
            .ext_data
            .iter()
            .enumerate()
            .map(|(i, d)| {
                format!(
                    "    . = {:#x};\n    {}\n",
                    base + d.off,
                    wrap(format!("*(.data.{})", ExternData::sym_in(tag, i)))
                )
            })
            .collect();
        data_part += &format!("  {pfx}extdata : {{\n{ext_place}  }} :{pt_data} =0\n");
    }

    if has_got_seg {
        let (goff, glen) = layout.got.unwrap();
        let g = base + goff;
        let g_end = g + glen;
        let g_page = g & !(PAGE - 1);
        let g_page_end = (g_end + PAGE - 1) & !(PAGE - 1);
        if g > g_page {
            data_part += &format!(
                "  . = {g_page:#x};\n  {pfx}got.lead : {{\n{}  }} :{pt_got} =0\n",
                zero_span(g_page, g)
            );
        }
        data_part += &format!(
            "  . = {g:#x};\n  {pfx}got : {{\n    . = {g:#x};\n    {}\n  }} :{pt_got} =0\n",
            wrap(format!("*(.rodata.{})", got_sym(tag)))
        );
        if g_end < g_page_end {
            data_part += &format!(
                "  . = {g_end:#x};\n  {pfx}got.pad : {{\n{}  }} :{pt_got} =0\n",
                zero_span(g_end, g_page_end)
            );
        }
    }

    let mut img_phdrs = format!("  {pt_text} PT_LOAD FLAGS(5);\n");
    if has_ro {
        img_phdrs += &format!("  {pt_ro} PT_LOAD FLAGS(4);\n");
    }
    if has_rw {
        img_phdrs += &format!("  {pt_data} PT_LOAD FLAGS(6);\n");
    }
    if has_got_seg {
        img_phdrs += &format!("  {pt_got} PT_LOAD FLAGS(4);\n");
    }

    let block = format!(
        "  . = {base:#x};\n  {pfx}text : {{\n{}{stub_place}  }} :{pt_text} =0\n{data_part}",
        place(im.text)
    );
    (img_phdrs, block)
}

/// Linker script for several images: each image gets either its default `imgtext<tag>` +
/// `imgdata<tag>` `PT_LOAD` pair (`ImageLayoutKind::Interleaved`) or page-disjoint `PT_LOAD`
/// segments (`imgtext<tag>` `r-x`, `imgro<tag>` `r--`, `imgdata<tag>` `rw-`, `imggot<tag>` `r--`
/// for `ImageLayoutKind::PageSeparated`), with every section pinned at `base + offset`. Images are
/// emitted in increasing `base` order (they must not overlap, see [`check_disjoint`]); the ELF and
/// program headers are mapped in the page below the lowest base, and the C runtime follows the
/// highest image.
pub fn linker_script_images(images: &[ImageLayout], gc_sections: bool) -> String {
    let mut sorted: Vec<&ImageLayout> = images.iter().collect();
    sorted.sort_by_key(|im| im.base);
    let any_pagesep = sorted
        .iter()
        .any(|im| matches!(im.kind, ImageLayoutKind::PageSeparated { .. }));
    let mut phdrs = String::new();
    let mut blocks = String::new();
    for im in &sorted {
        let (p, b) = match im.kind {
            ImageLayoutKind::Interleaved { data, got_off } => {
                image_script_block_interleaved(im, data, got_off, gc_sections, any_pagesep)
            }
            ImageLayoutKind::PageSeparated {
                rodata,
                rw_data,
                layout,
            } => image_script_block_pagesep(im, rodata, rw_data, layout, gc_sections),
        };
        phdrs += &p;
        blocks += &b;
    }
    let hdr = sorted.first().map_or(PAGE, |im| im.base) - PAGE;
    let discard_gcc = if gc_sections {
        " *(.gcc_except_table*)"
    } else {
        ""
    };
    if any_pagesep {
        format!(
            "PHDRS {{\n  phdr PT_PHDR PHDRS;\n  hdr PT_LOAD FILEHDR PHDRS FLAGS(4);\n\
             {phdrs}  text PT_LOAD FLAGS(5);\n  ro PT_LOAD FLAGS(4);\n  \
             data PT_LOAD FLAGS(6);\n  tls PT_TLS;\n  stack PT_GNU_STACK FLAGS(6);\n}}\n\
             SECTIONS {{\n  . = {hdr:#x} + SIZEOF_HEADERS;\n{blocks}  \
             . = ALIGN({PAGE:#x});\n  .text : {{ *(.text .text.*) }} :text\n  \
             . = ALIGN({PAGE:#x});\n  .rodata : {{ *(.rodata .rodata.*) }} :ro\n  \
             . = ALIGN({PAGE:#x});\n  .tdata : {{ *(.tdata .tdata.*) }} :data :tls\n  \
             .tbss : {{ *(.tbss .tbss.*) }} :data :tls\n  \
             .init_array : {{ KEEP(*(.init_array*)) }} :data\n  \
             .fini_array : {{ KEEP(*(.fini_array*)) }} :data\n  .data : {{ *(.data .data.*) }} :data\n  \
             .bss : {{ *(.bss .bss.* COMMON) }} :data\n  \
             /DISCARD/ : {{ *(.eh_frame){discard_gcc} *(.comment) *(.note*) *(.llvm_addrsig) }}\n}}\n",
        )
    } else {
        format!(
            "PHDRS {{\n  phdr PT_PHDR PHDRS;\n  hdr PT_LOAD FILEHDR PHDRS;\n{phdrs}  \
             text PT_LOAD;\n  ro PT_LOAD;\n  data PT_LOAD;\n  \
             tls PT_TLS;\n  stack PT_GNU_STACK FLAGS(6);\n}}\n\
             SECTIONS {{\n  . = {hdr:#x} + SIZEOF_HEADERS;\n{blocks}  \
             . = ALIGN({PAGE:#x});\n  .text : {{ *(.text .text.*) }} :text\n  \
             . = ALIGN({PAGE:#x});\n  .rodata : {{ *(.rodata .rodata.*) }} :ro\n  \
             . = ALIGN({PAGE:#x});\n  .tdata : {{ *(.tdata .tdata.*) }} :data :tls\n  \
             .tbss : {{ *(.tbss .tbss.*) }} :data :tls\n  \
             .init_array : {{ KEEP(*(.init_array*)) }} :data\n  \
             .fini_array : {{ KEEP(*(.fini_array*)) }}\n  .data : {{ *(.data .data.*) }}\n  \
             .bss : {{ *(.bss .bss.* COMMON) }}\n  \
             /DISCARD/ : {{ *(.eh_frame){discard_gcc} *(.comment) *(.note*) *(.llvm_addrsig) }}\n}}\n",
        )
    }
}

/// Linker script for pinned Rust `std` binary crates (with `0` or more pre-verified `images`),
/// mapping page-disjoint W^X `PT_LOAD` segments (`hdr`, optional pinned `images`, `text` `r-x`
/// with `.init`/`.text`/`.fini`, `ro` `r--` zero-filled, `data` `rw-` with TLS and
/// `__init_array_{start,end}` / `__fini_array_{start,end}`) and discarding unwind metadata.
pub fn linker_script_std_images(images: &[ImageLayout]) -> String {
    let mut sorted: Vec<&ImageLayout> = images.iter().collect();
    sorted.sort_by_key(|im| im.base);
    let mut phdrs = String::new();
    let mut blocks = String::new();
    for im in &sorted {
        let (p, b) = match im.kind {
            ImageLayoutKind::Interleaved { data, got_off } => {
                image_script_block_interleaved(im, data, got_off, true, true)
            }
            ImageLayoutKind::PageSeparated {
                rodata,
                rw_data,
                layout,
            } => image_script_block_pagesep(im, rodata, rw_data, layout, true),
        };
        phdrs += &p;
        blocks += &b;
    }
    let hdr = sorted.first().map_or(DEFAULT_BASE, |im| im.base) - PAGE;
    format!(
        "PHDRS {{\n  phdr PT_PHDR PHDRS;\n  hdr PT_LOAD FILEHDR PHDRS FLAGS(4);\n\
         {phdrs}  text PT_LOAD FLAGS(5);\n  ro PT_LOAD FLAGS(4);\n  \
         data PT_LOAD FLAGS(6);\n  tls PT_TLS;\n  stack PT_GNU_STACK FLAGS(6);\n}}\n\
         SECTIONS {{\n  . = {hdr:#x} + SIZEOF_HEADERS;\n{blocks}  \
         . = ALIGN({PAGE:#x});\n  \
         .init : {{ KEEP(*(SORT_NONE(.init))) }} :text\n  \
         .text : {{ *(.text .text.*) }} :text\n  \
         .fini : {{ KEEP(*(SORT_NONE(.fini))) }} :text\n  \
         . = ALIGN({PAGE:#x});\n  \
         .rodata : {{ *(.rodata .rodata.*) }} :ro =0\n  \
         . = ALIGN({PAGE:#x});\n  \
         .tdata : {{ *(.tdata .tdata.*) }} :data :tls\n  \
         .tbss : {{ *(.tbss .tbss.*) }} :data :tls\n  \
         .init_array : {{\n    \
           PROVIDE_HIDDEN(__init_array_start = .);\n    \
           KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*) SORT_BY_INIT_PRIORITY(.ctors.*)))\n    \
           KEEP(*(.init_array .ctors))\n    \
           PROVIDE_HIDDEN(__init_array_end = .);\n  \
         }} :data\n  \
         .fini_array : {{\n    \
           PROVIDE_HIDDEN(__fini_array_start = .);\n    \
           KEEP(*(SORT_BY_INIT_PRIORITY(.fini_array.*) SORT_BY_INIT_PRIORITY(.dtors.*)))\n    \
           KEEP(*(.fini_array .dtors))\n    \
           PROVIDE_HIDDEN(__fini_array_end = .);\n  \
         }} :data\n  \
         .data : {{ *(.data .data.*) }} :data\n  \
         .bss : {{ *(.bss .bss.* COMMON) }} :data\n  \
         /DISCARD/ : {{ *(.eh_frame*) *(.gcc_except_table*) *(.comment) *(.note*) *(.llvm_addrsig) }}\n}}\n",
    )
}

/// One translated image to link: the objects of one `translation.toml` and the
/// `Arm64.Obj.LinkedImage` that `rust-obj2lean` exports for them.
pub struct Image {
    pub objects: Vec<ObjObject>,
    pub externs: Vec<ExternDecl>,
    pub li: LinkedImage,
    pub page_separate_data: bool,
    pub rlibs: Vec<PathBuf>,
}

/// Bytes from the image base to the end of its code, data, bss, extern data and GOT in the
/// default interleaved layout.
#[cfg(test)]
pub fn image_extent(li: &LinkedImage) -> u64 {
    image_extent_with(li, false)
}

/// Bytes from the image base to the end of its code, data, bss, extern data and GOT (rounding the
/// GOT end up to a 4 KiB page boundary when `page_separate_data` is enabled).
pub fn image_extent_with(li: &LinkedImage, page_separate_data: bool) -> u64 {
    let got_end = if li.got.is_empty() {
        0
    } else {
        let raw_end = li.got_off + 8 * li.got.len() as u64;
        if page_separate_data {
            (raw_end + PAGE - 1) & !(PAGE - 1)
        } else {
            raw_end
        }
    };
    let ext_end = li
        .extern_data
        .iter()
        .map(|(_, o, sz)| o + sz)
        .max()
        .unwrap_or(0);
    li.data_end()
        .max(li.code.len() as u64)
        .max(got_end)
        .max(ext_end)
}

/// Load addresses of images with sizes `extents`: image `k` is at `requested[k]` when given;
/// otherwise the first image is at [`DEFAULT_BASE`] and a later one at the first page boundary
/// after every earlier image. Each base must be page aligned and at least one page above zero.
pub fn place_bases(requested: &[u64], extents: &[u64]) -> Result<Vec<u64>> {
    ensure!(
        requested.len() <= extents.len(),
        "{} --base values for {} --config images",
        requested.len(),
        extents.len()
    );
    let mut bases = Vec::with_capacity(extents.len());
    let mut next = DEFAULT_BASE;
    for (k, &ext) in extents.iter().enumerate() {
        let base = requested.get(k).copied().unwrap_or(next);
        ensure!(
            base % PAGE == 0 && base >= PAGE,
            "--base {base:#x} must be page aligned and at least {PAGE:#x}"
        );
        let end = base
            .checked_add(ext)
            .and_then(|e| e.checked_next_multiple_of(PAGE))
            .with_context(|| format!("image {k} at {base:#x} overflows the address space"))?;
        next = next.max(end);
        bases.push(base);
    }
    Ok(bases)
}

/// Fail if two images `[bases[k], bases[k] + extents[k])` overlap.
pub fn check_disjoint(labels: &[String], bases: &[u64], extents: &[u64]) -> Result<()> {
    for i in 0..bases.len() {
        for j in i + 1..bases.len() {
            let (a, b) = (bases[i], bases[i] + extents[i]);
            let (c, d) = (bases[j], bases[j] + extents[j]);
            ensure!(
                b <= c || d <= a,
                "image {i} ({}) at [{a:#x}, {b:#x}) overlaps image {j} ({}) at [{c:#x}, {d:#x})",
                labels[i],
                labels[j]
            );
        }
    }
    Ok(())
}

/// The global and weak symbols image `li` defines, as `(raw name, image offset, kind)` (the
/// first definition of each name; extern stubs and extern data are not definitions).
pub fn exported_symbols(objs: &[ObjObject], li: &LinkedImage) -> Vec<(String, u64, SymKind)> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for (o, offs) in objs.iter().zip(&li.sec_off) {
        for s in &o.symbols {
            if !matches!(s.bind, SymBind::Global | SymBind::Weak) {
                continue;
            }
            if let SymSection::Sec(i) = s.sec
                && let Some(off) = offs.get(i).copied().flatten()
                && seen.insert(s.raw_name.clone())
            {
                out.push((s.raw_name.clone(), off + s.value, s.kind));
            }
        }
    }
    out
}

/// The externs of one image: its stubs and extern data objects, and where each stub branches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImageExterns {
    pub stubs: Vec<Stub>,
    pub ext_data: Vec<ExternData>,
    /// Per stub: `Some((image, address))` when another image defines the extern, `None` when
    /// it is left to `main` and the C runtime.
    pub targets: Vec<Option<(usize, u64)>>,
}

/// Resolve the externs of every image (at `bases`): an extern function that another image
/// exports resolves to that image's symbol; the rest go to `main` and the C runtime. Fails on
/// a global or weak symbol defined by two images, on an extern function that another image
/// defines as data, and on an extern data object that another image defines (each image keeps
/// its own zero-filled placeholder, which would silently diverge from the definition).
pub fn resolve_externs(
    images: &[Image],
    bases: &[u64],
    labels: &[String],
) -> Result<Vec<ImageExterns>> {
    let mut exports: HashMap<String, (usize, u64, SymKind)> = HashMap::new();
    for (k, im) in images.iter().enumerate() {
        for (raw, off, kind) in exported_symbols(&im.objects, &im.li) {
            if let Some(&(j, _, _)) = exports.get(&raw) {
                bail!(
                    "symbol {raw} is defined by both image {j} ({}) and image {k} ({})",
                    labels[j],
                    labels[k]
                );
            }
            exports.insert(raw, (k, bases[k] + off, kind));
        }
    }
    let mut out = Vec::with_capacity(images.len());
    for (k, im) in images.iter().enumerate() {
        let other = |raw: &str| exports.get(raw).filter(|e| e.0 != k).copied();
        let (mut stubs, mut targets) = (Vec::new(), Vec::new());
        for (name, off) in &im.li.stubs {
            let x = im
                .externs
                .iter()
                .find(|x| &x.name == name)
                .with_context(|| format!("stub {name} has no extern declaration"))?;
            ensure!(
                x.kind == ExternKind::Func,
                "extern {name} is not a function"
            );
            let target = match other(&x.raw_name) {
                Some((j, _, SymKind::Object | SymKind::Tls)) => bail!(
                    "extern function {} of image {k} ({}) is a data symbol of image {j} ({})",
                    x.raw_name,
                    labels[k],
                    labels[j]
                ),
                Some((j, addr, _)) => Some((j, addr)),
                None => None,
            };
            stubs.push(Stub {
                raw: x.raw_name.clone(),
                off: *off,
            });
            targets.push(target);
        }
        let mut ext_data = Vec::new();
        for (name, off, size) in &im.li.extern_data {
            let x = im
                .externs
                .iter()
                .find(|x| &x.name == name)
                .with_context(|| format!("extern_data {name} has no extern declaration"))?;
            ensure!(
                x.kind == ExternKind::Object,
                "extern {name} is not a data object"
            );
            if let Some((j, _, _)) = other(&x.raw_name) {
                bail!(
                    "extern data object {} of image {k} ({}) is defined by image {j} ({}); \
                     cross-image data references are not supported",
                    x.raw_name,
                    labels[k],
                    labels[j]
                );
            }
            ext_data.push(ExternData {
                raw: x.raw_name.clone(),
                off: *off,
                size: *size,
            });
        }
        out.push(ImageExterns {
            stubs,
            ext_data,
            targets,
        });
    }
    Ok(out)
}

/// The C runtime inputs `zig cc` passes to `ld.lld` for a static aarch64-linux-musl link of
/// `main_o`, from its `-v` output: `(startup objects before main, archives, objects after)`.
pub fn musl_inputs(
    verbose: &str,
    main_o: &Path,
) -> Result<(Vec<PathBuf>, Vec<PathBuf>, Vec<PathBuf>)> {
    // With a cold zig cache, `-v` also prints the links that build musl's own libraries; the
    // final link is the `ld.lld` line that names `main_o`.
    let main_s = main_o.to_string_lossy();
    let line = verbose
        .lines()
        .filter(|l| l.contains("ld.lld"))
        .find(|l| l.split_whitespace().any(|t| t == main_s))
        .with_context(|| {
            format!(
                "no `zig cc -v` ld.lld link line mentions {}",
                main_o.display()
            )
        })?;
    let (mut pre, mut libs, mut post) = (Vec::new(), Vec::new(), Vec::new());
    let mut seen_main = false;
    for tok in line.split_whitespace() {
        let p = PathBuf::from(tok);
        if p == main_o {
            seen_main = true;
        } else if tok.ends_with(".a") {
            libs.push(p);
        } else if tok.ends_with(".o") {
            if seen_main { &mut post } else { &mut pre }.push(p);
        }
    }
    ensure!(
        seen_main,
        "`zig cc -v` link line does not mention {}",
        main_o.display()
    );
    ensure!(
        pre.iter()
            .any(|p| p.file_name().is_some_and(|n| n == "crt1.o")),
        "no crt1.o in `zig cc -v` link line"
    );
    Ok((pre, libs, post))
}

/// Stage C runtime objects (`.o`) and archives (`.a`) into `stage_dir` with debug info stripped
/// via `objcopy`, keeping bare file names and failing if two staged inputs share a file name.
pub fn stage_runtime_inputs(
    objcopy: &Path,
    paths: &[PathBuf],
    stage_dir: &Path,
) -> Result<Vec<PathBuf>> {
    std::fs::create_dir_all(stage_dir)?;
    let mut seen = HashSet::new();
    let mut staged = Vec::with_capacity(paths.len());
    for src in paths {
        let name = src
            .file_name()
            .with_context(|| format!("runtime input {} has no file name", src.display()))?;
        let dst = stage_dir.join(name);
        ensure!(
            seen.insert(name.to_os_string()) && !dst.exists(),
            "duplicate runtime input file name {:?} while staging {}",
            name,
            src.display()
        );
        let mut c = Command::new(objcopy);
        match src.extension().and_then(|e| e.to_str()) {
            Some("o") => {
                c.arg("--strip-debug");
            }
            Some("a") => {
                c.args(["--enable-deterministic-archives", "--strip-debug"]);
            }
            other => bail!(
                "unsupported runtime input extension {:?} for {}",
                other,
                src.display()
            ),
        };
        run_cmd(c.arg(src).arg(&dst))?;
        if src.extension().and_then(|e| e.to_str()) == Some("a") {
            let normalized = normalize_gnu_archive_member_names(&std::fs::read(&dst)?)?;
            std::fs::write(&dst, normalized)?;
        }
        staged.push(dst);
    }
    Ok(staged)
}

/// Strip directory prefixes from member names in a deterministic GNU `!<arch>\n` archive emitted
/// by `llvm-objcopy --enable-deterministic-archives`: names of `<= 15` bytes are written inline as
/// `<base>/`, longer names go into a canonical `//` string table, and member file offsets in the
/// `/` or `/SYM64/` symbol index are updated to match.
///
/// With a cold cache, `zig` builds `libc.a`, `libzigc.a`, and `libcompiler_rt.a` from object files
/// under `<ZIG_GLOBAL_CACHE_DIR>/o/<hash>/...` and records those full cache paths in the archive
/// `//` string table, which `llvm-objcopy --enable-deterministic-archives --strip-debug` keeps.
pub fn normalize_gnu_archive_member_names(buf: &[u8]) -> Result<Vec<u8>> {
    rewrite_gnu_archive(buf, false)
}

/// Drop non-`.o` payload members (such as `lib.rmeta` and `lib.rmeta-link` inside a `.rlib`) and
/// normalize remaining member names to basenames while rebasing `/` and `/SYM64/` symbol offsets.
pub fn filter_gnu_archive_obj_members(buf: &[u8]) -> Result<Vec<u8>> {
    rewrite_gnu_archive(buf, true)
}

fn rewrite_gnu_archive(buf: &[u8], keep_only_obj: bool) -> Result<Vec<u8>> {
    ensure!(buf.starts_with(b"!<arch>\n"), "not a regular GNU archive");
    let mut pos = 8usize;
    let mut records: Vec<(usize, [u8; 60], Vec<u8>)> = Vec::new();
    while pos < buf.len() {
        if pos % 2 == 1 {
            pos += 1;
        }
        if pos == buf.len() {
            break;
        }
        ensure!(pos + 60 <= buf.len(), "truncated archive header at {pos}");
        let mut hdr = [0u8; 60];
        hdr.copy_from_slice(&buf[pos..pos + 60]);
        let size: usize = std::str::from_utf8(&hdr[48..58])
            .context("non-UTF8 archive member size")?
            .trim()
            .parse()
            .context("invalid archive member size")?;
        ensure!(
            pos + 60 + size <= buf.len(),
            "truncated archive member payload at {pos} (size {size})"
        );
        records.push((pos, hdr, buf[pos + 60..pos + 60 + size].to_vec()));
        pos += 60 + size;
    }

    let old_strtab: Vec<u8> = records
        .iter()
        .find(|(_, hdr, _)| hdr[..16].trim_ascii_end() == b"//")
        .map(|(_, _, data)| data.clone())
        .unwrap_or_default();
    records.retain(|(_, hdr, _)| hdr[..16].trim_ascii_end() != b"//");

    let mut new_strtab: Vec<u8> = Vec::new();
    let mut kept_records: Vec<(usize, [u8; 60], Vec<u8>)> = Vec::with_capacity(records.len());
    for (rec_pos, mut hdr, payload) in records {
        let trimmed = hdr[..16].trim_ascii_end();
        if trimmed == b"/" || trimmed == b"/SYM64/" {
            kept_records.push((rec_pos, hdr, payload));
            continue;
        }
        let raw_name: &[u8] = if hdr[0] == b'/'
            && !trimmed[1..].is_empty()
            && trimmed[1..].iter().all(|b| b.is_ascii_digit())
        {
            let off: usize = std::str::from_utf8(&trimmed[1..])?.parse()?;
            ensure!(
                off < old_strtab.len(),
                "archive string-table offset /{off} out of bounds ({})",
                old_strtab.len()
            );
            let tail = &old_strtab[off..];
            let end = tail.iter().position(|&b| b == b'\n').unwrap_or(tail.len());
            tail[..end].strip_suffix(b"/").unwrap_or(&tail[..end])
        } else {
            trimmed.strip_suffix(b"/").unwrap_or(trimmed)
        };
        let base = raw_name.rsplit(|&b| b == b'/').next().unwrap_or(raw_name);
        if keep_only_obj && !base.ends_with(b".o") {
            continue;
        }
        if base.len() <= 15 {
            let mut field = [b' '; 16];
            field[..base.len()].copy_from_slice(base);
            field[base.len()] = b'/';
            hdr[..16].copy_from_slice(&field);
        } else {
            let new_off = new_strtab.len();
            new_strtab.extend_from_slice(base);
            new_strtab.extend_from_slice(b"/\n");
            let field = format!("/{new_off:<15}");
            hdr[..16].copy_from_slice(field.as_bytes());
        }
        kept_records.push((rec_pos, hdr, payload));
    }
    let mut records = kept_records;

    if !new_strtab.is_empty() {
        let mut st_hdr = [b' '; 60];
        st_hdr[..2].copy_from_slice(b"//");
        st_hdr[48..58].copy_from_slice(format!("{:<10}", new_strtab.len()).as_bytes());
        st_hdr[58..60].copy_from_slice(b"`\n");
        let insert_idx = records
            .iter()
            .position(|(_, hdr, _)| {
                let t = hdr[..16].trim_ascii_end();
                t != b"/" && t != b"/SYM64/"
            })
            .unwrap_or(records.len());
        records.insert(insert_idx, (0, st_hdr, new_strtab));
    }

    let mut old_pos_to_new: HashMap<usize, usize> = HashMap::with_capacity(records.len());
    let mut out_pos = 8usize;
    for (old_pos, _, data) in &records {
        if out_pos % 2 == 1 {
            out_pos += 1;
        }
        if *old_pos > 0 {
            old_pos_to_new.insert(*old_pos, out_pos);
        }
        out_pos += 60 + data.len();
    }

    for (_, hdr, data) in &mut records {
        let tag = hdr[..16].trim_ascii_end();
        if tag == b"/" {
            ensure!(data.len() >= 4, "short archive symbol table");
            let n = u32::from_be_bytes(data[0..4].try_into().unwrap()) as usize;
            ensure!(
                data.len() >= 4usize.saturating_add(n.saturating_mul(4)),
                "truncated archive symbol offsets"
            );
            for k in 0..n {
                let o = 4 + 4 * k;
                let old_m = u32::from_be_bytes(data[o..o + 4].try_into().unwrap()) as usize;
                let &new_m = old_pos_to_new
                    .get(&old_m)
                    .with_context(|| format!("unknown member offset {old_m} in `/`"))?;
                let new_m_u32: u32 = new_m.try_into().context("archive exceeds 4 GiB")?;
                data[o..o + 4].copy_from_slice(&new_m_u32.to_be_bytes());
            }
        } else if tag == b"/SYM64/" {
            ensure!(data.len() >= 8, "short SYM64 archive symbol table");
            let n = u64::from_be_bytes(data[0..8].try_into().unwrap()) as usize;
            ensure!(
                data.len() >= 8usize.saturating_add(n.saturating_mul(8)),
                "truncated SYM64 symbol offsets"
            );
            for k in 0..n {
                let o = 8 + 8 * k;
                let old_m = u64::from_be_bytes(data[o..o + 8].try_into().unwrap()) as usize;
                let &new_m = old_pos_to_new
                    .get(&old_m)
                    .with_context(|| format!("unknown member offset {old_m} in `/SYM64/`"))?;
                data[o..o + 8].copy_from_slice(&(new_m as u64).to_be_bytes());
            }
        }
    }

    let mut out = Vec::with_capacity(out_pos);
    out.extend_from_slice(b"!<arch>\n");
    for (_, hdr, data) in records {
        if out.len() % 2 == 1 {
            out.push(b'\n');
        }
        out.extend_from_slice(&hdr);
        out.extend_from_slice(&data);
    }
    Ok(out)
}

pub fn tool(env: &str, name: &str) -> Result<PathBuf> {
    tool_from_env(
        env,
        std::env::var_os(env).as_deref(),
        name,
        std::env::var_os("PATH").as_deref(),
    )
}

pub fn tool_from_env(
    env: &str,
    env_val: Option<&std::ffi::OsStr>,
    name: &str,
    path_val: Option<&std::ffi::OsStr>,
) -> Result<PathBuf> {
    if let Some(p) = env_val.filter(|v| !v.is_empty()) {
        return Ok(PathBuf::from(p));
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    which::which_in(name, path_val, cwd).with_context(|| {
        format!(
            "`{name}` not found on PATH; set `${env}=/path/to/{name}` or install \
             `rustup component add llvm-tools` and pass \
             `${env}=\"$(dirname \"$(rustc --print target-libdir)\")/bin/{name}\"` \
             (or add that `bin` directory to PATH)"
        )
    })
}

/// Reject any `--branch-stubs` entry that does not match an image extern stub (either by raw
/// symbol name or demangled Rust name).
pub fn validate_branch_stubs(stubs: &[Stub], branch_stubs: &[String]) -> Result<()> {
    let mut known: HashSet<String> = HashSet::with_capacity(stubs.len() * 2);
    for s in stubs {
        known.insert(s.raw.clone());
        known.insert(demangle_rust_symbol(&s.raw));
    }
    let mut seen = HashSet::new();
    let unknown: Vec<&str> = branch_stubs
        .iter()
        .map(String::as_str)
        .filter(|name| !known.contains(*name) && seen.insert(*name))
        .collect();
    if !unknown.is_empty() {
        bail!(
            "--branch-stubs names unknown extern stub(s) not present in image stubs: {}",
            unknown.join(", ")
        );
    }
    Ok(())
}

/// Check that strong global definitions in `main.o` and `native_objs` do not collide.
pub fn check_no_duplicate_strong_defs(
    main_o_bytes: &[u8],
    native_objs: &[(String, Vec<u8>)],
) -> Result<()> {
    use object::{Object, ObjectSymbol};

    let mut seen: HashMap<String, String> = HashMap::new();
    let iter = std::iter::once(("main.c (main.o)".to_string(), main_o_bytes)).chain(
        native_objs
            .iter()
            .map(|(n, b)| (format!("native/{n}.o"), b.as_slice())),
    );
    for (origin, bytes) in iter {
        let obj = object::File::parse(bytes)
            .with_context(|| format!("failed to parse ELF object `{origin}`"))?;
        for sym in obj.symbols() {
            if sym.is_undefined() || !sym.is_global() || sym.is_weak() {
                continue;
            }
            let Ok(name) = sym.name() else {
                continue;
            };
            if name.is_empty() {
                continue;
            }
            if let Some(prev) = seen.insert(name.to_string(), origin.clone()) {
                bail!(
                    "duplicate strong symbol definition `{name}` in `{prev}` and `{origin}` \
                     (remove duplicate definition from `--main-c` or narrow `--native-only`)"
                );
            }
        }
    }
    Ok(())
}

/// Subset of `[[native_objects]]` names to compile: explicit `--native-only` when provided;
/// `memcpy,memset,memmove,memcmp,bcmp` when `--musl-string` is passed without `--native-only`;
/// `None` (all declared `[[native_objects]]`) when `--native-objects <CONFIG>` is passed without
/// `--native-only`.
pub fn effective_native_only(cli: &Cli) -> Option<Vec<String>> {
    if !cli.native_only.is_empty() {
        Some(cli.native_only.clone())
    } else if cli.musl_string {
        Some(
            ["memcpy", "memset", "memmove", "memcmp", "bcmp"]
                .into_iter()
                .map(String::from)
                .collect(),
        )
    } else {
        None
    }
}

/// Archive member stems in the pinned Rust 1.98.1 bundled `self-contained/libc.a` backing
/// `VerifiedLibraries/Musl` (`--musl-string`).
pub const MUSL_STRING_MEMBERS: &[&str] = &[
    "memcpy", "memset", "memmove", "memcmp", "bcmp", "memchr", "memrchr", "memccpy", "mempcpy",
    "memmem",
];

/// Extract the requested `<name>.lo` members from the pinned Rust 1.98.1 `aarch64-unknown-linux-musl`
/// `self-contained/libc.a` (verified against [`crate::std_profile::BUNDLED_LIBC_SHA256`]).
pub fn extract_musl_string_objects(only: Option<&[String]>) -> Result<Vec<(String, Vec<u8>)>> {
    let selected: Vec<String> = match only {
        Some(names) => {
            ensure!(
                !names.is_empty(),
                "`--native-only` with `--musl-string` must select at least one member"
            );
            let mut deduped = Vec::with_capacity(names.len());
            let mut unknown = Vec::new();
            for raw in names {
                let canonical = if raw == "__memrchr" {
                    "memrchr"
                } else {
                    raw.as_str()
                };
                if !MUSL_STRING_MEMBERS.contains(&canonical) {
                    unknown.push(raw.as_str());
                } else if !deduped.iter().any(|s| s == canonical) {
                    deduped.push(canonical.to_string());
                }
            }
            if !unknown.is_empty() {
                bail!(
                    "unknown `--native-only` member(s) for `--musl-string`: {} (allowed: {})",
                    unknown.join(", "),
                    MUSL_STRING_MEMBERS.join(", ")
                );
            }
            deduped
        }
        None => MUSL_STRING_MEMBERS
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
    };

    let tc = crate::std_profile::StdToolchain::resolve()?;
    let libc_path = tc.self_contained_libc();
    let libc_bytes = std::fs::read(&libc_path)
        .with_context(|| format!("failed to read {}", libc_path.display()))?;
    let ar = object::read::archive::ArchiveFile::parse(libc_bytes.as_slice())
        .map_err(|e| anyhow::anyhow!("{}: invalid archive: {e}", libc_path.display()))?;
    let mut member_map: HashMap<String, Vec<u8>> = HashMap::new();
    for entry in ar.members() {
        let entry = entry.map_err(|e| anyhow::anyhow!("corrupt archive member: {e}"))?;
        let mname = std::str::from_utf8(entry.name()).unwrap_or("");
        if let Some(stem) = mname.strip_suffix(".lo")
            && MUSL_STRING_MEMBERS.contains(&stem)
        {
            let data = entry
                .data(libc_bytes.as_slice())
                .map_err(|e| anyhow::anyhow!("failed to read `{mname}` from libc.a: {e}"))?;
            member_map.insert(stem.to_string(), data.to_vec());
        }
    }

    let mut out = Vec::with_capacity(selected.len());
    for stem in selected {
        let bytes = member_map.remove(&stem).ok_or_else(|| {
            anyhow::anyhow!(
                "missing `{stem}.lo` in pinned bundled {}",
                libc_path.display()
            )
        })?;
        out.push((stem, bytes));
    }
    Ok(out)
}

fn resolve_native_objects_config(cli: &Cli, repo_root: &Path) -> Result<Option<PathBuf>> {
    if let Some(p) = &cli.native_objects {
        if p.is_file() {
            return Ok(Some(std::fs::canonicalize(p)?));
        }
        let joined = repo_root.join(p);
        return Ok(Some(std::fs::canonicalize(&joined).with_context(|| {
            format!("cannot find `--native-objects` config `{}`", p.display())
        })?));
    }
    Ok(None)
}

pub(crate) fn run_cmd(c: &mut Command) -> Result<String> {
    let out = c.output().with_context(|| format!("failed to run {c:?}"))?;
    ensure!(
        out.status.success(),
        "{c:?} failed:\n{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr))
}

pub(crate) fn version(p: &Path, arg: &str) -> Result<String> {
    let s = run_cmd(Command::new(p).arg(arg))?;
    Ok(s.lines().next().unwrap_or("").trim().to_string())
}

pub fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn global_offsets<'a>(objs: &'a [ObjObject], li: &'a LinkedImage) -> HashMap<&'a str, u64> {
    let mut g = HashMap::new();
    for want in [SymBind::Global, SymBind::Weak] {
        for (o, offs) in objs.iter().zip(&li.sec_off) {
            for s in o.symbols.iter().filter(|s| s.bind == want) {
                if let SymSection::Sec(i) = s.sec
                    && let Some(off) = offs.get(i).copied().flatten()
                {
                    g.entry(s.name.as_str()).or_insert(off + s.value);
                }
            }
        }
    }
    for (n, o) in &li.stubs {
        g.entry(n.as_str()).or_insert(*o);
    }
    for (n, o, _) in &li.extern_data {
        g.entry(n.as_str()).or_insert(*o);
    }
    g
}

/// Prepare `o.elf_bytes` for `ld.lld`: strip sections dropped by `Trim`, adjust `SHF_WRITE` on
/// read-only sections (on `SecKind::Rodata` in page-separated mode so `:imgro` is `r--` while
/// `SecKind::Data` stays `rw-` on `:imgdata`, or on `SecKind::Rodata` plus `StubMode::Zero`
/// `SecKind::Data` in the default interleaved mode), and redirect GOT / initial-exec TLS
/// relocations to `.img.got` via `ADR_PREL_PG_HI21` / `LDST64_ABS_LO12_NC` so `ld.lld` does not
/// relax or reorder GOT slots.
pub fn prepare_object_bytes(
    o: &ObjObject,
    offs: &[Option<u64>],
    globals: &HashMap<&str, u64>,
    li: &LinkedImage,
    mode: StubMode,
    page_separate_data: bool,
) -> Result<Vec<u8>> {
    use object::elf;
    use object::read::elf::{FileHeader as _, SectionHeader as _};
    use rust_obj2lean::trusted_common::RelocType;

    let data: &[u8] = &o.elf_bytes;
    let header = elf::FileHeader64::<object::Endianness>::parse(data)?;
    let endian = header.endian()?;
    let sections = header.sections(endian, data)?;
    let symbols = sections.symbols(endian, data, elf::SHT_SYMTAB)?;
    let kept_elf: HashSet<usize> = o.sections.iter().map(|s| s.elf_index).collect();
    let elf_to_sec: HashMap<usize, usize> = o
        .sections
        .iter()
        .enumerate()
        .map(|(i, s)| (s.elf_index, i))
        .collect();

    let has_dropped_alloc = sections.enumerate().any(|(idx, sh)| {
        idx.0 > 0
            && (sh.sh_flags(endian) & elf::SHF_ALLOC as u64) != 0
            && sections
                .section_name(endian, sh)
                .map(|n| n != b".eh_frame")
                .unwrap_or(true)
            && !kept_elf.contains(&idx.0)
    });

    let anchor: Option<(usize, u64)> =
        o.symbols
            .iter()
            .enumerate()
            .skip(1)
            .find_map(|(sym_idx, sym)| {
                let SymSection::Sec(sec_idx) = sym.sec else {
                    return None;
                };
                if o.sections.get(sec_idx)?.kind() != Some(SecKind::Text) {
                    return None;
                };
                let sec_off = (*offs.get(sec_idx)?)?;
                let img_off = sec_off + sym.value;
                if sym.bind == SymBind::Local || globals.get(sym.name.as_str()) == Some(&img_off) {
                    Some((sym_idx, img_off))
                } else {
                    None
                }
            });

    let mut buf = o.elf_bytes.clone();
    let e_shoff = header.e_shoff(endian) as usize;
    let e_shentsize = header.e_shentsize(endian) as usize;

    for s in &o.sections {
        let clear_write = if page_separate_data {
            s.kind() == Some(SecKind::Rodata)
        } else {
            s.kind() == Some(SecKind::Rodata)
                || (mode == StubMode::Zero && s.kind() == Some(SecKind::Data))
        };
        if clear_write {
            let sh_off = e_shoff + s.elf_index * e_shentsize;
            let flags = u64::from_le_bytes(buf[sh_off + 8..sh_off + 16].try_into().unwrap());
            let new_flags = flags & !(elf::SHF_WRITE as u64);
            buf[sh_off + 8..sh_off + 16].copy_from_slice(&new_flags.to_le_bytes());
        }
    }

    let mut rewrote_got_or_tls = false;
    let mut referenced_syms: HashSet<usize> = HashSet::new();
    for (_idx, sh) in sections.enumerate() {
        let sh_type = sh.sh_type(endian);
        if sh_type != elf::SHT_RELA && sh_type != elf::SHT_REL {
            continue;
        }
        let target = sh.sh_info(endian) as usize;
        let Some(&sec_idx) = elf_to_sec.get(&target) else {
            continue;
        };
        let s = &o.sections[sec_idx];
        if sh_type == elf::SHT_REL {
            let rels: &[elf::Rel64<object::Endianness>] = sh.data_as_array(endian, data)?;
            for r in rels {
                referenced_syms.insert(r.r_sym(endian) as usize);
            }
        } else {
            let rela_off = sh.sh_offset(endian) as usize;
            let rela_entsize = sh.sh_entsize(endian) as usize;
            let relas: &[elf::Rela64<object::Endianness>] = sh.data_as_array(endian, data)?;
            for (rel_idx, r) in relas.iter().enumerate() {
                let rel = &s.relocs[rel_idx];
                if s.kind() == Some(SecKind::Text)
                    && (untrusted_legacy_linker::is_got(rel.rtype)
                        || untrusted_legacy_linker::is_tls_ie(rel.rtype))
                {
                    let sym = &o.symbols[rel.sym];
                    let tls = untrusted_legacy_linker::is_tls_ie(rel.rtype);
                    let sym_off = if tls {
                        li.extern_tls
                            .iter()
                            .find(|(n, _)| *n == sym.name)
                            .map(|p| p.1)
                    } else {
                        match sym.sec {
                            SymSection::Sec(i) if sym.bind == SymBind::Local => {
                                offs.get(i).copied().flatten().map(|o| o + sym.value)
                            }
                            _ => globals.get(sym.name.as_str()).copied(),
                        }
                    }
                    .with_context(|| format!("cannot locate GOT target {}", sym.name))?;
                    let t = sym_off.wrapping_add(rel.addend as u64);
                    let entry = if tls {
                        GotEntry::TpOff(t)
                    } else {
                        GotEntry::Addr(t)
                    };
                    let slot =
                        li.got.iter().position(|&g| g == entry).with_context(|| {
                            format!("no GOT slot for {} ({entry:x?})", sym.name)
                        })?;
                    let slot_off = li.got_off + 8 * slot as u64;
                    let (anchor_idx, anchor_off) =
                        anchor.context("no anchor symbol in kept .text section")?;
                    let new_rtype: u32 = match rel.rtype {
                        RelocType::AdrGotPage | RelocType::TlsieAdrGottprelPage21 => {
                            elf::R_AARCH64_ADR_PREL_PG_HI21
                        }
                        RelocType::Ld64GotLo12Nc | RelocType::TlsieLd64GottprelLo12Nc => {
                            elf::R_AARCH64_LDST64_ABS_LO12_NC
                        }
                        _ => unreachable!(),
                    };
                    let new_r_info = ((anchor_idx as u64) << 32) | (new_rtype as u64);
                    let new_r_addend = (slot_off as i64) - (anchor_off as i64);
                    let entry_off = rela_off + rel_idx * rela_entsize;
                    buf[entry_off + 8..entry_off + 16].copy_from_slice(&new_r_info.to_le_bytes());
                    buf[entry_off + 16..entry_off + 24]
                        .copy_from_slice(&new_r_addend.to_le_bytes());
                    referenced_syms.insert(anchor_idx);
                    rewrote_got_or_tls = true;
                } else {
                    referenced_syms.insert(r.r_sym(endian, false) as usize);
                }
            }
        }
    }

    if !has_dropped_alloc && !rewrote_got_or_tls {
        return Ok(buf);
    }

    let shstrndx = header.shstrndx(endian, data)? as usize;
    let symtab_sec_idx = symbols.section().0;
    let symtab_sh = sections.section(symbols.section())?;
    let symtab_str_idx = symtab_sh.sh_link(endian) as usize;

    for (idx, sh) in sections.enumerate() {
        if idx.0 == 0
            || kept_elf.contains(&idx.0)
            || idx.0 == shstrndx
            || idx.0 == symtab_sec_idx
            || idx.0 == symtab_str_idx
            || sh.sh_type(endian) == elf::SHT_SYMTAB_SHNDX
        {
            continue;
        }
        let sh_type = sh.sh_type(endian);
        if (sh_type == elf::SHT_RELA || sh_type == elf::SHT_REL)
            && kept_elf.contains(&(sh.sh_info(endian) as usize))
        {
            continue;
        }
        let sh_off = e_shoff + idx.0 * e_shentsize;
        buf[sh_off + 4..sh_off + 8].fill(0);
        buf[sh_off + 8..sh_off + 16].fill(0);
        buf[sh_off + 32..sh_off + 40].fill(0);
    }

    let symtab_off = symtab_sh.sh_offset(endian) as usize;
    let symtab_entsize = symtab_sh.sh_entsize(endian) as usize;
    let first_global = symtab_sh.sh_info(endian) as usize;
    for (sym_idx, sym) in symbols.symbols().iter().enumerate().skip(1) {
        let elf_sec = symbols.symbol_section(endian, sym, object::SymbolIndex(sym_idx))?;
        let in_kept = matches!(elf_sec, Some(object::SectionIndex(j)) if kept_elf.contains(&j));
        if in_kept {
            continue;
        }
        let sym_off = symtab_off + sym_idx * symtab_entsize;
        if referenced_syms.contains(&sym_idx) {
            if elf_sec.is_some() {
                buf[sym_off + 4] = (elf::STB_GLOBAL << 4) | elf::STT_NOTYPE;
                buf[sym_off + 5] = 0;
                buf[sym_off + 6..sym_off + 8].fill(0);
                buf[sym_off + 8..sym_off + 16].fill(0);
                buf[sym_off + 16..sym_off + 24].fill(0);
            }
        } else {
            buf[sym_off..sym_off + 4].fill(0);
            buf[sym_off + 4] = if sym_idx < first_global {
                0
            } else {
                (elf::STB_WEAK << 4) | elf::STT_NOTYPE
            };
            buf[sym_off + 5] = 0;
            buf[sym_off + 6..sym_off + 24].fill(0);
        }
    }
    Ok(buf)
}

/// Extract trimmed reachable `.rlib` objects for any `--branch-stubs` externs defined in an
/// image's dependency or sysroot `.rlib` archives (and not already defined by an image, `main`,
/// or `native_objs`). Unbranched image-stub references inside extracted `.rlib` objects are
/// redirected to `__snapstub_<k>`.
#[allow(clippy::too_many_arguments)]
fn extract_branch_stub_rlib_objects(
    images: &[Image],
    resolved: &[ImageExterns],
    mode: StubMode,
    branch_stubs: &[String],
    main_o_bytes: Option<&[u8]>,
    native_objs: &[(String, Vec<u8>)],
    objcopy: &Path,
    zig: &Path,
    work: &Path,
    allow_unwind_trap_fallback: bool,
) -> Result<Vec<PathBuf>> {
    use object::{Object, ObjectSymbol};

    if branch_stubs.is_empty() || images.iter().all(|im| im.rlibs.is_empty()) {
        return Ok(Vec::new());
    }

    let mut defined_outside: HashSet<String> = HashSet::new();
    for im in images {
        for (raw, _, _) in exported_symbols(&im.objects, &im.li) {
            defined_outside.insert(raw);
        }
    }
    let ext_objs = main_o_bytes
        .into_iter()
        .chain(native_objs.iter().map(|(_, b)| b.as_slice()));
    for bytes in ext_objs {
        let obj = object::File::parse(bytes)?;
        for sym in obj.symbols() {
            if !sym.is_undefined()
                && (sym.is_global() || sym.is_weak())
                && let Ok(name) = sym.name()
                && !name.is_empty()
            {
                defined_outside.insert(name.to_string());
            }
        }
    }

    let mut out_paths = Vec::new();
    let mut needs_unwind_fallback = false;
    let mut used_stems: HashSet<String> = HashSet::new();

    for (tag, (im, rx)) in images.iter().zip(resolved).enumerate() {
        if im.rlibs.is_empty() {
            continue;
        }
        let unbranched_stubs: HashMap<&str, usize> = rx
            .stubs
            .iter()
            .enumerate()
            .filter(|(_, s)| effective_stub_mode(&s.raw, mode, branch_stubs) != StubMode::Branch)
            .map(|(k, s)| (s.raw.as_str(), k))
            .collect();
        let mut pending: BTreeSet<String> = rx
            .stubs
            .iter()
            .enumerate()
            .filter(|(k, s)| {
                rx.targets[*k].is_none()
                    && effective_stub_mode(&s.raw, mode, branch_stubs) == StubMode::Branch
                    && !defined_outside.contains(&s.raw)
            })
            .map(|(_, s)| s.raw.clone())
            .collect();
        if pending.is_empty() {
            continue;
        }

        let mut queried: HashSet<String> = HashSet::new();
        let mut roots_by_rlib: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
        while !pending.is_empty() {
            for raw in &pending {
                queried.insert(raw.clone());
            }
            let found = untrusted_driver::scan_rlib_func_indices(&im.rlibs, &pending)?;
            pending.clear();
            let mut changed_rlibs = Vec::new();
            for (raw, rlib_idx) in found {
                let root = demangle_rust_symbol(&raw);
                if roots_by_rlib.entry(rlib_idx).or_default().insert(root) {
                    changed_rlibs.push(rlib_idx);
                }
            }
            changed_rlibs.sort_unstable();
            changed_rlibs.dedup();
            for rlib_idx in changed_rlibs {
                let roots: Vec<String> = roots_by_rlib[&rlib_idx].iter().cloned().collect();
                let (_member, elf_bytes, keep) =
                    untrusted_driver::rlib_object_for_roots(&im.rlibs[rlib_idx], &roots)?;
                let trimmed = strip_unkept_rlib_sections(&elf_bytes, &keep)?;
                let obj = object::File::parse(trimmed.as_slice())?;
                for sym in obj.symbols() {
                    if sym.is_undefined()
                        && let Ok(name) = sym.name()
                        && !name.is_empty()
                        && !queried.contains(name)
                        && !defined_outside.contains(name)
                        && !unbranched_stubs.contains_key(name)
                    {
                        pending.insert(name.to_string());
                    }
                }
            }
        }
        if roots_by_rlib.is_empty() {
            continue;
        }

        let rlib_dir = work.join("rlib");
        std::fs::create_dir_all(&rlib_dir)?;
        for (rlib_idx, roots_set) in roots_by_rlib {
            let roots: Vec<String> = roots_set.into_iter().collect();
            let (_member, elf_bytes, keep) =
                untrusted_driver::rlib_object_for_roots(&im.rlibs[rlib_idx], &roots)?;
            let trimmed = strip_unkept_rlib_sections(&elf_bytes, &keep)?;
            let obj = object::File::parse(trimmed.as_slice())?;
            let mut present_undefs = Vec::new();
            for sym in obj.symbols() {
                if sym.is_undefined()
                    && let Ok(name) = sym.name()
                {
                    if name == "_Unwind_Resume" {
                        needs_unwind_fallback = true;
                    }
                    if let Some(&k) = unbranched_stubs.get(name) {
                        present_undefs.push((name.to_string(), k));
                    }
                }
            }
            present_undefs.sort_by(|a, b| a.0.cmp(&b.0));
            present_undefs.dedup_by(|a, b| a.0 == b.0);

            let base_stem = if tag == 0 {
                untrusted_driver::rlib_crate_name(&im.rlibs[rlib_idx])
            } else {
                format!(
                    "{}_i{tag}",
                    untrusted_driver::rlib_crate_name(&im.rlibs[rlib_idx])
                )
            };
            let mut stem = base_stem.clone();
            let mut n = 2usize;
            while !used_stems.insert(stem.clone()) {
                stem = format!("{base_stem}_{n}");
                n += 1;
            }
            let raw_p = rlib_dir.join(format!("{stem}.orig.o"));
            let dst_p = rlib_dir.join(format!("{stem}.o"));
            std::fs::write(&raw_p, &trimmed)?;
            let mut c = Command::new(objcopy);
            c.arg("--strip-debug");
            for (raw, k) in &present_undefs {
                ensure!(!raw.starts_with('-'), "unexpected symbol name `{raw}`");
                c.arg(format!("--redefine-sym={raw}={}", Stub::sym_in(tag, *k)));
            }
            run_cmd(c.arg("--").arg(&raw_p).arg(&dst_p))?;
            out_paths.push(dst_p);
        }
    }

    if needs_unwind_fallback
        && allow_unwind_trap_fallback
        && !defined_outside.contains("_Unwind_Resume")
    {
        let rlib_dir = work.join("rlib");
        std::fs::create_dir_all(&rlib_dir)?;
        let asm = ".section .text.__snap_unwind_resume,\"ax\",@progbits\n\
                   .p2align 2\n\
                   .weak _Unwind_Resume\n\
                   .type _Unwind_Resume,@function\n\
                   _Unwind_Resume:\n\
                   .word 0\n\
                   .size _Unwind_Resume,4\n";
        std::fs::write(rlib_dir.join("unwind_trap.s"), asm)?;
        let unwind_o = rlib_dir.join("unwind_trap.o");
        run_cmd(Command::new(zig).current_dir(&rlib_dir).args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-g0",
            "-c",
            "unwind_trap.s",
            "-o",
            "unwind_trap.o",
        ]))?;
        out_paths.push(unwind_o);
    }

    Ok(out_paths)
}

/// Strip every section of relocatable ELF `data` outside `keep` (plus its relocation section and
/// symbol/string tables) and clear unreferenced out-of-closure symbol entries.
pub fn strip_unkept_rlib_sections(data: &[u8], keep: &BTreeSet<usize>) -> Result<Vec<u8>> {
    use object::elf;
    use object::read::elf::{FileHeader as _, SectionHeader as _};

    let header = elf::FileHeader64::<object::Endianness>::parse(data)?;
    let endian = header.endian()?;
    let sections = header.sections(endian, data)?;
    let symbols = sections.symbols(endian, data, elf::SHT_SYMTAB)?;

    let mut referenced_syms: HashSet<usize> = HashSet::new();
    for (_idx, sh) in sections.enumerate() {
        let sh_type = sh.sh_type(endian);
        if (sh_type != elf::SHT_RELA && sh_type != elf::SHT_REL)
            || !keep.contains(&(sh.sh_info(endian) as usize))
        {
            continue;
        }
        if sh_type == elf::SHT_REL {
            let rels: &[elf::Rel64<object::Endianness>] = sh.data_as_array(endian, data)?;
            for r in rels {
                referenced_syms.insert(r.r_sym(endian) as usize);
            }
        } else {
            let relas: &[elf::Rela64<object::Endianness>] = sh.data_as_array(endian, data)?;
            for r in relas {
                referenced_syms.insert(r.r_sym(endian, false) as usize);
            }
        }
    }

    let mut buf = data.to_vec();
    let e_shoff = header.e_shoff(endian) as usize;
    let e_shentsize = header.e_shentsize(endian) as usize;
    let shstrndx = header.shstrndx(endian, data)? as usize;
    let symtab_sec_idx = symbols.section().0;
    let symtab_sh = sections.section(symbols.section())?;
    let symtab_str_idx = symtab_sh.sh_link(endian) as usize;

    for (idx, sh) in sections.enumerate() {
        if idx.0 == 0
            || keep.contains(&idx.0)
            || idx.0 == shstrndx
            || idx.0 == symtab_sec_idx
            || idx.0 == symtab_str_idx
            || sh.sh_type(endian) == elf::SHT_SYMTAB_SHNDX
        {
            continue;
        }
        let sh_type = sh.sh_type(endian);
        if (sh_type == elf::SHT_RELA || sh_type == elf::SHT_REL)
            && keep.contains(&(sh.sh_info(endian) as usize))
        {
            continue;
        }
        let sh_off = e_shoff + idx.0 * e_shentsize;
        buf[sh_off + 4..sh_off + 8].fill(0);
        buf[sh_off + 8..sh_off + 16].fill(0);
        buf[sh_off + 32..sh_off + 40].fill(0);
    }

    let symtab_off = symtab_sh.sh_offset(endian) as usize;
    let symtab_entsize = symtab_sh.sh_entsize(endian) as usize;
    let first_global = symtab_sh.sh_info(endian) as usize;
    for (sym_idx, sym) in symbols.symbols().iter().enumerate().skip(1) {
        let elf_sec = symbols.symbol_section(endian, sym, object::SymbolIndex(sym_idx))?;
        let in_kept = matches!(elf_sec, Some(object::SectionIndex(j)) if keep.contains(&j));
        if in_kept {
            continue;
        }
        let sym_off = symtab_off + sym_idx * symtab_entsize;
        if referenced_syms.contains(&sym_idx) {
            if elf_sec.is_some() {
                buf[sym_off + 4] = (elf::STB_GLOBAL << 4) | elf::STT_NOTYPE;
                buf[sym_off + 5] = 0;
                buf[sym_off + 6..sym_off + 24].fill(0);
            }
        } else {
            buf[sym_off..sym_off + 4].fill(0);
            buf[sym_off + 4] = if sym_idx < first_global {
                0
            } else {
                (elf::STB_WEAK << 4) | elf::STT_NOTYPE
            };
            buf[sym_off + 5] = 0;
            buf[sym_off + 6..sym_off + 24].fill(0);
        }
    }
    Ok(buf)
}

/// Deterministic `\x1f`-separated `CARGO_ENCODED_RUSTFLAGS` for building a Rust `staticlib`
/// driver crate for `aarch64-unknown-linux-musl` without leaking build or home paths.
///
/// When `sysroot_and_commit` is `Some((sysroot, commit))`, `<sysroot>/lib/rustlib/src/rust` is
/// remapped to `/rustc/<commit>` after `rustup_home`: when the `rust-src` component is installed,
/// `rustc` rewrites `/rustc/<commit>/library/...` in precompiled `core`/`alloc` metadata to
/// `<sysroot>/lib/rustlib/src/rust/library/...` before applying `--remap-path-prefix`, and `rustc`
/// applies the last matching prefix.
pub fn rust_encoded_rustflags(
    repo_root: &Path,
    work: &Path,
    cargo_home: Option<&Path>,
    rustup_home: Option<&Path>,
    sysroot_and_commit: Option<(&Path, &str)>,
) -> String {
    let mut flags = vec![
        "-C".to_string(),
        "relocation-model=static".to_string(),
        "-C".to_string(),
        "strip=debuginfo".to_string(),
        "-C".to_string(),
        "metadata=snapmain".to_string(),
        format!("--remap-path-prefix={}={}", work.display(), "/work"),
        format!("--remap-path-prefix={}={}", repo_root.display(), "/src"),
    ];
    // Same codegen pins as `rust-obj2lean`, so a pre-verified Rust dependency compiled into the
    // driver's `main_rust.a` (e.g. a runtime crate with its own `[profile.release.package.*]`)
    // yields the same machine code as its standalone translated object.
    flags.extend(
        untrusted_driver::config::DETERMINISTIC_CODEGEN_FLAGS
            .iter()
            .map(|s| s.to_string()),
    );
    if let Some(ch) = cargo_home {
        flags.push(format!("--remap-path-prefix={}={}", ch.display(), "/cargo"));
    }
    if let Some(rh) = rustup_home {
        flags.push(format!(
            "--remap-path-prefix={}={}",
            rh.display(),
            "/rustup"
        ));
    }
    if let Some((sysroot, commit)) = sysroot_and_commit {
        let rust_src = sysroot.join("lib").join("rustlib").join("src").join("rust");
        let to = format!("/rustc/{commit}");
        flags.push(format!("--remap-path-prefix={}={to}", rust_src.display()));
        if let Ok(canon) = std::fs::canonicalize(&rust_src)
            && canon != rust_src
        {
            flags.push(format!("--remap-path-prefix={}={to}", canon.display()));
        }
    }
    flags.join("\x1f")
}

pub(crate) fn build_rust_main_archive(
    repo_root: &Path,
    work: &Path,
    objcopy: &Path,
    manifest_rel: &Path,
    rustc_version: &str,
) -> Result<PathBuf> {
    let manifest_path = if manifest_rel.is_absolute() {
        manifest_rel.to_path_buf()
    } else {
        repo_root.join(manifest_rel)
    };
    let manifest_path = std::fs::canonicalize(&manifest_path)
        .with_context(|| format!("missing --main-rust manifest {}", manifest_path.display()))?;
    let cargo = tool("CARGO", "cargo")?;
    let target_dir = work.join("rust-target");
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")));
    let rustup_home = std::env::var_os("RUSTUP_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".rustup")));
    let sysroot = untrusted_driver::rustc_sysroot(repo_root)?;
    let rustc_commit = untrusted_driver::rustc_commit_hash(rustc_version)?;
    let encoded_flags = rust_encoded_rustflags(
        repo_root,
        work,
        cargo_home.as_deref(),
        rustup_home.as_deref(),
        Some((&sysroot, rustc_commit)),
    );
    let mut c = Command::new(&cargo);
    c.current_dir(repo_root)
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("CARGO_ENCODED_RUSTFLAGS", encoded_flags)
        .env_remove("RUSTFLAGS")
        .args(["build", "--manifest-path"])
        .arg(&manifest_path)
        .args([
            "--target",
            "aarch64-unknown-linux-musl",
            "--release",
            "--locked",
        ]);
    run_cmd(&mut c)?;
    let release_dir = target_dir
        .join("aarch64-unknown-linux-musl")
        .join("release");
    let mut archives: Vec<PathBuf> = std::fs::read_dir(&release_dir)?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.is_file()
                && p.extension().is_some_and(|ext| ext == "a")
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with("lib"))
        })
        .collect();
    archives.sort();
    ensure!(
        archives.len() == 1,
        "expected exactly 1 staticlib `lib*.a` in {}, found {:?}",
        release_dir.display(),
        archives
    );
    let out_archive = work.join("main_rust.a");
    run_cmd(
        Command::new(objcopy)
            .args(["--enable-deterministic-archives", "--strip-debug"])
            .arg(&archives[0])
            .arg(&out_archive),
    )?;
    Ok(out_archive)
}

/// Run the recipe for `cli`.
pub fn run(cli: Cli) -> Result<()> {
    if cli.check_std_toolchain {
        let msg = crate::std_profile::check_std_toolchain()?;
        println!("{msg}");
        return Ok(());
    }
    ensure!(!cli.out_dir.as_os_str().is_empty(), "--out-dir is required");
    let repo_root = std::fs::canonicalize(&cli.repo_root)?;
    let std_bin = match &cli.main_rust {
        Some(manifest_rel) => {
            match crate::std_profile::classify_rust_manifest(manifest_rel, &repo_root)? {
                crate::std_profile::RustMainKind::Staticlib => None,
                crate::std_profile::RustMainKind::StdBin(info) => Some(info),
            }
        }
        None => None,
    };

    let n = cli.config.len();
    if std_bin.is_none() {
        ensure!(n >= 1, "at least one --config is required");
    }
    for (flag, k) in [
        ("--base", cli.base.len()),
        ("--expect-code", cli.expect_code.len()),
        ("--expect-data", cli.expect_data.len()),
    ] {
        ensure!(k <= n, "{k} {flag} values for {n} --config images");
    }
    for &base in &cli.base {
        ensure!(
            base % PAGE == 0 && base >= PAGE,
            "--base {base:#x} must be page aligned and at least {PAGE:#x}"
        );
    }

    // 1. Each image, exactly as `rust-obj2lean` exports it.
    let mut images = Vec::with_capacity(n);
    let mut _gen_dirs = Vec::with_capacity(n);
    let mut tc = (n > 0 || std_bin.is_none())
        .then(|| Toolchain::new(repo_root.clone()))
        .transpose()?;
    if let Some(ref mut tc) = tc {
        for (k, config) in cli.config.iter().enumerate() {
            let gen_dir = tempfile::tempdir()?;
            let cfg = load_config(&repo_root.join(config), &repo_root, Some(gen_dir.path()))?;
            let (ex, rlibs) = untrusted_driver::extract_with_rlibs(&cfg, tc)
                .with_context(|| format!("cannot extract {}", config.display()))?;
            let page_separate_data = cli.page_separate_data || cfg.page_separate_data;
            let layout = if page_separate_data {
                untrusted_legacy_linker::DataLayout::PageSeparated
            } else {
                untrusted_legacy_linker::DataLayout::Interleaved
            };
            let li = untrusted_legacy_linker::link_with_layout(&ex.objects, &ex.externs, 0, layout)
                .with_context(|| format!("cannot link the objects of {}", config.display()))?;
            if let Some(p) = cli.expect_code.get(k) {
                ensure!(
                    std::fs::read(p)? == li.code,
                    "image code differs from {}",
                    p.display()
                );
            }
            if let Some(p) = cli.expect_data.get(k) {
                ensure!(
                    std::fs::read(p)? == li.data,
                    "image data differs from {}",
                    p.display()
                );
            }
            images.push(Image {
                objects: ex.objects,
                externs: ex.externs,
                li,
                page_separate_data,
                rlibs,
            });
            _gen_dirs.push(gen_dir);
        }
    }
    if let Some(std_crate) = std_bin {
        link_std_images(&cli, &repo_root, &std_crate, &images)
    } else {
        let rustc_version = &tc.as_ref().expect("toolchain initialized").rustc_version;
        link_images(&cli, &repo_root, rustc_version, &images)
    }
}

/// Link `images` (one per `cli.config`, in order) with `main` and the C runtime into
/// `cli.out_dir/cli.name`, check the embedding, and write `link.json`. `rustc_version` is only
/// used for `--main-rust`.
pub fn link_images(
    cli: &Cli,
    repo_root: &Path,
    rustc_version: &str,
    images: &[Image],
) -> Result<()> {
    let labels: Vec<String> = cli.config.iter().map(|p| p.display().to_string()).collect();
    ensure!(
        !images.is_empty() && labels.len() == images.len(),
        "{} images for {} --config paths",
        images.len(),
        labels.len()
    );
    let multi = images.len() > 1;
    let page_sep = |im: &Image| cli.page_separate_data || im.page_separate_data;
    let extents: Vec<u64> = images
        .iter()
        .map(|im| image_extent_with(&im.li, page_sep(im)))
        .collect();
    let bases = place_bases(&cli.base, &extents)?;
    check_disjoint(&labels, &bases, &extents)?;
    let resolved = resolve_externs(images, &bases, &labels)?;
    let all_stubs: Vec<Stub> = resolved
        .iter()
        .flat_map(|rx| rx.stubs.iter().cloned())
        .collect();
    validate_branch_stubs(&all_stubs, &cli.branch_stubs)?;
    std::fs::create_dir_all(&cli.out_dir)?;
    let out_dir = std::fs::canonicalize(&cli.out_dir)?;
    let work = out_dir.join("work");
    std::fs::create_dir_all(&work)?;

    // 2. The stubs, extern data, GOT, and the renamed objects of each image.
    let objcopy = tool("LLVM_OBJCOPY", "llvm-objcopy")?;
    let lld = tool("LLD", "ld.lld")?;
    let zig = untrusted_driver::find_zig_binary("snapshot-link")?;
    let mut obj_paths: Vec<Vec<PathBuf>> = Vec::with_capacity(images.len());
    let mut support = String::new();
    for (tag, (im, rx)) in images.iter().zip(&resolved).enumerate() {
        let is_pagesep = page_sep(im);
        let got_vals: Vec<u64> = im.li.got.iter().map(|g| g.value(bases[tag])).collect();
        let globals = global_offsets(&im.objects, &im.li);
        let mut paths = Vec::new();
        for (i, (o, offs)) in im.objects.iter().zip(&im.li.sec_off).enumerate() {
            let file = obj_file(tag, i);
            let raw = work.join(file.replace(".o", ".orig.o"));
            let prepared = prepare_object_bytes(o, offs, &globals, &im.li, cli.stubs, is_pagesep)?;
            std::fs::write(&raw, &prepared)?;
            let p = work.join(&file);
            let mut c = Command::new(&objcopy);
            for (k, s) in rx.stubs.iter().enumerate() {
                c.arg(format!("--redefine-sym={}={}", s.raw, Stub::sym_in(tag, k)));
            }
            for (k, d) in rx.ext_data.iter().enumerate() {
                c.arg(format!(
                    "--redefine-sym={}={}",
                    d.raw,
                    ExternData::sym_in(tag, k)
                ));
            }
            run_cmd(c.arg(&raw).arg(&p))?;
            paths.push(p);
        }
        obj_paths.push(paths);
        support += &image_support_asm_in_with(
            tag,
            &rx.stubs,
            &rx.ext_data,
            &got_vals,
            cli.stubs,
            &cli.branch_stubs,
            is_pagesep,
        );
    }
    let stub_s = work.join("stubs.s");
    let stub_o = work.join("stubs.o");
    std::fs::write(&stub_s, support)?;
    // Assembled with the pinned zig (not the host `llvm-mc`, whose version varies) so that
    // `stubs.o` is reproducible.
    run_cmd(
        Command::new(&zig)
            .current_dir(&work)
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-g0",
                "-c",
                "stubs.s",
            ])
            .args(["-o", "stubs.o"]),
    )?;

    // 2b. Optional native objects (`--musl-string` from pinned `self-contained/libc.a`, or
    //     `--native-objects` compiled via `rust-obj2lean::untrusted_driver`).
    let mut native_objs = Vec::new();
    let mut native_paths = Vec::new();
    if cli.musl_string {
        let effective_only = effective_native_only(cli);
        native_objs = extract_musl_string_objects(effective_only.as_deref())?;
    } else if let Some(native_cfg_path) = resolve_native_objects_config(cli, repo_root)? {
        let native_tc = Toolchain::new(repo_root.to_path_buf())?;
        let native_gen = tempfile::tempdir()?;
        let native_cfg = load_config(&native_cfg_path, repo_root, Some(native_gen.path()))?;
        let effective_only = effective_native_only(cli);
        let only = effective_only.as_deref();
        native_objs = untrusted_driver::compile_native_objects(&native_tc, &native_cfg, only)?;
    }
    if !native_objs.is_empty() {
        let native_dir = work.join("native");
        std::fs::create_dir_all(&native_dir)?;
        for (name, bytes) in &native_objs {
            let p = native_dir.join(format!("{name}.o"));
            std::fs::write(&p, bytes)?;
            native_paths.push(p);
        }
    }

    // 3. `main` and the musl runtime.
    let probe_c = work.join("main.c");
    match &cli.main_c {
        Some(p) => std::fs::copy(p, &probe_c).map(|_| ())?,
        None => std::fs::write(&probe_c, "int main(void) {\n  return 0;\n}\n")?,
    }
    let probe_o = work.join("main.o");
    let zcc = |c: &mut Command| {
        c.arg("cc")
            .args(["-target", "aarch64-linux-musl", "-O2", "-fno-sanitize=all"])
            .args(["-fno-pie", "-no-pie", "-static"]);
    };
    // Compile inside `work` with relative paths and no debug info so that
    // `main.o` (and hence the ELF) does not depend on the output directory.
    let mut c = Command::new(&zig);
    zcc(&mut c);
    c.current_dir(&work)
        .args(["-g0", "-c", "main.c", "-o", "main.o"]);
    run_cmd(&mut c)?;
    if !native_objs.is_empty() && cli.main_rust.is_none() {
        check_no_duplicate_strong_defs(&std::fs::read(&probe_o)?, &native_objs)?;
    }
    let mut c = Command::new(&zig);
    zcc(&mut c);
    c.arg("-v").arg(&probe_o);
    if cli.main_rust.is_some() {
        c.arg("-lunwind");
    }
    let verbose = run_cmd(c.arg("-o").arg(work.join("probe")))?;
    let (pre, libs, post) = musl_inputs(&verbose, &probe_o)?;
    let _runtime_stage;
    let (pre, libs, post) = if cli.strip_runtime_debug {
        let stage = tempfile::tempdir()?;
        let staged_pre = stage_runtime_inputs(&objcopy, &pre, stage.path())?;
        let staged_libs = stage_runtime_inputs(&objcopy, &libs, stage.path())?;
        let staged_post = stage_runtime_inputs(&objcopy, &post, stage.path())?;
        _runtime_stage = Some(stage);
        (staged_pre, staged_libs, staged_post)
    } else {
        _runtime_stage = None;
        (pre, libs, post)
    };
    let probe_o_bytes = cli
        .main_rust
        .is_none()
        .then(|| std::fs::read(&probe_o))
        .transpose()?;
    let rlib_paths = extract_branch_stub_rlib_objects(
        images,
        &resolved,
        cli.stubs,
        &cli.branch_stubs,
        probe_o_bytes.as_deref(),
        &native_objs,
        &objcopy,
        &zig,
        &work,
        cli.main_rust.is_none(),
    )?;
    let main_input = match &cli.main_rust {
        None => probe_o,
        Some(manifest_rel) => {
            build_rust_main_archive(repo_root, &work, &objcopy, manifest_rel, rustc_version)?
        }
    };

    // 4. Link.
    let kinds_data = [SecKind::Rodata, SecKind::Data];
    let mut pinned = Vec::with_capacity(images.len());
    for (tag, im) in images.iter().enumerate() {
        let file = |i: usize| obj_file(tag, i);
        let text = pinned_sections(&im.objects, &im.li, &[SecKind::Text], file)?;
        let combined_data = pinned_sections(&im.objects, &im.li, &kinds_data, file)?;
        let rodata = pinned_sections(&im.objects, &im.li, &[SecKind::Rodata], file)?;
        let rw_data = pinned_sections(&im.objects, &im.li, &[SecKind::Data], file)?;
        let bss = pinned_sections(&im.objects, &im.li, &[SecKind::Bss], file)?;
        pinned.push((text, combined_data, rodata, rw_data, bss));
    }
    let layouts: Vec<ImageLayout> = images
        .iter()
        .zip(&resolved)
        .zip(&pinned)
        .enumerate()
        .map(
            |(tag, ((im, rx), (text, combined_data, rodata, rw_data, bss)))| {
                let kind = if page_sep(im) {
                    ImageLayoutKind::PageSeparated {
                        rodata,
                        rw_data,
                        layout: ImageDataLayout::from_image(&im.li),
                    }
                } else {
                    ImageLayoutKind::Interleaved {
                        data: combined_data,
                        got_off: (!im.li.got.is_empty()).then_some(im.li.got_off),
                    }
                };
                ImageLayout {
                    tag,
                    base: bases[tag],
                    text,
                    stubs: &rx.stubs,
                    bss,
                    ext_data: &rx.ext_data,
                    kind,
                }
            },
        )
        .collect();
    let gc_sections = cli.main_rust.is_some();
    let script = work.join("link.ld");
    std::fs::write(&script, linker_script_images(&layouts, gc_sections))?;
    let exe = out_dir.join(&cli.name);
    let mut c = Command::new(&lld);
    c.args([
        "-static",
        "-no-pie",
        if gc_sections {
            "--gc-sections"
        } else {
            "--no-gc-sections"
        },
        "--icf=none",
        "--no-relax",
    ])
    .args([
        "-z",
        "norelro",
        "-z",
        "max-page-size=4096",
        "-z",
        "common-page-size=4096",
    ])
    // `--strip-debug`: the toolchain-built musl objects carry install paths in their debug info,
    // whose size would otherwise move `e_shoff` in the (mapped) ELF header.
    .args([
        "-O0",
        "--build-id=none",
        "--strip-debug",
        "-e",
        "_start",
        "-T",
    ])
    .arg(&script)
    .arg("-o")
    .arg(&exe)
    .args(&pre);
    if cli.main_rust.is_none() {
        c.arg(&main_input);
    }
    c.args(&native_paths)
        .args(obj_paths.iter().flatten())
        .arg(&stub_o)
        .arg("--start-group");
    if cli.main_rust.is_some() {
        c.arg(&main_input);
    }
    c.args(&libs)
        .args(&rlib_paths)
        .arg("--end-group")
        .args(&post);
    run_cmd(&mut c)?;

    // 5. Check the embedding and record provenance.
    let elf_bytes = std::fs::read(&exe)?;
    let checks: Vec<verify::ImageCheck> = images
        .iter()
        .zip(&resolved)
        .enumerate()
        .map(|(tag, (im, rx))| verify::ImageCheck {
            tag,
            objs: &im.objects,
            li: &im.li,
            base: bases[tag],
            extent: extents[tag],
            stubs: &rx.stubs,
            targets: rx.targets.iter().map(|t| t.map(|(_, a)| a)).collect(),
            page_separate_data: page_sep(im),
        })
        .collect();
    let report = verify::check_images(&elf_bytes, &checks, cli.stubs, &cli.branch_stubs)?;
    // Record paths relative to the output directory (or just the file name
    // for toolchain-cache inputs) so the manifest is reproducible.
    let input_hash = |p: &Path| -> Result<serde_json::Value> {
        let shown = match p.strip_prefix(&out_dir) {
            Ok(rel) => rel.display().to_string(),
            Err(_) => p.file_name().map_or_else(
                || p.display().to_string(),
                |n| n.to_string_lossy().into_owned(),
            ),
        };
        Ok(serde_json::json!({ "path": shown, "sha256": sha256(&std::fs::read(p)?) }))
    };
    let mut inputs = Vec::new();
    for p in pre
        .iter()
        .chain([&main_input])
        .chain(&native_paths)
        .chain(obj_paths.iter().flatten())
        .chain([&stub_o])
        .chain(&libs)
        .chain(&rlib_paths)
        .chain(&post)
    {
        inputs.push(input_hash(p)?);
    }
    let image_json = |li: &LinkedImage| {
        serde_json::json!({
            "codeLen": li.code.len(), "codeSha256": sha256(&li.code),
            "dataOff": li.data_off, "dataLen": li.data.len(), "dataSha256": sha256(&li.data),
            "bss": li.bss,
        })
    };
    let custom_stubs =
        cli.stubs == StubMode::Mixed || !cli.branch_stubs.is_empty() || !native_paths.is_empty();
    let stub_mode_str = if cli.stubs == StubMode::Mixed
        || (cli.stubs == StubMode::Zero && !cli.branch_stubs.is_empty())
    {
        "mixed".to_string()
    } else {
        format!("{:?}", cli.stubs).to_lowercase()
    };
    let stubs_json: Vec<serde_json::Value> = if custom_stubs {
        resolved[0]
            .stubs
            .iter()
            .map(|s| {
                let eff = effective_stub_mode(&s.raw, cli.stubs, &cli.branch_stubs);
                serde_json::json!({
                    "extern": s.raw,
                    "off": s.off,
                    "mode": format!("{eff:?}").to_lowercase(),
                    "target": report.stub_targets.get(&s.off).copied(),
                })
            })
            .collect()
    } else {
        resolved[0]
            .stubs
            .iter()
            .map(|s| serde_json::json!({ "extern": s.raw, "off": s.off }))
            .collect()
    };
    let first = &images[0];
    let mut manifest = serde_json::json!({
        "schema": "snapshot-link/1",
        "config": labels[0],
        "base": bases[0],
        "stubMode": stub_mode_str,
        "elf": { "file": cli.name, "sha256": sha256(&elf_bytes) },
        "image": image_json(&first.li),
        "stubs": stubs_json,
        "check": report.json(),
        "tools": {
            "ld.lld": version(&lld, "--version")?,
            "llvm-objcopy": version(&objcopy, "--version")?,
            "zig": version(&zig, "version")?,
        },
        "inputs": inputs,
    });
    if multi {
        // Several images: the top-level `config`/`base`/`image`/`stubs` describe the first
        // image (as for a single image), and `images` describes every image.
        let ranges: Vec<(u64, u64)> = bases
            .iter()
            .zip(&extents)
            .map(|(&b, &e)| (b, b + e))
            .collect();
        let syms = verify::extern_symbols(&elf_bytes, &ranges)?;
        let mut arr = Vec::with_capacity(images.len());
        for (tag, (im, rx)) in images.iter().zip(&resolved).enumerate() {
            let base = bases[tag];
            let li = &im.li;
            let layout = ImageDataLayout::from_image(li);
            let stubs: Vec<serde_json::Value> = rx
                .stubs
                .iter()
                .zip(&rx.targets)
                .map(|(s, t)| {
                    let eff = effective_stub_mode(&s.raw, cli.stubs, &cli.branch_stubs);
                    let (by, target) = match t {
                        Some((j, a)) => (
                            serde_json::json!(j),
                            (eff == StubMode::Branch).then_some(*a),
                        ),
                        None => (
                            serde_json::json!("runtime"),
                            (eff == StubMode::Branch)
                                .then(|| syms.get(s.raw.as_str()).copied())
                                .flatten(),
                        ),
                    };
                    serde_json::json!({
                        "extern": s.raw, "off": s.off, "addr": base + s.off,
                        "definedBy": by, "target": target,
                    })
                })
                .collect();
            let sections = if page_sep(im) {
                serde_json::json!({
                    "text": base,
                    "rodata": (layout.ro_end > layout.data_off).then_some(base + layout.data_off),
                    "data": (layout.data_end > layout.ro_end).then_some(base + layout.ro_end),
                    "got": (!li.got.is_empty()).then_some(base + li.got_off),
                    "end": base + extents[tag],
                })
            } else {
                serde_json::json!({
                    "text": base,
                    "data": (li.data_end() > li.data_off).then_some(base + li.data_off),
                    "got": (!li.got.is_empty()).then_some(base + li.got_off),
                    "end": base + extents[tag],
                })
            };
            arr.push(serde_json::json!({
                "config": labels[tag],
                "base": base,
                "image": image_json(li),
                "sections": sections,
                "stubs": stubs,
                "extData": rx.ext_data.iter().map(|d| serde_json::json!({
                    "extern": d.raw, "off": d.off, "size": d.size,
                })).collect::<Vec<_>>(),
            }));
        }
        manifest["images"] = serde_json::Value::Array(arr);
    }
    std::fs::write(
        out_dir.join("link.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;
    if !report.ok() {
        bail!("embedding check failed:\n{}", report.errors.join("\n"));
    }
    println!("{}: {}", exe.display(), report.summary());
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn write_std_link_manifest(
    cli: &Cli,
    out_dir: &Path,
    elf_bytes: &[u8],
    images: &[Image],
    labels: &[String],
    bases: &[u64],
    extents: &[u64],
    resolved: &[ImageExterns],
    report: &verify::Report,
    std_tc: &crate::std_profile::StdToolchain,
    objcopy: &Path,
    zig: Option<&Path>,
    native_paths: &[PathBuf],
    input_paths: &[PathBuf],
) -> Result<()> {
    let page_sep = |im: &Image| cli.page_separate_data || im.page_separate_data;
    let input_hash = |p: &Path| -> Result<serde_json::Value> {
        let shown = match p.strip_prefix(out_dir) {
            Ok(rel) => rel.display().to_string(),
            Err(_) => p.file_name().map_or_else(
                || p.display().to_string(),
                |n| n.to_string_lossy().into_owned(),
            ),
        };
        Ok(serde_json::json!({ "path": shown, "sha256": sha256(&std::fs::read(p)?) }))
    };
    let inputs: Vec<serde_json::Value> = input_paths
        .iter()
        .map(|p| input_hash(p))
        .collect::<Result<_>>()?;
    let image_json = |li: &LinkedImage| {
        serde_json::json!({
            "codeLen": li.code.len(), "codeSha256": sha256(&li.code),
            "dataOff": li.data_off, "dataLen": li.data.len(), "dataSha256": sha256(&li.data),
            "bss": li.bss,
        })
    };
    let custom_stubs =
        cli.stubs == StubMode::Mixed || !cli.branch_stubs.is_empty() || !native_paths.is_empty();
    let stub_mode_str = if cli.stubs == StubMode::Mixed
        || (cli.stubs == StubMode::Zero && !cli.branch_stubs.is_empty())
    {
        "mixed".to_string()
    } else {
        format!("{:?}", cli.stubs).to_lowercase()
    };
    let (top_config, top_base, top_image, top_stubs) = if images.is_empty() {
        (
            serde_json::Value::Null,
            DEFAULT_BASE,
            serde_json::Value::Null,
            serde_json::json!([]),
        )
    } else {
        let stubs_json: Vec<serde_json::Value> = if custom_stubs {
            resolved[0]
                .stubs
                .iter()
                .map(|s| {
                    let eff = effective_stub_mode(&s.raw, cli.stubs, &cli.branch_stubs);
                    serde_json::json!({
                        "extern": s.raw,
                        "off": s.off,
                        "mode": format!("{eff:?}").to_lowercase(),
                        "target": report.stub_targets.get(&s.off).copied(),
                    })
                })
                .collect()
        } else {
            resolved[0]
                .stubs
                .iter()
                .map(|s| serde_json::json!({ "extern": s.raw, "off": s.off }))
                .collect()
        };
        (
            serde_json::json!(labels[0]),
            bases[0],
            image_json(&images[0].li),
            serde_json::Value::Array(stubs_json),
        )
    };
    let mut tools_json = serde_json::json!({
        "rust-lld": std_tc.lld.version()?,
        "llvm-objcopy": version(objcopy, "--version")?,
    });
    if let Some(z) = zig {
        tools_json["zig"] = serde_json::json!(version(z, "version")?);
    }
    let mut manifest = serde_json::json!({
        "schema": "snapshot-link/1",
        "config": top_config,
        "base": top_base,
        "stubMode": stub_mode_str,
        "elf": { "file": cli.name, "sha256": sha256(elf_bytes) },
        "image": top_image,
        "stubs": top_stubs,
        "check": report.json(),
        "stdProfile": std_tc.std_profile_json(),
        "tools": tools_json,
        "inputs": inputs,
    });
    if images.len() > 1 {
        let ranges: Vec<(u64, u64)> = bases
            .iter()
            .zip(extents)
            .map(|(&b, &e)| (b, b + e))
            .collect();
        let syms = verify::extern_symbols(elf_bytes, &ranges)?;
        let mut arr = Vec::with_capacity(images.len());
        for (tag, (im, rx)) in images.iter().zip(resolved).enumerate() {
            let base = bases[tag];
            let li = &im.li;
            let layout = ImageDataLayout::from_image(li);
            let stubs: Vec<serde_json::Value> = rx
                .stubs
                .iter()
                .zip(&rx.targets)
                .map(|(s, t)| {
                    let eff = effective_stub_mode(&s.raw, cli.stubs, &cli.branch_stubs);
                    let (by, target) = match t {
                        Some((j, a)) => (
                            serde_json::json!(j),
                            (eff == StubMode::Branch).then_some(*a),
                        ),
                        None => (
                            serde_json::json!("runtime"),
                            (eff == StubMode::Branch)
                                .then(|| syms.get(s.raw.as_str()).copied())
                                .flatten(),
                        ),
                    };
                    serde_json::json!({
                        "extern": s.raw, "off": s.off, "addr": base + s.off,
                        "definedBy": by, "target": target,
                    })
                })
                .collect();
            let sections = if page_sep(im) {
                serde_json::json!({
                    "text": base,
                    "rodata": (layout.ro_end > layout.data_off).then_some(base + layout.data_off),
                    "data": (layout.data_end > layout.ro_end).then_some(base + layout.ro_end),
                    "got": (!li.got.is_empty()).then_some(base + li.got_off),
                    "end": base + extents[tag],
                })
            } else {
                serde_json::json!({
                    "text": base,
                    "data": (li.data_end() > li.data_off).then_some(base + li.data_off),
                    "got": (!li.got.is_empty()).then_some(base + li.got_off),
                    "end": base + extents[tag],
                })
            };
            arr.push(serde_json::json!({
                "config": labels[tag],
                "base": base,
                "image": image_json(li),
                "sections": sections,
                "stubs": stubs,
                "extData": rx.ext_data.iter().map(|d| serde_json::json!({
                    "extern": d.raw, "off": d.off, "size": d.size,
                })).collect::<Vec<_>>(),
            }));
        }
        manifest["images"] = serde_json::Value::Array(arr);
    }
    std::fs::write(
        out_dir.join("link.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;
    Ok(())
}

/// Compile `std_crate` under the pinned Rust 1.98.1 `-Zbuild-std=std,panic_abort` profile, link
/// it with `images` (`0` or more pre-verified images) and the bundled musl `self-contained`
/// runtime via `rust-lld`, run [`verify::check_images`] + [`verify::check_std_elf`], and write
/// `link.json`.
pub fn link_std_images(
    cli: &Cli,
    repo_root: &Path,
    std_crate: &crate::std_profile::StdBinCrate,
    images: &[Image],
) -> Result<()> {
    let std_tc = crate::std_profile::StdToolchain::resolve()?;
    let objcopy = std_tc.resolve_objcopy()?;
    let labels: Vec<String> = cli.config.iter().map(|p| p.display().to_string()).collect();
    ensure!(
        labels.len() == images.len(),
        "{} images for {} --config paths",
        images.len(),
        labels.len()
    );
    let page_sep = |im: &Image| cli.page_separate_data || im.page_separate_data;
    let extents: Vec<u64> = images
        .iter()
        .map(|im| image_extent_with(&im.li, page_sep(im)))
        .collect();
    let bases = place_bases(&cli.base, &extents)?;
    check_disjoint(&labels, &bases, &extents)?;
    let resolved = resolve_externs(images, &bases, &labels)?;
    let all_stubs: Vec<Stub> = resolved
        .iter()
        .flat_map(|rx| rx.stubs.iter().cloned())
        .collect();
    validate_branch_stubs(&all_stubs, &cli.branch_stubs)?;

    std::fs::create_dir_all(&cli.out_dir)?;
    let out_dir = std::fs::canonicalize(&cli.out_dir)?;
    let work = out_dir.join("work");
    std::fs::create_dir_all(&work)?;

    let native_cfg_opt = resolve_native_objects_config(cli, repo_root)?;
    let zig = (!images.is_empty() || native_cfg_opt.is_some())
        .then(|| untrusted_driver::find_zig_binary("snapshot-link"))
        .transpose()?;

    let mut native_objs = Vec::new();
    let mut native_paths = Vec::new();
    if let Some(native_cfg_path) = native_cfg_opt {
        let native_tc = Toolchain::new(repo_root.to_path_buf())?;
        let native_gen = tempfile::tempdir()?;
        let native_cfg = load_config(&native_cfg_path, repo_root, Some(native_gen.path()))?;
        let effective_only = effective_native_only(cli);
        native_objs = untrusted_driver::compile_native_objects(
            &native_tc,
            &native_cfg,
            effective_only.as_deref(),
        )?;
        let native_dir = work.join("native");
        std::fs::create_dir_all(&native_dir)?;
        for (name, bytes) in &native_objs {
            let p = native_dir.join(format!("{name}.o"));
            std::fs::write(&p, bytes)?;
            native_paths.push(p);
        }
    }

    let mut image_exports = HashSet::new();
    for im in images {
        for (name, _, _) in exported_symbols(&im.objects, &im.li) {
            image_exports.insert(name);
        }
    }
    let (main_rust_o, compiler_builtins_a) = crate::std_profile::build_std_main_objects(
        &std_tc,
        std_crate,
        repo_root,
        &work,
        &objcopy,
        &image_exports,
    )?;

    let mut obj_paths: Vec<Vec<PathBuf>> = Vec::with_capacity(images.len());
    let mut stub_o: Option<PathBuf> = None;
    if !images.is_empty() {
        let zig_bin = zig.as_ref().expect("zig resolved for image stubs");
        let mut support = String::new();
        for (tag, (im, rx)) in images.iter().zip(&resolved).enumerate() {
            let is_pagesep = page_sep(im);
            let got_vals: Vec<u64> = im.li.got.iter().map(|g| g.value(bases[tag])).collect();
            let globals = global_offsets(&im.objects, &im.li);
            let mut paths = Vec::new();
            for (i, (o, offs)) in im.objects.iter().zip(&im.li.sec_off).enumerate() {
                let file = obj_file(tag, i);
                let raw = work.join(file.replace(".o", ".orig.o"));
                let prepared =
                    prepare_object_bytes(o, offs, &globals, &im.li, cli.stubs, is_pagesep)?;
                std::fs::write(&raw, &prepared)?;
                let p = work.join(&file);
                let mut c = Command::new(&objcopy);
                for (k, s) in rx.stubs.iter().enumerate() {
                    c.arg(format!("--redefine-sym={}={}", s.raw, Stub::sym_in(tag, k)));
                }
                for (k, d) in rx.ext_data.iter().enumerate() {
                    c.arg(format!(
                        "--redefine-sym={}={}",
                        d.raw,
                        ExternData::sym_in(tag, k)
                    ));
                }
                run_cmd(c.arg(&raw).arg(&p))?;
                paths.push(p);
            }
            obj_paths.push(paths);
            support += &image_support_asm_in_with(
                tag,
                &rx.stubs,
                &rx.ext_data,
                &got_vals,
                cli.stubs,
                &cli.branch_stubs,
                is_pagesep,
            );
        }

        let mut already_defined =
            crate::std_profile::defined_nonlocal_symbols(&std::fs::read(&main_rust_o)?)?;
        for (_, bytes) in &native_objs {
            already_defined.extend(crate::std_profile::defined_nonlocal_symbols(bytes)?);
        }
        let mut needed_alloc_shims = Vec::new();
        for rx in &resolved {
            for (s, target) in rx.stubs.iter().zip(&rx.targets) {
                if target.is_none()
                    && effective_stub_mode(&s.raw, cli.stubs, &cli.branch_stubs) == StubMode::Branch
                    && !already_defined.contains(&s.raw)
                {
                    needed_alloc_shims.push(s.raw.clone());
                }
            }
        }
        support += &crate::std_profile::rust_alloc_bridge_asm(&needed_alloc_shims);

        let stub_s = work.join("stubs.s");
        let so = work.join("stubs.o");
        std::fs::write(&stub_s, support)?;
        run_cmd(Command::new(zig_bin).current_dir(&work).args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-g0",
            "-c",
            "stubs.s",
            "-o",
            "stubs.o",
        ]))?;
        stub_o = Some(so);
    }

    let runtime_dir = work.join("runtime");
    if runtime_dir.exists() {
        std::fs::remove_dir_all(&runtime_dir)?;
    }
    let staged_pre = stage_runtime_inputs(&objcopy, &std_tc.self_contained_pre(), &runtime_dir)?;
    let staged_libs = stage_runtime_inputs(
        &objcopy,
        &[std_tc.self_contained_libc(), std_tc.self_contained_unwind()],
        &runtime_dir,
    )?;
    let staged_post = stage_runtime_inputs(&objcopy, &std_tc.self_contained_post(), &runtime_dir)?;
    let (staged_libc, staged_unwind) = (&staged_libs[0], &staged_libs[1]);

    let kinds_data = [SecKind::Rodata, SecKind::Data];
    let mut pinned = Vec::with_capacity(images.len());
    for (tag, im) in images.iter().enumerate() {
        let file = |i: usize| obj_file(tag, i);
        let text = pinned_sections(&im.objects, &im.li, &[SecKind::Text], file)?;
        let combined_data = pinned_sections(&im.objects, &im.li, &kinds_data, file)?;
        let rodata = pinned_sections(&im.objects, &im.li, &[SecKind::Rodata], file)?;
        let rw_data = pinned_sections(&im.objects, &im.li, &[SecKind::Data], file)?;
        let bss = pinned_sections(&im.objects, &im.li, &[SecKind::Bss], file)?;
        pinned.push((text, combined_data, rodata, rw_data, bss));
    }
    let layouts: Vec<ImageLayout> = images
        .iter()
        .zip(&resolved)
        .zip(&pinned)
        .enumerate()
        .map(
            |(tag, ((im, rx), (text, combined_data, rodata, rw_data, bss)))| {
                let kind = if page_sep(im) {
                    ImageLayoutKind::PageSeparated {
                        rodata,
                        rw_data,
                        layout: ImageDataLayout::from_image(&im.li),
                    }
                } else {
                    ImageLayoutKind::Interleaved {
                        data: combined_data,
                        got_off: (!im.li.got.is_empty()).then_some(im.li.got_off),
                    }
                };
                ImageLayout {
                    tag,
                    base: bases[tag],
                    text,
                    stubs: &rx.stubs,
                    bss,
                    ext_data: &rx.ext_data,
                    kind,
                }
            },
        )
        .collect();

    let script = work.join("link.ld");
    std::fs::write(&script, linker_script_std_images(&layouts))?;
    let exe = out_dir.join(&cli.name);
    let mut c = std_tc.lld.command();
    c.args([
        "-static",
        "-no-pie",
        "--gc-sections",
        "--icf=none",
        "--no-relax",
        "-z",
        "norelro",
        "-z",
        "max-page-size=4096",
        "-z",
        "common-page-size=4096",
        "-z",
        "noexecstack",
        "-O0",
        "--build-id=none",
        "--strip-debug",
        "-e",
        "_start",
        "-T",
    ])
    .arg(&script)
    .arg("-o")
    .arg(&exe)
    .args(&staged_pre)
    .args(&native_paths)
    .args(obj_paths.iter().flatten());
    if let Some(ref so) = stub_o {
        c.arg(so);
    }
    c.arg("--start-group")
        .arg(&main_rust_o)
        .arg(staged_libc)
        .arg(&compiler_builtins_a)
        .arg("--as-needed")
        .arg(staged_unwind)
        .arg("--no-as-needed")
        .arg("--end-group")
        .args(&staged_post);
    run_cmd(&mut c)?;

    let elf_bytes = std::fs::read(&exe)?;
    let checks: Vec<verify::ImageCheck> = images
        .iter()
        .zip(&resolved)
        .enumerate()
        .map(|(tag, (im, rx))| verify::ImageCheck {
            tag,
            objs: &im.objects,
            li: &im.li,
            base: bases[tag],
            extent: extents[tag],
            stubs: &rx.stubs,
            targets: rx.targets.iter().map(|t| t.map(|(_, a)| a)).collect(),
            page_separate_data: page_sep(im),
        })
        .collect();
    let report = verify::check_images(&elf_bytes, &checks, cli.stubs, &cli.branch_stubs)?;

    let mut input_paths: Vec<PathBuf> = Vec::new();
    input_paths.extend(staged_pre);
    input_paths.extend(native_paths.iter().cloned());
    input_paths.extend(obj_paths.into_iter().flatten());
    if let Some(so) = stub_o {
        input_paths.push(so);
    }
    input_paths.push(main_rust_o);
    input_paths.push(staged_libc.clone());
    input_paths.push(compiler_builtins_a);
    input_paths.push(staged_unwind.clone());
    input_paths.extend(staged_post);

    write_std_link_manifest(
        cli,
        &out_dir,
        &elf_bytes,
        images,
        &labels,
        &bases,
        &extents,
        &resolved,
        &report,
        &std_tc,
        &objcopy,
        zig.as_deref(),
        &native_paths,
        &input_paths,
    )?;

    if !report.ok() {
        bail!("embedding check failed:\n{}", report.errors.join("\n"));
    }
    verify::check_std_elf(&elf_bytes)?;
    println!("{}: {}", exe.display(), report.summary());
    Ok(())
}
