// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! 4-Layer differential test suite for `Arm64.Obj.Placed` (`MultiPlacedLib` / `CodeBlock`)
//! against stock `ld.lld`, `untrusted_placed`, and `Arm64/Testing/.lake/build/bin/placed_eval` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (`#[cfg(test)]` differential test suite validating the `[TCB]`
//!   relocation/relaxation definitions in `Arm64/Trusted/Object/Placed.lean` and the `[OUTSIDE TCB]`
//!   Rust mirror in `untrusted_placed/`).
//! - **Purpose:** Implements the 4-layer differential testing architecture:
//!   1. **Layer 1 (`lake -d Arm64/Testing exe placed_eval`)**: Evaluates the real Lean TCB definitions via
//!      `Arm64/Testing/.lake/build/bin/placed_eval` (`MultiPlacedLib.Placeable`, `CodeBlock.patchedWord`,
//!      `MultiPlacedLib.patchedData`) on concrete `MultiPlacement`s.
//!   2. **Layer 2 (Byte-for-Byte Differential Harness vs. Stock `ld.lld`)**: Synthesizes
//!      non-canonical placements (Near `< 1 MiB` relaxed & unrelaxed, Medium `2..120 MiB`, High
//!      canonical ASLR `0x0000_aaaa_0000_0000`, and Page-boundary stress `0xff8`/`0xffc`), pins
//!      every section/symbol VMA via `-T layout.lds`, runs stock `ld.lld`, and asserts 100%
//!      byte-for-byte equality across `ld.lld`, `untrusted_placed`, and `placed_eval`.
//!   3. **Layer 3 (Negative / Soundness Rejection Differential Tests)**: Asserts that out-of-range
//!      branches/pages/offsets, misaligned targets, overlapping regions, and overflowed TLS offsets
//!      are rejected by both `ld.lld` (non-zero exit) and `placed_eval` (`valid == false`).
//!   4. **Layer 4 (Real Multi-TU C & Rust Corpus + `thread_local!`)**: Compiles multi-TU C and
//!      Rust programs (including trait-object `.data.rel.ro` vtables, jump tables, 8..128-bit
//!      loads/stores, `.rlib` PIC `TLSDESC -> TLSLE` relaxation, and static `TLSLE` thread-locals
//!      with `.tdata` and `.tbss`) and verifies 3-way byte-for-byte equality across all layouts.
//!
//! # When to Read This File
//! - Read this file when adding new relocations, relaxation rules, or TLS/section layouts to
//!   `Arm64/Trusted/Object/Placed.lean` or `tools/rust-obj2lean/src/untrusted_placed/`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use anyhow::{Context, Result, bail, ensure};
use object::{Object as _, ObjectSection as _};
use serde_json::{Value, json};

use crate::test_infra::{
    Tool, find_lld, find_llvm_mc, repo_root, require_link_diff, skip_or_panic,
};
use crate::trusted_common::{ObjObject, RelocKind, SymSection};
use crate::trusted_extractor::parse_object;
use crate::untrusted_placed::model::{
    PData, PMultiLib as MultiPlacedLib, PReloc, build_multi_placed_lib,
    build_multi_placed_lib_bounded, build_placed_lib,
};
use crate::untrusted_placed::patch::{
    PPlacement, add_signed, code_reloc_in_range, data_reloc_width, tls_base_offset,
};

/// Concrete multi-block placement passed to `placed_eval`, `untrusted_placed`, and `ld.lld`.
#[derive(Clone, Debug, Default)]
pub struct PlacedEvalPlacement {
    pub code_addrs: Vec<u64>,
    pub data_addrs: BTreeMap<String, u64>,
    /// TP-relative (`TPIDR_EL0`) offsets for TLS symbols.
    pub tls_addrs: BTreeMap<String, u64>,
    /// External symbol addresses.
    pub extern_addrs: BTreeMap<String, u64>,
    /// Per-block offsets where `ADRP + ADD -> NOP + ADR` relaxation is enabled.
    pub relax: Vec<BTreeSet<u64>>,
    /// Per-block offsets where branch-to-branch forwarding is enabled.
    pub b2b: Vec<BTreeSet<u64>>,
    /// Weak references the linker leaves undefined (`MultiPlacement.undefWeak`).
    pub undef_weak: BTreeSet<String>,
}

/// Output materialized by `placed_eval` or `eval_untrusted_placed`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlacedEvalResult {
    pub valid: bool,
    pub error: Option<String>,
    pub code_blocks: Vec<Vec<u8>>,
    pub data_blocks: BTreeMap<String, Vec<u8>>,
    pub tls_blocks: BTreeMap<String, Vec<u8>>,
}

/// Deterministic non-canonical placement strategies for Layer 2 & Layer 4 differential testing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LayoutVariant {
    /// `< 1 MiB` code-to-data distance with `ld.lld` relaxation enabled (`ADRP+ADD -> NOP+ADR`).
    NearRelax,
    /// `< 1 MiB` code-to-data distance with `ld.lld --no-relax` (`Placement.relax` empty).
    NearNoRelax,
    /// `32 MiB` code-to-data distance (`ADRP+ADD` outside ±1 MiB -> unrelaxed even with relax on).
    Medium,
    /// High canonical PIE/ASLR layout (`0x0000_aaaa_0000_0000` code, `0x0000_aaaa_0400_0000` data).
    HighCanonicalAslr,
    /// Page-boundary stress (`0xff0` / `0xff8` / `0xffc` page-end offsets).
    PageBoundaryStress,
}

/// Ensure `Arm64/Testing/.lake/build/bin/placed_eval` is built and up to date.
pub fn ensure_placed_eval_bin() -> Result<&'static Path> {
    static PLACED_EVAL_BIN: OnceLock<std::result::Result<PathBuf, String>> = OnceLock::new();
    let res = PLACED_EVAL_BIN.get_or_init(|| {
        let root = repo_root();
        let bin = root.join("Arm64/Testing/.lake/build/bin/placed_eval");
        let needed = [
            bin.clone(),
            root.join("Arm64/.lake/build/ir/Arm64/Trusted/Object/Reloc.c"),
            root.join("Arm64/.lake/build/ir/Arm64/Trusted/Object/Placed.c"),
            root.join("Arm64/Testing/.lake/build/ir/Arm64/Testing/Harness/PlacedEval.c"),
        ];
        if !needed.iter().all(|p| p.is_file()) {
            let out = Command::new("lake")
                .args(["-d", "Arm64/Testing", "build", "--no-ansi", "placed_eval"])
                .current_dir(&root)
                .output()
                .map_err(|e| format!("failed to run `lake -d Arm64/Testing build --no-ansi placed_eval`: {e}"))?;
            if !out.status.success() {
                return Err(format!(
                    "`lake -d Arm64/Testing build --no-ansi placed_eval` failed:\nstdout:\n{}\nstderr:\n{}",
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                ));
            }
        }
        if let Some(p) = needed.iter().find(|p| !p.is_file()) {
            return Err(format!("expected {} after building placed_eval", p.display()));
        }
        Ok(bin)
    });
    match res {
        Ok(p) => Ok(p.as_path()),
        Err(msg) => bail!("{msg}"),
    }
}

fn hex_u64(v: u64) -> String {
    format!("0x{v:016x}")
}

fn reloc_json(r: &PReloc) -> Value {
    json!({
        "off": r.off,
        "kind": r.kind.lean_name().trim_start_matches('.'),
        "sym": r.sym,
        "addend": r.addend,
        "local_sym": false,
    })
}

fn data_json(d: &PData) -> Value {
    json!({
        "sym": d.sym,
        "align": d.align,
        "read_only": d.read_only,
        "bytes_hex": hex::encode(&d.bytes),
        "zero_tail": d.zero_tail,
        "relocs": d.relocs.iter().map(reloc_json).collect::<Vec<_>>(),
    })
}

/// Invoke `Arm64/Testing/.lake/build/bin/placed_eval` on `(lib, pl)` and parse its JSON response.
pub fn run_placed_eval(lib: &MultiPlacedLib, pl: &PlacedEvalPlacement) -> Result<PlacedEvalResult> {
    let bin = ensure_placed_eval_bin()?;
    let blocks_json: Vec<Value> = lib
        .blocks
        .iter()
        .map(|b| {
            json!({
                "code_hex": hex::encode(&b.code),
                "align": b.align,
                "symbols": b.symbols.iter().map(|(n, o)| json!({"name": n, "off": o})).collect::<Vec<_>>(),
                "relocs": b.relocs.iter().map(reloc_json).collect::<Vec<_>>(),
                "externs": b.externs,
                "weak_refs": b.weak_refs,
            })
        })
        .collect();
    let req = json!({
        "name": lib.name,
        "blocks": blocks_json,
        "data": lib.data.iter().map(data_json).collect::<Vec<_>>(),
        "tls": lib.tls.iter().map(data_json).collect::<Vec<_>>(),
        "exports": lib.exports,
        "placement": {
            "code_addrs": pl.code_addrs.iter().copied().map(hex_u64).collect::<Vec<_>>(),
            "data_addrs": pl.data_addrs.iter().map(|(k, &v)| json!({"name": k, "addr": hex_u64(v)})).collect::<Vec<_>>(),
            "tls_addrs": pl.tls_addrs.iter().map(|(k, &v)| json!({"name": k, "addr": hex_u64(v)})).collect::<Vec<_>>(),
            "rho": pl.extern_addrs.iter().map(|(k, &v)| json!({"name": k, "addr": hex_u64(v)})).collect::<Vec<_>>(),
            "relax": pl.relax.iter().map(|s| s.iter().copied().collect::<Vec<_>>()).collect::<Vec<_>>(),
            "b2b": pl.b2b.iter().map(|s| s.iter().copied().collect::<Vec<_>>()).collect::<Vec<_>>(),
            "undef_weak": pl.undef_weak,
        }
    });

    let dir = tempfile::tempdir()?;
    let req_path = dir.path().join("placed_req.json");
    std::fs::write(&req_path, serde_json::to_vec(&req)?)?;
    let out = Command::new(bin)
        .arg(&req_path)
        .output()
        .with_context(|| format!("failed to execute {}", bin.display()))?;
    ensure!(
        out.status.success(),
        "placed_eval exited with {}:\nstdout:\n{}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let resp: Value = serde_json::from_slice(&out.stdout).with_context(|| {
        format!(
            "failed to parse placed_eval JSON:\n{}",
            String::from_utf8_lossy(&out.stdout)
        )
    })?;
    let valid = resp["valid"]
        .as_bool()
        .context("placed_eval missing boolean 'valid'")?;
    let error = resp.get("error").and_then(Value::as_str).map(String::from);
    let mut code_blocks = Vec::new();
    if let Some(arr) = resp["code"].as_array() {
        for item in arr {
            let hex_str = item["bytes_hex"]
                .as_str()
                .context("code entry missing bytes_hex")?;
            code_blocks.push(hex::decode(hex_str)?);
        }
    }
    let mut data_blocks = BTreeMap::new();
    if let Some(arr) = resp["data"].as_array() {
        for item in arr {
            let sym = item["sym"].as_str().context("data entry missing sym")?;
            let hex_str = item["bytes_hex"]
                .as_str()
                .context("data entry missing bytes_hex")?;
            data_blocks.insert(sym.to_string(), hex::decode(hex_str)?);
        }
    }
    let mut tls_blocks = BTreeMap::new();
    if let Some(arr) = resp["tls"].as_array() {
        for item in arr {
            let sym = item["sym"].as_str().context("tls entry missing sym")?;
            let hex_str = item["bytes_hex"]
                .as_str()
                .context("tls entry missing bytes_hex")?;
            tls_blocks.insert(sym.to_string(), hex::decode(hex_str)?);
        }
    }
    Ok(PlacedEvalResult {
        valid,
        error,
        code_blocks,
        data_blocks,
        tls_blocks,
    })
}

fn build_full_rho(lib: &MultiPlacedLib, pl: &PlacedEvalPlacement) -> BTreeMap<String, u64> {
    let mut rho = pl.extern_addrs.clone();
    for (k, &v) in &pl.data_addrs {
        rho.insert(k.clone(), v);
    }
    for (k, &v) in &pl.tls_addrs {
        rho.insert(k.clone(), v);
    }
    for (i, blk) in lib.blocks.iter().enumerate() {
        let base = pl.code_addrs.get(i).copied().unwrap_or(0);
        for (sym, off) in &blk.symbols {
            rho.insert(sym.clone(), base.wrapping_add(*off));
        }
    }
    rho
}

fn patch_pdata_bytes(d: &PData, addr: u64, full_rho: &BTreeMap<String, u64>) -> Vec<u8> {
    let mut bytes = d.bytes.clone();
    for r in &d.relocs {
        let sym_addr = full_rho.get(&r.sym).copied().unwrap_or(0);
        let t = add_signed(sym_addr, r.addend);
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

/// Evaluate `untrusted_placed` (Rust mirror) on `(lib, pl)`.
pub fn eval_untrusted_placed(lib: &MultiPlacedLib, pl: &PlacedEvalPlacement) -> PlacedEvalResult {
    let full_rho = build_full_rho(lib, pl);
    let check = || -> Result<()> {
        for (i, blk) in lib.blocks.iter().enumerate() {
            let bpl = PPlacement {
                undef_weak: pl.undef_weak.clone(),
                base: pl.code_addrs.get(i).copied().unwrap_or(0),
                rho: full_rho.clone(),
                relax: pl.relax.get(i).cloned().unwrap_or_default(),
                b2b: pl.b2b.get(i).cloned().unwrap_or_default(),
            };
            blk.check_placeable(&bpl)?;
        }
        // Check pairwise code block disjointness.
        for i in 0..lib.blocks.len() {
            for j in (i + 1)..lib.blocks.len() {
                let b1 = pl.code_addrs[i] as u128;
                let n1 = lib.blocks[i].code.len() as u128;
                let b2 = pl.code_addrs[j] as u128;
                let n2 = lib.blocks[j].code.len() as u128;
                ensure!(b1 + n1 <= b2 || b2 + n2 <= b1, "code blocks {i} and {j} overlap");
            }
        }
        // Check data blocks.
        for (i, d) in lib.data.iter().enumerate() {
            let a = full_rho.get(&d.sym).copied().unwrap_or(0);
            let sz = d.bytes.len() as u128 + d.zero_tail as u128;
            ensure!(lib.lookup_block_sym(&d.sym).is_none(), "data {} is block sym", d.sym);
            ensure!(d.align > 0 && a % d.align == 0, "data {} misaligned", d.sym);
            ensure!(a as u128 + sz <= 1u128 << 64, "data {} wraps", d.sym);
            for r in &d.relocs {
                let w = data_reloc_width(r.kind);
                ensure!(w > 0 && r.off + w <= d.bytes.len() as u64, "data reloc bounds");
                let t = add_signed(full_rho.get(&r.sym).copied().unwrap_or(0), r.addend);
                match r.kind {
                    RelocKind::Abs32 => {
                        let ti = t as i64 as i128;
                        ensure!(-(1i128 << 31) <= ti && ti < (1i128 << 32), "abs32 range");
                    }
                    RelocKind::Prel32 => {
                        let diff = t.wrapping_sub(a.wrapping_add(r.off)) as i64 as i128;
                        ensure!(-(1i128 << 31) <= diff && diff < (1i128 << 31), "prel32 range");
                    }
                    RelocKind::Abs64 => {}
                    _ => bail!("invalid data reloc"),
                }
            }
            for (bi, blk) in lib.blocks.iter().enumerate() {
                let b = pl.code_addrs[bi] as u128;
                let bn = blk.code.len() as u128;
                ensure!(
                    b + bn <= a as u128 || a as u128 + sz <= b,
                    "data {} overlaps block {bi}",
                    d.sym
                );
            }
            for d2 in lib.data.iter().skip(i + 1) {
                let a2 = full_rho.get(&d2.sym).copied().unwrap_or(0) as u128;
                let sz2 = d2.bytes.len() as u128 + d2.zero_tail as u128;
                ensure!(
                    a as u128 + sz <= a2 || a2 + sz2 <= a as u128,
                    "data {} and {} overlap",
                    d.sym,
                    d2.sym
                );
            }
        }
        // Check TLS blocks.
        for (i, d) in lib.tls.iter().enumerate() {
            let a = full_rho.get(&d.sym).copied().unwrap_or(0);
            let sz = d.bytes.len() as u128 + d.zero_tail as u128;
            ensure!(lib.lookup_block_sym(&d.sym).is_none(), "tls {} is block sym", d.sym);
            ensure!(d.align > 0 && a % d.align == 0, "tls {} misaligned", d.sym);
            ensure!(a >= 16, "tls {} overlaps 16-byte TCB header", d.sym);
            ensure!(a as u128 + sz <= 1u128 << 64, "tls {} wraps", d.sym);
            for d2 in lib.tls.iter().skip(i + 1) {
                let a2 = full_rho.get(&d2.sym).copied().unwrap_or(0) as u128;
                let sz2 = d2.bytes.len() as u128 + d2.zero_tail as u128;
                ensure!(
                    a as u128 + sz <= a2 || a2 + sz2 <= a as u128,
                    "tls {} and {} overlap",
                    d.sym,
                    d2.sym
                );
            }
        }
        Ok(())
    };

    if let Err(e) = check() {
        return PlacedEvalResult {
            valid: false,
            error: Some(e.to_string()),
            code_blocks: vec![],
            data_blocks: BTreeMap::new(),
            tls_blocks: BTreeMap::new(),
        };
    }

    let code_blocks = lib
        .blocks
        .iter()
        .enumerate()
        .map(|(i, blk)| {
            let bpl = PPlacement {
                undef_weak: pl.undef_weak.clone(),
                base: pl.code_addrs[i],
                rho: full_rho.clone(),
                relax: pl.relax.get(i).cloned().unwrap_or_default(),
                b2b: pl.b2b.get(i).cloned().unwrap_or_default(),
            };
            blk.patched(&bpl)
        })
        .collect();
    let data_blocks = lib
        .data
        .iter()
        .map(|d| {
            let addr = full_rho.get(&d.sym).copied().unwrap_or(0);
            (d.sym.clone(), patch_pdata_bytes(d, addr, &full_rho))
        })
        .collect();
    let tls_blocks = lib
        .tls
        .iter()
        .map(|d| {
            let addr = full_rho.get(&d.sym).copied().unwrap_or(0);
            (d.sym.clone(), patch_pdata_bytes(d, addr, &full_rho))
        })
        .collect();
    PlacedEvalResult {
        valid: true,
        error: None,
        code_blocks,
        data_blocks,
        tls_blocks,
    }
}

fn align_up(v: u64, align: u64) -> u64 {
    let a = align.max(1);
    (v + a - 1) / a * a
}

/// Summary of a multi-variant differential run on a `placed_only` `multi` repository config.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlacedRepoReport {
    pub blocks: usize,
    pub code_bytes: usize,
    pub data_syms: usize,
    pub tls_syms: usize,
    pub got_slots: usize,
    pub variants: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum GotSymKey {
    Local(usize, usize),
    Global(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct GotSlotPin {
    label: String,
    slot_vma: u64,
    target_addr: u64,
}

#[derive(Clone, Debug, Default)]
struct SynthesizedLayout {
    pl: PlacedEvalPlacement,
    /// Linker-script `sym = addr;` definitions for external symbols.
    lds_extern_addrs: BTreeMap<String, u64>,
    text_secs: Vec<((usize, usize), u64)>,
    data_secs: Vec<((usize, usize), u64)>,
    tls_secs: Vec<((usize, usize), u64)>,
    /// VMA of `.got` when any kept `.text` relocation uses GOT addressing.
    got_vma: Option<u64>,
    /// Every 8-byte `.got` slot (both internal and external) and its expected resolved target VMA.
    got_pins: Vec<GotSlotPin>,
}

/// Prepare a relocatable ELF64 copy for pinned `ld.lld` linking:
/// 1. Clear `SHF_MERGE | SHF_STRINGS` on all section headers so `ld.lld` preserves input-section
///    offsets verbatim when pinned by a linker script.
/// 2. Rename each pinned `(obj, sec)` (at `sec.elf_index`) to a unique `.shstrtab` entry so
///    duplicate input section names (e.g. multiple `.rodata.str1.1` sections after `ld -r --unique`)
///    pin 1-to-1 to their distinct VMAs.
/// 3. Rename unpinned `SHF_ALLOC` sections (other than `.eh_frame`) to `.__unreferenced_alloc` so
///    `/DISCARD/` drops unreachable sections pruned by `build_multi_placed_lib` along with their
///    `.rela` tables.
fn prepare_elf64_for_lld(
    elf_bytes: &mut Vec<u8>,
    obj: &ObjObject,
    pinned_renames: &BTreeMap<usize, String>,
) {
    if elf_bytes.len() < 64 || &elf_bytes[0..4] != b"\x7fELF" || elf_bytes[4] != 2 {
        return;
    }
    let shoff = u64::from_le_bytes(elf_bytes[40..48].try_into().unwrap()) as usize;
    let shentsize = u16::from_le_bytes(elf_bytes[58..60].try_into().unwrap()) as usize;
    let mut shnum = u16::from_le_bytes(elf_bytes[60..62].try_into().unwrap()) as usize;
    let mut shstrndx = u16::from_le_bytes(elf_bytes[62..64].try_into().unwrap()) as usize;
    if shentsize < 64 || shoff == 0 || shoff + shentsize > elf_bytes.len() {
        return;
    }
    if shnum == 0 {
        shnum = u64::from_le_bytes(elf_bytes[shoff + 32..shoff + 40].try_into().unwrap()) as usize;
    }
    if shstrndx == (object::elf::SHN_XINDEX as usize) {
        shstrndx =
            u32::from_le_bytes(elf_bytes[shoff + 40..shoff + 44].try_into().unwrap()) as usize;
    }
    let mask = !((object::elf::SHF_MERGE | object::elf::SHF_STRINGS) as u64);
    for i in 0..shnum {
        let off = shoff + i * shentsize;
        if off + 64 <= elf_bytes.len() {
            let flags = u64::from_le_bytes(elf_bytes[off + 8..off + 16].try_into().unwrap());
            elf_bytes[off + 8..off + 16].copy_from_slice(&(flags & mask).to_le_bytes());
        }
    }

    neutralize_discarded_relocs(elf_bytes, obj, pinned_renames, shoff, shentsize, shnum);

    if shstrndx >= shnum {
        return;
    }
    let shstr_hdr = shoff + shstrndx * shentsize;
    if shstr_hdr + 64 > elf_bytes.len() {
        return;
    }
    let orig_shstr_off = u64::from_le_bytes(
        elf_bytes[shstr_hdr + 24..shstr_hdr + 32]
            .try_into()
            .unwrap(),
    ) as usize;
    let orig_shstr_size = u64::from_le_bytes(
        elf_bytes[shstr_hdr + 32..shstr_hdr + 40]
            .try_into()
            .unwrap(),
    ) as usize;
    if orig_shstr_off.saturating_add(orig_shstr_size) > elf_bytes.len() {
        return;
    }

    let mut new_shstr = elf_bytes[orig_shstr_off..orig_shstr_off + orig_shstr_size].to_vec();
    let mut unref_name_off: Option<u32> = None;
    let mut changed_names = false;

    for sec in &obj.sections {
        let elf_idx = sec.elf_index;
        if elf_idx == 0 || elf_idx >= shnum {
            continue;
        }
        let hdr_off = shoff + elf_idx * shentsize;
        if hdr_off + 64 > elf_bytes.len() {
            continue;
        }
        if let Some(new_name) = pinned_renames.get(&elf_idx) {
            let name_off = new_shstr.len() as u32;
            new_shstr.extend_from_slice(new_name.as_bytes());
            new_shstr.push(0);
            elf_bytes[hdr_off..hdr_off + 4].copy_from_slice(&name_off.to_le_bytes());
            changed_names = true;
        } else if (sec.sh_flags & (object::elf::SHF_ALLOC as u64)) != 0 && sec.name != ".eh_frame" {
            let name_off = *unref_name_off.get_or_insert_with(|| {
                let off = new_shstr.len() as u32;
                new_shstr.extend_from_slice(b".__unreferenced_alloc\0");
                off
            });
            elf_bytes[hdr_off..hdr_off + 4].copy_from_slice(&name_off.to_le_bytes());
            changed_names = true;
        }
    }

    if changed_names {
        let new_shstr_off = elf_bytes.len() as u64;
        let new_shstr_len = new_shstr.len() as u64;
        elf_bytes.extend_from_slice(&new_shstr);
        elf_bytes[shstr_hdr + 24..shstr_hdr + 32].copy_from_slice(&new_shstr_off.to_le_bytes());
        elf_bytes[shstr_hdr + 32..shstr_hdr + 40].copy_from_slice(&new_shstr_len.to_le_bytes());
    }
}

/// Rewrite to `R_AARCH64_NONE` every relocation of a pinned non-code section whose symbol is
/// defined in a section that `prepare_elf64_for_lld` discards (an unpinned `SHF_ALLOC` section
/// other than `.eh_frame`), which `ld.lld` would otherwise reject ("relocation refers to a
/// discarded section"). Such relocations lie in data pieces pruned by `build_multi_placed_lib`
/// that share an input section with kept pieces; one inside a kept piece would leave its bytes
/// unpatched and fail the byte comparison against the model.
fn neutralize_discarded_relocs(
    elf_bytes: &mut [u8],
    obj: &ObjObject,
    pinned_renames: &BTreeMap<usize, String>,
    shoff: usize,
    shentsize: usize,
    shnum: usize,
) {
    let alloc = object::elf::SHF_ALLOC as u64;
    let discarded: BTreeSet<usize> = obj
        .sections
        .iter()
        .filter(|s| {
            s.elf_index != 0
                && (s.sh_flags & alloc) != 0
                && s.name != ".eh_frame"
                && !pinned_renames.contains_key(&s.elf_index)
        })
        .map(|s| s.elf_index)
        .collect();
    if discarded.is_empty() {
        return;
    }
    let len = elf_bytes.len();
    let rd32 = |b: &[u8], o: usize| u32::from_le_bytes(b[o..o + 4].try_into().unwrap());
    let rd64 = |b: &[u8], o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    let hdr = |i: usize| Some(shoff + i * shentsize).filter(|h| h + 64 <= len);
    let mut to_clear = Vec::new();
    for i in 0..shnum {
        let Some(h) = hdr(i) else { continue };
        if rd32(elf_bytes, h + 4) != object::elf::SHT_RELA {
            continue;
        }
        let target = rd32(elf_bytes, h + 44) as usize;
        let Some(th) = hdr(target) else { continue };
        if !pinned_renames.contains_key(&target)
            || rd64(elf_bytes, th + 8) & (object::elf::SHF_EXECINSTR as u64) != 0
        {
            continue;
        }
        let Some(sh) = hdr(rd32(elf_bytes, h + 40) as usize) else { continue };
        let sym_off = rd64(elf_bytes, sh + 24) as usize;
        let (off, size) = (rd64(elf_bytes, h + 24) as usize, rd64(elf_bytes, h + 32) as usize);
        for eo in (off..off.saturating_add(size)).step_by(24) {
            if eo + 24 > len {
                break;
            }
            let si = (rd64(elf_bytes, eo + 8) >> 32) as usize;
            let so = sym_off + si * 24;
            if si == 0 || so + 24 > len {
                continue;
            }
            let shndx = u16::from_le_bytes(elf_bytes[so + 6..so + 8].try_into().unwrap());
            if discarded.contains(&(shndx as usize)) {
                to_clear.push(eo + 8);
            }
        }
    }
    for o in to_clear {
        elf_bytes[o..o + 8].copy_from_slice(&0u64.to_le_bytes());
    }
}

/// Stock `ld.lld` (`AArch64::tryRelaxAdrpAdd`) only relaxes `ADRP + ADD -> NOP + ADR` when both
/// raw input ELF relocations have `r_addend == 0`.
fn raw_reloc_addend_zero(objs: &[ObjObject], obj_idx: usize, sec_idx: usize, raw_off: u64) -> bool {
    objs[obj_idx].sections[sec_idx]
        .relocs
        .iter()
        .find(|r| r.offset == raw_off)
        .is_some_and(|r| r.addend == 0)
}

/// Synthesize a concrete `PlacedEvalPlacement` and per-input-section VMA map for `variant`.
fn synthesize_layout(
    objs: &[ObjObject],
    lib: &MultiPlacedLib,
    variant: LayoutVariant,
) -> Result<SynthesizedLayout> {
    let (code_start, data_start, code_gap, page_stress) = match variant {
        LayoutVariant::NearRelax | LayoutVariant::NearNoRelax => {
            (0x0040_0000u64, 0x0044_0000u64, 0x100u64, false)
        }
        LayoutVariant::Medium => (0x0040_0000u64, 0x0240_0000u64, 0x1400u64, false),
        LayoutVariant::HighCanonicalAslr => (
            0x0000_aaaa_0000_0000u64,
            0x0000_aaaa_0400_0000u64,
            0x2000u64,
            false,
        ),
        LayoutVariant::PageBoundaryStress => (0x0080_0ff8u64, 0x0088_0ff0u64, 0x1000u64, true),
    };

    // Group code blocks by their underlying input section `(obj, sec)`.
    let mut text_sec_vmas: BTreeMap<(usize, usize), u64> = BTreeMap::new();
    let mut text_sec_order: Vec<((usize, usize), u64)> = Vec::new();
    let mut cur_code = code_start;
    let mut sec_base_ts_off: BTreeMap<(usize, usize), u64> = BTreeMap::new();
    let mut code_addrs = Vec::with_capacity(lib.blocks.len());

    let single_block = lib.blocks.len() == 1 && lib.text_secs.len() != lib.blocks.len();
    if single_block {
        let blk_align = lib.blocks[0].align.max(4);
        let mut base_vma = align_up(code_start, blk_align);
        if page_stress && blk_align <= 8 && (base_vma & 0xfff) < 0xff0 {
            let page_end = (base_vma & !0xfff) + 0xff8;
            if page_end >= base_vma && page_end % blk_align == 0 {
                base_vma = page_end;
            }
        }
        code_addrs.push(base_vma);
        for ts in &lib.text_secs {
            let key = (ts.obj, ts.sec);
            let vma = base_vma + ts.off;
            text_sec_vmas.insert(key, vma);
            text_sec_order.push((key, vma));
            sec_base_ts_off.insert(key, ts.off);
        }
        cur_code = base_vma + (lib.blocks[0].code.len() as u64) + code_gap;
    } else {
        for (i, ts) in lib.text_secs.iter().enumerate() {
            let key = (ts.obj, ts.sec);
            if let Some(&sec_vma) = text_sec_vmas.get(&key) {
                let base_ts_off = sec_base_ts_off[&key];
                code_addrs.push(sec_vma + (ts.off - base_ts_off));
            } else {
                let sec_align = objs[ts.obj].sections[ts.sec]
                    .align
                    .max(lib.blocks[i].align)
                    .max(4);
                let mut vma = align_up(cur_code, sec_align);
                if page_stress && sec_align <= 8 && (vma & 0xfff) < 0xff0 {
                    let page_end = (vma & !0xfff) + 0xff8;
                    if page_end >= vma && page_end % sec_align == 0 {
                        vma = page_end;
                    }
                }
                text_sec_vmas.insert(key, vma);
                text_sec_order.push((key, vma));
                sec_base_ts_off.insert(key, ts.off);
                code_addrs.push(vma);
                let sec_size = objs[ts.obj].sections[ts.sec].size.max(ts.size);
                cur_code = vma + sec_size + code_gap;
            }
        }
    }

    // Group non-TLS data objects by their input section `(obj, sec)`.
    let actual_data_start = if cur_code <= data_start {
        data_start
    } else {
        (align_up(cur_code + 0x1000, 0x1000) & !0xfff) + (data_start & 0xfff)
    };
    let mut data_sec_vmas: BTreeMap<(usize, usize), u64> = BTreeMap::new();
    let mut data_sec_order: Vec<((usize, usize), u64)> = Vec::new();
    let mut cur_data = actual_data_start;
    let mut data_addrs = BTreeMap::new();

    for d in &lib.data {
        let key = (d.origin.0, d.origin.1);
        let sec_vma = if let Some(&v) = data_sec_vmas.get(&key) {
            v
        } else {
            let sec = &objs[key.0].sections[key.1];
            let sec_align = sec.align.max(d.align).max(1);
            let mut vma = align_up(cur_data, sec_align);
            if page_stress && sec_align <= 8 && (vma & 0xfff) < 0xff0 {
                let cand = (vma & !0xfff) + 0xff8;
                if cand >= vma && cand % sec_align == 0 {
                    vma = cand;
                }
            }
            data_sec_vmas.insert(key, vma);
            data_sec_order.push((key, vma));
            cur_data = vma + sec.size.max(d.bytes.len() as u64 + d.zero_tail) + 0x80;
            vma
        };
        data_addrs.insert(d.sym.clone(), sec_vma + d.origin.2);
    }

    // Record GOT slot allocation order across kept `.text` sections in exact linker-script order.
    let mut got_order: Vec<GotSymKey> = Vec::new();
    let mut got_slot_index: BTreeMap<GotSymKey, usize> = BTreeMap::new();
    for &((oi, si), _) in &text_sec_order {
        for r in &objs[oi].sections[si].relocs {
            let sym = &objs[oi].symbols[r.sym];
            let is_got_slot_reloc = matches!(
                r.rtype,
                crate::trusted_common::RelocType::AdrGotPage
                    | crate::trusted_common::RelocType::Ld64GotLo12Nc
            ) || (matches!(
                r.rtype,
                crate::trusted_common::RelocType::TlsieAdrGottprelPage21
                    | crate::trusted_common::RelocType::TlsieLd64GottprelLo12Nc
            ) && sym.sec == SymSection::Undef);
            if is_got_slot_reloc {
                ensure!(
                    r.addend == 0,
                    "unexpected non-zero addend {} on GOT relocation",
                    r.addend
                );
                let key = if sym.bind == crate::trusted_common::SymBind::Local {
                    GotSymKey::Local(oi, r.sym)
                } else {
                    GotSymKey::Global(sym.raw_name.clone())
                };
                got_slot_index.entry(key.clone()).or_insert_with(|| {
                    let idx = got_order.len();
                    got_order.push(key);
                    idx
                });
            }
        }
    }
    let got_vma = if got_order.is_empty() {
        None
    } else {
        let vma = align_up(cur_data, 8);
        cur_data = vma + (got_order.len() as u64) * 8 + 0x80;
        Some(vma)
    };

    // Place TLS sections (`.tdata` PROGBITS first, then `.tbss` NOBITS) contiguously in `PT_TLS`.
    let mut tls_sec_vmas: BTreeMap<(usize, usize), u64> = BTreeMap::new();
    let mut tls_sec_order: Vec<((usize, usize), u64)> = Vec::new();
    let mut tls_addrs = BTreeMap::new();
    let mut cur_tls_end = cur_data;
    if !lib.tls.is_empty() {
        let max_tls_align = lib
            .tls
            .iter()
            .map(|d| objs[d.origin.0].sections[d.origin.1].align.max(d.align))
            .max()
            .unwrap_or(1)
            .max(1);
        let tls_vma_start = align_up(cur_data + 0x10000, max_tls_align.max(0x1000));
        let mut cur_tls = tls_vma_start;
        // Order: PROGBITS (`.tdata`) before NOBITS (`.tbss`), matching `ld.lld` `PT_TLS` layout.
        let mut ordered_tls: Vec<&PData> = lib.tls.iter().collect();
        ordered_tls.sort_by_key(|d| {
            let is_nobits = d.bytes.is_empty() && d.zero_tail > 0;
            (is_nobits, d.origin.0, d.origin.1, d.origin.2)
        });
        for d in ordered_tls {
            let key = (d.origin.0, d.origin.1);
            let sec_vma = if let Some(&v) = tls_sec_vmas.get(&key) {
                v
            } else {
                let sec = &objs[key.0].sections[key.1];
                let sec_align = sec.align.max(d.align).max(1);
                let vma = align_up(cur_tls, sec_align);
                tls_sec_vmas.insert(key, vma);
                tls_sec_order.push((key, vma));
                cur_tls = vma + sec.size.max(d.bytes.len() as u64 + d.zero_tail);
                vma
            };
            let offset_in_tls = (sec_vma + d.origin.2) - tls_vma_start;
            let tprel = tls_base_offset(max_tls_align) + offset_in_tls;
            tls_addrs.insert(d.sym.clone(), tprel);
        }
        cur_tls_end = cur_tls;
    }

    // Collect any external symbols (undefined symbols referenced by code or data relocations).
    let mut known_syms: BTreeSet<String> = BTreeSet::new();
    for b in &lib.blocks {
        for (s, _) in &b.symbols {
            known_syms.insert(s.clone());
        }
    }
    for d in &lib.data {
        known_syms.insert(d.sym.clone());
    }
    for d in &lib.tls {
        known_syms.insert(d.sym.clone());
    }
    let mut lds_extern_addrs = BTreeMap::new();
    let mut next_ext = if cur_code + 0x8000 <= actual_data_start {
        align_up(cur_code + 0x4000, 16)
    } else {
        align_up(cur_tls_end + 0x4000, 16)
    };
    for b in &lib.blocks {
        for r in &b.relocs {
            if !known_syms.contains(&r.sym) && !lds_extern_addrs.contains_key(&r.sym) {
                lds_extern_addrs.insert(r.sym.clone(), next_ext);
                next_ext += 0x100;
            }
        }
    }
    for d in &lib.data {
        for r in &d.relocs {
            if !known_syms.contains(&r.sym) && !lds_extern_addrs.contains_key(&r.sym) {
                lds_extern_addrs.insert(r.sym.clone(), next_ext);
                next_ext += 0x100;
            }
        }
    }

    let mut extern_addrs = lds_extern_addrs.clone();

    // For external symbols referenced via GOT relocations (`AdrGotPage` / `Ld64GotLo12Nc`),
    // linker-script absolute definitions (`"sym" = addr;`) are never GOT-relaxed by `ld.lld`;
    // `ld.lld` emits an 8-byte `.got` slot holding `addr` and patches the instructions against
    // the `.got` slot VMA. Map `pl.extern_addrs[sym]` to that `.got` slot VMA.
    let mut extern_got_syms: BTreeSet<String> = BTreeSet::new();
    let mut extern_non_got_syms: BTreeSet<String> = BTreeSet::new();
    for b in &lib.blocks {
        for r in &b.relocs {
            if !known_syms.contains(&r.sym) {
                if matches!(
                    r.kind,
                    RelocKind::AdrGotPage
                        | RelocKind::Ld64GotLo12Nc
                        | RelocKind::TlsieAdrGottprelPage21
                        | RelocKind::TlsieLd64GottprelLo12Nc
                ) {
                    extern_got_syms.insert(r.sym.clone());
                } else {
                    extern_non_got_syms.insert(r.sym.clone());
                }
            }
        }
    }
    for d in &lib.data {
        for r in &d.relocs {
            if !known_syms.contains(&r.sym) {
                extern_non_got_syms.insert(r.sym.clone());
            }
        }
    }

    // An undefined weak reference (`weakRefs`) used through the GOT and by direct `CALL26` /
    // `JUMP26` branches only is left undefined for `ld.lld`: its `.got` slot holds 0 and each
    // branch becomes `b/bl .+4` (`MultiPlacement.undefWeak`).
    let weak_refs: BTreeSet<&String> = lib.blocks.iter().flat_map(|b| &b.weak_refs).collect();
    let mut extern_other_syms: BTreeSet<String> = BTreeSet::new();
    for b in &lib.blocks {
        for r in &b.relocs {
            if !matches!(
                r.kind,
                RelocKind::AdrGotPage
                    | RelocKind::Ld64GotLo12Nc
                    | RelocKind::Call26
                    | RelocKind::Jump26
            ) {
                extern_other_syms.insert(r.sym.clone());
            }
        }
    }
    for d in &lib.data {
        for r in &d.relocs {
            extern_other_syms.insert(r.sym.clone());
        }
    }
    let undef_weak: BTreeSet<String> = extern_got_syms
        .iter()
        .filter(|s| {
            weak_refs.contains(s)
                && extern_non_got_syms.contains(*s)
                && !extern_other_syms.contains(*s)
        })
        .cloned()
        .collect();
    for sym in &undef_weak {
        lds_extern_addrs.remove(sym);
    }

    for sym in &extern_got_syms {
        ensure!(
            undef_weak.contains(sym) || !extern_non_got_syms.contains(sym),
            "external symbol '{sym}' is referenced by both GOT and direct relocations"
        );
        let base_got = got_vma.context("missing .got VMA for external GOT symbol")?;
        let &slot_idx = got_slot_index
            .get(&GotSymKey::Global(sym.clone()))
            .with_context(|| format!("missing GOT slot index for external symbol '{sym}'"))?;
        let slot_vma = base_got + (slot_idx as u64) * 8;
        extern_addrs.insert(sym.clone(), slot_vma);
    }

    let mut pl = PlacedEvalPlacement {
        code_addrs,
        data_addrs,
        tls_addrs,
        extern_addrs,
        relax: vec![BTreeSet::new(); lib.blocks.len()],
        b2b: vec![BTreeSet::new(); lib.blocks.len()],
        undef_weak: undef_weak.clone(),
    };

    // Determine which `ADRP + ADD` / `GOT` / `TLSIE` sites are relaxed by `ld.lld`.
    let allow_relax = !matches!(variant, LayoutVariant::NearNoRelax);
    let full_rho = build_full_rho(lib, &pl);
    for (i, blk) in lib.blocks.iter().enumerate() {
        let bpl = PPlacement {
            undef_weak: Default::default(),
            base: pl.code_addrs[i],
            rho: full_rho.clone(),
            relax: BTreeSet::new(),
            b2b: BTreeSet::new(),
        };
        for r in &blk.relocs {
            let (ts_obj, ts_sec, sec_rel_off) = if single_block {
                let ts = lib
                    .text_secs
                    .iter()
                    .find(|ts| ts.off <= r.off && r.off < ts.off + ts.size)
                    .context("missing text_sec covering single-block relocation")?;
                (ts.obj, ts.sec, r.off - ts.off)
            } else {
                let ts = &lib.text_secs[i];
                let sec_rel_base = ts.off - sec_base_ts_off[&(ts.obj, ts.sec)];
                (ts.obj, ts.sec, sec_rel_base + r.off)
            };
            // Static ET_EXEC `ld.lld` relaxes defined-TLS IE -> LE (`MOVZ + MOVK`) when in 32-bit TP range
            // (external linker-script symbols stay unrelaxed GOT loads).
            if blk.tlsie_relaxable_at(r.off)
                && !extern_got_syms.contains(&r.sym)
                && blk.target(&bpl, r) < (1u64 << 32)
            {
                pl.relax[i].insert(r.off);
            }
            if allow_relax {
                if blk.relaxable_at(r.off)
                    && raw_reloc_addend_zero(objs, ts_obj, ts_sec, sec_rel_off)
                    && raw_reloc_addend_zero(objs, ts_obj, ts_sec, sec_rel_off + 4)
                    && let Some(r2) = blk.reloc_at(r.off + 4)
                {
                    let place4 = bpl.base.wrapping_add(r.off + 4);
                    let target = blk.target(&bpl, r2);
                    if code_reloc_in_range(RelocKind::AdrPrelLo21, place4, target) {
                        pl.relax[i].insert(r.off);
                    }
                } else if blk.got_pair_at(r.off)
                    && !extern_got_syms.contains(&r.sym)
                    && let Some(r2) = blk.reloc_at(r.off + 4)
                {
                    let place4 = bpl.base.wrapping_add(r.off + 4);
                    let target = blk.target(&bpl, r2);
                    if code_reloc_in_range(RelocKind::AdrPrelLo21, place4, target) {
                        pl.relax[i].insert(r.off);
                    } else {
                        pl.relax[i].insert(r.off + 4);
                    }
                }
            }
        }
    }

    // Compute the expected 8-byte resolved target VMA for EVERY `.got` slot (internal and external).
    let mut got_pins = Vec::with_capacity(got_order.len());
    if let Some(base_got) = got_vma {
        for (slot_idx, key) in got_order.iter().enumerate() {
            let slot_vma = base_got + (slot_idx as u64) * 8;
            let (label, target_addr) = match key {
                GotSymKey::Local(oi, sym_idx) => {
                    let sym = &objs[*oi].symbols[*sym_idx];
                    let crate::trusted_common::SymSection::Sec(sec_idx) = sym.sec else {
                        bail!("unexpected non-section local GOT symbol '{}'", sym.name);
                    };
                    let sec_vma = text_sec_vmas
                        .get(&(*oi, sec_idx))
                        .or_else(|| data_sec_vmas.get(&(*oi, sec_idx)))
                        .copied()
                        .with_context(|| {
                            format!(
                                "missing pinned VMA for local GOT symbol '{}' in ({oi}, {sec_idx})",
                                sym.name
                            )
                        })?;
                    (format!("obj_{oi}:{}", sym.name), sec_vma + sym.value)
                }
                GotSymKey::Global(raw_name) => {
                    let addr = if undef_weak.contains(raw_name) {
                        0
                    } else if let Some(&ext_addr) = lds_extern_addrs.get(raw_name) {
                        ext_addr
                    } else if let Some(&rho_addr) = full_rho.get(raw_name) {
                        rho_addr
                    } else {
                        let mut found = None;
                        for (oi, obj) in objs.iter().enumerate() {
                            for sym in &obj.symbols {
                                if sym.bind != crate::trusted_common::SymBind::Local
                                    && sym.raw_name == *raw_name
                                    && let crate::trusted_common::SymSection::Sec(sec_idx) = sym.sec
                                    && let Some(&sec_vma) = text_sec_vmas
                                        .get(&(oi, sec_idx))
                                        .or_else(|| data_sec_vmas.get(&(oi, sec_idx)))
                                {
                                    found = Some(sec_vma + sym.value);
                                    break;
                                }
                            }
                            if found.is_some() {
                                break;
                            }
                        }
                        found.with_context(|| {
                            format!("missing resolved VMA for global GOT symbol '{raw_name}'")
                        })?
                    };
                    (raw_name.clone(), addr)
                }
            };
            got_pins.push(GotSlotPin {
                label,
                slot_vma,
                target_addr,
            });
        }
    }

    Ok(SynthesizedLayout {
        pl,
        lds_extern_addrs,
        text_secs: text_sec_order,
        data_secs: data_sec_order,
        tls_secs: tls_sec_order,
        got_vma,
        got_pins,
    })
}

fn parse_elf_object(name: &str, bytes: &[u8]) -> Result<ObjObject> {
    parse_object(name, bytes.to_vec())
}

/// Link `raw_objs` with stock `ld.lld` using a generated linker script that pins every input
/// section to its exact address in `synthesize_layout`, and assert 100% byte-for-byte equality
/// across:
/// 1. Stock `ld.lld` output bytes,
/// 2. `untrusted_placed` Rust mirror bytes, and
/// 3. `lake exe placed_eval` Lean TCB bytes.
pub fn compare_against_lld_and_placed_eval(
    lld: &Tool,
    name: &str,
    raw_objs: &[Vec<u8>],
    exports: &[String],
    variant: LayoutVariant,
) -> Result<()> {
    let mut objs = Vec::with_capacity(raw_objs.len());
    for (idx, bytes) in raw_objs.iter().enumerate() {
        objs.push(parse_elf_object(&format!("obj_{idx}.o"), bytes)?);
    }
    let lib = build_multi_placed_lib(name, &objs, exports)?;
    compare_built_lib_against_lld_and_placed_eval(lld, name, raw_objs, &objs, &lib, variant)
        .map(|_| ())
}

fn compare_built_lib_against_lld_and_placed_eval(
    lld: &Tool,
    name: &str,
    raw_objs: &[Vec<u8>],
    objs: &[ObjObject],
    lib: &MultiPlacedLib,
    variant: LayoutVariant,
) -> Result<usize> {
    let layout = synthesize_layout(objs, lib, variant)?;
    let pl = &layout.pl;
    let text_secs = &layout.text_secs;
    let data_secs = &layout.data_secs;
    let tls_secs = &layout.tls_secs;

    // 1. Evaluate `untrusted_placed` (Rust mirror) and `placed_eval` (Lean TCB).
    let rust_res = eval_untrusted_placed(lib, pl);
    ensure!(
        rust_res.valid,
        "[{name} @ {variant:?}] untrusted_placed rejected valid placement: {:?}",
        rust_res.error
    );
    // Single-block libraries over 64 KiB skip the quadratic list scan in `placed_eval` while
    // still comparing every byte against `ld.lld`.
    let ref_res = if lib.blocks.iter().all(|b| b.code.len() <= 65_536) {
        let lean_res = run_placed_eval(lib, pl)?;
        ensure!(
            lean_res.valid,
            "[{name} @ {variant:?}] placed_eval rejected valid placement: {:?}",
            lean_res.error
        );
        ensure!(
            rust_res == lean_res,
            "[{name} @ {variant:?}] untrusted_placed != placed_eval:\nrust: {rust_res:#?}\nlean: {lean_res:#?}"
        );
        lean_res
    } else {
        rust_res
    };

    // Build 1-to-1 unique section renames per object so duplicate input section names (e.g.,
    // multiple `.rodata.str1.1` sections after `ld -r --unique`) pin unambiguously and
    // unreachable `SHF_ALLOC` sections can be discarded cleanly.
    let mut pinned_renames_per_obj: Vec<BTreeMap<usize, String>> =
        vec![BTreeMap::new(); objs.len()];
    let mut expected_alloc_secs: BTreeSet<String> = BTreeSet::new();

    let single_block = lib.blocks.len() == 1 && lib.text_secs.len() != lib.blocks.len();
    let mut text_pin_names = Vec::with_capacity(text_secs.len());
    for (k, &((oi, si), _)) in text_secs.iter().enumerate() {
        let pin = format!(".__pinned_text_{k}");
        pinned_renames_per_obj[oi].insert(objs[oi].sections[si].elf_index, pin.clone());
        text_pin_names.push(pin);
        if !single_block && objs[oi].sections[si].size > 0 {
            expected_alloc_secs.insert(format!(".text.pinned_{k}"));
        }
    }
    if single_block && !lib.blocks[0].code.is_empty() {
        expected_alloc_secs.insert(".text.pinned_0".to_string());
    }
    let mut data_pin_names = Vec::with_capacity(data_secs.len());
    for (k, &((oi, si), _)) in data_secs.iter().enumerate() {
        let pin = format!(".__pinned_data_{k}");
        pinned_renames_per_obj[oi].insert(objs[oi].sections[si].elf_index, pin.clone());
        data_pin_names.push(pin);
        if objs[oi].sections[si].size > 0 {
            expected_alloc_secs.insert(format!(".data.pinned_{k}"));
        }
    }
    let mut tls_pin_names: BTreeMap<(usize, usize), String> = BTreeMap::new();
    for (k, &((oi, si), _)) in tls_secs.iter().enumerate() {
        let pin = format!(".__pinned_tls_{k}");
        pinned_renames_per_obj[oi].insert(objs[oi].sections[si].elf_index, pin.clone());
        tls_pin_names.insert((oi, si), pin);
    }

    // Guard: no section emitted by `placed_eval` may ever be unpinned / discarded.
    for ts in &lib.text_secs {
        ensure!(
            pinned_renames_per_obj[ts.obj].contains_key(&objs[ts.obj].sections[ts.sec].elf_index),
            "[{name}] placed text section ({}, {}) missing from pinned set",
            ts.obj,
            ts.sec
        );
    }
    for d in lib.data.iter().chain(lib.tls.iter()) {
        let (oi, si, _) = d.origin;
        ensure!(
            pinned_renames_per_obj[oi].contains_key(&objs[oi].sections[si].elf_index),
            "[{name}] placed data/tls section ({oi}, {si}) missing from pinned set"
        );
    }

    // 2. Write prepared `.o` files and linker script `-T layout.lds`, then invoke stock `ld.lld`.
    let dir = tempfile::tempdir()?;
    let mut obj_paths = Vec::with_capacity(raw_objs.len());
    for (idx, bytes) in raw_objs.iter().enumerate() {
        let mut copy = bytes.clone();
        prepare_elf64_for_lld(&mut copy, &objs[idx], &pinned_renames_per_obj[idx]);
        let p = dir.path().join(format!("obj_{idx}.o"));
        std::fs::write(&p, &copy)?;
        obj_paths.push(p);
    }

    let mut lds = String::new();
    for (ext_sym, &addr) in &layout.lds_extern_addrs {
        lds.push_str(&format!("\"{ext_sym}\" = 0x{addr:x};\n"));
    }
    lds.push_str("SECTIONS {\n");
    if single_block && !text_secs.is_empty() {
        lds.push_str(&format!("  .text.pinned_0 0x{:x} : {{\n", pl.code_addrs[0]));
        for (k, &((oi, _), _)) in text_secs.iter().enumerate() {
            let sec_name = &text_pin_names[k];
            lds.push_str(&format!(
                "    \"{}\"({sec_name})\n",
                obj_paths[oi].display()
            ));
        }
        lds.push_str("  } =0\n");
    } else {
        for (k, &((oi, _), vma)) in text_secs.iter().enumerate() {
            let sec_name = &text_pin_names[k];
            lds.push_str(&format!(
                "  .text.pinned_{k} 0x{vma:x} : SUBALIGN(1) {{ \"{}\"({sec_name}) }}\n",
                obj_paths[oi].display()
            ));
        }
    }
    for (k, &((oi, _), vma)) in data_secs.iter().enumerate() {
        let sec_name = &data_pin_names[k];
        lds.push_str(&format!(
            "  .data.pinned_{k} 0x{vma:x} : SUBALIGN(1) {{ \"{}\"({sec_name}) }}\n",
            obj_paths[oi].display()
        ));
    }
    if let Some(got_vma) = layout.got_vma {
        lds.push_str(&format!(
            "  .got 0x{got_vma:x} : SUBALIGN(8) {{ *(.got) *(.got.plt) }}\n"
        ));
        expected_alloc_secs.insert(".got".to_string());
    }
    if !tls_secs.is_empty() {
        let max_tls_align = lib
            .tls
            .iter()
            .map(|d| objs[d.origin.0].sections[d.origin.1].align.max(d.align))
            .max()
            .unwrap_or(1)
            .max(1);
        let mut tdata_entries = Vec::new();
        let mut tbss_entries = Vec::new();
        for &((oi, si), vma) in tls_secs {
            let sec = &objs[oi].sections[si];
            if sec.sh_type == object::elf::SHT_NOBITS {
                tbss_entries.push(((oi, si), vma));
            } else {
                tdata_entries.push(((oi, si), vma));
            }
        }
        if !tdata_entries.is_empty() {
            let tdata_start = tdata_entries[0].1;
            lds.push_str(&format!(
                "  .tdata 0x{tdata_start:x} : ALIGN({max_tls_align}) {{\n"
            ));
            for ((oi, si), _) in &tdata_entries {
                let sec_name = &tls_pin_names[&(*oi, *si)];
                lds.push_str(&format!("    \"{}\"({sec_name})\n", obj_paths[*oi].display()));
            }
            lds.push_str("  }\n");
            if tdata_entries
                .iter()
                .any(|((oi, si), _)| objs[*oi].sections[*si].size > 0)
            {
                expected_alloc_secs.insert(".tdata".to_string());
            }
        }
        if !tbss_entries.is_empty() {
            let tbss_start = tbss_entries[0].1;
            if tdata_entries.is_empty() {
                lds.push_str(&format!("  . = 0x{tbss_start:x};\n"));
                lds.push_str(&format!("  .tbss : ALIGN({max_tls_align}) {{\n"));
            } else {
                lds.push_str(&format!("  .tbss 0x{tbss_start:x} : {{\n"));
            }
            for ((oi, si), _) in &tbss_entries {
                let sec_name = &tls_pin_names[&(*oi, *si)];
                lds.push_str(&format!("    \"{}\"({sec_name})\n", obj_paths[*oi].display()));
            }
            lds.push_str("  }\n");
            if tbss_entries
                .iter()
                .any(|((oi, si), _)| objs[*oi].sections[*si].size > 0)
            {
                expected_alloc_secs.insert(".tbss".to_string());
            }
        }
    }
    lds.push_str(
        "  /DISCARD/ : { *(.__unreferenced_alloc) *(.eh_frame*) *(.note*) *(.comment*) *(.debug*) *(.llvmbc*) *(.llvmcmd*) *(.group*) *(.ARM.attributes) *(.llvm_addrsig) }\n",
    );
    lds.push_str("}\n");

    let lds_path = dir.path().join("layout.lds");
    std::fs::write(&lds_path, &lds)?;
    let elf_path = dir.path().join("out.elf");

    let mut cmd = lld.cmd();
    cmd.arg("--image-base=0")
        .arg("--no-gc-sections")
        .arg("--no-merge-exidx-entries")
        .arg("-e")
        .arg("0")
        .arg("-T")
        .arg(&lds_path);
    if matches!(variant, LayoutVariant::NearNoRelax) {
        cmd.arg("--no-relax");
    }
    for p in &obj_paths {
        cmd.arg(p);
    }
    cmd.arg("-o").arg(&elf_path);

    let out = cmd.output().context("failed to run ld.lld")?;
    ensure!(
        out.status.success(),
        "[{name} @ {variant:?}] ld.lld failed ({}):\nstderr:\n{}\nlds:\n{lds}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    // 3. Parse linked ELF from `ld.lld`, verify exact `SHF_ALLOC` section-set equality, and
    //    compare every code block, data block, TLS block, and `.got` slot byte-for-byte against
    //    `lean_res` (`placed_eval`) and `rust_res` (`untrusted_placed`)!
    let elf_bytes = std::fs::read(&elf_path)?;
    let elf = object::File::parse(&*elf_bytes)?;

    let mut actual_alloc_secs: BTreeSet<String> = BTreeSet::new();
    for sec in elf.sections() {
        let is_alloc = match sec.flags() {
            object::SectionFlags::Elf { sh_flags } => {
                (sh_flags & (object::elf::SHF_ALLOC as u64)) != 0
            }
            _ => false,
        };
        if is_alloc && sec.size() > 0 {
            actual_alloc_secs.insert(sec.name()?.to_string());
        }
    }
    ensure!(
        actual_alloc_secs == expected_alloc_secs,
        "[{name} @ {variant:?}] allocated section set mismatch between ld.lld and placed_eval!\n  ld.lld:      {actual_alloc_secs:?}\n  placed_eval: {expected_alloc_secs:?}"
    );

    for (i, blk) in lib.blocks.iter().enumerate() {
        let vma = pl.code_addrs[i];
        let len = blk.code.len() as u64;
        let lld_bytes = read_elf_vma_bytes(&elf, vma, len, false).with_context(|| {
            format!("[{name} @ {variant:?}] failed to read code block {i} at {vma:#x}")
        })?;
        ensure!(
            lld_bytes == ref_res.code_blocks[i],
            "[{name} @ {variant:?}] code block {i} ({}) at {vma:#x} mismatch vs ld.lld!\n  ld.lld:      {}\n  placed_eval: {}",
            if single_block {
                "<merged>"
            } else {
                lib.text_secs[i].label.as_str()
            },
            hex::encode(&lld_bytes),
            hex::encode(&ref_res.code_blocks[i]),
        );
    }

    for d in &lib.data {
        let vma = pl.data_addrs[&d.sym];
        let len = d.bytes.len() as u64 + d.zero_tail;
        let is_nobits = d.bytes.is_empty() && d.zero_tail > 0;
        let lld_bytes = read_elf_vma_bytes(&elf, vma, len, is_nobits).with_context(|| {
            format!(
                "[{name} @ {variant:?}] failed to read data '{}' at {vma:#x}",
                d.sym
            )
        })?;
        let expected = &ref_res.data_blocks[&d.sym];
        ensure!(
            &lld_bytes == expected,
            "[{name} @ {variant:?}] data '{}' at {vma:#x} mismatch vs ld.lld!\n  ld.lld:      {}\n  placed_eval: {}",
            d.sym,
            hex::encode(&lld_bytes),
            hex::encode(expected),
        );
    }

    for (tls_idx, d) in lib.tls.iter().enumerate() {
        let expected = &ref_res.tls_blocks[&d.sym];
        let is_nobits = d.bytes.is_empty() && d.zero_tail > 0;
        let sec_vma = tls_secs
            .iter()
            .find(|((oi, si), _)| (*oi, *si) == (d.origin.0, d.origin.1))
            .map(|(_, v)| *v + d.origin.2)
            .context("missing TLS section VMA")?;
        let len = d.bytes.len() as u64 + d.zero_tail;
        let lld_bytes =
            read_elf_vma_bytes(&elf, sec_vma, len, is_nobits).with_context(|| {
                format!(
                    "[{name} @ {variant:?}] failed to read TLS#{tls_idx} '{}' at {sec_vma:#x}",
                    d.sym
                )
            })?;
        ensure!(
            &lld_bytes == expected,
            "[{name} @ {variant:?}] TLS '{}' initializer mismatch vs ld.lld!\n  ld.lld:      {}\n  placed_eval: {}",
            d.sym,
            hex::encode(&lld_bytes),
            hex::encode(expected),
        );
    }

    if !layout.got_pins.is_empty() {
        let got_sec = elf.section_by_name(".got").with_context(|| {
            format!("[{name} @ {variant:?}] missing .got section in ld.lld ELF")
        })?;
        let expected_got_bytes = (layout.got_pins.len() as u64) * 8;
        ensure!(
            got_sec.size() == expected_got_bytes,
            "[{name} @ {variant:?}] .got size mismatch vs ld.lld: got {} bytes, expected {expected_got_bytes}",
            got_sec.size()
        );
        for pin in &layout.got_pins {
            let lld_slot = read_elf_vma_bytes(&elf, pin.slot_vma, 8, false).with_context(|| {
                format!(
                    "[{name} @ {variant:?}] failed to read .got slot for '{}' at {:#x}",
                    pin.label, pin.slot_vma
                )
            })?;
            let expected_slot = pin.target_addr.to_le_bytes();
            ensure!(
                lld_slot.as_slice() == expected_slot,
                "[{name} @ {variant:?}] .got slot for '{}' at {:#x} mismatch vs ld.lld!\n  ld.lld:   {}\n  expected: {}",
                pin.label,
                pin.slot_vma,
                hex::encode(&lld_slot),
                hex::encode(expected_slot),
            );
        }
    }

    Ok(layout.got_pins.len())
}

/// Run the full 3-way `PlacedLib` / `MultiPlacedLib` differential comparison (`ld.lld` vs
/// `untrusted_placed` vs `placed_eval`) across all applicable [`LayoutVariant`]s for a repository
/// config.
pub fn compare_multi_placed_repo_config(
    lld: &Tool,
    name: &str,
    objs: &[ObjObject],
    exports: &[String],
    boundary: &[String],
    multi: bool,
) -> Result<PlacedRepoReport> {
    let raw_objs: Vec<Vec<u8>> = objs.iter().map(|o| o.elf_bytes.clone()).collect();
    let lib = if multi {
        let (lib, _) = build_multi_placed_lib_bounded(name, objs, exports, boundary)?;
        lib
    } else {
        let plib = build_placed_lib(name, objs, exports)?;
        MultiPlacedLib {
            name: plib.name,
            blocks: vec![plib.text],
            data: plib.data,
            tls: plib.tls,
            exports: plib.exports,
            text_secs: plib.text_secs,
            unreferenced_data: plib.unreferenced_data,
            block_raw: plib.block_raw,
            export_syms: vec![],
        }
    };

    let mut known_syms: BTreeSet<&str> = BTreeSet::new();
    for b in &lib.blocks {
        for (s, _) in &b.symbols {
            known_syms.insert(s.as_str());
        }
    }
    for d in &lib.data {
        known_syms.insert(d.sym.as_str());
    }
    for d in &lib.tls {
        known_syms.insert(d.sym.as_str());
    }
    let has_internal_got = lib.blocks.iter().any(|b| {
        b.relocs.iter().any(|r| {
            matches!(r.kind, RelocKind::AdrGotPage | RelocKind::Ld64GotLo12Nc)
                && known_syms.contains(r.sym.as_str())
        })
    });
    // Omit `NearNoRelax` (`ld.lld --no-relax`) when the library has an internal GOT pair:
    // with `--no-relax`, `ld.lld` keeps `ADRP + LDR` indirecting through a `.got` slot, whereas
    // trusted `CodeBlock.patchedWord` (`Arm64/Trusted/Object/Placed.lean:353-369`) patches an
    // unrelaxed GOT pair against `blk.target pl r` (which for an internal symbol is the symbol
    // itself, not a `.got` slot). Because no `Placement` reproduces `--no-relax` for internal GOT
    // pairs, the model fails closed (no false proof) and `NearNoRelax` is a stated coverage cut.
    let variants: &[LayoutVariant] = if has_internal_got {
        &[
            LayoutVariant::NearRelax,
            LayoutVariant::Medium,
            LayoutVariant::HighCanonicalAslr,
            LayoutVariant::PageBoundaryStress,
        ]
    } else {
        &ALL_VARIANTS
    };

    let mut got_slots = 0;
    for &variant in variants {
        got_slots = compare_built_lib_against_lld_and_placed_eval(
            lld, name, &raw_objs, objs, &lib, variant,
        )?;
    }

    Ok(PlacedRepoReport {
        blocks: lib.blocks.len(),
        code_bytes: lib.blocks.iter().map(|b| b.code.len()).sum(),
        data_syms: lib.data.len(),
        tls_syms: lib.tls.len(),
        got_slots,
        variants: variants.len(),
    })
}

fn read_elf_vma_bytes(
    elf: &object::File<'_>,
    vma: u64,
    len: u64,
    allow_nobits: bool,
) -> Result<Vec<u8>> {
    if len == 0 {
        return Ok(vec![]);
    }
    for sec in elf.sections() {
        let addr = sec.address();
        let size = sec.size();
        if addr <= vma && vma + len <= addr + size {
            let off = (vma - addr) as usize;
            let n = len as usize;
            let data = sec.data()?;
            if data.is_empty() && allow_nobits {
                return Ok(vec![0u8; n]);
            }
            if off + n <= data.len() {
                return Ok(data[off..off + n].to_vec());
            } else if allow_nobits {
                let mut out = Vec::with_capacity(n);
                if off < data.len() {
                    let take = (data.len() - off).min(n);
                    out.extend_from_slice(&data[off..off + take]);
                }
                out.resize(n, 0);
                return Ok(out);
            }
        }
    }
    bail!("VMA range [{vma:#x}, {:#x}) not covered by any ELF section", vma + len)
}

fn assemble_one(mc: &Tool, asm: &str) -> Result<Vec<u8>> {
    let dir = tempfile::tempdir()?;
    let s_path = dir.path().join("in.s");
    let o_path = dir.path().join("out.o");
    std::fs::write(&s_path, asm)?;
    let out = mc
        .cmd()
        .args([
            "-triple=aarch64-unknown-linux-gnu",
            "-filetype=obj",
            s_path.to_str().unwrap(),
            "-o",
            o_path.to_str().unwrap(),
        ])
        .output()
        .context("failed to run llvm-mc")?;
    ensure!(
        out.status.success(),
        "llvm-mc failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(std::fs::read(&o_path)?)
}

fn find_clang() -> Option<Tool> {
    for cand in ["clang", "clang-20", "clang-19", "clang-18"] {
        if let Ok(prog) = which::which(cand) {
            return Some(Tool { prog, args: vec![] });
        }
    }
    if let Ok(prog) = which::which("zig") {
        return Some(Tool {
            prog,
            args: vec!["cc".into()],
        });
    }
    None
}

fn extract_rlib_objects(rlib_bytes: &[u8]) -> Result<Vec<Vec<u8>>> {
    let archive = object::read::archive::ArchiveFile::parse(rlib_bytes)?;
    let mut objs = Vec::new();
    for member in archive.members() {
        let member = member?;
        let name = String::from_utf8_lossy(member.name()).to_string();
        if name.ends_with(".o") {
            objs.push(member.data(rlib_bytes)?.to_vec());
        }
    }
    ensure!(!objs.is_empty(), "no .o members found in .rlib archive");
    Ok(objs)
}

const ALL_VARIANTS: [LayoutVariant; 5] = [
    LayoutVariant::NearRelax,
    LayoutVariant::NearNoRelax,
    LayoutVariant::Medium,
    LayoutVariant::HighCanonicalAslr,
    LayoutVariant::PageBoundaryStress,
];

// ============================================================================
// Layer 1 & Layer 2 Tests: All Relocations, Relaxation (`rd != 31`), and TLS
// ============================================================================

#[test]
fn layer2_all_reloc_families_and_layouts_match_lld_and_placed_eval() {
    let Some(mc) = find_llvm_mc() else {
        return skip_or_panic::<()>("llvm-mc not found").unwrap_or(());
    };
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };

    let asm = r#"
.section .text.entry,"ax",@progbits
.globl entry
.type entry, @function
.p2align 2
entry:
  // ADRP + ADD (relaxable when < 1 MiB)
  adrp x0, ro_u64
  add  x0, x0, :lo12:ro_u64
  // ADRP + LDST{8,16,32,64,128}_ABS_LO12_NC
  adrp x1, rw_bytes
  ldrb w2, [x1, :lo12:rw_bytes]
  adrp x3, rw_u16
  ldrh w4, [x3, :lo12:rw_u16]
  adrp x5, rw_u32
  ldr  w6, [x5, :lo12:rw_u32]
  adrp x7, ro_u64
  ldr  x8, [x7, :lo12:ro_u64]
  adrp x9, ro_u128
  ldr  q0, [x9, :lo12:ro_u128]
  // Direct ADR_PREL_LO21 and LD_PREL_LO19 to local function / constant within code
  adr  x10, helper_fn
  ldr  x11, helper_fn
  // CONDBR19 and TSTBR14 and CALL26/JUMP26
  cbz  x2, helper_fn
  tbz  w4, #3, helper_fn
  bl   helper_fn
  b    tail_fn

.section .text.helper_fn,"ax",@progbits
.globl helper_fn
.type helper_fn, @function
.p2align 2
helper_fn:
  adrp x12, bss_buf
  add  x12, x12, :lo12:bss_buf
  str  x8, [x12]
  ret

.section .text.tail_fn,"ax",@progbits
.globl tail_fn
.type tail_fn, @function
.p2align 2
tail_fn:
  adrp x13, ptr_table
  ldr  x14, [x13, :lo12:ptr_table]
  ret

.section .rodata.ro_u64,"a",@progbits
.globl ro_u64
.type ro_u64, @object
.p2align 3
ro_u64:
  .quad 0xdeadbeefcafebabe

.section .rodata.ro_u128,"a",@progbits
.globl ro_u128
.type ro_u128, @object
.p2align 4
ro_u128:
  .quad 0x0102030405060708
  .quad 0x1112131415161718

.section .data.rw_bytes,"aw",@progbits
.globl rw_bytes
.type rw_bytes, @object
rw_bytes:
  .byte 0x7f, 0x45, 0x4c, 0x46

.section .data.rw_u16,"aw",@progbits
.globl rw_u16
.type rw_u16, @object
.p2align 1
rw_u16:
  .hword 0x1234

.section .data.rw_u32,"aw",@progbits
.globl rw_u32
.type rw_u32, @object
.p2align 2
rw_u32:
  .word 0x89abcdef

.section .data.ptr_table,"aw",@progbits
.globl ptr_table
.type ptr_table, @object
.p2align 3
ptr_table:
  .quad helper_fn
  .quad ro_u64 + 4
  .word helper_fn - .
  .word 0

.section .bss.bss_buf,"aw",@nobits
.globl bss_buf
.type bss_buf, @object
.p2align 3
bss_buf:
  .zero 32
"#;

    let obj = assemble_one(&mc, asm).unwrap();
    let exports = vec![
        "entry".to_string(),
        "helper_fn".to_string(),
        "tail_fn".to_string(),
    ];
    for variant in ALL_VARIANTS {
        compare_against_lld_and_placed_eval(&lld, "all_relocs", &[obj.clone()], &exports, variant)
            .unwrap();
    }

    // GOT pair (`R_AARCH64_ADR_GOT_PAGE` + `R_AARCH64_LD64_GOT_LO12_NC`) relaxed by `ld.lld` to
    // `NOP + ADR` in `NearRelax` / `PageBoundaryStress` and `ADRP + ADD` in `Medium` / `HighCanonicalAslr`.
    let got_asm = r#"
.section .text.got_entry,"ax",@progbits
.globl got_entry
.type got_entry, @function
.p2align 2
got_entry:
  adrp x0, :got:got_target
  ldr  x0, [x0, :got_lo12:got_target]
  ret

.section .rodata.got_target,"a",@progbits
.globl got_target
.type got_target, @object
.p2align 3
got_target:
  .quad 0x0123456789abcdef
"#;
    let got_obj = assemble_one(&mc, got_asm).unwrap();
    for variant in [
        LayoutVariant::NearRelax,
        LayoutVariant::Medium,
        LayoutVariant::HighCanonicalAslr,
        LayoutVariant::PageBoundaryStress,
    ] {
        compare_against_lld_and_placed_eval(
            &lld,
            "got_relax",
            &[got_obj.clone()],
            &["got_entry".into()],
            variant,
        )
        .unwrap();
    }
}

#[test]
fn layer2_undefined_weak_got_and_branches_match_lld_and_placed_eval() {
    let Some(mc) = find_llvm_mc() else {
        return skip_or_panic::<()>("llvm-mc not found").unwrap_or(());
    };
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };
    // An undefined weak symbol loaded through the GOT (slot holds 0, never relaxed) and called /
    // tail-called directly (`ld.lld` patches each branch to the next instruction).
    let asm = r#"
.weak weak_fn
.section .text.weak_entry,"ax",@progbits
.globl weak_entry
.type weak_entry, @function
.p2align 2
weak_entry:
  adrp x0, :got:weak_fn
  ldr  x0, [x0, :got_lo12:weak_fn]
  cbz  x0, 1f
  bl   weak_fn
1:
  b    weak_fn
"#;
    let obj = assemble_one(&mc, asm).unwrap();
    for variant in ALL_VARIANTS {
        compare_against_lld_and_placed_eval(
            &lld,
            "undef_weak",
            &[obj.clone()],
            &["weak_entry".into()],
            variant,
        )
        .unwrap();
    }
    let parsed = parse_elf_object("obj_0.o", &obj).unwrap();
    let lib = build_multi_placed_lib("undef_weak", &[parsed.clone()], &["weak_entry".into()])
        .unwrap();
    assert_eq!(lib.blocks[0].weak_refs, vec!["weak_fn".to_string()]);
    let layout = synthesize_layout(&[parsed], &lib, LayoutVariant::NearRelax).unwrap();
    assert!(layout.pl.undef_weak.contains("weak_fn"));
    let code = &eval_untrusted_placed(&lib, &layout.pl).code_blocks[0];
    let word = |i: usize| u32::from_le_bytes(code[4 * i..4 * i + 4].try_into().unwrap());
    assert_eq!(word(3), 0x9400_0001, "bl weak_fn -> bl .+4");
    assert_eq!(word(4), 0x1400_0001, "b weak_fn -> b .+4");
}

#[test]
fn layer2_rd_31_sp_vs_xzr_relaxation_guard_matches_lld_and_placed_eval() {
    let Some(mc) = find_llvm_mc() else {
        return skip_or_panic::<()>("llvm-mc not found").unwrap_or(());
    };
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };

    // Case A: `adrp x0, sym; add sp, x0, :lo12:sym` (`rd = 31 != rn = 0`) and
    // `adrp xzr, sym; add x0, sp, :lo12:sym` (`rd = 0 != rn = 31`), plus normal `adrp x2 + add x2`
    // alongside `adrp xzr, sym; add sp, sp, :lo12:sym`.
    // In `NearNoRelax`, `Medium`, `HighCanonicalAslr`, and `PageBoundaryStress` (and with `rd != rn`
    // in `NearRelax`), `ld.lld`, `untrusted_placed`, and `placed_eval` match 100% byte-for-byte.
    let asm_mixed = r#"
.section .text.sp_guard,"ax",@progbits
.globl sp_guard
.type sp_guard, @function
.p2align 2
sp_guard:
  // Relaxable normal pair (x2)
  adrp x2, target_sym
  add  x2, x2, :lo12:target_sym
  // Non-relaxable: rd = sp (31), rn = x0 (0)
  adrp x0, target_sym
  add  sp, x0, :lo12:target_sym
  // Non-relaxable: rd = x1 (1), rn = sp (31)
  adrp xzr, target_sym
  add  x1, sp, :lo12:target_sym
  ret

.section .rodata.target_sym,"a",@progbits
.globl target_sym
.type target_sym, @object
.p2align 3
target_sym:
  .quad 0xfeedface12345678
"#;
    let obj_mixed = assemble_one(&mc, asm_mixed).unwrap();
    for variant in ALL_VARIANTS {
        compare_against_lld_and_placed_eval(
            &lld,
            "sp_guard_mixed",
            &[obj_mixed.clone()],
            &["sp_guard".into()],
            variant,
        )
        .unwrap();
    }

    // Case B: `adrp xzr, target_sym; add sp, sp, :lo12:target_sym` (`w1 & 0x1f == 0x1f`,
    // `w2 & 0x1f == 0x1f`, `(w2 >> 5) & 0x1f == 0x1f`).
    // Verify that `placed_eval` and `untrusted_placed` refuse to relax `rd = 31` even if offset 0
    // is explicitly placed in `pl.relax`, and match `ld.lld` across `NearNoRelax`, `Medium`, and
    // `HighCanonicalAslr`!
    let asm_rd31 = r#"
.section .text.sp_rd31,"ax",@progbits
.globl sp_rd31
.type sp_rd31, @function
.p2align 2
sp_rd31:
  adrp xzr, target_sym
  add  sp, sp, :lo12:target_sym
  ret

.section .rodata.target_sym,"a",@progbits
.globl target_sym
.type target_sym, @object
.p2align 3
target_sym:
  .quad 0xfeedface12345678
"#;
    let obj_rd31 = assemble_one(&mc, asm_rd31).unwrap();
    for variant in [
        LayoutVariant::NearNoRelax,
        LayoutVariant::Medium,
        LayoutVariant::HighCanonicalAslr,
    ] {
        compare_against_lld_and_placed_eval(
            &lld,
            "sp_rd31",
            &[obj_rd31.clone()],
            &["sp_rd31".into()],
            variant,
        )
        .unwrap();
    }
    // Also verify directly with `placed_eval` that requesting `relax = [0]` at `NearRelax` keeps
    // `adrp xzr + add sp, sp` unrelaxed in the Lean TCB!
    let parsed = parse_elf_object("sp_rd31.o", &obj_rd31).unwrap();
    let lib = build_multi_placed_lib("sp_rd31", &[parsed], &["sp_rd31".into()]).unwrap();
    let mut pl = PlacedEvalPlacement {
        code_addrs: vec![0x0040_0000],
        data_addrs: [("target_sym".into(), 0x0040_1238)].into(),
        tls_addrs: BTreeMap::new(),
        extern_addrs: BTreeMap::new(),
        relax: vec![[0u64].into()],
        b2b: vec![BTreeSet::new()],
        undef_weak: BTreeSet::new(),
    };
    let lean_with_relax = run_placed_eval(&lib, &pl).unwrap();
    pl.relax[0].clear();
    let lean_without_relax = run_placed_eval(&lib, &pl).unwrap();
    assert!(lean_with_relax.valid);
    assert_eq!(lean_with_relax.code_blocks, lean_without_relax.code_blocks);
}

#[test]
fn layer2_tlsdesc_to_tlsle_and_direct_tlsle_match_lld_and_placed_eval() {
    let Some(mc) = find_llvm_mc() else {
        return skip_or_panic::<()>("llvm-mc not found").unwrap_or(());
    };
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };

    // Test both 16-byte aligned TLS (`tlsBaseOffset = 16`) and 32-byte aligned TLS (`tlsBaseOffset = 32`),
    // covering:
    // - 4-instruction `TLSDESC -> TLSLE` sequence (`R_AARCH64_TLSDESC_ADR_PAGE21`,
    //   `R_AARCH64_TLSDESC_LD64_LO12`, `R_AARCH64_TLSDESC_ADD_LO12`, `R_AARCH64_TLSDESC_CALL`),
    // - `R_AARCH64_TLSLE_ADD_TPREL_HI12`, `R_AARCH64_TLSLE_ADD_TPREL_LO12`,
    //   `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC`,
    // - `R_AARCH64_TLSLE_LDST{8,16,32,64,128}_TPREL_LO12_NC`,
    // - `R_AARCH64_TLSLE_MOVW_TPREL_G1`, `R_AARCH64_TLSLE_MOVW_TPREL_G0_NC`, `R_AARCH64_TLSLE_MOVW_TPREL_G0`.
    for align_pow2 in [4u32, 5u32] {
        let asm = format!(
            r#"
.section .text.tls_entry,"ax",@progbits
.globl tls_entry
.type tls_entry, @function
.p2align 2
tls_entry:
  // 1. TLSDESC -> TLSLE relaxation on `.tdata` symbol `tls_init`
  adrp x0, :tlsdesc:tls_init
  ldr  x1, [x0, :tlsdesc_lo12:tls_init]
  add  x0, x0, :tlsdesc_lo12:tls_init
  .tlsdesccall tls_init
  blr  x1
  // 2. TLSDESC -> TLSLE relaxation on `.tbss` symbol `tls_zero`
  adrp x0, :tlsdesc:tls_zero
  ldr  x1, [x0, :tlsdesc_lo12:tls_zero]
  add  x0, x0, :tlsdesc_lo12:tls_zero
  .tlsdesccall tls_zero
  blr  x1
  // 3. Direct TLSLE ADD HI12 + LO12_NC
  mrs  x2, tpidr_el0
  add  x3, x2, :tprel_hi12:tls_init
  add  x3, x3, :tprel_lo12_nc:tls_init
  add  x4, x2, :tprel_lo12_nc:tls_zero
  // 4. Direct TLSLE LDST{{8,16,32,64,128}}_TPREL_LO12_NC
  ldrb w5, [x2, :tprel_lo12_nc:tls_init]
  ldrh w6, [x2, :tprel_lo12_nc:tls_init]
  ldr  w7, [x2, :tprel_lo12_nc:tls_init]
  ldr  x8, [x2, :tprel_lo12_nc:tls_init]
  ldr  q0, [x2, :tprel_lo12_nc:tls_vec]
  // 5. Direct TLSLE MOVW_TPREL_G1 + G0_NC and MOVW_TPREL_G0
  movz x9, :tprel_g1:tls_zero
  movk x9, :tprel_g0_nc:tls_zero
  movz x10, :tprel_g0:tls_init
  // 6. TLSIE -> TLSLE relaxation (`R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` + `LD64_GOTTPREL_LO12_NC`,
  //    including `XZR` destination register 31)
  adrp x11, :gottprel:tls_init
  ldr  x11, [x11, :gottprel_lo12:tls_init]
  adrp xzr, :gottprel:tls_zero
  ldr  xzr, [sp, :gottprel_lo12:tls_zero]
  ret

.section .tdata.tls_init,"awT",@progbits
.globl tls_init
.type tls_init, @object
.p2align 3
tls_init:
  .quad 0x1122334455667788

.section .tdata.tls_vec,"awT",@progbits
.globl tls_vec
.type tls_vec, @object
.p2align {align_pow2}
tls_vec:
  .quad 0xaabbccddeeff0011
  .quad 0x2233445566778899

.section .tbss.tls_zero,"awT",@nobits
.globl tls_zero
.type tls_zero, @object
.p2align 3
tls_zero:
  .zero 24
"#
        );
        let obj = assemble_one(&mc, &asm).unwrap();
        for variant in ALL_VARIANTS {
            compare_against_lld_and_placed_eval(
                &lld,
                &format!("tls_align_{}", 1u32 << align_pow2),
                &[obj.clone()],
                &["tls_entry".into()],
                variant,
            )
            .unwrap();
        }
    }
}

// ============================================================================
// Layer 3 Tests: Negative / Soundness Rejection Differential Tests
// ============================================================================

/// Assert that an invalid placement is rejected by **both** `placed_eval` (`valid == false`)
/// and `untrusted_placed` (`valid == false`), and (when representable as a linker script VMA)
/// also causes `ld.lld` to exit with a non-zero status.
fn assert_rejected_by_lld_and_placed_eval(
    mc: &Tool,
    lld: &Tool,
    case_name: &str,
    asm: &str,
    code_vma: u64,
    target_vma: u64,
    is_tls_target: bool,
) {
    let obj_bytes = assemble_one(mc, asm).unwrap();
    let obj = parse_elf_object("neg.o", &obj_bytes).unwrap();
    let lib = build_multi_placed_lib(case_name, &[obj], &["neg_entry".into()]).unwrap();

    let mut pl = PlacedEvalPlacement {
        code_addrs: vec![code_vma],
        data_addrs: BTreeMap::new(),
        tls_addrs: BTreeMap::new(),
        extern_addrs: BTreeMap::new(),
        relax: vec![BTreeSet::new()],
        b2b: vec![BTreeSet::new()],
        undef_weak: BTreeSet::new(),
    };
    if is_tls_target {
        for d in &lib.tls {
            pl.tls_addrs.insert(d.sym.clone(), target_vma);
        }
    } else {
        for d in &lib.data {
            pl.data_addrs.insert(d.sym.clone(), target_vma);
        }
        for ext in &lib.blocks[0].externs {
            pl.extern_addrs.insert(ext.clone(), target_vma);
        }
        for r in &lib.blocks[0].relocs {
            if !pl.data_addrs.contains_key(&r.sym) && !pl.extern_addrs.contains_key(&r.sym) {
                pl.extern_addrs.insert(r.sym.clone(), target_vma);
            }
        }
    }

    let rust_res = eval_untrusted_placed(&lib, &pl);
    let lean_res = run_placed_eval(&lib, &pl).unwrap();
    assert!(
        !rust_res.valid,
        "[{case_name}] expected untrusted_placed to reject out-of-range placement"
    );
    assert!(
        !lean_res.valid,
        "[{case_name}] expected placed_eval to reject out-of-range placement"
    );

    // Also run stock `ld.lld` with a linker script pinning the same out-of-range address and
    // verify `ld.lld` exits with a non-zero error code!
    let dir = tempfile::tempdir().unwrap();
    let o_path = dir.path().join("neg.o");
    std::fs::write(&o_path, &obj_bytes).unwrap();
    let lds_path = dir.path().join("neg.lds");
    let code_len = lib.blocks[0].code.len();
    let lds = if is_tls_target {
        // Place a dummy `.tdata.pad` before `tls_sym` so `tls_sym` has `tprel >= target_vma`.
        let pad = target_vma.saturating_sub(16);
        format!(
            "MEMORY {{ code (rx) : ORIGIN = 0x{code_vma:x}, LENGTH = {code_len} }}\nSECTIONS {{\n  .text 0x{code_vma:x} : {{ \"{}\"(.text*) }} > code\n  .tdata 0x500000 : {{ . = . + 0x{pad:x}; \"{}\"(.tdata*) }}\n}}\n",
            o_path.display(),
            o_path.display()
        )
    } else {
        format!(
            "MEMORY {{ code (rx) : ORIGIN = 0x{code_vma:x}, LENGTH = {code_len} }}\n\"target_sym\" = 0x{target_vma:x};\nSECTIONS {{\n  .text 0x{code_vma:x} : {{ \"{}\"(.text*) }} > code\n}}\n",
            o_path.display()
        )
    };
    std::fs::write(&lds_path, &lds).unwrap();
    let elf_path = dir.path().join("neg.elf");
    let out = lld
        .cmd()
        .args([
            "--image-base=0",
            "--no-relax",
            "-e",
            "0",
            "-T",
            lds_path.to_str().unwrap(),
            o_path.to_str().unwrap(),
            "-o",
            elf_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        !out.status.success(),
        "[{case_name}] expected ld.lld to fail on out-of-range/misaligned target {target_vma:#x} from {code_vma:#x}, but it succeeded!"
    );
}

#[test]
fn layer3_negative_soundness_rejections_match_lld_and_placed_eval() {
    let Some(mc) = find_llvm_mc() else {
        return skip_or_panic::<()>("llvm-mc not found").unwrap_or(());
    };
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };

    // 1. Out-of-range CALL26 (>= +128 MiB: 0x0800_0000)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "call26_overflow_pos",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  bl target_sym\n  ret\n",
        0x0040_0000,
        0x0040_0000 + (1 << 27),
        false,
    );
    // 2. Out-of-range JUMP26 (< -128 MiB)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "jump26_overflow_neg",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  b target_sym\n",
        0x1000_0000,
        0x1000_0000 - (1 << 27) - 4,
        false,
    );
    // 3. Misaligned LDST128_ABS_LO12_NC (`target % 16 != 0`)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "ldst128_misaligned",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  ldr q0, [x1, :lo12:target_sym]\n  ret\n",
        0x0040_0000,
        0x0040_1008,
        false,
    );
    // 4. Out-of-range ADR_PREL_PG_HI21 (>= +4 GiB)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "adrp_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  adrp x0, target_sym\n  ret\n",
        0x0040_0000,
        0x0040_0000 + (1u64 << 32) + 0x1000,
        false,
    );
    // 5. Out-of-range CONDBR19 (>= +1 MiB)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "condbr19_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  cbz x0, target_sym\n  ret\n",
        0x0040_0000,
        0x0040_0000 + (1 << 20),
        false,
    );
    // 6. Out-of-range TSTBR14 (>= +32 KiB)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "tstbr14_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  tbz w0, #1, target_sym\n  ret\n",
        0x0040_0000,
        0x0040_0000 + (1 << 15),
        false,
    );
    // 7. Out-of-range ADR_PREL_LO21 (>= +1 MiB)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "adr_lo21_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  adr x0, target_sym\n  ret\n",
        0x0040_0000,
        0x0040_0000 + (1 << 20),
        false,
    );
    // 8. Misaligned LDST64_ABS_LO12_NC (`target % 8 != 0`)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "ldst64_misaligned",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  ldr x0, [x1, :lo12:target_sym]\n  ret\n",
        0x0040_0000,
        0x0040_1004,
        false,
    );
    // 9. Overflowed TLSDESC -> TLSLE (`tprel >= 2^32`)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "tlsdesc_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  adrp x0, :tlsdesc:tls_sym\n  ldr x1, [x0, :tlsdesc_lo12:tls_sym]\n  add x0, x0, :tlsdesc_lo12:tls_sym\n  .tlsdesccall tls_sym\n  blr x1\n  ret\n.section .tdata.tls_sym,\"awT\",@progbits\n.globl tls_sym\n.p2align 3\ntls_sym:\n  .quad 1\n",
        0x0040_0000,
        1u64 << 32,
        true,
    );
    // 10. Overflowed TLSLE_ADD_TPREL_HI12 (`tprel >= 2^24`)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "tlsle_hi12_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  add x0, x1, :tprel_hi12:tls_sym\n  ret\n.section .tdata.tls_sym,\"awT\",@progbits\n.globl tls_sym\n.p2align 3\ntls_sym:\n  .quad 1\n",
        0x0040_0000,
        1u64 << 24,
        true,
    );
    // 11. Overflowed TLSLE_MOVW_TPREL_G0 (`tprel >= 2^16`)
    assert_rejected_by_lld_and_placed_eval(
        &mc,
        &lld,
        "tlsle_movw_g0_overflow",
        ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  movz x0, :tprel_g0:tls_sym\n  ret\n.section .tdata.tls_sym,\"awT\",@progbits\n.globl tls_sym\n.p2align 3\ntls_sym:\n  .quad 1\n",
        0x0040_0000,
        1u64 << 16,
        true,
    );

    // 12. Misaligned CALL26 target (`target % 4 != 0`) and overflowed TLSLE_ADD_TPREL_LO12
    // rejected by `placed_eval` and `untrusted_placed`.
    for (name, asm, target_vma, is_tls) in [
        (
            "call26_misaligned",
            ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  bl target_sym\n  ret\n",
            0x0040_1002u64,
            false,
        ),
        (
            "tlsle_lo12_overflow",
            ".section .text.neg_entry,\"ax\",@progbits\n.globl neg_entry\n.type neg_entry,@function\nneg_entry:\n  add x0, x1, :tprel_lo12:tls_sym\n  ret\n.section .tdata.tls_sym,\"awT\",@progbits\n.globl tls_sym\n.p2align 3\ntls_sym:\n  .quad 1\n",
            0x1000u64,
            true,
        ),
    ] {
        let obj_bytes = assemble_one(&mc, asm).unwrap();
        let obj = parse_elf_object("neg.o", &obj_bytes).unwrap();
        let lib = build_multi_placed_lib(name, &[obj], &["neg_entry".into()]).unwrap();
        let mut pl = PlacedEvalPlacement {
            code_addrs: vec![0x0040_0000],
            data_addrs: BTreeMap::new(),
            tls_addrs: BTreeMap::new(),
            extern_addrs: BTreeMap::new(),
            relax: vec![BTreeSet::new()],
            b2b: vec![BTreeSet::new()],
            undef_weak: BTreeSet::new(),
        };
        if is_tls {
            pl.tls_addrs.insert("tls_sym".into(), target_vma);
        } else {
            pl.extern_addrs.insert("target_sym".into(), target_vma);
        }
        assert!(!eval_untrusted_placed(&lib, &pl).valid, "[{name}] expected untrusted_placed rejection");
        assert!(!run_placed_eval(&lib, &pl).unwrap().valid, "[{name}] expected placed_eval rejection");
    }

    // 12. Overlapping code and data blocks rejected by `placed_eval` and `untrusted_placed`.
    let overlap_asm = r#"
.section .text.f1,"ax",@progbits
.globl f1
.type f1, @function
f1:
  adrp x0, dat
  ldr  x0, [x0, :lo12:dat]
  bl   f2
  ret
.section .text.f2,"ax",@progbits
.globl f2
.type f2, @function
f2:
  ret
.section .data.dat,"aw",@progbits
.globl dat
.type dat, @object
.p2align 3
dat:
  .quad 99
"#;
    let obj_bytes = assemble_one(&mc, overlap_asm).unwrap();
    let obj = parse_elf_object("overlap.o", &obj_bytes).unwrap();
    let lib = build_multi_placed_lib("overlap", &[obj], &["f1".into(), "f2".into()]).unwrap();
    let bad_pl = PlacedEvalPlacement {
        // `f1` (16 bytes at 0x400000) overlaps `f2` (at 0x400008).
        code_addrs: vec![0x0040_0000, 0x0040_0008],
        data_addrs: [("dat".into(), 0x0041_0000)].into(),
        tls_addrs: BTreeMap::new(),
        extern_addrs: BTreeMap::new(),
        relax: vec![BTreeSet::new(); 2],
        b2b: vec![BTreeSet::new(); 2],
        undef_weak: BTreeSet::new(),
    };
    assert!(!eval_untrusted_placed(&lib, &bad_pl).valid);
    assert!(!run_placed_eval(&lib, &bad_pl).unwrap().valid);
}

// ============================================================================
// Layer 4 Tests: Multi-TU C & Safe Rust Corpus (incl. `thread_local!`)
// ============================================================================

#[test]
fn layer4_multi_tu_c_corpus_matches_lld_and_placed_eval() {
    let Some(clang) = find_clang() else {
        return skip_or_panic::<()>("clang not found").unwrap_or(());
    };
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };

    let c_tu1 = r#"
#pragma GCC visibility push(hidden)
#include <stdint.h>

extern uint64_t helper_compute(uint32_t tag, uint64_t x);
extern _Thread_local uint64_t tls_counter;
extern _Thread_local uint64_t tls_scratch_bss;

static const uint64_t RO_TABLE[4] = {
    0x1111222233334444ULL,
    0x5555666677778888ULL,
    0x9999aaaabbbbccccULL,
    0xddddeeeeffff0001ULL,
};

uint64_t (*global_fn_ptr)(uint32_t, uint64_t) = &helper_compute;

uint64_t c_corpus_entry(uint32_t op, uint64_t arg) {
    tls_counter += arg + RO_TABLE[op & 3];
    tls_scratch_bss ^= tls_counter;
    switch (op) {
        case 0: return helper_compute(1, arg) + tls_counter;
        case 1: return helper_compute(2, arg ^ RO_TABLE[1]) + tls_scratch_bss;
        case 2: return global_fn_ptr(3, arg + RO_TABLE[2]);
        case 3: return helper_compute(4, arg - RO_TABLE[3]);
        case 4: return tls_counter ^ RO_TABLE[0];
        default: return tls_scratch_bss;
    }
}
"#;

    let c_tu2 = r#"
#pragma GCC visibility push(hidden)
#include <stdint.h>

_Thread_local uint64_t tls_counter = 0x4242424200000001ULL;
_Thread_local uint64_t tls_scratch_bss = 0;

static uint16_t step_weights[4] = { 17, 31, 47, 61 };
static uint32_t total_invocations = 0;

uint64_t helper_compute(uint32_t tag, uint64_t x) {
    total_invocations += 1;
    uint16_t w = step_weights[tag & 3];
    return (x * (uint64_t)w) + (uint64_t)total_invocations + tls_counter;
}
"#;

    let dir = tempfile::tempdir().unwrap();
    let mut raw_objs = Vec::new();
    for (mode_name, tls_flags) in [
        ("c_corpus_tlsdesc", &["-fPIC", "-fvisibility=hidden"][..]),
        (
            "c_corpus_tlsle",
            &["-fno-PIE", "-ftls-model=local-exec"][..],
        ),
    ] {
        raw_objs.clear();
        for (idx, src) in [c_tu1, c_tu2].iter().enumerate() {
            let c_path = dir.path().join(format!("{mode_name}_{idx}.c"));
            let o_path = dir.path().join(format!("{mode_name}_{idx}.o"));
            std::fs::write(&c_path, src).unwrap();
            let mut cmd = clang.cmd();
            cmd.args([
                "--target=aarch64-linux-gnu",
                "-O2",
                "-ffunction-sections",
                "-fdata-sections",
                "-c",
                c_path.to_str().unwrap(),
                "-o",
                o_path.to_str().unwrap(),
            ]);
            cmd.args(tls_flags);
            let out = cmd.output().unwrap();
            assert!(
                out.status.success(),
                "clang failed ({mode_name}):\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
            raw_objs.push(std::fs::read(&o_path).unwrap());
        }
        let exports = vec!["c_corpus_entry".to_string(), "helper_compute".to_string()];
        for variant in ALL_VARIANTS {
            compare_against_lld_and_placed_eval(&lld, mode_name, &raw_objs, &exports, variant)
                .unwrap();
        }
    }
}
#[test]
fn layer4_rust_corpus_and_thread_local_rlib_and_bin_match_lld_and_placed_eval() {
    let Some(lld) = find_lld() else {
        return skip_or_panic::<()>("ld.lld not found").unwrap_or(());
    };

    // Check that `aarch64-unknown-linux-musl` or `aarch64-unknown-none` target is installed.
    let target = "aarch64-unknown-linux-musl";
    let dir = tempfile::tempdir().unwrap();

    // Rust program exercising:
    // - `std::thread_local!` (via `Cell<u64>` in `.tdata` with non-zero init and `.tbss` with zero init),
    // - trait-object `.data.rel.ro` vtables with `R_AARCH64_ABS64`,
    // - `match` jump tables and cross-function calls,
    // - `.rodata` constants and mutable statics in `.data` / `.bss`.
    let rust_src = r#"
#![allow(dead_code)]
use std::cell::Cell;

std::thread_local! {
    static TLS_INIT_COUNTER: Cell<u64> = const { Cell::new(0x1234_5678_9abc_def0) };
    static TLS_ZERO_ACCUM: Cell<u64> = const { Cell::new(0) };
}

pub trait Processor {
    fn process(&self, x: u64) -> u64;
}

pub struct ScaleAdd {
    pub factor: u64,
    pub bias: u64,
}

impl Processor for ScaleAdd {
    #[inline(never)]
    fn process(&self, x: u64) -> u64 {
        x.wrapping_mul(self.factor).wrapping_add(self.bias)
    }
}

static DEFAULT_PROC: ScaleAdd = ScaleAdd {
    factor: 0x0101_0101_0101_0101,
    bias: 0x00ff_00ff_00ff_00ff,
};

static mut GLOBAL_STATE: u64 = 0xfeed_face_cafe_beef;
static mut GLOBAL_BSS_HIST: [u64; 4] = [0; 4];

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn rust_apply_dyn(p: &dyn Processor, x: u64) -> u64 {
    p.process(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_tls_and_vtable_entry(op: u32, input: u64) -> u64 {
    let c = TLS_INIT_COUNTER.with(|cell| {
        let next = cell.get().wrapping_add(input).wrapping_add(1);
        cell.set(next);
        next
    });
    let z = TLS_ZERO_ACCUM.with(|cell| {
        let next = cell.get() ^ c;
        cell.set(next);
        next
    });
    let dyn_res = rust_apply_dyn(&DEFAULT_PROC, input ^ c);
    unsafe {
        GLOBAL_STATE = GLOBAL_STATE.wrapping_add(dyn_res);
        GLOBAL_BSS_HIST[(op as usize) & 3] ^= z;
        match op {
            0 => GLOBAL_STATE ^ c,
            1 => dyn_res.wrapping_add(z),
            2 => GLOBAL_BSS_HIST[2].wrapping_add(c),
            3 => GLOBAL_STATE.wrapping_sub(z),
            _ => dyn_res ^ z ^ c,
        }
    }
}
"#;

    let src_path = dir.path().join("corpus.rs");
    std::fs::write(&src_path, rust_src).unwrap();

    // Compile in two modes:
    // 1. PIC `.rlib` (`-C relocation-model=pic`): emits 4-relocation `TLSDESC -> TLSLE` sequence
    //    (`R_AARCH64_TLSDESC_ADR_PAGE21`, `LD64_LO12`, `ADD_LO12`, `CALL`) + `.tdata` + `.tbss`.
    // 2. Static local-exec (`-C relocation-model=static`): emits direct `TLSLE` relocations
    //    (`R_AARCH64_TLSLE_ADD_TPREL_HI12`, `LO12_NC`, etc.) + `.tdata` + `.tbss`.
    for (mode_name, reloc_model) in [
        ("rust_rlib_tlsdesc", "pic"),
        ("rust_static_tlsle", "static"),
    ] {
        let rlib_path = dir.path().join(format!("lib{mode_name}.rlib"));
        let out = Command::new("rustc")
            .args([
                "--edition=2024",
                "--target",
                target,
                "--crate-type=rlib",
                "-O",
                "-C",
                &format!("relocation-model={reloc_model}"),
                "-C",
                "codegen-units=1",
                "-C",
                "panic=abort",
                src_path.to_str().unwrap(),
                "-o",
                rlib_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        if !out.status.success() {
            let stderr = String::from_utf8_lossy(&out.stderr);
            if stderr.contains("can't find crate for `std`")
                || stderr.contains("target may not be installed")
            {
                return skip_or_panic::<()>(format!("rustc target {target} not installed: {stderr}"))
                    .unwrap_or(());
            }
            panic!("rustc failed ({mode_name}):\n{stderr}");
        }
        let rlib_bytes = std::fs::read(&rlib_path).unwrap();
        let raw_objs = extract_rlib_objects(&rlib_bytes).unwrap();
        let exports = vec![
            "rust_tls_and_vtable_entry".to_string(),
            "rust_apply_dyn".to_string(),
        ];

        // Verify that the expected TLS relocation family actually appeared in the extracted model!
        let parsed_objs: Vec<ObjObject> = raw_objs
            .iter()
            .enumerate()
            .map(|(i, b)| parse_elf_object(&format!("{mode_name}_{i}.o"), b).unwrap())
            .collect();
        let mlib = build_multi_placed_lib(mode_name, &parsed_objs, &exports).unwrap();
        assert!(
            mlib.tls.len() >= 2,
            "[{mode_name}] expected both .tdata and .tbss TLS objects in PMultiLib, got {:?}",
            mlib.tls.iter().map(|d| (&d.sym, d.bytes.len(), d.zero_tail)).collect::<Vec<_>>()
        );
        let has_init_tdata = mlib.tls.iter().any(|d| !d.bytes.is_empty());
        let has_zero_tbss = mlib.tls.iter().any(|d| d.bytes.is_empty() && d.zero_tail > 0);
        assert!(has_init_tdata, "[{mode_name}] missing non-zero .tdata initializer");
        assert!(has_zero_tbss, "[{mode_name}] missing zero-initialized .tbss block");

        let all_reloc_kinds: Vec<RelocKind> = mlib
            .blocks
            .iter()
            .flat_map(|b| b.relocs.iter().map(|r| r.kind))
            .collect();
        if reloc_model == "pic" {
            assert!(
                all_reloc_kinds.contains(&RelocKind::TlsdescAdrPage21)
                    && all_reloc_kinds.contains(&RelocKind::TlsdescLd64Lo12)
                    && all_reloc_kinds.contains(&RelocKind::TlsdescAddLo12)
                    && all_reloc_kinds.contains(&RelocKind::TlsdescCall),
                "[{mode_name}] expected 4 TLSDESC relocations, got {all_reloc_kinds:?}"
            );
        } else {
            assert!(
                all_reloc_kinds.iter().any(|k| matches!(
                    k,
                    RelocKind::TlsleAddTprelHi12
                        | RelocKind::TlsleAddTprelLo12
                        | RelocKind::TlsleAddTprelLo12Nc
                        | RelocKind::TlsleLdst64TprelLo12Nc
                )),
                "[{mode_name}] expected direct TLSLE relocations, got {all_reloc_kinds:?}"
            );
        }

        for variant in ALL_VARIANTS {
            compare_against_lld_and_placed_eval(&lld, mode_name, &raw_objs, &exports, variant)
                .unwrap();
        }
    }
}

const REPO_CRATES_ALLOWLIST: &[(&str, &str)] = &[];

fn discover_translation_tomls(root: &Path) -> Vec<String> {
    #[derive(serde::Deserialize)]
    struct ObjNameProbe {
        obj_name: Option<String>,
    }
    let mut out: Vec<(String, String, String)> = Vec::new();
    for base in [
        root.join("Arm64/Testing/Fixtures"),
        root.join("VerifiedLibraries"),
        root.join("CaseStudies"),
    ] {
        let walker = walkdir::WalkDir::new(base)
            .sort_by_file_name()
            .into_iter()
            .filter_entry(|e| {
                let name = e.file_name().to_string_lossy();
                e.depth() == 0
                    || !(e.file_type().is_dir()
                        && (name.starts_with('.')
                            || name == "_template"
                            || name == "target"
                            || name == "vendor"))
            });
        for entry in walker.filter_map(|e| e.ok()) {
            let name = entry.file_name().to_string_lossy();
            if !entry.file_type().is_file() || !name.ends_with(".toml") || name == "Cargo.toml" {
                continue;
            }
            let Ok(rel) = entry.path().strip_prefix(root) else {
                continue;
            };
            let path = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
            let Ok(Some(obj_name)) = std::fs::read_to_string(entry.path())
                .ok()
                .and_then(|s| toml::from_str::<ObjNameProbe>(&s).ok())
                .map(|p| p.obj_name)
                .ok_or(())
            else {
                continue;
            };
            let dir = path.rsplit_once('/').map_or("", |(d, _)| d).to_string();
            out.push((dir, obj_name, path));
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
    out.into_iter().map(|(_, _, p)| p).collect()
}

/// Every translation config in the repository (`Arm64/Testing/Fixtures/**/*.toml`,
/// `VerifiedLibraries/*/Implementation/*.toml`, and `CaseStudies/*/Implementation/*.toml`)
/// is extracted and differentially checked against stock `ld.lld`, `untrusted_placed`, and
/// C-extracted `placed_eval`.
#[test]
fn repo_crates_match_lld() {
    use crate::untrusted_driver::{Toolchain, extract, load_config};
    let Some(lld) = find_lld().or_else(|| skip_or_panic("ld.lld not found ($LLD or PATH)")) else {
        return;
    };
    let suite_t0 = std::time::Instant::now();
    let root = repo_root();
    let cfgs = discover_translation_tomls(&root);
    let campaign_dirs = root.join("CaseStudies").read_dir().map_or(0, |d| {
        d.flatten()
            .filter(|e| e.path().join("Implementation").is_dir())
            .count()
    });
    let min_expected = if campaign_dirs > 5 { 25 } else { 5 };
    assert!(
        cfgs.len() >= min_expected,
        "expected at least {min_expected} translation configs, discovered {}: {cfgs:?}",
        cfgs.len()
    );
    // `REPO_CRATES_LLD_ONLY=<prefix>[,<prefix>...]` restricts the check to configs under the
    // given repository-relative prefixes (change-scoped local runs; CI always checks every
    // config). Discovery and the minimum-count guard above still see the whole repository.
    let cfgs = match std::env::var("REPO_CRATES_LLD_ONLY") {
        Ok(spec) => {
            let prefixes: Vec<String> = spec
                .split(',')
                .map(|p| p.trim().trim_end_matches('/').to_string())
                .filter(|p| !p.is_empty())
                .collect();
            let kept: Vec<String> = cfgs
                .into_iter()
                .filter(|c| prefixes.iter().any(|p| c.starts_with(&format!("{p}/"))))
                .collect();
            eprintln!(
                "REPO_CRATES_LLD_ONLY={spec}: checking {} config(s): {kept:?}",
                kept.len()
            );
            kept
        }
        Err(_) => cfgs,
    };
    let mut groups: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for c in &cfgs {
        let parts: Vec<&str> = c.split('/').collect();
        let key = if parts.len() >= 2 {
            format!("{}/{}", parts[0], parts[1])
        } else {
            c.clone()
        };
        groups.entry(key).or_default().push(c.clone());
    }
    let group_list: Vec<Vec<String>> = groups.into_values().collect();
    let workers = std::thread::available_parallelism()
        .map(|n| n.get().min(6))
        .unwrap_or(4)
        .min(group_list.len().max(1));
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let tested = std::sync::atomic::AtomicUsize::new(0);
    let allowlisted = std::sync::atomic::AtomicUsize::new(0);
    let failures = std::sync::Mutex::new(Vec::<String>::new());

    std::thread::scope(|s| {
        for _ in 0..workers {
            let lld = &lld;
            let root = &root;
            let group_list = &group_list;
            let next_idx = &next_idx;
            let tested = &tested;
            let allowlisted = &allowlisted;
            let failures = &failures;
            s.spawn(move || {
                loop {
                    let i = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(group) = group_list.get(i) else { break };
                    for c in group {
                        if let Some((_, reason)) =
                            REPO_CRATES_ALLOWLIST.iter().find(|(p, _)| *p == c.as_str())
                        {
                            eprintln!("allowlisted {c}: {reason}");
                            allowlisted.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            continue;
                        }
                        let step = (|| -> Result<PlacedRepoReport> {
                            let t0 = std::time::Instant::now();
                            let out = tempfile::tempdir()?;
                            let cfg = load_config(&root.join(c), root, Some(out.path()))?;
                            let name = cfg.code_def_name();
                            let (exports, boundary, multi) = cfg
                                .placed
                                .as_ref()
                                .map(|p| (p.exports.clone(), p.extern_boundary.clone(), p.multi))
                                .unwrap_or_default();
                            let mut tc = Toolchain::new(root.clone())?;
                            let ex = extract(&cfg, &mut tc)?;
                            let t_extract = t0.elapsed();
                            let rep = compare_multi_placed_repo_config(
                                lld,
                                &name,
                                &ex.objects,
                                &exports,
                                &boundary,
                                multi,
                            )?;
                            eprintln!(
                                "[timing] {c}: extract {t_extract:.1?}, compare {:.1?}",
                                t0.elapsed() - t_extract
                            );
                            Ok(rep)
                        })();
                        match step {
                            Ok(rep) => {
                                eprintln!("[placed_eval] {c}: {rep:?}");
                                tested.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            }
                            Err(e) => {
                                eprintln!("FAIL {c}: {e:#}");
                                failures.lock().unwrap().push(format!("{c}: {e:#}"));
                            }
                        }
                    }
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    let n_tested = tested.load(std::sync::atomic::Ordering::Relaxed);
    let n_allow = allowlisted.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(n_tested + n_allow, cfgs.len());
    let elapsed = suite_t0.elapsed();
    eprintln!(
        "repo_crates_match_lld verified {n_tested}/{} configs in {elapsed:.2?}",
        cfgs.len()
    );
    if require_link_diff() {
        assert_eq!(n_allow, 0, "REQUIRE_LINK_DIFF=1: {n_allow} configs skipped");
    }
}
