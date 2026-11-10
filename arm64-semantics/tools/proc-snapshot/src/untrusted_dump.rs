// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Human-readable hex text dumper for `proc-snapshot` entry snapshots (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — untrusted test and demo formatting utility.
//! - **Purpose:** Formats an `entry.snapshot.{json,bin}` into a compact hex text representation
//!   (mapped regions, entry registers, `brk`, stack `argc`/`argv`/`envp`/`auxv` table, and memory
//!   hex dumps) matching `elf_eval --dump-load-state` byte for byte.
//!
//! # Key Types & Functions
//! - [`DumpStateArgs`], [`run`]: CLI entry for `proc-snapshot dump-state`.
//! - [`format_snapshot_text`]: Formats a snapshot and binary image into the canonical text layout.
//!
//! # When to Read This File
//! - Read this file to see how QEMU entry snapshots are formatted into human-readable hex text for
//!   differential comparisons against `ElfImage.loadState`.

use anyhow::{Context, Result, bail, ensure};
use serde::Deserialize;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

#[derive(clap::Args, Debug)]
pub struct DumpStateArgs {
    /// Path to `entry.snapshot.json`.
    pub snapshot_json: PathBuf,
    /// Optional `<vaddr>:<len>` byte ranges to hex-dump (in addition to `@pc` 32 B).
    #[arg(long = "hex")]
    pub hex_ranges: Vec<String>,
}

#[derive(clap::Args, Debug)]
pub struct PokeArgs {
    /// Path to `entry.snapshot.json`.
    pub snapshot_json: PathBuf,
    /// Virtual address in hex (`0x...`) or decimal to overwrite in `entry.snapshot.bin`.
    pub vaddr: String,
    /// Hex byte string (e.g. `efbeadde`) to write at `vaddr`.
    pub hex_bytes: String,
}

#[derive(Deserialize, Debug)]
pub struct DumpBinRef {
    pub file: String,
    pub size: usize,
}

#[derive(Deserialize, Debug)]
pub struct DumpRegion {
    pub start: u64,
    pub size: u64,
    pub perm: String,
    pub kind: String,
    #[serde(rename = "binOff")]
    pub bin_off: usize,
}

#[derive(Deserialize, Debug)]
pub struct DumpRegs {
    pub x: Vec<u64>,
    pub sp: u64,
    pub pc: u64,
    pub tpidr_el0: Option<u64>,
}

#[derive(Deserialize, Debug)]
pub struct DumpSnapshot {
    pub bin: DumpBinRef,
    #[serde(rename = "brkStart")]
    pub brk_start: u64,
    pub regions: Vec<DumpRegion>,
    pub regs: DumpRegs,
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn parse_u64_auto(s: &str) -> Result<u64> {
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        Ok(u64::from_str_radix(hex, 16)?)
    } else {
        Ok(s.parse::<u64>()?)
    }
}

pub fn parse_hex_range(spec: &str) -> Result<(u64, usize)> {
    let (a, l) = spec
        .split_once(':')
        .with_context(|| format!("expected <vaddr>:<len>, got {spec:?}"))?;
    let vaddr = parse_u64_auto(a)?;
    let len = parse_u64_auto(l)? as usize;
    Ok((vaddr, len))
}

fn read_bytes<'a>(snap: &DumpSnapshot, bin: &'a [u8], addr: u64, len: usize) -> Result<&'a [u8]> {
    let r = snap
        .regions
        .iter()
        .find(|r| r.start <= addr && addr + (len as u64) <= r.start + r.size)
        .with_context(|| format!("address 0x{addr:x} (+{len}) not mapped in snapshot"))?;
    let off = r.bin_off + (addr - r.start) as usize;
    ensure!(off + len <= bin.len(), "snapshot bin out of bounds at {off}+{len}");
    Ok(&bin[off..off + len])
}

fn read_u64(snap: &DumpSnapshot, bin: &[u8], addr: u64) -> Result<u64> {
    let bs = read_bytes(snap, bin, addr, 8)?;
    Ok(u64::from_le_bytes(bs.try_into().unwrap()))
}

fn read_cstr(snap: &DumpSnapshot, bin: &[u8], addr: u64) -> Result<String> {
    let r = snap
        .regions
        .iter()
        .find(|r| r.start <= addr && addr < r.start + r.size)
        .with_context(|| format!("C-string address 0x{addr:x} not mapped in snapshot"))?;
    let off = r.bin_off + (addr - r.start) as usize;
    let max_len = ((r.start + r.size) - addr) as usize;
    let slice = &bin[off..off + max_len];
    let nul = slice
        .iter()
        .position(|&b| b == 0)
        .with_context(|| format!("unterminated C-string at 0x{addr:x}"))?;
    Ok(String::from_utf8_lossy(&slice[..nul]).into_owned())
}

/// Format a QEMU entry snapshot (`entry.snapshot.{json,bin}`) into canonical hex text.
pub fn format_snapshot_text(
    snap: &DumpSnapshot,
    bin: &[u8],
    extra_hex: &[(u64, usize)],
) -> Result<String> {
    ensure!(bin.len() == snap.bin.size, "bin size {} != {}", bin.len(), snap.bin.size);
    let mut out = String::new();
    writeln!(out, "regions:")?;
    for r in &snap.regions {
        let end = r.start + r.size;
        if r.kind == "load" {
            let bs = &bin[r.bin_off..r.bin_off + (r.size as usize)];
            writeln!(
                out,
                "  0x{:x}-0x{:x} {} load  size=0x{:x} fnv64=0x{:x}",
                r.start, end, r.perm, r.size, fnv1a64(bs)
            )?;
        } else if r.kind == "stack" {
            writeln!(out, "  0x{:x}-0x{:x} {} stack size=0x{:x}", r.start, end, r.perm, r.size)?;
        }
    }

    writeln!(out, "registers & brk:")?;
    let x_summary = if snap.regs.x.iter().all(|&v| v == 0) {
        "x0..x30=0x0".to_string()
    } else {
        snap.regs
            .x
            .iter()
            .enumerate()
            .filter(|&(_, &v)| v != 0)
            .map(|(i, v)| format!("x{i}=0x{v:x}"))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let tpidr = snap.regs.tpidr_el0.unwrap_or(0);
    writeln!(
        out,
        "  pc=0x{:x} {} tpidr_el0=0x{:x} brk=0x{:x}",
        snap.regs.pc, x_summary, tpidr, snap.brk_start
    )?;

    writeln!(out, "stack (from sp):")?;
    let sp = snap.regs.sp;
    let argc = read_u64(snap, bin, sp)? as usize;
    writeln!(out, "  [sp+0x0] 0x{argc:x}  (argc={argc})")?;
    for i in 0..argc {
        let off = 8 * (1 + i);
        let ptr = read_u64(snap, bin, sp + off as u64)?;
        let s = read_cstr(snap, bin, ptr)?;
        writeln!(out, "  [sp+0x{off:x}] 0x{ptr:x} (\"{s}\")  (argv[{i}])")?;
    }
    let argv_null_off = 8 * (1 + argc);
    let argv_null = read_u64(snap, bin, sp + argv_null_off as u64)?;
    writeln!(out, "  [sp+0x{argv_null_off:x}] 0x{argv_null:x}  (argv[{argc}] = NULL)")?;

    let mut envc = 0usize;
    loop {
        let off = 8 * (argc + 2 + envc);
        let ptr = read_u64(snap, bin, sp + off as u64)?;
        if ptr == 0 {
            writeln!(out, "  [sp+0x{off:x}] 0x0  (envp[{envc}] = NULL)")?;
            break;
        }
        let s = read_cstr(snap, bin, ptr)?;
        writeln!(out, "  [sp+0x{off:x}] 0x{ptr:x} (\"{s}\")  (envp[{envc}])")?;
        envc += 1;
        if envc > 256 {
            bail!("envp exceeded 256 entries without NULL");
        }
    }

    writeln!(out, "  auxv:")?;
    let auxv_base = sp + (8 * (argc + 2 + envc + 1)) as u64;
    let mut auxv = Vec::new();
    for i in 0..64u64 {
        let t = read_u64(snap, bin, auxv_base + 16 * i)?;
        let v = read_u64(snap, bin, auxv_base + 16 * i + 8)?;
        if t == 0 {
            break;
        }
        auxv.push((t, v));
    }
    const CANONICAL_AUXV: &[(u64, &str)] = &[
        (3, "AT_PHDR"),
        (4, "AT_PHENT"),
        (5, "AT_PHNUM"),
        (6, "AT_PAGESZ"),
        (7, "AT_BASE"),
        (8, "AT_FLAGS"),
        (9, "AT_ENTRY"),
        (11, "AT_UID"),
        (12, "AT_EUID"),
        (13, "AT_GID"),
        (14, "AT_EGID"),
        (15, "AT_PLATFORM"),
        (16, "AT_HWCAP"),
        (17, "AT_CLKTCK"),
        (23, "AT_SECURE"),
        (25, "AT_RANDOM"),
        (26, "AT_HWCAP2"),
        (31, "AT_EXECFN"),
    ];
    for &(tag, name) in CANONICAL_AUXV {
        let val = auxv
            .iter()
            .find(|&&(t, _)| t == tag)
            .map(|&(_, v)| v)
            .with_context(|| format!("missing auxv tag {name} ({tag})"))?;
        if tag == 15 || tag == 31 {
            let s = read_cstr(snap, bin, val)?;
            writeln!(out, "    {name} ({tag}) = 0x{val:x} (\"{s}\")")?;
        } else if tag == 25 {
            let rand_bs = read_bytes(snap, bin, val, 16)?;
            let hex16: String = rand_bs.iter().map(|b| format!("{b:02x}")).collect();
            writeln!(out, "    {name} ({tag}) = 0x{val:x} (0x{hex16})")?;
        } else {
            writeln!(out, "    {name} ({tag}) = 0x{val:x}")?;
        }
    }
    writeln!(out, "    AT_NULL (0) = 0x0")?;

    writeln!(out, "bytes:")?;
    let mut ranges = vec![(snap.regs.pc, 32usize)];
    ranges.extend_from_slice(extra_hex);
    for (vaddr, len) in ranges {
        writeln!(out, "  @0x{vaddr:x} ({len} B):")?;
        let bs = read_bytes(snap, bin, vaddr, len)?;
        for (i, chunk) in bs.chunks(16).enumerate() {
            let row_addr = vaddr + (i * 16) as u64;
            let row_hex = chunk.iter().map(|b| format!("{b:02x}")).collect::<Vec<_>>().join(" ");
            writeln!(out, "    0x{row_addr:x}: {row_hex}")?;
        }
    }
    Ok(out)
}

pub fn run(args: DumpStateArgs) -> Result<()> {
    let raw = fs::read_to_string(&args.snapshot_json)
        .with_context(|| format!("reading {}", args.snapshot_json.display()))?;
    let snap: DumpSnapshot = serde_json::from_str(&raw)
        .with_context(|| format!("parsing {}", args.snapshot_json.display()))?;
    let parent = args.snapshot_json.parent().unwrap_or_else(|| std::path::Path::new("."));
    let bin_path = parent.join(&snap.bin.file);
    let bin = fs::read(&bin_path).with_context(|| format!("reading {}", bin_path.display()))?;
    let mut extra_hex = Vec::new();
    for spec in &args.hex_ranges {
        extra_hex.push(parse_hex_range(spec)?);
    }
    let text = format_snapshot_text(&snap, &bin, &extra_hex)?;
    print!("{text}");
    Ok(())
}

pub fn run_poke(args: PokeArgs) -> Result<()> {
    let raw = fs::read_to_string(&args.snapshot_json)
        .with_context(|| format!("reading {}", args.snapshot_json.display()))?;
    let snap: DumpSnapshot = serde_json::from_str(&raw)
        .with_context(|| format!("parsing {}", args.snapshot_json.display()))?;
    let vaddr = parse_u64_auto(&args.vaddr)?;
    let hex = args.hex_bytes.strip_prefix("0x").unwrap_or(&args.hex_bytes);
    ensure!(hex.len().is_multiple_of(2), "hex_bytes must have even length");
    let patch: Vec<u8> = (0..hex.len() / 2)
        .map(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16))
        .collect::< std::result::Result<_, _>>()?;
    let r = snap
        .regions
        .iter()
        .find(|r| r.start <= vaddr && vaddr + (patch.len() as u64) <= r.start + r.size)
        .with_context(|| format!("address 0x{vaddr:x} not mapped in snapshot"))?;
    let parent = args.snapshot_json.parent().unwrap_or_else(|| std::path::Path::new("."));
    let bin_path = parent.join(&snap.bin.file);
    let mut bin = fs::read(&bin_path).with_context(|| format!("reading {}", bin_path.display()))?;
    let off = r.bin_off + (vaddr - r.start) as usize;
    bin[off..off + patch.len()].copy_from_slice(&patch);
    fs::write(&bin_path, &bin).with_context(|| format!("writing {}", bin_path.display()))?;
    Ok(())
}
