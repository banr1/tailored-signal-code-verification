// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Process snapshots of an AArch64 ELF under qemu-user (`[CASE-STUDIES TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[CASE-STUDIES TCB]` — the snapshot is the initial machine state a process-snapshot
//!   proof starts from (trusted only by snapshot-based proofs, outside the core engine `[tcb]`).
//!   This file decides which memory is dumped and checks the facts those proofs rely on.
//! - **Purpose:** `proc-snapshot snapshot` spawns `qemu-aarch64 -g <port> -seed 0 -0 <argv0> [-E <env>...] <elf> [<arg>...]` with
//!   a cleared host environment, attaches over GDB RSP, and writes `entry.snapshot.{json,bin}` at
//!   the first guest instruction (pc == `e_entry`) plus (unless `--entry-only` is set)
//!   `<stop>.snapshot.{json,bin}` at a breakpoint on the stop symbol (default `main`).
//!   Runs are reproducible: host ASLR is off (`ADDR_NO_RANDOMIZE`) and `-seed 0` fixes the
//!   guest's `AT_RANDOM` bytes (the remaining run-to-run difference is the host tid libc
//!   stores before `main`).
//!   Regions: every PT_LOAD rounded out to 4 KiB pages (perm from `p_flags`), the stack
//!   `[pagefloor(sp) - 16 KiB, top)` (top probed page by page), and the brk area if it holds
//!   readable pages. Checks: pc values, stack layout (`argc`, `argv`, `envp`) and unmapped gap
//!   pages at entry, same stack top at both stops, a non-zero `tpidr_el0` points into a region,
//!   and every non-writable region is byte-identical between the two snapshots.
//!
//! # Key Types & Functions
//! - [`SnapshotArgs`], [`run`]: CLI entry. [`Snapshot`]: the JSON schema
//!   (`arm64-proc-snapshot/1`). [`load_regions`]: PT_LOAD -> page-rounded regions.
//!
//! # When to Read This File
//! - Read this file to audit the snapshot schema, region selection, and consistency checks.

use crate::elf::{ElfInfo, Symbol};
use crate::rsp::{Rsp, TargetReg};
use anyhow::{Context, Result, bail, ensure};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

const PAGE: u64 = 0x1000;
const STACK_BELOW_SP: u64 = 0x4000;
const PROBE_CAP: u64 = 1 << 20;

#[derive(clap::Args, Debug)]
pub struct SnapshotArgs {
    /// Static non-PIE AArch64 ELF to run.
    #[arg(long)]
    pub elf: PathBuf,
    /// qemu-aarch64 binary (see `scripts/fetch-qemu-aarch64`).
    #[arg(long)]
    pub qemu: PathBuf,
    /// Output directory for `*.snapshot.{json,bin}`.
    #[arg(long)]
    pub out_dir: PathBuf,
    /// Symbol to stop at for the second snapshot (ignored when `--entry-only` is set).
    #[arg(long, default_value = "main")]
    pub stop_symbol: String,
    /// Stop after writing `entry.snapshot.{json,bin}` at `e_entry`.
    #[arg(long)]
    pub entry_only: bool,
    /// Guest argv[0] (default: the ELF file name).
    #[arg(long)]
    pub argv0: Option<String>,
    /// Additional guest `argv[1..]` arguments (repeatable).
    #[arg(long = "arg", allow_hyphen_values = true)]
    pub args: Vec<String>,
    /// Guest `KEY=VAL` environment variables passed via `qemu-aarch64 -E` (repeatable).
    #[arg(long = "env", allow_hyphen_values = true)]
    pub envs: Vec<String>,
    /// Input files the run depends on; recorded with their SHA-256.
    #[arg(long)]
    pub input: Vec<PathBuf>,
}

#[derive(Serialize, Clone)]
pub struct FileHash {
    pub path: String,
    pub sha256: String,
}

#[derive(Serialize, Clone)]
pub struct Runner {
    pub kind: &'static str,
    pub version: String,
    pub sha256: String,
}

#[derive(Serialize, Clone)]
pub struct ElfRef {
    pub path: String,
    pub sha256: String,
    pub entry: u64,
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub start: u64,
    pub size: u64,
    pub perm: String,
    pub kind: &'static str,
    #[serde(rename = "binOff")]
    pub bin_off: u64,
}

#[derive(Serialize, Clone)]
pub struct Regs {
    pub x: Vec<u64>,
    pub sp: u64,
    pub pc: u64,
    pub cpsr: u64,
    pub tpidr_el0: Option<u64>,
}

#[derive(Serialize)]
pub struct BinRef {
    pub file: String,
    pub size: u64,
    pub sha256: String,
}

/// `<stop>.snapshot.json` (field order is the on-disk key order).
#[derive(Serialize)]
pub struct Snapshot {
    pub schema: &'static str,
    pub stop: String,
    pub runner: Runner,
    pub argv: Vec<String>,
    pub envp: Vec<String>,
    pub elf: ElfRef,
    pub inputs: Vec<FileHash>,
    pub regions: Vec<Region>,
    #[serde(rename = "brkStart")]
    pub brk_start: u64,
    pub regs: Regs,
    pub symbols: Vec<Symbol>,
    pub bin: BinRef,
}

fn sha256_hex(data: &[u8]) -> String {
    Sha256::digest(data)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

fn hash_file(p: &Path) -> Result<FileHash> {
    let data = std::fs::read(p).with_context(|| format!("reading {}", p.display()))?;
    Ok(FileHash {
        path: p.display().to_string(),
        sha256: sha256_hex(&data),
    })
}

/// PT_LOAD segments rounded out to pages, ascending; errors if two overlap after rounding.
pub fn load_regions(elf: &ElfInfo) -> Result<Vec<Region>> {
    let mut rs: Vec<Region> = elf
        .segments
        .iter()
        .map(|s| {
            let start = s.vaddr / PAGE * PAGE;
            let end = (s.vaddr + s.memsz).div_ceil(PAGE) * PAGE;
            Region {
                start,
                size: end - start,
                perm: s.perm(),
                kind: "load",
                bin_off: 0,
            }
        })
        .collect();
    rs.sort_by_key(|r| r.start);
    for w in rs.windows(2) {
        ensure!(
            w[0].start + w[0].size <= w[1].start,
            "PT_LOAD pages overlap after 4 KiB rounding: {:#x}+{:#x} and {:#x}",
            w[0].start,
            w[0].size,
            w[1].start
        );
    }
    Ok(rs)
}

/// Kills and reaps qemu on drop (normal exit and every error path).
struct QemuGuard(Child);

impl Drop for QemuGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Disables host ASLR for this process and its children (`setarch -R`), so qemu-user places the
/// guest stack and mmap areas at the same addresses on every run.
fn disable_aslr() -> Result<()> {
    // SAFETY: personality(2) only reads/sets this process's execution domain flags.
    let cur = unsafe { libc::personality(0xffff_ffff) };
    ensure!(cur != -1, "personality query failed");
    let want = (cur as libc::c_ulong) | libc::ADDR_NO_RANDOMIZE as libc::c_ulong;
    ensure!(
        unsafe { libc::personality(want) } != -1,
        "personality(ADDR_NO_RANDOMIZE) failed"
    );
    Ok(())
}

fn spawn_qemu(
    qemu: &Path,
    argv0: &str,
    elf: &Path,
    args: &[String],
    envs: &[String],
) -> Result<(QemuGuard, Rsp)> {
    disable_aslr()?;
    for _ in 0..5 {
        let port = TcpListener::bind("127.0.0.1:0")?.local_addr()?.port();
        let mut cmd = Command::new(qemu);
        cmd.env_clear()
            .args(["-g", &port.to_string(), "-seed", "0", "-0", argv0]);
        // `qemu-aarch64` inserts each `-E` at the head of its `envlist`, so pass in reverse
        // to preserve the caller's `envs` order in the guest `envp` array.
        for e in envs.iter().rev() {
            cmd.args(["-E", e]);
        }
        let child = cmd
            .arg(elf)
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .spawn()
            .with_context(|| format!("spawning {}", qemu.display()))?;
        let mut guard = QemuGuard(child);
        let deadline = Instant::now() + Duration::from_secs(10);
        while Instant::now() < deadline {
            if let Ok(sock) = TcpStream::connect(("127.0.0.1", port)) {
                return Ok((guard, Rsp::new(sock)?));
            }
            if guard.0.try_wait()?.is_some() {
                break; // e.g. the port was taken in the meantime; retry with a new one
            }
            std::thread::sleep(Duration::from_millis(20));
        }
    }
    bail!("could not attach to the qemu gdbstub")
}

/// Register numbers of the snapshot registers, located by name in the target description.
struct RegMap {
    x: Vec<u32>,
    sp: u32,
    pc: u32,
    cpsr: u32,
    tpidr: Option<u32>,
    all: Vec<TargetReg>,
}

impl RegMap {
    fn new(all: Vec<TargetReg>) -> Result<Self> {
        let find = |n: &str| all.iter().find(|r| r.name == n).map(|r| r.regnum);
        let need = |n: &str| find(n).with_context(|| format!("target XML lacks register `{n}`"));
        let x = (0..31)
            .map(|i| need(&format!("x{i}")))
            .collect::<Result<_>>()?;
        let (sp, pc, cpsr) = (need("sp")?, need("pc")?, need("cpsr")?);
        // `tpidr` from org.gnu.gdb.aarch64.tls, else qemu's system-register feature `TPIDR_EL0`.
        let tpidr = find("tpidr")
            .or_else(|| find("TPIDR_EL0"))
            .or_else(|| find("tpidr_el0"));
        Ok(Self {
            x,
            sp,
            pc,
            cpsr,
            tpidr,
            all,
        })
    }

    fn read(&self, rsp: &mut Rsp) -> Result<Regs> {
        let x: Vec<u64> = self
            .x
            .iter()
            .map(|&n| rsp.read_reg(n))
            .collect::<Result<_>>()?;
        let regs = Regs {
            x,
            sp: rsp.read_reg(self.sp)?,
            pc: rsp.read_reg(self.pc)?,
            cpsr: rsp.read_reg(self.cpsr)?,
            tpidr_el0: self.tpidr.map(|n| rsp.read_reg(n)).transpose()?,
        };
        // Cross-check `p` against the `g` block (registers laid out in regnum order).
        let g = rsp.read_all_regs()?;
        let mut sorted = self.all.clone();
        sorted.sort_by_key(|r| r.regnum);
        let mut off = 0usize;
        for (i, r) in sorted.iter().enumerate() {
            let len = (r.bitsize / 8) as usize;
            if r.regnum as usize != i || off + len > g.len() {
                break;
            }
            if len <= 8 && (r.regnum <= self.cpsr) {
                let v = g[off..off + len]
                    .iter()
                    .rev()
                    .fold(0u64, |a, &b| (a << 8) | u64::from(b));
                ensure!(
                    v == rsp.read_reg(r.regnum)?,
                    "`g` and `p` disagree on {}",
                    r.name
                );
            }
            off += len;
        }
        Ok(regs)
    }
}

fn read_region(rsp: &mut Rsp, start: u64, size: u64) -> Result<Vec<u8>> {
    rsp.read_mem(start, size as usize)?
        .with_context(|| format!("memory [{start:#x}, {:#x}) is not readable", start + size))
}

/// First unreadable page boundary at or above `from` (page aligned), probing up to `PROBE_CAP`.
fn probe_top(rsp: &mut Rsp, from: u64) -> Result<u64> {
    let mut p = from;
    while p < from + PROBE_CAP {
        if rsp.read_mem(p, 1)?.is_none() {
            return Ok(p);
        }
        p += PAGE;
    }
    bail!(
        "readable memory continues past {:#x}; refusing to guess a region end",
        from + PROBE_CAP
    )
}

struct Capture {
    regions: Vec<Region>,
    bytes: Vec<Vec<u8>>,
    regs: Regs,
    stack_top: u64,
}

fn capture(rsp: &mut Rsp, map: &RegMap, loads: &[Region], brk_start: u64) -> Result<Capture> {
    let regs = map.read(rsp)?;
    let sp_page = regs.sp / PAGE * PAGE;
    let stack_top = probe_top(rsp, sp_page)?;
    let mut regions = loads.to_vec();
    let stack_start = sp_page - STACK_BELOW_SP;
    regions.push(Region {
        start: stack_start,
        size: stack_top - stack_start,
        perm: "rw-".into(),
        kind: "stack",
        bin_off: 0,
    });
    if rsp.read_mem(brk_start, 1)?.is_some() {
        let end = probe_top(rsp, brk_start)?;
        let r = Region {
            start: brk_start,
            size: end - brk_start,
            perm: "rw-".into(),
            kind: "brk",
            bin_off: 0,
        };
        regions.push(r);
    }
    regions.sort_by_key(|r| r.start);
    let mut off = 0;
    for w in regions.windows(2) {
        ensure!(
            w[0].start + w[0].size <= w[1].start,
            "regions overlap: {:?} / {:?}",
            w[0],
            w[1]
        );
    }
    let mut bytes = Vec::new();
    for r in &mut regions {
        r.bin_off = off;
        off += r.size;
        bytes.push(read_region(rsp, r.start, r.size)?);
    }
    if let Some(t) = regs.tpidr_el0.filter(|&t| t != 0) {
        ensure!(
            regions.iter().any(|r| r.start <= t && t < r.start + r.size),
            "tpidr_el0 = {t:#x} points outside every snapshot region (TLS not captured)"
        );
    }
    Ok(Capture {
        regions,
        bytes,
        regs,
        stack_top,
    })
}

fn u64_at(c: &Capture, addr: u64) -> Result<u64> {
    let b = byte_range(c, addr, 8)?;
    Ok(u64::from_le_bytes(b.try_into()?))
}

fn byte_range(c: &Capture, addr: u64, len: u64) -> Result<&[u8]> {
    for (r, b) in c.regions.iter().zip(&c.bytes) {
        if r.start <= addr && addr + len <= r.start + r.size {
            let o = (addr - r.start) as usize;
            return Ok(&b[o..o + len as usize]);
        }
    }
    bail!("address {addr:#x} not in snapshot")
}

/// Checks the exec-entry stack: `argc`, `argv[0..argc]`, `argv[argc] == 0`, `envp[0..envc]`,
/// and `envp[envc] == 0`.
fn check_initial_stack(c: &Capture, argv: &[String], envp: &[String]) -> Result<()> {
    let sp = c.regs.sp;
    let argc = u64_at(c, sp)?;
    ensure!(
        argc == argv.len() as u64,
        "argc at entry is {argc}, expected {}",
        argv.len()
    );
    for (i, arg) in argv.iter().enumerate() {
        let s = u64_at(c, sp + 8 * (1 + i as u64))?;
        let got = byte_range(c, s, arg.len() as u64 + 1)?;
        ensure!(
            got[..arg.len()] == *arg.as_bytes() && got[arg.len()] == 0,
            "argv[{i}] is not {arg:?}"
        );
    }
    let argv_null_off = 8 * (1 + argv.len() as u64);
    ensure!(
        u64_at(c, sp + argv_null_off)? == 0,
        "argv not NULL-terminated after argv[{}]",
        argv.len() - 1
    );
    let envp_base = sp + argv_null_off + 8;
    for (i, env) in envp.iter().enumerate() {
        let s = u64_at(c, envp_base + 8 * (i as u64))?;
        let got = byte_range(c, s, env.len() as u64 + 1)?;
        ensure!(
            got[..env.len()] == *env.as_bytes() && got[env.len()] == 0,
            "envp[{i}] is not {env:?}"
        );
    }
    ensure!(
        u64_at(c, envp_base + 8 * (envp.len() as u64))? == 0,
        "envp not NULL-terminated"
    );
    Ok(())
}

/// Probes boundary pages outside the `PT_LOAD` envelope (`0x0`, `loads[0].start - PAGE`,
/// `brk_start` at entry, and `stack_top`) over the GDB stub to verify that QEMU leaves them
/// unmapped (`!PAGE_VALID`).
///
/// Note on inter-segment gaps inside `[loads[0].start, brk_start)`: `qemu-aarch64`'s
/// `load_elf_image` (`linux-user/elfload.c`) first reserves the entire `[loaddr, hiaddr)`
/// envelope with `target_mmap(loaddr, hiaddr - loaddr, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0)`
/// before over-mapping each `PT_LOAD` segment. That reservation marks inter-segment gaps as
/// `PAGE_VALID` with `PROT_NONE` (`---`). When GDB RSP sends an `m` packet (`cpu_memory_rw_debug`),
/// QEMU rejects non-`PAGE_VALID` addresses immediately, but for `PAGE_VALID` pages without
/// `PAGE_READ` it falls back to `pread64` on `/proc/self/mem`, which on upstream Linux kernels
/// uses `FOLL_FORCE` and reads `0x00` from anonymous `PROT_NONE` VMAs even though guest accesses
/// fault with `SIGSEGV`. Inter-segment gaps are excluded from `Snapshot.regions` by
/// `load_regions` and checked for absence in the Lean differential harness.
fn check_entry_unmapped_gaps(
    rsp: &mut Rsp,
    loads: &[Region],
    brk_start: u64,
    stack_top: u64,
) -> Result<()> {
    ensure!(
        rsp.read_mem(0, 1)?.is_none(),
        "null page 0x0 is unexpectedly readable at entry"
    );
    if let Some(first) = loads.first()
        && first.start >= PAGE
    {
        let prev_page = first.start - PAGE;
        ensure!(
            rsp.read_mem(prev_page, 1)?.is_none(),
            "unmapped page {prev_page:#x} before first PT_LOAD {:#x} is unexpectedly readable",
            first.start
        );
    }
    ensure!(
        rsp.read_mem(brk_start, 1)?.is_none(),
        "brk_start {brk_start:#x} is unexpectedly readable at e_entry"
    );
    ensure!(
        rsp.read_mem(stack_top, 1)?.is_none(),
        "stack_top {stack_top:#x} is unexpectedly readable at e_entry"
    );
    Ok(())
}

fn write_snapshot(out: &Path, stop: &str, c: &Capture, base: &Snapshot) -> Result<()> {
    let bin: Vec<u8> = c.bytes.concat();
    let file = format!("{stop}.snapshot.bin");
    std::fs::write(out.join(&file), &bin)?;
    let snap = Snapshot {
        schema: base.schema,
        stop: if stop == "entry" {
            "exec-entry".into()
        } else {
            stop.into()
        },
        runner: base.runner.clone(),
        argv: base.argv.clone(),
        envp: base.envp.clone(),
        elf: base.elf.clone(),
        inputs: base.inputs.clone(),
        regions: c.regions.clone(),
        brk_start: base.brk_start,
        regs: c.regs.clone(),
        symbols: base.symbols.clone(),
        bin: BinRef {
            file,
            size: bin.len() as u64,
            sha256: sha256_hex(&bin),
        },
    };
    let json = serde_json::to_string_pretty(&snap)? + "\n";
    std::fs::write(out.join(format!("{stop}.snapshot.json")), json)?;
    Ok(())
}

/// Frozen (non-writable) regions must not change between the two stops; reports writable diffs.
fn compare(a: &Capture, b: &Capture, stop: &str) -> Result<()> {
    for (ra, ba) in a.regions.iter().zip(&a.bytes) {
        let Some(i) = b
            .regions
            .iter()
            .position(|r| r.start == ra.start && r.kind == ra.kind)
        else {
            ensure!(ra.kind == "stack", "region {ra:?} missing at {stop}");
            continue;
        };
        let (rb, bb) = (&b.regions[i], &b.bytes[i]);
        if !ra.perm.contains('w') {
            ensure!(
                ra.size == rb.size && ba == bb,
                "frozen region {:#x} ({}) changed between entry and {stop}",
                ra.start,
                ra.perm
            );
            continue;
        }
        if ra.kind == "stack" {
            continue; // reported below over the common range
        }
        let n = ba.iter().zip(bb).filter(|(x, y)| x != y).count();
        eprintln!(
            "proc-snapshot: writable {} {:#x}+{:#x}: {n} bytes changed entry -> {stop}",
            ra.kind, ra.start, ra.size
        );
    }
    let [sa, sb] = [a, b].map(|c| {
        c.regions
            .iter()
            .zip(&c.bytes)
            .find(|(r, _)| r.kind == "stack")
            .unwrap()
    });
    let lo = sa.0.start.max(sb.0.start);
    let hi = a.stack_top;
    let n = (lo..hi)
        .filter(|&p| sa.1[(p - sa.0.start) as usize] != sb.1[(p - sb.0.start) as usize])
        .count();
    eprintln!("proc-snapshot: stack [{lo:#x}, {hi:#x}): {n} bytes changed entry -> {stop}");
    Ok(())
}

pub fn run(args: SnapshotArgs) -> Result<()> {
    let elf_bytes =
        std::fs::read(&args.elf).with_context(|| format!("reading {}", args.elf.display()))?;
    let elf = ElfInfo::parse(&elf_bytes)?;
    let loads = load_regions(&elf)?;
    let brk_start = loads
        .iter()
        .map(|r| r.start + r.size)
        .max()
        .context("ELF has no PT_LOAD")?;
    let stop_addr = if args.entry_only {
        None
    } else {
        Some(elf.symbol(&args.stop_symbol)?)
    };
    let argv0 = match &args.argv0 {
        Some(a) => a.clone(),
        None => args
            .elf
            .file_name()
            .context("ELF path has no file name")?
            .to_string_lossy()
            .into_owned(),
    };
    let mut full_argv = vec![argv0.clone()];
    full_argv.extend(args.args.iter().cloned());
    let ver = Command::new(&args.qemu)
        .env_clear()
        .arg("--version")
        .output()?;
    ensure!(
        ver.status.success(),
        "{} --version failed",
        args.qemu.display()
    );
    let base = Snapshot {
        schema: "arm64-proc-snapshot/1",
        stop: String::new(),
        runner: Runner {
            kind: "qemu-user-gdbstub",
            version: String::from_utf8(ver.stdout)?
                .lines()
                .next()
                .unwrap_or("")
                .to_string(),
            sha256: hash_file(&args.qemu)?.sha256,
        },
        argv: full_argv.clone(),
        envp: args.envs.clone(),
        elf: ElfRef {
            path: args.elf.display().to_string(),
            sha256: sha256_hex(&elf_bytes),
            entry: elf.entry,
        },
        inputs: args
            .input
            .iter()
            .map(|p| hash_file(p))
            .collect::<Result<_>>()?,
        regions: Vec::new(),
        brk_start,
        regs: Regs {
            x: Vec::new(),
            sp: 0,
            pc: 0,
            cpsr: 0,
            tpidr_el0: None,
        },
        symbols: elf.symbols.clone(),
        bin: BinRef {
            file: String::new(),
            size: 0,
            sha256: String::new(),
        },
    };
    std::fs::create_dir_all(&args.out_dir)?;

    let (_guard, mut rsp) = spawn_qemu(&args.qemu, &argv0, &args.elf, &args.args, &args.envs)?;
    rsp.handshake()?;
    ensure!(rsp.halt_reason()? == 5, "initial stop is not SIGTRAP");
    let map = RegMap::new(rsp.target_regs()?)?;
    if map.tpidr.is_none() {
        eprintln!("proc-snapshot: warning: target XML exposes no tpidr register; tpidr_el0 = null");
    }

    let entry = capture(&mut rsp, &map, &loads, brk_start)?;
    ensure!(
        entry.regs.pc == elf.entry,
        "entry pc {:#x} != e_entry {:#x}",
        entry.regs.pc,
        elf.entry
    );
    check_entry_unmapped_gaps(&mut rsp, &loads, brk_start, entry.stack_top)?;
    check_initial_stack(&entry, &full_argv, &args.envs)?;
    write_snapshot(&args.out_dir, "entry", &entry, &base)?;

    let Some(stop_addr) = stop_addr else {
        rsp.kill()?;
        eprintln!(
            "proc-snapshot: wrote entry snapshot to {}",
            args.out_dir.display()
        );
        return Ok(());
    };

    rsp.set_breakpoint(stop_addr)?;
    ensure!(
        rsp.cont()? == 5,
        "stop at `{}` is not SIGTRAP",
        args.stop_symbol
    );
    let stop = capture(&mut rsp, &map, &loads, brk_start)?;
    ensure!(
        stop.regs.pc == stop_addr,
        "stopped at {:#x}, not `{}` = {stop_addr:#x}",
        stop.regs.pc,
        args.stop_symbol
    );
    ensure!(
        stop.stack_top == entry.stack_top,
        "stack top moved: {:#x} -> {:#x}",
        entry.stack_top,
        stop.stack_top
    );
    write_snapshot(&args.out_dir, &args.stop_symbol, &stop, &base)?;
    compare(&entry, &stop, &args.stop_symbol)?;
    rsp.kill()?;
    eprintln!(
        "proc-snapshot: wrote entry and {} snapshots to {}",
        args.stop_symbol,
        args.out_dir.display()
    );
    Ok(())
}
