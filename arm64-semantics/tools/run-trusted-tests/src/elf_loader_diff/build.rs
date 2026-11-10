// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Corpus builder for `Arm64/Testing/ElfLoaderDiff/` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted host test infrastructure under
//!   `tools/run-trusted-tests`).
//! - **Purpose:** Compiles the static AArch64 (`ET_EXEC`) test corpus (and rejected fail-closed
//!   ELF variants) from `Arm64/Testing/ElfLoaderDiff/src/` using:
//!   - the pinned zig's integrated assembler (`zig clang -cc1as`, else `llvm-mc`) + the pinned
//!     Rust toolchain's `ld.lld` (hand-written assembly and custom linker-script layouts: multiple RW
//!     segments, mid-page `p_filesz < p_memsz` / `p_filesz == p_memsz`, `PT_TLS`, `PT_GNU_RELRO`),
//!   - `zig cc -target aarch64-linux-musl -static` at `-O0` and `-O2`,
//!   - `rustc --target=aarch64-unknown-linux-musl` (`no_std` and full `std` with `PT_TLS` + 64 KiB
//!     `.bss`),
//!   - `GOOS=linux GOARCH=arm64 CGO_ENABLED=0 go build` (Go static binary with unusual segment
//!     layout and `PT_NOTE`),
//!   - `aarch64-linux-gnu-gcc -static` (optional when installed on the host).

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail, ensure};
use object::elf::{ELFCLASS64, EM_AARCH64, PF_R, PT_LOAD};
use object::read::elf::{FileHeader, ProgramHeader};
use object::Endianness;
use walkdir::WalkDir;

use crate::process_e2e::build::PINNED_RUST_TOOLCHAIN;

use super::fixture_dir;

/// Committed small (< 16 KiB) binaries in `Arm64/Testing/ElfLoaderDiff/bin/`.
pub const COMMITTED_BINARIES: &[&str] = &[
    "tiny_asm.elf",
    "layout_multi_rw.elf",
    "layout_midpage_bss.elf",
    "layout_tls_relro.elf",
    "c_zig_o0.elf",
    "c_zig_o2.elf",
    "rust_nostd_tls_bss.elf",
    "layout_text_only.elf",
    "layout_entry_deep.elf",
    "layout_bss_page_end.elf",
    "layout_filesz_page_end.elf",
    "layout_large_bss.elf",
    "layout_palign_4k.elf",
    "layout_palign_16k.elf",
    "layout_palign_2m.elf",
    "layout_unaligned_straddle.elf",
    "layout_phdr_unmapped.elf",
    "layout_pure_bss_midpage.elf",
    "layout_many_loads.elf",
    "layout_many_sections.elf",
    "layout_high_vaddr.elf",
    "layout_rw_file_tail.elf",
    "reject_pie.elf",
    "reject_dynamic.elf",
    "reject_relocatable.elf",
    "reject_wx_segment.elf",
    "reject_exec_stack.elf",
    "reject_ro_bss.elf",
];

/// One additional hand-written assembly + `ld.lld` positive layout binary.
struct ExtraLayout {
    /// Output file name in `bin/`.
    out: &'static str,
    /// Assembly source stem in `src/` (`<src>.s`).
    src: &'static str,
    /// Linker script stem in `src/` (`<ld>.ld`), or `None` for `ld.lld`'s default layout.
    ld: Option<&'static str>,
    /// `-z max-page-size=` value (also the `p_align` of every `PT_LOAD` without a linker script).
    max_page_size: &'static str,
    /// Keep `.symtab` / non-alloc sections (no `--strip-all`).
    keep_symbols: bool,
}

impl ExtraLayout {
    /// `src/<name>.s` linked with `src/<name>.ld` and 4 KiB `max-page-size` into `bin/<name>.elf`.
    const fn scripted(out: &'static str, name: &'static str) -> Self {
        Self { out, src: name, ld: Some(name), max_page_size: "4096", keep_symbols: false }
    }

    const fn keep_symbols(self) -> Self {
        Self { keep_symbols: true, ..self }
    }
}

/// Additional positive layouts (see `Arm64/Testing/ElfLoaderDiff/README.md` for what each tests).
const EXTRA_LAYOUTS: &[ExtraLayout] = &[
    ExtraLayout::scripted("layout_text_only.elf", "layout_text_only"),
    ExtraLayout::scripted("layout_entry_deep.elf", "layout_entry_deep"),
    ExtraLayout::scripted("layout_bss_page_end.elf", "layout_bss_page_end"),
    ExtraLayout::scripted("layout_filesz_page_end.elf", "layout_filesz_page_end"),
    ExtraLayout::scripted("layout_large_bss.elf", "layout_large_bss"),
    // The same source in `ld.lld`'s default layout at three `max-page-size` / `p_align` values.
    ExtraLayout {
        out: "layout_palign_4k.elf",
        src: "layout_palign",
        ld: None,
        max_page_size: "0x1000",
        keep_symbols: false,
    },
    ExtraLayout {
        out: "layout_palign_16k.elf",
        src: "layout_palign",
        ld: None,
        max_page_size: "0x4000",
        keep_symbols: false,
    },
    ExtraLayout {
        out: "layout_palign_2m.elf",
        src: "layout_palign",
        ld: None,
        max_page_size: "0x200000",
        keep_symbols: false,
    },
    ExtraLayout::scripted("layout_unaligned_straddle.elf", "layout_unaligned_straddle"),
    ExtraLayout::scripted("layout_phdr_unmapped.elf", "layout_phdr_unmapped"),
    ExtraLayout::scripted("layout_pure_bss_midpage.elf", "layout_pure_bss_midpage"),
    ExtraLayout::scripted("layout_many_loads.elf", "layout_many_loads"),
    // `ld.lld`'s default layout; keep `.symtab` (40 `STT_FUNC` symbols).
    ExtraLayout {
        out: "layout_many_sections.elf",
        src: "layout_many_sections",
        ld: None,
        max_page_size: "4096",
        keep_symbols: true,
    },
    ExtraLayout::scripted("layout_high_vaddr.elf", "layout_high_vaddr"),
    // Keep `.rw_tail_marker` (no `--strip-all`) so non-zero bytes follow `p_offset + p_filesz`.
    ExtraLayout::scripted("layout_rw_file_tail.elf", "layout_rw_file_tail").keep_symbols(),
];

/// Paths to live on-demand binaries compiled into a staging directory during `elf_loader_diff run`.
#[derive(Debug, Clone)]
pub struct LiveExtraBinaries {
    pub rust_std_tls_bss: PathBuf,
    pub go_static: PathBuf,
    pub c_gcc_glibc: Option<PathBuf>,
    pub reject_zig_pie: PathBuf,
    pub reject_zig_dynamic: PathBuf,
}

fn find_rustc_and_lld() -> Result<(PathBuf, PathBuf, PathBuf)> {
    let rustc = if let Ok(rustup) = which::which("rustup")
        && let Ok(w) = Command::new(&rustup)
            .args(["which", "--toolchain", PINNED_RUST_TOOLCHAIN, "rustc"])
            .output()
        && w.status.success()
    {
        PathBuf::from(String::from_utf8_lossy(&w.stdout).trim())
    } else {
        which::which("rustc").context("`rustc` not found in PATH")?
    };
    let sysroot_out = Command::new(&rustc)
        .env_remove("RUSTUP_TOOLCHAIN")
        .args(["--print", "sysroot"])
        .output()
        .context("failed to invoke `rustc --print sysroot`")?;
    ensure!(sysroot_out.status.success(), "`rustc --print sysroot` failed");
    let sysroot = PathBuf::from(String::from_utf8_lossy(&sysroot_out.stdout).trim());
    // Prefer the pinned toolchain's bundled `gcc-ld/ld.lld` so the committed bytes do not depend
    // on the host's LLVM version; fall back to `ld.lld` on `PATH`.
    let rustlib = sysroot.join("lib").join("rustlib");
    let mut lld_candidates: Vec<PathBuf> = WalkDir::new(&rustlib)
        .into_iter()
        .filter_map(std::result::Result::ok)
        .map(|e| e.into_path())
        .filter(|p| p.is_file() && p.file_name().and_then(|s| s.to_str()) == Some("ld.lld"))
        .collect();
    lld_candidates.sort();
    let lld = match lld_candidates.into_iter().next() {
        Some(lld) => lld,
        None => which::which("ld.lld")
            .map_err(|_| anyhow!("`ld.lld` not found under {} or in PATH", rustlib.display()))?,
    };
    Ok((rustc, sysroot, lld))
}

/// AArch64 assembler for the hand-written `.s` sources: an LLVM integrated assembler invoked
/// with fixed flags, so the object bytes depend only on the assembler's LLVM version.
struct Assembler {
    program: PathBuf,
    prefix: Vec<&'static str>,
}

impl Assembler {
    /// Prefer the pinned zig's bundled clang (`zig clang -cc1as`), whose LLVM version is fixed by
    /// the zig pin; fall back to `llvm-mc` on `PATH`, whose output can differ across LLVM
    /// releases (e.g. `.fill` pattern truncation) and so may not match the committed bytes.
    fn find(zig: Option<&Path>) -> Result<Self> {
        if let Some(zig) = zig {
            return Ok(Self {
                program: zig.to_path_buf(),
                prefix: vec!["clang", "-cc1as", "-triple", "aarch64-unknown-linux-gnu", "-filetype", "obj"],
            });
        }
        let llvm_mc = which::which("llvm-mc")
            .context("neither `zig` nor `llvm-mc` found in PATH (install the pinned zig)")?;
        eprintln!(
            "WARNING: `zig` not found; assembling with {} (bytes may differ from the committed corpus)",
            llvm_mc.display()
        );
        Ok(Self {
            program: llvm_mc,
            prefix: vec!["-triple=aarch64-unknown-linux-gnu", "-filetype=obj"],
        })
    }
}

fn assemble_aarch64(asm: &Assembler, src_s: &Path, out_o: &Path) -> Result<()> {
    let out = Command::new(&asm.program)
        .args(&asm.prefix)
        .arg(src_s)
        .arg("-o")
        .arg(out_o)
        .output()
        .with_context(|| format!("invoking {} on {}", asm.program.display(), src_s.display()))?;
    if !out.status.success() {
        bail!(
            "assembler {} failed on {}:\n{}",
            asm.program.display(),
            src_s.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(())
}

fn link_lld(lld: &Path, args: &[&str], obj: &Path, out_elf: &Path) -> Result<()> {
    let out = Command::new(lld)
        .args(args)
        .arg(obj)
        .arg("-o")
        .arg(out_elf)
        .output()
        .with_context(|| format!("invoking ld.lld for {}", out_elf.display()))?;
    if !out.status.success() {
        bail!(
            "ld.lld failed for {}:\n{}",
            out_elf.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let mut perms = fs::metadata(out_elf)?.permissions();
    perms.set_mode(0o755);
    fs::set_permissions(out_elf, perms)?;
    Ok(())
}

/// Mutate the first `PT_LOAD` segment with `p_filesz < p_memsz` in `src_elf` to have `p_flags = PF_R`
/// (read-only `.bss`), producing `dst_elf`.
fn make_readonly_bss_elf(src_elf: &Path, dst_elf: &Path) -> Result<()> {
    let mut bytes = fs::read(src_elf)?;
    let endian = Endianness::Little;
    let hdr = object::elf::FileHeader64::<Endianness>::parse(&*bytes)?;
    ensure!(hdr.e_ident.class == ELFCLASS64 && hdr.e_machine(endian) == EM_AARCH64);
    let phoff = hdr.e_phoff(endian) as usize;
    let phentsize = hdr.e_phentsize(endian) as usize;
    let phnum = hdr.e_phnum(endian) as usize;
    let phdrs = hdr.program_headers(endian, &*bytes)?;
    let mut patched = false;
    for (i, ph) in phdrs.iter().enumerate() {
        if ph.p_type(endian) == PT_LOAD && ph.p_filesz(endian) < ph.p_memsz(endian) {
            let flags_off = phoff + i * phentsize + 4;
            bytes[flags_off..flags_off + 4].copy_from_slice(&PF_R.to_le_bytes());
            patched = true;
            break;
        }
    }
    ensure!(patched && phnum > 0, "found no PT_LOAD with p_filesz < p_memsz to patch");
    fs::write(dst_elf, bytes)?;
    Ok(())
}

/// Build all committed small corpus binaries into `Arm64/Testing/ElfLoaderDiff/bin/` (when
/// `check_only == false`), or verify that all committed binaries are present (`check_only == true`).
pub fn build_or_check_corpus(repo_root: &Path, check_only: bool) -> Result<()> {
    let bin_dir = fixture_dir(repo_root).join("bin");

    if check_only {
        for &name in COMMITTED_BINARIES {
            let p = bin_dir.join(name);
            ensure!(
                p.is_file() && fs::metadata(&p)?.len() >= 64,
                "missing or empty committed ELF {} (run `./scripts/elf-loader-diff build`)",
                p.display()
            );
        }
        return Ok(());
    }
    build_corpus_into(repo_root, &bin_dir).map(|_| ())
}

/// Rebuild every committed corpus binary into a temporary directory and require it to be
/// byte-identical to the committed file in `Arm64/Testing/ElfLoaderDiff/bin/`. Binaries whose
/// compiler is unavailable (`c_zig_*.elf` without `zig`) are reported as skipped.
pub fn verify_corpus(repo_root: &Path) -> Result<()> {
    let bin_dir = fixture_dir(repo_root).join("bin");
    let out = tempfile::TempDir::new()?;
    let skipped = build_corpus_into(repo_root, out.path())?;
    let mut mismatched = Vec::new();
    for &name in COMMITTED_BINARIES.iter().filter(|n| !skipped.contains(n)) {
        let committed = bin_dir.join(name);
        let fresh = fs::read(out.path().join(name))
            .with_context(|| format!("reading freshly built {name}"))?;
        match fs::read(&committed) {
            Ok(bytes) if bytes == fresh => {}
            Ok(_) => mismatched.push(format!("{} differs from a fresh build", committed.display())),
            Err(_) => mismatched.push(format!("{} is missing", committed.display())),
        }
    }
    ensure!(
        mismatched.is_empty(),
        "ElfLoaderDiff corpus is not reproducible (run `./scripts/elf-loader-diff build`):\n  {}",
        mismatched.join("\n  ")
    );
    let note = if skipped.is_empty() { String::new() } else { format!(" (skipped: {})", skipped.join(", ")) };
    println!(
        "OK: {} ElfLoaderDiff corpus binaries are byte-identical to a fresh build{note}",
        COMMITTED_BINARIES.len() - skipped.len()
    );
    Ok(())
}

/// Build every corpus binary into `bin_dir`, returning the names skipped because their compiler
/// is unavailable (`c_zig_*.elf` when `zig` is not on `PATH`).
fn build_corpus_into(repo_root: &Path, bin_dir: &Path) -> Result<Vec<&'static str>> {
    let src_dir = fixture_dir(repo_root).join("src");
    let bin_dir = bin_dir.to_path_buf();
    fs::create_dir_all(&bin_dir)?;
    let zig = which::which("zig").ok();
    let asm = Assembler::find(zig.as_deref())?;
    let (rustc, sysroot, lld) = find_rustc_and_lld()?;
    let mut skipped: Vec<&'static str> = Vec::new();
    let tmp = tempfile::TempDir::new()?;

    // 1. tiny_asm.elf + rejected variants from tiny_asm.s
    let tiny_o = tmp.path().join("tiny_asm.o");
    assemble_aarch64(&asm, &src_dir.join("tiny_asm.s"), &tiny_o)?;
    link_lld(
        &lld,
        &["-static", "--build-id=none", "--strip-all"],
        &tiny_o,
        &bin_dir.join("tiny_asm.elf"),
    )?;
    link_lld(
        &lld,
        &["-pie", "--build-id=none", "--strip-all"],
        &tiny_o,
        &bin_dir.join("reject_pie.elf"),
    )?;
    link_lld(
        &lld,
        &[
            "-dynamic-linker",
            "/lib/ld-linux-aarch64.so.1",
            "--build-id=none",
            "--strip-all",
        ],
        &tiny_o,
        &bin_dir.join("reject_dynamic.elf"),
    )?;
    fs::copy(&tiny_o, bin_dir.join("reject_relocatable.elf"))?;
    link_lld(
        &lld,
        &["-static", "--omagic", "--build-id=none", "--strip-all"],
        &tiny_o,
        &bin_dir.join("reject_wx_segment.elf"),
    )?;
    link_lld(
        &lld,
        &["-static", "-z", "execstack", "--build-id=none", "--strip-all"],
        &tiny_o,
        &bin_dir.join("reject_exec_stack.elf"),
    )?;

    // 2. Unusual linker-script layouts: layout_multi_rw, layout_midpage_bss, layout_tls_relro
    let multi_o = tmp.path().join("layout_multi_rw.o");
    assemble_aarch64(&asm, &src_dir.join("layout_multi_rw.s"), &multi_o)?;
    let multi_ld = src_dir.join("layout_multi_rw.ld");
    link_lld(
        &lld,
        &[
            "-static",
            "-z",
            "max-page-size=4096",
            "--build-id=none",
            "--strip-all",
            "-T",
            multi_ld.to_str().unwrap(),
        ],
        &multi_o,
        &bin_dir.join("layout_multi_rw.elf"),
    )?;
    make_readonly_bss_elf(
        &bin_dir.join("layout_multi_rw.elf"),
        &bin_dir.join("reject_ro_bss.elf"),
    )?;

    let mid_o = tmp.path().join("layout_midpage_bss.o");
    assemble_aarch64(&asm, &src_dir.join("layout_midpage_bss.s"), &mid_o)?;
    let mid_ld = src_dir.join("layout_midpage_bss.ld");
    // Preserve `.file_tail_marker` (do not `--strip-all`) so non-zero bytes remain in the file
    // immediately after `p_offset + p_filesz` in the `.mid_data`/`.mid_bss` page.
    link_lld(
        &lld,
        &[
            "-static",
            "-z",
            "max-page-size=4096",
            "--build-id=none",
            "-T",
            mid_ld.to_str().unwrap(),
        ],
        &mid_o,
        &bin_dir.join("layout_midpage_bss.elf"),
    )?;

    let tls_o = tmp.path().join("layout_tls_relro.o");
    assemble_aarch64(&asm, &src_dir.join("layout_tls_relro.s"), &tls_o)?;
    let tls_ld = src_dir.join("layout_tls_relro.ld");
    link_lld(
        &lld,
        &[
            "-static",
            "-z",
            "max-page-size=4096",
            "--build-id=none",
            "--strip-all",
            "-T",
            tls_ld.to_str().unwrap(),
        ],
        &tls_o,
        &bin_dir.join("layout_tls_relro.elf"),
    )?;

    // 2b. Additional positive layouts (`EXTRA_LAYOUTS`).
    for layout in EXTRA_LAYOUTS {
        let obj = tmp.path().join(format!("{}.o", layout.out));
        assemble_aarch64(&asm, &src_dir.join(format!("{}.s", layout.src)), &obj)?;
        let max_page = format!("max-page-size={}", layout.max_page_size);
        let ld_path = layout.ld.map(|ld| src_dir.join(format!("{ld}.ld")));
        let mut args: Vec<&str> = vec!["-static", "-z", &max_page, "--build-id=none"];
        if !layout.keep_symbols {
            args.push("--strip-all");
        }
        if let Some(ld) = &ld_path {
            args.push("-T");
            args.push(ld.to_str().context("non-UTF-8 linker script path")?);
        }
        link_lld(&lld, &args, &obj, &bin_dir.join(layout.out))?;
    }

    // 3. C with zig cc / musl at -O0 and -O2
    let c_src = src_dir.join("c_zig_musl.c");
    for (opt, out_name) in [("-O0", "c_zig_o0.elf"), ("-O2", "c_zig_o2.elf")] {
        let Some(zig) = &zig else {
            eprintln!("SKIPPED: {out_name} (`zig` not found in PATH; install the pinned zig)");
            skipped.push(out_name);
            continue;
        };
        let out_elf = bin_dir.join(out_name);
        let st = Command::new(zig)
            .args([
                "cc",
                "-target",
                "aarch64-linux-musl",
                "-static",
                "-fno-pie",
                "-no-pie",
                "-fno-sanitize=undefined",
                "-ffunction-sections",
                "-fdata-sections",
                opt,
                "-Wl,--gc-sections",
                "-Wl,--build-id=none",
                "-Wl,--strip-all",
                "-o",
            ])
            .arg(&out_elf)
            .arg(&c_src)
            .status()
            .with_context(|| format!("invoking zig cc for {out_name}"))?;
        ensure!(st.success(), "zig cc failed for {out_name}");
    }

    // 4. Rust (`aarch64-unknown-linux-musl`, static, release, `#![no_std]` with `.tdata`/`.tbss` + 64 KiB `.bss`)
    let rust_nostd_src = src_dir.join("rust_nostd_tls_bss.rs");
    let rust_nostd_elf = bin_dir.join("rust_nostd_tls_bss.elf");
    let st = Command::new(&rustc)
        .env_remove("RUSTUP_TOOLCHAIN")
        .arg("--sysroot")
        .arg(&sysroot)
        .args([
            "--edition=2024",
            "--target=aarch64-unknown-linux-musl",
            "-O",
            "-C",
            "panic=abort",
            "-C",
            "relocation-model=static",
            "-C",
            "link-self-contained=no",
            "-C",
            "link-arg=-nostdlib",
            "-C",
            "link-arg=-static",
            "-C",
            "link-arg=--build-id=none",
            "-C",
            "link-arg=--strip-all",
        ])
        .arg(format!("-Clinker={}", lld.display()))
        .arg(&rust_nostd_src)
        .arg("-o")
        .arg(&rust_nostd_elf)
        .status()
        .context("invoking rustc for rust_nostd_tls_bss.elf")?;
    ensure!(st.success(), "rustc failed for rust_nostd_tls_bss.elf");
    Ok(skipped)
}

/// Build the larger multi-compiler live binaries (`rust_tls_bss.elf` with `std::thread_local!`,
/// `go_static.elf` with `GOOS=linux GOARCH=arm64 CGO_ENABLED=0`, optional `c_gcc_glibc.elf`, and
/// `zig cc` PIE/dynamic rejected binaries) in `stage_dir`.
pub fn build_live_extras(repo_root: &Path, stage_dir: &Path) -> Result<LiveExtraBinaries> {
    fs::create_dir_all(stage_dir)?;
    let src_dir = fixture_dir(repo_root).join("src");
    let (rustc, sysroot, lld) = find_rustc_and_lld()?;
    let zig = which::which("zig").context("`zig` not found in PATH")?;

    // 1. Full `std` Rust (`aarch64-unknown-linux-musl`, static, release) with `PT_TLS` + 64 KiB `.bss`
    let rust_std_elf = stage_dir.join("rust_tls_bss.elf");
    let st = Command::new(&rustc)
        .env_remove("RUSTUP_TOOLCHAIN")
        .arg("--sysroot")
        .arg(&sysroot)
        .args([
            "--edition=2024",
            "--target=aarch64-unknown-linux-musl",
            "-O",
            "-C",
            "panic=abort",
            "-C",
            "relocation-model=static",
            "-C",
            "link-arg=--build-id=none",
            "-C",
            "link-arg=--strip-all",
        ])
        .arg(format!("-Clinker={}", lld.display()))
        .arg(src_dir.join("rust_tls_bss.rs"))
        .arg("-o")
        .arg(&rust_std_elf)
        .status()
        .context("invoking rustc for rust_tls_bss.elf")?;
    ensure!(st.success(), "rustc failed for rust_tls_bss.elf");

    // 2. Go (`GOOS=linux GOARCH=arm64 CGO_ENABLED=0`) static binary (mandatory in live suite)
    let go = which::which("go")
        .context("`go` not found in PATH (required to build go_static.elf for elf-loader-diff)")?;
    let go_static = stage_dir.join("go_static.elf");
    let st = Command::new(&go)
        .env("GOOS", "linux")
        .env("GOARCH", "arm64")
        .env("CGO_ENABLED", "0")
        .args(["build", "-trimpath", "-ldflags=-s -w -buildid=", "-o"])
        .arg(&go_static)
        .arg(src_dir.join("go_minimal.go"))
        .status()
        .context("invoking go build for go_static.elf")?;
    ensure!(st.success(), "go build failed for go_static.elf");

    // 3. Optional C with `aarch64-linux-gnu-gcc -static` (if installed on the host, or required via
    // `ELF_LOADER_DIFF_REQUIRE_GCC_GLIBC=1`)
    let require_gcc =
        std::env::var("ELF_LOADER_DIFF_REQUIRE_GCC_GLIBC").as_deref() == Ok("1");
    let c_src = src_dir.join("c_zig_musl.c");
    let c_gcc_glibc = if let Ok(gcc) = which::which("aarch64-linux-gnu-gcc") {
        let out_gcc = stage_dir.join("c_gcc_glibc.elf");
        let st = Command::new(&gcc)
            .args([
                "-static",
                "-fno-pie",
                "-no-pie",
                "-O2",
                "-Wl,--build-id=none",
                "-s",
                "-o",
            ])
            .arg(&out_gcc)
            .arg(&c_src)
            .status()
            .context("invoking aarch64-linux-gnu-gcc")?;
        if st.success() {
            Some(out_gcc)
        } else if require_gcc {
            bail!("ELF_LOADER_DIFF_REQUIRE_GCC_GLIBC=1 but `aarch64-linux-gnu-gcc -static` failed");
        } else {
            eprintln!(
                "[elf-loader-diff] SKIP optional case c_gcc_glibc_default: `aarch64-linux-gnu-gcc -static` failed"
            );
            None
        }
    } else if require_gcc {
        bail!("ELF_LOADER_DIFF_REQUIRE_GCC_GLIBC=1 but `aarch64-linux-gnu-gcc` not found in PATH");
    } else {
        eprintln!(
            "[elf-loader-diff] SKIP optional case c_gcc_glibc_default: `aarch64-linux-gnu-gcc` not found in PATH"
        );
        None
    };

    // 4. Real `zig cc` PIE (`ET_DYN`) and dynamic (`PT_INTERP`) binaries for fail-closed testing
    let reject_zig_pie = stage_dir.join("reject_zig_pie.elf");
    let st = Command::new(&zig)
        .args([
            "cc",
            "-target",
            "aarch64-linux-musl",
            "-nostdlib",
            "-fPIE",
            "-pie",
            "-O1",
            "-Wl,-e,main",
            "-Wl,--strip-all",
            "-o",
        ])
        .arg(&reject_zig_pie)
        .arg(&c_src)
        .status()
        .context("invoking zig cc for reject_zig_pie.elf")?;
    ensure!(st.success(), "zig cc -pie failed");

    let dummy_so = stage_dir.join("libdummy.so");
    let st = Command::new(&zig)
        .args([
            "cc",
            "-target",
            "aarch64-linux-gnu",
            "-nostdlib",
            "-shared",
            "-fPIC",
            "-O1",
            "-o",
        ])
        .arg(&dummy_so)
        .arg(&c_src)
        .status()
        .context("invoking zig cc for libdummy.so")?;
    ensure!(st.success(), "zig cc -shared failed");

    let reject_zig_dynamic = stage_dir.join("reject_zig_dynamic.elf");
    let st = Command::new(&zig)
        .args([
            "cc",
            "-target",
            "aarch64-linux-gnu",
            "-nostdlib",
            "-fno-pie",
            "-no-pie",
            "-O1",
            "-Wl,-e,main",
            "-Wl,-dynamic-linker,/lib/ld-linux-aarch64.so.1",
            "-Wl,--strip-all",
            "-o",
        ])
        .arg(&reject_zig_dynamic)
        .arg(&c_src)
        .arg(&dummy_so)
        .status()
        .context("invoking zig cc for reject_zig_dynamic.elf")?;
    ensure!(st.success(), "zig cc dynamic failed");

    Ok(LiveExtraBinaries {
        rust_std_tls_bss: rust_std_elf,
        go_static,
        c_gcc_glibc,
        reject_zig_pie,
        reject_zig_dynamic,
    })
}
