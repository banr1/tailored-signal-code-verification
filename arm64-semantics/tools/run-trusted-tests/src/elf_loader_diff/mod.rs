// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Differential test driver comparing the Lean ELF64 process loader (`Arm64/Trusted/Process/Loader.lean`)
//! against `qemu-aarch64` user-mode entry snapshots (`tools/proc-snapshot`) (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (untrusted host test driver under `tools/run-trusted-tests`).
//! - **Purpose:** Builds the multi-compiler static AArch64 (`ET_EXEC`) corpus (and fail-closed
//!   rejected binaries), captures `entry.snapshot.{json,bin}` at `pc == e_entry` via
//!   `proc-snapshot snapshot --entry-only` under the pinned `qemu-aarch64` (`ADDR_NO_RANDOMIZE`,
//!   `-seed 0`), writes or checks `Arm64/Testing/ElfLoaderDiff/expected_snapshots.json`, and
//!   invokes `Arm64/Testing/.lake/build/bin/elf_eval --loader-diff` (`Arm64.Testing.Harness.ElfLoaderDiff`) to
//!   compare every `PT_LOAD` page, register, stack frame (`argc`/`argv`/`envp`/`auxv`), `brk`, and
//!   unmapped gap against `ElfImage.loadState`.

pub mod build;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail, ensure};
use serde::{Deserialize, Serialize};
use serde_json::Value;

pub use build::{LiveExtraBinaries, build_live_extras, build_or_check_corpus, verify_corpus};

/// Relative path from repository root to the `ElfLoaderDiff` fixture directory.
pub const FIXTURE_REL_DIR: &str = "Arm64/Testing/ElfLoaderDiff";

/// Relative path from repository root to the committed snapshot manifest.
pub const MANIFEST_REL_PATH: &str = "Arm64/Testing/ElfLoaderDiff/expected_snapshots.json";

pub fn fixture_dir(repo_root: &Path) -> PathBuf {
    repo_root.join(FIXTURE_REL_DIR)
}

pub fn manifest_path(repo_root: &Path) -> PathBuf {
    repo_root.join(MANIFEST_REL_PATH)
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SparseChunk {
    pub offset: usize,
    pub hex: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct InitialFileSpec {
    pub path: String,
    pub utf8: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PositiveDiffCase {
    pub id: String,
    pub category: String,
    pub description: String,
    pub elf_path: String,
    pub snapshot: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub snapshot_bin_path: Option<String>,
    pub sparse_bin_chunks: Vec<SparseChunk>,
    pub include_vdso_in_extra_auxv: bool,
    pub stdin_utf8: String,
    pub initial_files: Vec<InitialFileSpec>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RejectedDiffCase {
    pub id: String,
    pub category: String,
    pub description: String,
    pub elf_path: String,
    pub expected_error_substr: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ElfLoaderDiffManifest {
    pub schema_version: u32,
    pub qemu_version: String,
    pub positive_cases: Vec<PositiveDiffCase>,
    pub rejected_cases: Vec<RejectedDiffCase>,
}

struct CaseSpec {
    id: &'static str,
    category: &'static str,
    description: &'static str,
    elf_rel: String,
    argv0: &'static str,
    args: Vec<String>,
    envs: Vec<String>,
    include_vdso_in_extra_auxv: bool,
    stdin_utf8: &'static str,
    initial_files: Vec<InitialFileSpec>,
}

/// Extract non-zero byte runs from `bin` into compact `SparseChunk`s (coalescing gaps < 16 zero bytes).
pub fn extract_sparse_chunks(bin: &[u8]) -> Vec<SparseChunk> {
    let mut chunks = Vec::new();
    let mut i = 0;
    while i < bin.len() {
        if bin[i] == 0 {
            i += 1;
            continue;
        }
        let start = i;
        let mut end = i + 1;
        while end < bin.len() {
            if bin[end] != 0 {
                end += 1;
                continue;
            }
            let mut z = end;
            while z < bin.len() && z - end < 16 && bin[z] == 0 {
                z += 1;
            }
            if z < bin.len() && bin[z] != 0 {
                end = z + 1;
            } else {
                break;
            }
        }
        let hex: String = bin[start..end].iter().map(|b| format!("{b:02x}")).collect();
        chunks.push(SparseChunk { offset: start, hex });
        i = end;
    }
    chunks
}

fn find_qemu(repo_root: &Path) -> Result<PathBuf> {
    if let Some(p) = std::env::var_os("QEMU_AARCH64") {
        let pb = PathBuf::from(p);
        if pb.is_file() {
            return Ok(pb);
        }
    }
    let fetch_script = repo_root.join("scripts").join("fetch-qemu-aarch64");
    if fetch_script.is_file() {
        let out = Command::new(&fetch_script)
            .output()
            .context("invoking scripts/fetch-qemu-aarch64")?;
        if out.status.success() {
            let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
            if p.is_file() {
                return Ok(p);
            }
        }
    }
    which::which("qemu-aarch64").context("`qemu-aarch64` not found (run scripts/fetch-qemu-aarch64)")
}

fn ensure_proc_snapshot_bin(repo_root: &Path) -> Result<PathBuf> {
    let release_bin = repo_root
        .join("tools")
        .join("target")
        .join("release")
        .join("proc-snapshot");
    let st = Command::new("cargo")
        .args([
            "build",
            "--release",
            "--locked",
            "--manifest-path",
            repo_root.join("tools/Cargo.toml").to_str().unwrap(),
            "-p",
            "proc-snapshot",
        ])
        .status()
        .context("building proc-snapshot")?;
    ensure!(st.success(), "cargo build -p proc-snapshot failed");
    Ok(release_bin)
}

fn ensure_elf_eval_bin(repo_root: &Path) -> Result<PathBuf> {
    let bin = repo_root.join("Arm64/Testing/.lake/build/bin/elf_eval");
    let st = Command::new("lake")
        .current_dir(repo_root)
        .args(["-d", "Arm64/Testing", "build", "--no-ansi", "elf_eval"])
        .status()
        .context("invoking `lake -d Arm64/Testing build --no-ansi elf_eval`")?;
    ensure!(st.success(), "`lake -d Arm64/Testing build --no-ansi elf_eval` failed");
    ensure!(bin.is_file(), "missing {}", bin.display());
    Ok(bin)
}

fn committed_positive_specs() -> Vec<CaseSpec> {
    let large_args: Vec<String> = (0..48)
        .map(|i| format!("--arg-{i:02}={}", "x".repeat(64 + (i % 17))))
        .collect();
    let large_envs: Vec<String> = (0..32)
        .map(|i| format!("LOADER_ENV_{i:02}={}", "Y".repeat(72 + (i % 13))))
        .collect();

    vec![
        CaseSpec {
            id: "tiny_asm_default",
            category: "asm",
            description: "Hand-written AArch64 assembly (_start, .rodata, .data, .bss) with default argv/envp",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf".into(),
            argv0: "tiny_asm",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "tiny_asm_multi_arg_env",
            category: "asm_argv_envp",
            description: "Hand-written AArch64 assembly with multi-element argv (flags, spaces, empty string) and envp",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf".into(),
            argv0: "custom_argv0",
            args: vec!["--flag".into(), "-v".into(), "hello world".into(), "".into()],
            envs: vec![
                "PATH=/usr/local/bin:/usr/bin:/bin".into(),
                "LANG=C.UTF-8".into(),
                "EMPTY=".into(),
            ],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "layout_multi_rw_default",
            category: "unusual_layout",
            description: "Three distinct RW PT_LOAD segments (pure data, mixed data+bss, pure bss) with multi-page unmapped gaps",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/layout_multi_rw.elf".into(),
            argv0: "layout_multi_rw",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "layout_midpage_bss_default",
            category: "unusual_layout",
            description: "Mid-page p_vaddr & mid-page p_filesz == p_memsz (trailing file bytes mapped) vs p_filesz < p_memsz (trailing file bytes zeroed by padzero)",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/layout_midpage_bss.elf".into(),
            argv0: "layout_midpage_bss",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "layout_tls_relro_default",
            category: "unusual_layout",
            description: "Explicit PT_PHDR, PT_NOTE, PT_TLS (.tdata + .tbss), PT_GNU_RELRO, and PT_GNU_STACK",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/layout_tls_relro.elf".into(),
            argv0: "layout_tls_relro",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "c_zig_o0_default",
            category: "c_zig_musl",
            description: "C with zig cc / musl static at -O0 (.rodata, .data, 8 KiB .bss)",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/c_zig_o0.elf".into(),
            argv0: "c_zig_o0",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "c_zig_o2_default",
            category: "c_zig_musl",
            description: "C with zig cc / musl static at -O2 (.rodata, .data, 8 KiB .bss)",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/c_zig_o2.elf".into(),
            argv0: "c_zig_o2",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "c_zig_o2_vdso_extra_auxv",
            category: "c_zig_musl_auxv",
            description: "C with zig cc / musl at -O2 with AuxvConfig.extra carrying AT_SYSINFO_EHDR (33) for exact 19-entry auxv parity",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/c_zig_o2.elf".into(),
            argv0: "c_zig_o2",
            args: vec!["--check-auxv".into(), "42".into()],
            envs: vec!["MODE=strict".into(), "TERM=vt100".into()],
            include_vdso_in_extra_auxv: true,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "c_zig_o2_large_argv_envp",
            category: "large_stack",
            description: "C with zig cc / musl at -O2 with 49 argv entries and 32 envp entries (> 6 KiB info block spanning multiple stack pages)",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/c_zig_o2.elf".into(),
            argv0: "c_zig_o2",
            args: large_args,
            envs: large_envs,
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "c_zig_o2_stdin_and_files",
            category: "stdio_vfs",
            description: "C with zig cc / musl at -O2 with non-empty stdin and pre-populated regular files in ProcessInputs",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/c_zig_o2.elf".into(),
            argv0: "c_zig_o2",
            args: vec!["--input".into(), "config.txt".into()],
            envs: vec!["APP_ENV=test".into()],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "hello from stdin\nsecond line\n",
            initial_files: vec![InitialFileSpec {
                path: "config.txt".into(),
                utf8: "key=value\ncount=10\n".into(),
            }],
        },
        CaseSpec {
            id: "rust_nostd_tls_bss_default",
            category: "rust_musl",
            description: "Rust (aarch64-unknown-linux-musl, static, release, no_std) with .tdata/.tbss and 64 KiB .bss",
            elf_rel: "Arm64/Testing/ElfLoaderDiff/bin/rust_nostd_tls_bss.elf".into(),
            argv0: "rust_nostd_tls_bss",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
    ]
    .into_iter()
    .chain(extra_layout_positive_specs())
    .collect()
}

/// Positive cases for the additional hand-written layouts in `build::EXTRA_LAYOUTS`.
fn extra_layout_positive_specs() -> Vec<CaseSpec> {
    fn layout(id: &'static str, bin: &str, argv0: &'static str, description: &'static str) -> CaseSpec {
        CaseSpec {
            id,
            category: "unusual_layout",
            description,
            elf_rel: format!("Arm64/Testing/ElfLoaderDiff/bin/{bin}"),
            argv0,
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        }
    }
    // 200 argv + 120 envp entries (~ 21 KiB of strings): the info block alone spans 6 stack pages.
    let huge_args: Vec<String> = (0..200)
        .map(|i| format!("a{i:03}={}", "z".repeat(40 + (i % 29))))
        .collect();
    let huge_envs: Vec<String> = (0..120)
        .map(|i| format!("TEXT_ONLY_ENV_{i:03}={}", "q".repeat(50 + (i % 23))))
        .collect();
    vec![
        layout(
            "layout_text_only_default",
            "layout_text_only.elf",
            "layout_text_only",
            "Single r-x PT_LOAD (headers + .rodata + .text) with no writable segment; e_entry mid-segment; brk right after the only page",
        ),
        CaseSpec {
            id: "layout_text_only_huge_argv_envp",
            category: "large_stack",
            description: "Single r-x PT_LOAD binary with 201 argv and 120 envp entries (~21 KiB info block spanning 6+ stack pages)",
            args: huge_args,
            envs: huge_envs,
            ..layout("", "layout_text_only.elf", "layout_text_only", "")
        },
        layout(
            "layout_entry_deep_default",
            "layout_entry_deep.elf",
            "layout_entry_deep",
            "3-page r-x segment with e_entry on its third page, separate r-- header segment sharing file page 0, rw- data+bss",
        ),
        layout(
            "layout_bss_page_end_default",
            "layout_bss_page_end.elf",
            "layout_bss_page_end",
            "Mid-page rw- segment whose .bss is padded so p_vaddr + p_memsz ends exactly on a 4 KiB page boundary",
        ),
        layout(
            "layout_filesz_page_end_default",
            "layout_filesz_page_end.elf",
            "layout_filesz_page_end",
            "rw- segment whose non-zero .data ends exactly on a page boundary (p_vaddr + p_filesz page-aligned) with 24 B of .bss just past it",
        ),
        layout(
            "layout_large_bss_default",
            "layout_large_bss.elf",
            "layout_large_bss",
            "Mid-page rw- segment with 0x58 B .data and 1 MiB + 0x234 B .bss (258 pages, 257 anonymous) ending mid-page",
        ),
        layout(
            "layout_palign_4k_default",
            "layout_palign_4k.elf",
            "layout_palign_4k",
            "ld.lld default layout with -z max-page-size=0x1000 (p_align 0x1000, segments on consecutive pages)",
        ),
        layout(
            "layout_palign_16k_default",
            "layout_palign_16k.elf",
            "layout_palign_16k",
            "ld.lld default layout with -z max-page-size=0x4000 (p_align 0x4000, 3-page unmapped gaps between segments)",
        ),
        layout(
            "layout_palign_2m_default",
            "layout_palign_2m.elf",
            "layout_palign_2m",
            "ld.lld default layout with -z max-page-size=0x200000 (p_align 2 MiB, segments 2 MiB apart sharing one file page)",
        ),
        layout(
            "layout_unaligned_straddle_default",
            "layout_unaligned_straddle.elf",
            "layout_unaligned_straddle",
            "r-x, r--, rw- PT_LOADs at non-page-aligned p_vaddr/p_offset (congruent mod 4 KiB), each straddling a page boundary; .bss tail zeroed mid-page",
        ),
        layout(
            "layout_phdr_unmapped_default",
            "layout_phdr_unmapped.elf",
            "layout_phdr_unmapped",
            "ELF/program headers outside every PT_LOAD (no PT_PHDR); page-aligned r-x, then r-- .rodata after text, then rw-",
        ),
        layout(
            "layout_pure_bss_midpage_default",
            "layout_pure_bss_midpage.elf",
            "layout_pure_bss_midpage",
            "Pure .bss PT_LOAD (p_filesz == 0) starting and ending mid-page, separate from a p_filesz == p_memsz rw- segment",
        ),
        layout(
            "layout_many_loads_default",
            "layout_many_loads.elf",
            "layout_many_loads",
            "Eight PT_LOADs (r--, r-x, r--, rw-, r--, r-x, rw- data+bss, rw- pure bss) sharing file pages, with gaps; e_entry in the second r-x segment",
        ),
        layout(
            "layout_many_sections_default",
            "layout_many_sections.elf",
            "layout_many_sections",
            "70+ small output sections (40 .fnNN functions with STT_FUNC symbols in an unstripped .symtab, 30 odd-sized .dNN data/rodata) in ld.lld's default layout",
        ),
        layout(
            "layout_high_vaddr_default",
            "layout_high_vaddr.elf",
            "layout_high_vaddr",
            "r-x text at 0x10000 and rw- data+bss above 4 GiB (0x100002110), leaving a ~4 GiB unmapped gap; brk above 4 GiB",
        ),
        layout(
            "layout_rw_file_tail_default",
            "layout_rw_file_tail.elf",
            "layout_rw_file_tail",
            "rw- PT_LOAD with p_filesz == p_memsz ending mid-page followed by non-alloc 0xfeedface bytes in the file (mapped, not zeroed)",
        ),
    ]
}

fn committed_rejected_cases() -> Vec<RejectedDiffCase> {
    vec![
        RejectedDiffCase {
            id: "reject_pie_et_dyn".into(),
            category: "fail_closed".into(),
            description: "Position-independent executable (ET_DYN = 3) rejected fail-closed".into(),
            elf_path: "Arm64/Testing/ElfLoaderDiff/bin/reject_pie.elf".into(),
            expected_error_substr: "expected static ET_EXEC (2), got e_type=3".into(),
        },
        RejectedDiffCase {
            id: "reject_dynamic_pt_interp".into(),
            category: "fail_closed".into(),
            description: "Dynamically linked ELF (PT_INTERP / PT_DYNAMIC) rejected fail-closed".into(),
            elf_path: "Arm64/Testing/ElfLoaderDiff/bin/reject_dynamic.elf".into(),
            expected_error_substr: "is not supported".into(),
        },
        RejectedDiffCase {
            id: "reject_relocatable_et_rel".into(),
            category: "fail_closed".into(),
            description: "Relocatable object file (ET_REL = 1) rejected fail-closed".into(),
            elf_path: "Arm64/Testing/ElfLoaderDiff/bin/reject_relocatable.elf".into(),
            expected_error_substr: "expected static ET_EXEC (2), got e_type=1".into(),
        },
        RejectedDiffCase {
            id: "reject_wx_pt_load".into(),
            category: "fail_closed".into(),
            description: "Writable + executable (PF_R | PF_W | PF_X) PT_LOAD segment rejected fail-closed".into(),
            elf_path: "Arm64/Testing/ElfLoaderDiff/bin/reject_wx_segment.elf".into(),
            expected_error_substr: "W+X PT_LOAD segment is not supported".into(),
        },
        RejectedDiffCase {
            id: "reject_exec_gnu_stack".into(),
            category: "fail_closed".into(),
            description: "Executable stack (PT_GNU_STACK with PF_X) rejected fail-closed".into(),
            elf_path: "Arm64/Testing/ElfLoaderDiff/bin/reject_exec_stack.elf".into(),
            expected_error_substr: "executable stack (PT_GNU_STACK with PF_X) is not supported".into(),
        },
        RejectedDiffCase {
            id: "reject_readonly_bss".into(),
            category: "fail_closed".into(),
            description: "Non-writable PT_LOAD segment with p_filesz < p_memsz rejected fail-closed".into(),
            elf_path: "Arm64/Testing/ElfLoaderDiff/bin/reject_ro_bss.elf".into(),
            expected_error_substr: "non-writable PT_LOAD segment has p_filesz < p_memsz".into(),
        },
    ]
}

fn capture_one_case(
    repo_root: &Path,
    proc_snapshot_bin: &Path,
    qemu_bin: &Path,
    spec: &CaseSpec,
    out_dir: &Path,
    embed_sparse: bool,
) -> Result<PositiveDiffCase> {
    fs::create_dir_all(out_dir)?;
    let mut cmd = Command::new(proc_snapshot_bin);
    cmd.current_dir(repo_root)
        .args([
            "snapshot",
            "--entry-only",
            "--elf",
            &spec.elf_rel,
            "--qemu",
            qemu_bin.to_str().unwrap(),
            "--out-dir",
            out_dir.to_str().unwrap(),
            "--argv0",
            spec.argv0,
        ]);
    for a in &spec.args {
        cmd.args(["--arg", a]);
    }
    for e in &spec.envs {
        cmd.args(["--env", e]);
    }
    let out = cmd
        .output()
        .with_context(|| format!("running proc-snapshot on {}", spec.id))?;
    if !out.status.success() {
        bail!(
            "proc-snapshot failed on {}:\n{}",
            spec.id,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let snap_json_str = fs::read_to_string(out_dir.join("entry.snapshot.json"))?;
    let snapshot: Value = serde_json::from_str(&snap_json_str)?;
    let bin_path = out_dir.join("entry.snapshot.bin");
    let (snapshot_bin_path, sparse_bin_chunks) = if embed_sparse {
        let bin = fs::read(&bin_path)?;
        (None, extract_sparse_chunks(&bin))
    } else {
        (Some(bin_path.display().to_string()), Vec::new())
    };
    Ok(PositiveDiffCase {
        id: spec.id.into(),
        category: spec.category.into(),
        description: spec.description.into(),
        elf_path: spec.elf_rel.clone(),
        snapshot,
        snapshot_bin_path,
        sparse_bin_chunks,
        include_vdso_in_extra_auxv: spec.include_vdso_in_extra_auxv,
        stdin_utf8: spec.stdin_utf8.into(),
        initial_files: spec.initial_files.clone(),
    })
}

/// Reconstruct a full binary buffer of `total_size` bytes from `SparseChunk`s.
fn reconstruct_sparse_bin(total_size: usize, chunks: &[SparseChunk]) -> Result<Vec<u8>> {
    let mut buf = vec![0u8; total_size];
    for c in chunks {
        ensure!(
            c.hex.len().is_multiple_of(2),
            "odd hex length in sparse chunk at offset {}",
            c.offset
        );
        let len = c.hex.len() / 2;
        ensure!(
            c.offset + len <= total_size,
            "sparse chunk {}+{} exceeds total_size {}",
            c.offset,
            len,
            total_size
        );
        for i in 0..len {
            buf[c.offset + i] = u8::from_str_radix(&c.hex[2 * i..2 * i + 2], 16)?;
        }
    }
    Ok(buf)
}

/// Compare a committed `ElfLoaderDiffManifest` against a freshly captured live QEMU manifest.
///
/// Checks exact equality of all `PT_LOAD` (`kind == "load"`) region descriptors (`start`, `size`,
/// `perm`, `binOff`) and all `PT_LOAD` bytes in `entry.snapshot.bin`, `brkStart`, `pc`, `x0`..`x30`,
/// `cpsr`, `tpidr_el0`, `argv`, `envp`, `elf.sha256`, `runner.sha256`, stack `size`/`perm`/`binOff`,
/// and `stack_top - sp`, while skipping `stack.start`, `regs.sp`, and the raw stack/auxv bytes in
/// `entry.snapshot.bin` (which depend on the host runner UID/GID and stack base placement; full
/// stack and `auxv` contents are verified against `ElfImage.loadState` by `elf-loader-diff run` and
/// `unit_tests`).
fn verify_committed_vs_live_manifest(
    committed: &ElfLoaderDiffManifest,
    live: &ElfLoaderDiffManifest,
) -> Result<()> {
    ensure!(
        committed.schema_version == live.schema_version,
        "schema_version mismatch: committed {} vs live {}",
        committed.schema_version,
        live.schema_version
    );
    ensure!(
        committed.qemu_version == live.qemu_version,
        "qemu_version mismatch: committed {:?} vs live {:?}",
        committed.qemu_version,
        live.qemu_version
    );
    ensure!(
        committed.rejected_cases == live.rejected_cases,
        "rejected_cases mismatch between committed and live manifests"
    );
    ensure!(
        committed.positive_cases.len() == live.positive_cases.len(),
        "positive_cases count mismatch: committed {} vs live {}",
        committed.positive_cases.len(),
        live.positive_cases.len()
    );
    for (exp, act) in committed.positive_cases.iter().zip(&live.positive_cases) {
        let id = &exp.id;
        ensure!(exp.id == act.id, "case id mismatch: {} vs {}", exp.id, act.id);
        ensure!(exp.category == act.category, "{id}: category mismatch");
        ensure!(exp.description == act.description, "{id}: description mismatch");
        ensure!(exp.elf_path == act.elf_path, "{id}: elf_path mismatch");
        ensure!(
            exp.include_vdso_in_extra_auxv == act.include_vdso_in_extra_auxv,
            "{id}: include_vdso_in_extra_auxv mismatch"
        );
        ensure!(exp.stdin_utf8 == act.stdin_utf8, "{id}: stdin_utf8 mismatch");
        ensure!(exp.initial_files == act.initial_files, "{id}: initial_files mismatch");

        let (es, as_) = (&exp.snapshot, &act.snapshot);
        for key in ["schema", "stop", "runner", "argv", "envp", "elf", "brkStart"] {
            ensure!(
                es[key] == as_[key],
                "{id}: snapshot.{key} mismatch: committed {} vs live {}",
                es[key],
                as_[key]
            );
        }
        for rkey in ["pc", "x", "cpsr", "tpidr_el0"] {
            ensure!(
                es["regs"][rkey] == as_["regs"][rkey],
                "{id}: snapshot.regs.{rkey} mismatch: committed {} vs live {}",
                es["regs"][rkey],
                as_["regs"][rkey]
            );
        }
        let exp_bin_size = es["bin"]["size"]
            .as_u64()
            .context("committed bin.size")? as usize;
        let act_bin_size = as_["bin"]["size"].as_u64().context("live bin.size")? as usize;
        ensure!(
            exp_bin_size == act_bin_size,
            "{id}: bin.size mismatch: committed {exp_bin_size} vs live {act_bin_size}"
        );
        let exp_bin = reconstruct_sparse_bin(exp_bin_size, &exp.sparse_bin_chunks)?;
        let act_bin = reconstruct_sparse_bin(act_bin_size, &act.sparse_bin_chunks)?;

        let exp_regs = es["regions"].as_array().context("committed regions")?;
        let act_regs = as_["regions"].as_array().context("live regions")?;
        ensure!(
            exp_regs.len() == act_regs.len(),
            "{id}: region count mismatch: committed {} vs live {}",
            exp_regs.len(),
            act_regs.len()
        );
        for (er, ar) in exp_regs.iter().zip(act_regs) {
            for k in ["kind", "perm", "size", "binOff"] {
                ensure!(
                    er[k] == ar[k],
                    "{id}: region {k} mismatch: committed {} vs live {}",
                    er[k],
                    ar[k]
                );
            }
            let kind = er["kind"].as_str().unwrap_or("");
            let off = er["binOff"].as_u64().unwrap() as usize;
            let sz = er["size"].as_u64().unwrap() as usize;
            if kind == "load" {
                ensure!(
                    er["start"] == ar["start"],
                    "{id}: PT_LOAD start mismatch: committed {} vs live {}",
                    er["start"],
                    ar["start"]
                );
                ensure!(
                    exp_bin[off..off + sz] == act_bin[off..off + sz],
                    "{id}: PT_LOAD bytes at {:#x}+{:#x} differ between committed and live QEMU snapshot",
                    er["start"].as_u64().unwrap_or(0),
                    sz
                );
            } else if kind == "stack" {
                let exp_top = er["start"].as_u64().unwrap() + sz as u64;
                let act_top = ar["start"].as_u64().unwrap() + sz as u64;
                let exp_sp = es["regs"]["sp"].as_u64().unwrap();
                let act_sp = as_["regs"]["sp"].as_u64().unwrap();
                ensure!(
                    exp_top - exp_sp == act_top - act_sp,
                    "{id}: stack frame size (stack_top - sp) mismatch: committed {} vs live {}",
                    exp_top - exp_sp,
                    act_top - act_sp
                );
            }
        }
    }
    Ok(())
}

/// Regenerate or check `Arm64/Testing/ElfLoaderDiff/expected_snapshots.json` for the committed
/// small corpus.
pub fn regen_or_check_snapshots(repo_root: &Path, check_only: bool) -> Result<()> {
    build_or_check_corpus(repo_root, true)?;
    let qemu = find_qemu(repo_root)?;
    let proc_snapshot = ensure_proc_snapshot_bin(repo_root)?;
    let tmp = tempfile::TempDir::new()?;

    let specs = committed_positive_specs();
    let mut positive_cases = Vec::with_capacity(specs.len());
    for spec in &specs {
        let case_out = tmp.path().join(spec.id);
        positive_cases.push(capture_one_case(
            repo_root,
            &proc_snapshot,
            &qemu,
            spec,
            &case_out,
            true,
        )?);
    }
    let qemu_version = positive_cases[0].snapshot["runner"]["version"]
        .as_str()
        .unwrap_or("unknown")
        .to_string();
    let manifest = ElfLoaderDiffManifest {
        schema_version: 1,
        qemu_version,
        positive_cases,
        rejected_cases: committed_rejected_cases(),
    };
    let dest = manifest_path(repo_root);
    if check_only {
        let committed_str = fs::read_to_string(&dest)
            .with_context(|| format!("reading {}", dest.display()))?;
        let committed: ElfLoaderDiffManifest = serde_json::from_str(&committed_str)
            .with_context(|| format!("parsing {}", dest.display()))?;
        verify_committed_vs_live_manifest(&committed, &manifest)?;
        eprintln!(
            "[elf-loader-diff] Verified zero drift on {} ({} positive cases, {} rejected cases)",
            dest.display(),
            manifest.positive_cases.len(),
            manifest.rejected_cases.len()
        );
    } else {
        let rendered = serde_json::to_string_pretty(&manifest)? + "\n";
        fs::write(&dest, rendered)?;
        eprintln!(
            "[elf-loader-diff] Wrote {} ({} positive cases, {} rejected cases)",
            dest.display(),
            manifest.positive_cases.len(),
            manifest.rejected_cases.len()
        );
    }
    Ok(())
}

/// Build the full live multi-compiler corpus (C `zig cc` `-O0`/`-O2`, optional `gcc`+`glibc`,
/// Rust `no_std` and `std` with `PT_TLS` + 64 KiB `.bss`, Go `GOOS=linux GOARCH=arm64`,
/// hand-written assembly, unusual linker layouts, existing repo binaries, and PIE/dynamic/invalid
/// rejected binaries), snapshot every positive case under `qemu-aarch64`, and run the Lean
/// comparison harness (`elf_eval --loader-diff`).
pub fn run_live_diff_suite(repo_root: &Path) -> Result<()> {
    build_or_check_corpus(repo_root, true)?;
    let qemu = find_qemu(repo_root)?;
    let proc_snapshot = ensure_proc_snapshot_bin(repo_root)?;
    let elf_eval = ensure_elf_eval_bin(repo_root)?;
    let tmp = tempfile::TempDir::new()?;
    let extras = build_live_extras(repo_root, &tmp.path().join("bins"))?;

    let mut specs = committed_positive_specs();
    let committed_positive = specs.len();
    specs.extend([
        CaseSpec {
            id: "rust_std_tls_bss_default",
            category: "rust_musl_std",
            description: "Rust std (aarch64-unknown-linux-musl, static, release) with std::thread_local! PT_TLS, PT_GNU_RELRO, and 64 KiB .bss",
            elf_rel: extras.rust_std_tls_bss.display().to_string(),
            argv0: "rust_tls_bss",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "rust_std_tls_bss_multi_arg_env",
            category: "rust_musl_std",
            description: "Rust std (aarch64-unknown-linux-musl) with PT_TLS + 64 KiB .bss and custom argv/envp",
            elf_rel: extras.rust_std_tls_bss.display().to_string(),
            argv0: "rust_tls_bss",
            args: vec!["--threads=1".into(), "payload".into()],
            envs: vec!["RUST_BACKTRACE=0".into(), "HOME=/tmp".into()],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "repo_nostd_minimal",
            category: "repo_binary",
            description: "Existing repo static binary Arm64/Testing/ProcessE2E/bin/nostd_minimal.elf",
            elf_rel: "Arm64/Testing/ProcessE2E/bin/nostd_minimal.elf".into(),
            argv0: "nostd_minimal",
            args: vec!["-n".into()],
            envs: vec!["LC_ALL=C".into()],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "echo payload",
            initial_files: vec![],
        },
        CaseSpec {
            id: "repo_std_startup_probe",
            category: "repo_binary",
            description: "Existing repo Rust std startup probe binary Arm64/Testing/ProcessE2E/bin/std_startup_probe.elf",
            elf_rel: "Arm64/Testing/ProcessE2E/bin/std_startup_probe.elf".into(),
            argv0: "std_startup_probe",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "repo_btreemap_vec",
            category: "repo_binary",
            description: "Existing repo Rust std static musl binary Arm64/Testing/ProcessE2E/bin/btreemap_vec.elf",
            elf_rel: "Arm64/Testing/ProcessE2E/bin/btreemap_vec.elf".into(),
            argv0: "btreemap_vec",
            args: vec!["16".into()],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "go_static_default",
            category: "go_arm64",
            description: "Go (GOOS=linux GOARCH=arm64 CGO_ENABLED=0) static binary with 0x10000 text segment, PT_NOTE, and large noptrdata/bss",
            elf_rel: extras.go_static.display().to_string(),
            argv0: "go_static",
            args: vec![],
            envs: vec![],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
        CaseSpec {
            id: "go_static_multi_arg_env",
            category: "go_arm64",
            description: "Go (GOOS=linux GOARCH=arm64 CGO_ENABLED=0) static binary with multi-element argv and envp",
            elf_rel: extras.go_static.display().to_string(),
            argv0: "go_static",
            args: vec!["-test.v".into(), "run_all".into()],
            envs: vec!["GOGC=off".into(), "GOMAXPROCS=1".into()],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        },
    ]);
    let mandatory_positive = specs.len();
    ensure!(
        mandatory_positive == committed_positive + 7,
        "expected {} mandatory positive cases, got {mandatory_positive}",
        committed_positive + 7
    );
    let (optional_positive, optional_skipped) = if let Some(gcc_elf) = &extras.c_gcc_glibc {
        specs.push(CaseSpec {
            id: "c_gcc_glibc_default",
            category: "c_gcc_glibc",
            description: "C with aarch64-linux-gnu-gcc + static glibc at -O2",
            elf_rel: gcc_elf.display().to_string(),
            argv0: "c_gcc_glibc",
            args: vec!["--glibc".into()],
            envs: vec!["LC_ALL=C".into()],
            include_vdso_in_extra_auxv: false,
            stdin_utf8: "",
            initial_files: vec![],
        });
        (1usize, 0usize)
    } else {
        (0usize, 1usize)
    };

    let mut positive_cases = Vec::with_capacity(specs.len());
    for spec in &specs {
        let case_out = tmp.path().join("snaps").join(spec.id);
        positive_cases.push(capture_one_case(
            repo_root,
            &proc_snapshot,
            &qemu,
            spec,
            &case_out,
            false,
        )?);
    }

    let mut rejected_cases = committed_rejected_cases();
    rejected_cases.extend([
        RejectedDiffCase {
            id: "reject_zig_cc_pie".into(),
            category: "fail_closed_zig".into(),
            description: "C compiled with zig cc -target aarch64-linux-musl -fPIE -pie (ET_DYN) rejected fail-closed".into(),
            elf_path: extras.reject_zig_pie.display().to_string(),
            expected_error_substr: "expected static ET_EXEC (2), got e_type=3".into(),
        },
        RejectedDiffCase {
            id: "reject_zig_cc_dynamic_glibc".into(),
            category: "fail_closed_zig".into(),
            description: "C compiled with zig cc -target aarch64-linux-gnu dynamic (PT_INTERP/PT_DYNAMIC) rejected fail-closed".into(),
            elf_path: extras.reject_zig_dynamic.display().to_string(),
            expected_error_substr: "is not supported".into(),
        },
    ]);
    let rejected_count = rejected_cases.len();
    ensure!(
        rejected_count == 8,
        "expected 8 mandatory rejected cases, got {rejected_count}"
    );

    let qemu_version = positive_cases[0].snapshot["runner"]["version"]
        .as_str()
        .unwrap_or("unknown")
        .to_string();
    let live_manifest = ElfLoaderDiffManifest {
        schema_version: 1,
        qemu_version,
        positive_cases,
        rejected_cases,
    };
    let live_manifest_path = tmp.path().join("live_manifest.json");
    fs::write(
        &live_manifest_path,
        serde_json::to_string_pretty(&live_manifest)?,
    )?;

    let st = Command::new(&elf_eval)
        .current_dir(repo_root)
        .arg("--loader-diff")
        .arg(&live_manifest_path)
        .status()
        .context("invoking `elf_eval --loader-diff`")?;
    ensure!(st.success(), "`elf_eval --loader-diff` reported failures");

    for (case_id, elf_rel, extra_args) in [
        ("tiny_asm_default", "Arm64/Testing/ElfLoaderDiff/bin/tiny_asm.elf", vec![]),
        (
            "layout_midpage_bss_default",
            "Arm64/Testing/ElfLoaderDiff/bin/layout_midpage_bss.elf",
            vec!["--hex", "0x402490:32"],
        ),
    ] {
        let snap_json = tmp.path().join("snaps").join(case_id).join("entry.snapshot.json");
        let qemu_out = Command::new(&proc_snapshot)
            .current_dir(repo_root)
            .arg("dump-state")
            .arg(&snap_json)
            .args(&extra_args)
            .output()
            .with_context(|| format!("proc-snapshot dump-state on {case_id}"))?;
        ensure!(qemu_out.status.success(), "proc-snapshot dump-state failed on {case_id}");
        let lean_out = Command::new(&elf_eval)
            .current_dir(repo_root)
            .arg("--dump-load-state")
            .arg(elf_rel)
            .arg(&snap_json)
            .args(&extra_args)
            .output()
            .with_context(|| format!("elf_eval --dump-load-state on {case_id}"))?;
        ensure!(lean_out.status.success(), "elf_eval --dump-load-state failed on {case_id}");
        ensure!(
            qemu_out.stdout == lean_out.stdout,
            "dump-state text mismatch on {case_id}:\nQEMU:\n{}\nLean:\n{}",
            String::from_utf8_lossy(&qemu_out.stdout),
            String::from_utf8_lossy(&lean_out.stdout),
        );
    }

    eprintln!(
        "[elf-loader-diff] SUMMARY: mandatory_positive={mandatory_positive} optional_positive={optional_positive} optional_skipped={optional_skipped} rejected={rejected_count}"
    );
    Ok(())
}
