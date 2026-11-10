// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Reproducible static AArch64 (`ET_EXEC`) builder and drift check for guest Rust binaries
//! (`[TEST ONLY]`).

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};
use object::elf::{
    ELFCLASS64, EM_AARCH64, ET_EXEC, PF_R, PF_W, PF_X, PT_DYNAMIC, PT_GNU_STACK, PT_INTERP, PT_LOAD,
};
use object::read::elf::{FileHeader, ProgramHeader};
use object::{Endianness, Object};
use walkdir::WalkDir;

use super::{fixture_dir, sha256_hex};

/// Static specification of one guest Rust program under `Arm64/Testing/ProcessE2E/src/bin/`.
#[derive(Debug, Clone, Copy)]
pub struct GuestBinarySpec {
    pub name: &'static str,
    pub runtime_flavor: &'static str,
    pub no_std: bool,
    pub description: &'static str,
}

/// Ordered manifest of all 26 static AArch64 guest Rust binaries.
pub const GUEST_BINARIES: &[GuestBinarySpec] = &[
    GuestBinarySpec {
        name: "nostd_minimal",
        runtime_flavor: "no_std_custom_start",
        no_std: true,
        description: "Zero-libc `#![no_std]` custom `_start` binary reading stack `argc`/`argv`/`envp`, growing `brk`, copying `stdin`->`stdout`, writing `stderr`, and calling `exit_group`.",
    },
    GuestBinarySpec {
        name: "exit_codes",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Rust `std` (`#![no_main]` + static musl `__libc_start_main`) returning exit codes `0`, `1`, `2`, `42`, and `255`.",
    },
    GuestBinarySpec {
        name: "echo_cat",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Rust `std` (`io::stdin().read_to_end` -> `io::stdout().write_all`) streaming empty, binary, and multi-page inputs.",
    },
    GuestBinarySpec {
        name: "word_count",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Rust `std` line/word/byte counter formatting counts via `writeln!` to `stdout`.",
    },
    GuestBinarySpec {
        name: "argv_envp",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Rust `std` inspector printing `argc`, `argv[0..argc]`, `envc`, and musl `environ[0..envc]`.",
    },
    GuestBinarySpec {
        name: "arith_sort",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Rust `std` `i64`/`i128` arithmetic, `slice::sort`, FNV-1a digest, and malformed-input `stderr` error path (`exit 2`).",
    },
    GuestBinarySpec {
        name: "btreemap_vec",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Hashbrown-free `BTreeMap<String, Vec<u8>>` insert/remove/range workload over `SYS_brk` plus 32 KiB `SYS_mmap` + `SYS_munmap` scratch buffer.",
    },
    GuestBinarySpec {
        name: "stderr_stdio",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Interleaved `io::stdout()` (`fd 1`) and `io::stderr()` (`fd 2`) writes with `exit 0` and `exit 1` modes.",
    },
    GuestBinarySpec {
        name: "getrandom_use",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "`SYS_getrandom` (`278`) conformance checker (`0`, `GRND_NONBLOCK`, `-EINVAL`, `-EFAULT`) plus live/oracle 16-byte hex dump mode.",
    },
    GuestBinarySpec {
        name: "session_store",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Stateful pre-key session protocol CLI (`keygen`/`init`/`send`/`recv`) with atomic `BTreeMap` directory stores, `coins` randomness file, `0`-byte pre-key deletion, and VFS edge-case probes.",
    },
    GuestBinarySpec {
        name: "std_startup_probe",
        runtime_flavor: "std_lang_start",
        no_std: false,
        description: "Full Rust `fn main()` (`std::rt::lang_start`) binary capturing every startup/teardown syscall emitted before and after `main`.",
    },
    GuestBinarySpec {
        name: "unmodified_std_probe",
        runtime_flavor: "std_no_main_unmodified",
        no_std: false,
        description: "Zero-shim `#![no_main]` `std` binary probing stock `std::fs` (`fcntl`), stock musl `mallocng` (`mmap PROT_NONE`), `panic!`, `abort()`, `udf #0`, `brk #1`, and `brk #0`.",
    },
    GuestBinarySpec {
        name: "base64_codec",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "RFC 4648 base64 encoder (76-column wrapping) and whitespace-tolerant decoder reporting the offset of invalid symbols, misplaced padding, or truncated quanta (`exit 1`).",
    },
    GuestBinarySpec {
        name: "hexdump",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "`hexdump -C` canonical formatter (offset, two 8-byte hex groups, `|ascii|` gutter) with `*` squeezing of repeated rows and `-v` to disable it.",
    },
    GuestBinarySpec {
        name: "sha256sum",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Crate-free FIPS 180-4 SHA-256 of `stdin` (`<hex>  -`) plus `-c <hex>` verification mode (`OK` / `FAILED` with `exit 1`).",
    },
    GuestBinarySpec {
        name: "rle_codec",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Byte-level `(count, byte)` run-length compressor/decompressor with corrupt-stream detection (`exit 1`) and an in-memory roundtrip self-check mode.",
    },
    GuestBinarySpec {
        name: "sort_uniq",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "`sort | uniq -c` emulation over `stdin` lines via `slice::sort_unstable`, with `-r` (reverse), `-n` (by count), and `-d` (duplicates only).",
    },
    GuestBinarySpec {
        name: "grep_lite",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Fixed-string `grep` over `stdin` with `-i`/`-v`/`-n`/`-c` flags and POSIX exit status (`0` match, `1` no match, `2` usage).",
    },
    GuestBinarySpec {
        name: "rpn_calc",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Per-line reverse-Polish `i64` calculator with checked arithmetic and stack operations, reporting underflow, division by zero, overflow, or unknown tokens on `stderr` (`exit 1`).",
    },
    GuestBinarySpec {
        name: "file_copy",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Stock `std::fs` file copy / ASCII-uppercase transform with `File::open` read-back verification, and a multi-file `cat` mode reporting `ENOENT` (`exit 1`).",
    },
    GuestBinarySpec {
        name: "json_lint",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Non-recursive JSON tokenizer and bracket matcher validating escapes, numbers, and literals, printing token-class counts and max depth or the first error offset (`exit 1`).",
    },
    GuestBinarySpec {
        name: "bignum",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Base-`10^9` arbitrary-precision factorial, Fibonacci, and power-of-two printer with digit count and digit sum.",
    },
    GuestBinarySpec {
        name: "matrix_mul",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Deterministic LCG-seeded `N x N` `i64` matrix multiply with trace, FNV-1a checksum, first row, and `A * I == A` self-check.",
    },
    GuestBinarySpec {
        name: "env_lookup",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "`std::env::var_os` (musl `getenv`) lookups over the initial environment (`exit 1` if any name is unset) and a sorted raw-`environ` listing mode.",
    },
    GuestBinarySpec {
        name: "rot_cipher",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "ROT13, signed Caesar shift, and Atbash substitution of `stdin` selected by `argv`, plus a letter-frequency histogram mode.",
    },
    GuestBinarySpec {
        name: "collatz_stats",
        runtime_flavor: "std_no_main_musl",
        no_std: false,
        description: "Collatz chain statistics over an `argv` range: longest chain, highest peak with `u64` overflow checks, total and median length, and a `BTreeMap` histogram.",
    },
];

/// Summary of one compiled and validated static AArch64 `ET_EXEC` binary.
#[derive(Debug, Clone)]
pub struct BuiltElfInfo {
    pub spec: GuestBinarySpec,
    pub source_rel: String,
    pub elf_rel: String,
    pub size_bytes: u64,
    pub sha256: String,
    pub entry_va: u64,
}

/// Pinned Rust toolchain version matching `.github/workflows/ci.yml` (`toolchain: '1.98.1'`).
pub const PINNED_RUST_TOOLCHAIN: &str = "1.98.1";

fn find_rustc_and_lld() -> Result<(PathBuf, String, PathBuf, PathBuf)> {
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
    let ver_out = Command::new(&rustc)
        .env_remove("RUSTUP_TOOLCHAIN")
        .arg("--version")
        .output()
        .context("failed to invoke `rustc --version`")?;
    if !ver_out.status.success() {
        bail!("`rustc --version` failed");
    }
    let rustc_version = String::from_utf8_lossy(&ver_out.stdout).trim().to_owned();

    let sysroot_out = Command::new(&rustc)
        .env_remove("RUSTUP_TOOLCHAIN")
        .arg("--print")
        .arg("sysroot")
        .output()
        .context("failed to invoke `rustc --print sysroot`")?;
    if !sysroot_out.status.success() {
        bail!("`rustc --print sysroot` failed");
    }
    let sysroot = PathBuf::from(String::from_utf8_lossy(&sysroot_out.stdout).trim());
    let rustlib = sysroot.join("lib").join("rustlib");
    let mut lld_candidates: Vec<PathBuf> = WalkDir::new(&rustlib)
        .into_iter()
        .filter_map(std::result::Result::ok)
        .map(|e| e.into_path())
        .filter(|p| {
            p.is_file()
                && p.file_name().and_then(|s| s.to_str()) == Some("ld.lld")
                && p.parent()
                    .and_then(|d| d.file_name())
                    .and_then(|s| s.to_str())
                    == Some("gcc-ld")
        })
        .collect();
    lld_candidates.sort();
    let lld = lld_candidates.into_iter().next().ok_or_else(|| {
        anyhow!(
            "bundled `gcc-ld/ld.lld` not found under {} (install rustup component `llvm-tools-preview`)",
            rustlib.display()
        )
    })?;
    Ok((rustc, rustc_version, sysroot, lld))
}

/// Validate that `bytes` is a static, non-PIE AArch64 Linux `ET_EXEC` binary compatible with `loadElf`.
pub fn validate_static_aarch64_elf(name: &str, bytes: &[u8]) -> Result<u64> {
    let endian = Endianness::Little;
    let hdr = object::elf::FileHeader64::<Endianness>::parse(bytes)
        .with_context(|| format!("{name}: invalid ELF64 header"))?;
    if hdr.e_ident.class != ELFCLASS64 {
        bail!("{name}: expected ELF64 (`EI_CLASS`), got {}", hdr.e_ident.class);
    }
    if hdr.e_machine(endian) != EM_AARCH64 {
        bail!("{name}: expected EM_AARCH64, got {}", hdr.e_machine(endian));
    }
    if hdr.e_type(endian) != ET_EXEC {
        bail!(
            "{name}: expected non-PIE static executable ET_EXEC (2), got {}",
            hdr.e_type(endian)
        );
    }
    let phdrs = hdr
        .program_headers(endian, bytes)
        .with_context(|| format!("{name}: invalid ELF program headers"))?;
    let mut load_count = 0usize;
    for ph in phdrs {
        let p_type = ph.p_type(endian);
        let p_flags = ph.p_flags(endian);
        if p_type == PT_INTERP {
            bail!("{name}: unexpected PT_INTERP in static executable");
        }
        if p_type == PT_DYNAMIC {
            bail!("{name}: unexpected PT_DYNAMIC in static executable");
        }
        if p_type == PT_GNU_STACK && (p_flags & PF_X) != 0 {
            bail!("{name}: unexpected executable PT_GNU_STACK");
        }
        if p_type == PT_LOAD {
            load_count += 1;
            if (p_flags & PF_W) != 0 && (p_flags & PF_X) != 0 {
                bail!("{name}: W+X PT_LOAD segment forbidden");
            }
            if (p_flags & (PF_R | PF_W | PF_X)) == 0 {
                bail!("{name}: PT_LOAD segment with empty permissions");
            }
        }
    }
    if load_count == 0 {
        bail!("{name}: zero PT_LOAD segments");
    }
    let parsed = object::File::parse(bytes).with_context(|| format!("{name}: object parse failed"))?;
    Ok(parsed.entry())
}

fn copy_guest_sources_to(src_root: &Path, dst_src: &Path) -> Result<()> {
    for entry in WalkDir::new(src_root) {
        let entry = entry?;
        let rel = entry.path().strip_prefix(src_root)?;
        let target = dst_src.join(rel);
        if entry.file_type().is_dir() {
            fs::create_dir_all(&target)?;
        } else if entry.file_type().is_file() {
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(entry.path(), &target)?;
        }
    }
    Ok(())
}

/// Compile all 26 guest binaries inside a fresh temporary directory using the deterministic
/// static `aarch64-unknown-linux-musl` + `gcc-ld/ld.lld` recipe, then either write `bin/*.elf`
/// (`check_only == false`) or assert byte-for-byte equality with committed `bin/*.elf` (`check_only == true`).
pub fn build_or_check_elfs(repo_root: &Path, check_only: bool) -> Result<(String, Vec<BuiltElfInfo>)> {
    let (rustc, rustc_version, sysroot, lld) = find_rustc_and_lld()?;
    let fix_dir = fixture_dir(repo_root);
    let src_dir = fix_dir.join("src");
    let bin_dir = fix_dir.join("bin");
    if !check_only {
        fs::create_dir_all(&bin_dir)?;
    }

    // Build inside an ephemeral directory with random host path components so every `build` and
    // `build --check` proves path-independent, reproducible output bytes.
    // Stage a clean sysroot that omits `lib/rustlib/src` so `rustc` emits identical `/rustc/<hash>`
    // monomorphized panic locations whether or not the host has the `rust-src` component installed.
    let work_tmp = tempfile::TempDir::new().context("failed to create temporary build dir")?;
    let staged_root = work_tmp.path().join("guest_build");
    let staged_src = staged_root.join("src");
    let staged_out = staged_root.join("out");
    let staged_sysroot = work_tmp.path().join("clean_sysroot");
    let staged_rustlib = staged_sysroot.join("lib").join("rustlib");
    fs::create_dir_all(&staged_out)?;
    fs::create_dir_all(&staged_rustlib)?;
    for entry in fs::read_dir(sysroot.join("lib").join("rustlib"))
        .context("failed to read sysroot `lib/rustlib`")?
    {
        let entry = entry?;
        let name = entry.file_name();
        if name.as_os_str() != "src" {
            std::os::unix::fs::symlink(entry.path(), staged_rustlib.join(name))?;
        }
    }
    copy_guest_sources_to(&src_dir, &staged_src)?;

    let remap_workspace = format!("{}=/workspace", staged_root.display());
    let remap_staged_sysroot = format!("{}=/rust-sysroot", staged_sysroot.display());
    let remap_sysroot = format!("{}=/rust-sysroot", sysroot.display());

    let mut built = Vec::with_capacity(GUEST_BINARIES.len());
    let mut drift_errors: Vec<String> = Vec::new();

    for &spec in GUEST_BINARIES {
        let rs_file = staged_src.join("bin").join(format!("{}.rs", spec.name));
        let out_elf = staged_out.join(format!("{}.elf", spec.name));

        let mut cmd = Command::new(&rustc);
        cmd.current_dir(&staged_root)
            .env_remove("RUSTUP_TOOLCHAIN")
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env("LC_ALL", "C")
            .env("SOURCE_DATE_EPOCH", "0")
            .arg("--sysroot")
            .arg(&staged_sysroot)
            .arg("--edition=2024")
            .arg("--target=aarch64-unknown-linux-musl")
            .arg("-O")
            .arg("-C")
            .arg("codegen-units=1")
            .arg("-C")
            .arg("panic=abort")
            .arg("-C")
            .arg("debuginfo=0")
            .arg("-C")
            .arg("relocation-model=static")
            .arg("-C")
            .arg(format!("linker={}", lld.display()))
            .arg("-C")
            .arg("link-arg=--build-id=none")
            .arg("-C")
            .arg("link-arg=--strip-all")
            .arg("--remap-path-prefix")
            .arg(&remap_workspace)
            .arg("--remap-path-prefix")
            .arg(&remap_staged_sysroot)
            .arg("--remap-path-prefix")
            .arg(&remap_sysroot);

        if spec.no_std {
            cmd.arg("-C")
                .arg("link-self-contained=no")
                .arg("-C")
                .arg("link-arg=-nostdlib")
                .arg("-C")
                .arg("link-arg=-static");
        }

        cmd.arg(&rs_file).arg("-o").arg(&out_elf);

        let output = cmd
            .output()
            .with_context(|| format!("failed to invoke rustc for {}", spec.name))?;
        if !output.status.success() {
            bail!(
                "rustc failed building {}:\nstdout:\n{}\nstderr:\n{}",
                spec.name,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }

        let bytes = fs::read(&out_elf)?;
        let entry_va = validate_static_aarch64_elf(spec.name, &bytes)?;
        let sha256 = sha256_hex(&bytes);
        let committed_path = bin_dir.join(format!("{}.elf", spec.name));

        if check_only {
            if !committed_path.is_file() {
                drift_errors.push(format!(
                    "missing committed ELF {} (run `./scripts/process-e2e build`)",
                    committed_path.display()
                ));
            } else {
                let committed = fs::read(&committed_path)?;
                let committed_sha = sha256_hex(&committed);
                if committed != bytes {
                    drift_errors.push(format!(
                        "{}: ELF drift detected (committed {} B sha256={}, rebuilt {} B sha256={})",
                        spec.name,
                        committed.len(),
                        committed_sha,
                        bytes.len(),
                        sha256
                    ));
                }
            }
        } else {
            fs::write(&committed_path, &bytes)?;
            fs::set_permissions(&committed_path, fs::Permissions::from_mode(0o755))?;
        }

        built.push(BuiltElfInfo {
            spec,
            source_rel: format!("Arm64/Testing/ProcessE2E/src/bin/{}.rs", spec.name),
            elf_rel: format!("Arm64/Testing/ProcessE2E/bin/{}.elf", spec.name),
            size_bytes: bytes.len() as u64,
            sha256,
            entry_va,
        });
    }

    if !drift_errors.is_empty() {
        bail!(
            "process-e2e ELF drift check failed:\n  - {}",
            drift_errors.join("\n  - ")
        );
    }

    Ok((rustc_version, built))
}

/// Read metadata directly from the already checked-in `bin/*.elf` binaries without invoking `rustc`.
pub fn load_checked_in_elf_infos(repo_root: &Path) -> Result<Vec<BuiltElfInfo>> {
    let bin_dir = fixture_dir(repo_root).join("bin");
    let mut infos = Vec::with_capacity(GUEST_BINARIES.len());
    for &spec in GUEST_BINARIES {
        let p = bin_dir.join(format!("{}.elf", spec.name));
        let bytes = fs::read(&p)
            .with_context(|| format!("missing ELF {} (run `./scripts/process-e2e build`)", p.display()))?;
        let entry_va = validate_static_aarch64_elf(spec.name, &bytes)?;
        infos.push(BuiltElfInfo {
            spec,
            source_rel: format!("Arm64/Testing/ProcessE2E/src/bin/{}.rs", spec.name),
            elf_rel: format!("Arm64/Testing/ProcessE2E/bin/{}.elf", spec.name),
            size_bytes: bytes.len() as u64,
            sha256: sha256_hex(&bytes),
            entry_va,
        });
    }
    Ok(infos)
}
