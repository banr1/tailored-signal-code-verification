// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Untrusted Build Driver, Archive Unpacker, and Reachability Selector
//! (`untrusted_driver`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (orchestrates `cargo rustc --emit=obj` and `zig cc` builds,
//!   unpacks `.rlib`/`.a` archives, computes dead-section reachability sets, and loads
//!   `translation.toml` configurations; every resulting byte buffer and section-index filter is
//!   validated by [`crate::trusted_extractor`], which fails closed if any required section or
//!   symbol is missing or malformed).
//! - **Purpose:**
//!   1. Loads `translation.toml` configurations and CLI flags ([`config`]).
//!   2. Resolves upstream git checkouts and vendor symlinks (`resolve_upstream_src`,
//!      `link_vendor_symlink`).
//!   3. Invokes `cargo rustc --emit=obj` (with deterministic path remapping) or `zig cc`
//!      ([`Toolchain`], [`build_crate_object`], `extract_native_object`).
//!   4. Unpacks `.rlib` and `.a` archives, computes local-relocation section reachability
//!      ([`root_section_closure`]), scans `.rlib` symbol definitions ([`scan_rlib_definitions`]),
//!      and hands the raw `.o` bytes and extern metadata to [`crate::trusted_extractor`].
//!
//! # Key Types & Functions
//! - [`Toolchain`], [`extract`]: Build toolchain runner and top-level object/extern extraction
//!   driver for an [`ExportConfig`].
//! - [`resolve_crates`], [`build_crate_object`], [`path_remaps`], [`check_no_host_paths`]:
//!   Reproducible Rust crate compilation.
//! - [`find_zig_binary`], [`native_cc_args_with_flags`]: Deterministic C compilation via `zig cc`.
//! - [`root_section_closure`], [`scan_rlib_definitions`]: Reachable section selection and `.rlib`
//!   external symbol table scanning.
//!
//! # When to Read This File
//! - Read this file when debugging `cargo rustc` / `zig cc` invocation flags, host-path remapping,
//!   `.rlib`/`.a` archive member selection, or upstream source checkout resolution.

pub mod config;
pub mod externs;
pub mod pipeline;
pub use config::*;
pub use externs::{
    NeededExtern, RlibDef, check_extern_collisions, needed_externs, resolve_externs,
    resolve_externs_with_config,
};

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Cursor;
use std::os::unix::fs as unix_fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, anyhow, bail};
use cargo_metadata::Message;
use itertools::Itertools;
use object::SymbolIndex;
use object::elf;
use object::read::archive::ArchiveFile;
use object::read::elf::{SectionHeader, Sym};

use crate::trusted_common::{
    ExternKind, Extraction, ObjObject, SymBind, SymSection, sha256_hex,
};
use crate::trusted_extractor::{
    Trim, check_name_collisions, demangle_rust_symbol, disambiguate_symbol_names, parse_c_object,
    parse_elf_rel, parse_object, parse_object_with,
};

fn git_output(args: &[&str], cwd: &Path) -> Option<String> {
    let out = Command::new("git")
        .args(args)
        .current_dir(cwd)
        .output()
        .ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
}

// ---------------------------------------------------------------------------
// Toolchain Discovery & Execution
// ---------------------------------------------------------------------------

pub struct Toolchain {
    pub repo_root: PathBuf,
    pub rustc_version: String,
    pub path_aliases: Vec<(String, String)>,
}

impl Toolchain {
    pub fn new(repo_root: PathBuf) -> Result<Self> {
        if which::which("rustc").is_err() || which::which("cargo").is_err() {
            bail!(
                "`rustc`/`cargo` are not on PATH; a Rust toolchain with the {DEFAULT_TARGET} \
                 target is required to build this repository (see README.md)"
            );
        }
        let ver_out = Command::new("rustc")
            .args(["--version", "--verbose"])
            .current_dir(&repo_root)
            .output()
            .context("failed to invoke `rustc --version --verbose`")?;
        let rustc_version = String::from_utf8_lossy(&ver_out.stdout).trim().to_string();
        let path_aliases = vec![(
            repo_root.to_string_lossy().into_owned(),
            "$REPO".to_string(),
        )];
        Ok(Self {
            repo_root,
            rustc_version,
            path_aliases,
        })
    }

    pub fn add_alias(&mut self, path: &Path, alias: impl Into<String>) {
        let entry = (path.to_string_lossy().into_owned(), alias.into());
        if !self.path_aliases.contains(&entry) {
            self.path_aliases.push(entry);
        }
    }

    pub fn format_cmd(&self, argv: &[impl AsRef<str>], env: &[(&str, &str)]) -> String {
        let prefix = env.iter().map(|(k, v)| format!("{k}='{v}' ")).join("");
        let rendered = argv.iter().map(AsRef::as_ref).join(" ");
        let mut text = format!("{prefix}{rendered}");
        // Longest host path first, so that a directory nested in another aliased one (e.g. an
        // upstream checkout below the crate's repository) shows as its own alias however the
        // aliases were added.
        let mut aliases: Vec<&(String, String)> = self.path_aliases.iter().collect();
        aliases.sort_by_key(|(real, _)| std::cmp::Reverse(real.len()));
        for (real, alias) in aliases {
            text = text.replace(real.as_str(), alias);
        }
        text
    }

    /// Run `argv` (with `CARGO_ENCODED_RUSTFLAGS` removed, so `RUSTFLAGS` in `env` applies) and
    /// return its stdout. On failure, print its stdout and stderr.
    pub fn run(
        &self,
        argv: &[impl AsRef<str>],
        cwd: Option<&Path>,
        env: &[(&str, &str)],
    ) -> Result<String> {
        let prog = argv[0].as_ref();
        let mut cmd = Command::new(prog);
        cmd.args(argv[1..].iter().map(AsRef::as_ref))
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .envs(env.iter().copied());
        if let Some(dir) = cwd {
            cmd.current_dir(dir);
        }
        let out = cmd
            .output()
            .with_context(|| format!("failed to spawn `{prog}`"))?;
        if !out.status.success() {
            eprint!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            bail!(
                "command failed ({}): {}",
                out.status,
                argv.iter().map(AsRef::as_ref).join(" ")
            );
        }
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    }

    pub fn provenance(
        &self,
        config_rel: &str,
        config_hash: &str,
        commands: &[(String, String)],
    ) -> Vec<(String, String)> {
        let version = self.rustc_version.lines().map(str::trim).join(" / ");
        let mut tcb_bytes = Vec::new();
        tcb_bytes.extend_from_slice(include_bytes!("../trusted_common/mod.rs"));
        tcb_bytes.extend_from_slice(include_bytes!("../trusted_extractor/mod.rs"));
        tcb_bytes.extend_from_slice(include_bytes!("../trusted_extractor/extracted_obj.rs"));
        let exporter_hash = sha256_hex(&tcb_bytes);
        let mut entries = vec![
            ("Toolchain".into(), version),
            (
                "Exporter (TCB)".into(),
                format!(
                    "`tools/rust-obj2lean/src/{{trusted_common,trusted_extractor}}` sha256 {exporter_hash}"
                ),
            ),
            (
                "Translation config".into(),
                format!("`{config_rel}` sha256 {config_hash}"),
            ),
        ];
        entries.extend(
            commands
                .iter()
                .map(|(label, cmd)| (format!("Command ({label})"), format!("`{cmd}`"))),
        );
        entries
    }
}

// ---------------------------------------------------------------------------
// `.rlib` Symbol Definition Scanner
// ---------------------------------------------------------------------------

/// Scan every ELF member of `rlibs` for global/weak definitions of the symbols in `wanted`
/// (exact mangled names). Members that are not AArch64 relocatable ELF files are skipped.
pub fn scan_rlib_definitions(
    rlibs: &[PathBuf],
    wanted: &BTreeSet<String>,
) -> Result<BTreeMap<String, Vec<RlibDef>>> {
    let mut defs: BTreeMap<String, Vec<RlibDef>> = BTreeMap::new();
    for rlib in rlibs {
        let bytes = fs::read(rlib).with_context(|| format!("failed to read {}", rlib.display()))?;
        let archive = ArchiveFile::parse(&*bytes)
            .map_err(|e| anyhow!("{}: not an archive: {e}", rlib.display()))?;
        let rlib_name = rlib.file_name().unwrap_or_default().to_string_lossy();
        for member in archive.members() {
            let member = member.map_err(|e| anyhow!("{}: {e}", rlib.display()))?;
            let member_name = String::from_utf8_lossy(member.name()).into_owned();
            let data = member
                .data(&*bytes)
                .map_err(|e| anyhow!("{}({member_name}): {e}", rlib.display()))?;
            let Ok(e) = parse_elf_rel(data) else {
                continue;
            };
            for (i, sym) in e.symbols.symbols().iter().enumerate() {
                if !matches!(sym.st_bind(), elf::STB_GLOBAL | elf::STB_WEAK) {
                    continue;
                }
                let shndx = sym.st_shndx(e.endian);
                if shndx == elf::SHN_UNDEF || shndx == elf::SHN_COMMON {
                    continue;
                }
                let Ok(raw) = e.symbols.symbol_name(e.endian, sym) else {
                    continue;
                };
                let Ok(raw) = std::str::from_utf8(raw) else {
                    continue;
                };
                if !wanted.contains(raw) {
                    continue;
                }
                let origin = format!("{rlib_name}({member_name})");
                let kind = match sym.st_type() {
                    elf::STT_FUNC => ExternKind::Func,
                    elf::STT_OBJECT => ExternKind::Object,
                    elf::STT_TLS => ExternKind::Tls,
                    t => bail!("`{raw}` is defined in {origin} with unsupported type {t}"),
                };
                let align = match e
                    .symbols
                    .symbol_section(e.endian, sym, SymbolIndex(i))
                    .ok()
                    .flatten()
                {
                    Some(j) => e
                        .sections
                        .section(j)
                        .map_err(|err| anyhow!("{origin}: {err}"))?
                        .sh_addralign(e.endian)
                        .max(1),
                    None => 1,
                };
                defs.entry(raw.to_string()).or_default().push(RlibDef {
                    kind,
                    size: sym.st_size(e.endian),
                    align,
                    origin,
                });
            }
        }
    }
    Ok(defs)
}

/// Locate the first `.rlib` index in `rlibs` defining each requested mangled global/weak function
/// symbol in `wanted`.
pub fn scan_rlib_func_indices(
    rlibs: &[PathBuf],
    wanted: &BTreeSet<String>,
) -> Result<BTreeMap<String, usize>> {
    let mut found: BTreeMap<String, usize> = BTreeMap::new();
    if wanted.is_empty() {
        return Ok(found);
    }
    for (idx, rlib) in rlibs.iter().enumerate() {
        let bytes = fs::read(rlib).with_context(|| format!("failed to read {}", rlib.display()))?;
        let archive = ArchiveFile::parse(&*bytes)
            .map_err(|e| anyhow!("{}: not an archive: {e}", rlib.display()))?;
        for member in archive.members() {
            let member = member.map_err(|e| anyhow!("{}: {e}", rlib.display()))?;
            let member_name = String::from_utf8_lossy(member.name()).into_owned();
            let data = member
                .data(&*bytes)
                .map_err(|e| anyhow!("{}({member_name}): {e}", rlib.display()))?;
            let Ok(e) = parse_elf_rel(data) else {
                continue;
            };
            for sym in e.symbols.symbols() {
                if !matches!(sym.st_bind(), elf::STB_GLOBAL | elf::STB_WEAK)
                    || sym.st_type() != elf::STT_FUNC
                {
                    continue;
                }
                let shndx = sym.st_shndx(e.endian);
                if shndx == elf::SHN_UNDEF || shndx == elf::SHN_COMMON {
                    continue;
                }
                let Ok(raw) = e.symbols.symbol_name(e.endian, sym) else {
                    continue;
                };
                let Ok(raw) = std::str::from_utf8(raw) else {
                    continue;
                };
                if wanted.contains(raw) {
                    found.entry(raw.to_string()).or_insert(idx);
                }
            }
        }
    }
    Ok(found)
}

// ---------------------------------------------------------------------------
// Crate Compilation (`cargo rustc --emit=obj`)
// ---------------------------------------------------------------------------

/// A configured crate resolved against `cargo metadata`.
#[derive(Clone, Debug)]
pub struct ResolvedCrate {
    /// Package name (for `cargo rustc -p`).
    pub package: String,
    /// Library target (crate) name, `-` replaced by `_`.
    pub lib_name: String,
}

fn find_crate_in_packages(
    packages: &[cargo_metadata::Package],
    spec: &str,
    only_path_deps: bool,
) -> Vec<ResolvedCrate> {
    let want = spec.replace('-', "_");
    packages
        .iter()
        .filter(|p| !only_path_deps || p.source.is_none())
        .filter_map(|p| {
            let lib = p.targets.iter().find(|t| t.is_lib() || t.is_rlib())?;
            let lib_name = lib.name.replace('-', "_");
            (p.name.replace('-', "_") == want || lib_name == want).then(|| ResolvedCrate {
                package: p.name.to_string(),
                lib_name,
            })
        })
        .collect()
}

/// Resolve each configured crate name (package name or library name, `-`/`_` insensitive)
/// against the packages of the workspace in `crate_dir`, falling back to path packages
/// (`p.source.is_none()`) in the dependency graph when not found in `--no-deps`.
pub fn resolve_crates(crate_dir: &Path, crates: &[String]) -> Result<Vec<ResolvedCrate>> {
    let meta = cargo_metadata::MetadataCommand::new()
        .current_dir(crate_dir)
        .no_deps()
        .exec()
        .with_context(|| format!("`cargo metadata` failed in `{}`", crate_dir.display()))?;
    let mut full_meta: Option<cargo_metadata::Metadata> = None;
    crates
        .iter()
        .map(|spec| {
            let mut matches = find_crate_in_packages(&meta.packages, spec, false);
            if matches.is_empty() {
                let full = match &full_meta {
                    Some(m) => m,
                    None => full_meta.insert(
                        cargo_metadata::MetadataCommand::new()
                            .current_dir(crate_dir)
                            .exec()
                            .with_context(|| {
                                format!("`cargo metadata` failed in `{}`", crate_dir.display())
                            })?,
                    ),
                };
                matches = find_crate_in_packages(&full.packages, spec, true);
                if matches.is_empty() {
                    matches = find_crate_in_packages(&full.packages, spec, false);
                }
            }
            match matches.as_slice() {
                [one] => Ok(one.clone()),
                [] => bail!(
                    "no package with a library named `{spec}` in `{}`",
                    crate_dir.display()
                ),
                _ => bail!("crate `{spec}` is ambiguous in `{}`", crate_dir.display()),
            }
        })
        .collect()
}

/// The single relocatable object of one crate, and the rlibs of its dependencies.
pub struct CrateObject {
    pub elf_bytes: Vec<u8>,
    pub rlibs: Vec<PathBuf>,
    pub build_cmd: String,
}

/// Fixed replacement of `<CARGO_HOME>/registry/src` (crates.io sources); see `path_remaps`.
pub const REMAPPED_REGISTRY_SRC: &str = "/cargo-registry";

/// Fixed replacement of cargo's target directory (build scripts' `OUT_DIR`s); see `path_remaps`.
pub const REMAPPED_TARGET_DIR: &str = "/cargo-target";

/// Fixed replacement of `<CARGO_HOME>/git/checkouts` (git dependencies); see `path_remaps`.
pub const REMAPPED_GIT_CHECKOUTS: &str = "/cargo-git";

/// Prefix of the fixed replacement of the `[upstream]` source directory; see
/// `upstream_remap_target`.
pub const REMAPPED_UPSTREAM_PREFIX: &str = "/upstream";

/// The fixed replacement `/upstream/<name>/<commit>` of the source directory of the `[upstream]`
/// checkout `name` at `commit` (see `path_remaps`). It names the commit so that `RUSTFLAGS`, and
/// with them every unit's cargo fingerprint, change whenever the checkout does: cargo decides
/// whether a path dependency is fresh by source mtimes, which miss a `vendor_symlink` retargeted
/// to (or a directory replaced by) an older tree.
pub fn upstream_remap_target(name: &str, commit: &str) -> Result<String> {
    if name.is_empty()
        || name
            .chars()
            .any(|c| c.is_whitespace() || c.is_control() || c == '=' || c == '/')
    {
        bail!("invalid upstream name `{name}` for --remap-path-prefix");
    }
    if commit.is_empty() || !commit.chars().all(|c| c.is_ascii_hexdigit()) {
        bail!("invalid upstream commit `{commit}` for --remap-path-prefix");
    }
    Ok(format!("{REMAPPED_UPSTREAM_PREFIX}/{name}/{commit}"))
}

/// `CARGO_HOME` as cargo resolves it: `$CARGO_HOME` if set and non-empty (required to be
/// absolute here, since cargo runs in another directory), else `$HOME/.cargo`.
pub fn cargo_home() -> Result<PathBuf> {
    let home = match env::var_os("CARGO_HOME").filter(|v| !v.is_empty()) {
        Some(v) => PathBuf::from(v),
        None => PathBuf::from(env::var_os("HOME").context("neither CARGO_HOME nor HOME is set")?)
            .join(".cargo"),
    };
    if !home.is_absolute() {
        bail!("CARGO_HOME `{}` must be an absolute path", home.display());
    }
    Ok(home)
}

/// cargo's target directory for builds in `crate_dir` (honours `CARGO_TARGET_DIR` and
/// `build.target-dir`).
pub fn cargo_target_dir(crate_dir: &Path) -> Result<PathBuf> {
    let meta = cargo_metadata::MetadataCommand::new()
        .current_dir(crate_dir)
        .no_deps()
        .exec()
        .with_context(|| format!("`cargo metadata` failed in `{}`", crate_dir.display()))?;
    Ok(meta.target_directory.into_std_path_buf())
}

/// Canonicalize `dir`, or its longest existing ancestor if `dir` does not exist yet (e.g.
/// `<CARGO_HOME>/git/checkouts` or `target/` before cargo runs).
fn canonicalize_existing_prefix(dir: &Path) -> Option<PathBuf> {
    dir.canonicalize().ok().or_else(|| {
        dir.ancestors().find_map(|ancestor| {
            let canon_ancestor = ancestor.canonicalize().ok()?;
            let rel = dir.strip_prefix(ancestor).ok()?;
            Some(canon_ancestor.join(rel))
        })
    })
}

/// `dir` (as given, and canonicalized if that differs), each spelling with its
/// `--remap-path-prefix=<dir>=<to>` flag. `what` names the directory in errors.
fn prefix_remaps(what: &str, dir: &Path, to: &str) -> Result<Vec<(String, String)>> {
    let mut dirs = vec![dir.to_path_buf()];
    if let Some(canon) = canonicalize_existing_prefix(dir)
        && canon != dir
    {
        dirs.push(canon);
    }
    dirs.into_iter()
        .map(|d| {
            let d = d
                .to_str()
                .with_context(|| format!("{what} path `{}` is not UTF-8", d.display()))?
                .to_string();
            if d.chars()
                .any(|c| c.is_ascii_whitespace() || c.is_ascii_control())
            {
                bail!("{what} path `{d}` contains whitespace; it cannot be passed in RUSTFLAGS");
            }
            if d.contains('=') {
                bail!(
                    "{what} path `{d}` contains '='; it cannot be passed in --remap-path-prefix"
                );
            }
            let flag = format!("--remap-path-prefix={d}={to}");
            Ok((d, flag))
        })
        .collect()
}

/// The active toolchain's sysroot directory (`rustc --print sysroot`), as seen from `crate_dir`.
pub fn rustc_sysroot(crate_dir: &Path) -> Result<PathBuf> {
    let out = Command::new("rustc")
        .args(["--print", "sysroot"])
        .current_dir(crate_dir)
        .output()
        .context("failed to invoke `rustc --print sysroot`")?;
    if !out.status.success() {
        bail!(
            "`rustc --print sysroot` failed ({}): {}",
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    let sysroot = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    if !sysroot.is_absolute() {
        bail!(
            "rustc sysroot `{}` must be an absolute path",
            sysroot.display()
        );
    }
    Ok(sysroot)
}

/// Parse the `commit-hash: <sha>` field from `rustc --version --verbose` output.
pub fn rustc_commit_hash(rustc_version: &str) -> Result<&str> {
    let hash = rustc_version
        .lines()
        .find_map(|line| line.trim().strip_prefix("commit-hash:"))
        .map(str::trim)
        .filter(|h| !h.is_empty() && *h != "unknown")
        .ok_or_else(|| {
            anyhow!("failed to parse `commit-hash:` from `rustc --version --verbose`")
        })?;
    if hash
        .chars()
        .any(|c| c.is_ascii_whitespace() || c.is_ascii_control() || c == '=')
    {
        bail!("invalid `commit-hash` `{hash}` in `rustc --version --verbose`");
    }
    Ok(hash)
}

/// The host directories rustc compiles crates from with absolute paths, each with the
/// `--remap-path-prefix` flag that replaces it by a fixed path: `<cargo_home>/registry/src` by
/// `/cargo-registry` (crates.io dependencies), cargo's target directory `target_dir` by
/// `/cargo-target` (generated sources in build scripts' `OUT_DIR`s that are `include!`d),
/// `<cargo_home>/git/checkouts` by `/cargo-git` (git dependencies), and
/// `<sysroot>/lib/rustlib/src/rust` by `/rustc/<rustc_commit>` (when the `rust-src` component is
/// installed, rustc rewrites `/rustc/<commit>/library/...` in precompiled `core`/`alloc`/`std`
/// metadata to `<sysroot>/lib/rustlib/src/rust/library/...` before applying `--remap-path-prefix`).
/// With `upstream = Some((src, to))` (the `[upstream]` source directory and its replacement from
/// `upstream_remap_target`), also `src` by `to`, in its absolute spellings only: a relative one
/// could match the relative paths rustc sees for path packages below the workspace root.
/// Each directory as given and canonicalized. In that order, except that a directory nested in
/// another listed one comes after it: rustc applies the LAST matching prefix, so the nested
/// directory wins. The order does not depend on the directories' lengths, which differ between
/// hosts, so the flags (shown in the generated provenance) are the same on every host whose
/// directories nest the same way.
pub fn path_remaps(
    target_dir: &Path,
    cargo_home: &Path,
    sysroot: &Path,
    rustc_commit: &str,
    upstream: Option<(&Path, &str)>,
) -> Result<Vec<(String, String)>> {
    if rustc_commit.is_empty()
        || rustc_commit
            .chars()
            .any(|c| c.is_ascii_whitespace() || c.is_ascii_control() || c == '=')
    {
        bail!("invalid rustc commit hash `{rustc_commit}` for --remap-path-prefix");
    }
    let mut remaps = prefix_remaps(
        "registry",
        &cargo_home.join("registry").join("src"),
        REMAPPED_REGISTRY_SRC,
    )?;
    remaps.extend(prefix_remaps("target", target_dir, REMAPPED_TARGET_DIR)?);
    remaps.extend(prefix_remaps(
        "git checkouts",
        &cargo_home.join("git").join("checkouts"),
        REMAPPED_GIT_CHECKOUTS,
    )?);
    remaps.extend(prefix_remaps(
        "sysroot rust-src",
        &sysroot.join("lib").join("rustlib").join("src").join("rust"),
        &format!("/rustc/{rustc_commit}"),
    )?);
    if let Some((src, to)) = upstream {
        remaps.extend(
            prefix_remaps("upstream source", src, to)?
                .into_iter()
                .filter(|(d, _)| Path::new(d).is_absolute()),
        );
    }
    // Stable sort by the number of other listed directories each is nested in: an ancestor is
    // nested in strictly fewer, so it comes first; unrelated directories keep the order above.
    let dirs: Vec<PathBuf> = remaps.iter().map(|(d, _)| PathBuf::from(d)).collect();
    let depth = |d: &Path| {
        dirs.iter()
            .filter(|other| other.as_path() != d && d.starts_with(other))
            .count()
    };
    remaps.sort_by_cached_key(|(d, _)| depth(Path::new(d)));
    Ok(remaps)
}

/// The host directories that must not occur in a crate object: the remapped
/// directories (`remaps`, from `path_remaps`), the rustc `sysroot`, the crate directory (the
/// checkout path) and the upstream source directory (if any), the last three as given (if
/// absolute) and canonicalized.
pub fn host_path_check_dirs(
    remaps: &[(String, String)],
    sysroot: &Path,
    crate_dir: &Path,
    upstream_src: Option<&Path>,
) -> Vec<String> {
    let mut dirs: Vec<String> = remaps.iter().map(|(d, _)| d.clone()).collect();
    for p in [sysroot, crate_dir].into_iter().chain(upstream_src) {
        let given = p.is_absolute().then(|| p.to_path_buf());
        for q in [given, canonicalize_existing_prefix(p)]
            .into_iter()
            .flatten()
        {
            let q = q.to_string_lossy().into_owned();
            if !dirs.contains(&q) {
                dirs.push(q);
            }
        }
    }
    dirs
}

/// Fail if a directory of `dirs` (from `host_path_check_dirs`) occurs in the object `bytes`.
pub fn check_no_host_paths(name: &str, bytes: &[u8], dirs: &[String]) -> Result<()> {
    for dir in dirs {
        if !dir.is_empty() && bytes.windows(dir.len()).any(|w| w == dir.as_bytes()) {
            bail!(
                "object `{name}` contains the host path `{dir}`, so the image would depend on \
                 the build host (see \"Reproducible paths\" in tools/rust-obj2lean/README.md)"
            );
        }
    }
    Ok(())
}

/// Build `krate`'s library as one relocatable AArch64 object, with `extra_rustflags` appended
/// to `RUSTFLAGS` (for the whole build, dependencies included).
pub fn build_crate_object(
    tc: &Toolchain,
    crate_dir: &Path,
    krate: &ResolvedCrate,
    target: &str,
    extra_rustflags: &[String],
) -> Result<CrateObject> {
    // Note: passing `RUSTFLAGS` in the environment causes Cargo to ignore any
    // `[target.<triple>].rustflags` table in `<crate_dir>/.cargo/config.toml`. Single-Cargo
    // packages that also compile a standalone `[[bin]]` with `cargo build` mirror these flags
    // in `.cargo/config.toml` so crate-disambiguator hashes match (drift fails closed at `LinkedIn`).
    let rustflags = ["-C", "codegen-units=1", "-C", "relocation-model=static"]
        .into_iter()
        .chain(DETERMINISTIC_CODEGEN_FLAGS.iter().copied())
        .chain(extra_rustflags.iter().map(String::as_str))
        .join(" ");
    let build_env = [
        ("RUSTFLAGS", rustflags.as_str()),
        ("CARGO_PROFILE_RELEASE_CODEGEN_UNITS", "1"),
        ("CARGO_PROFILE_RELEASE_PANIC", "abort"),
        ("CARGO_PROFILE_RELEASE_LTO", "off"),
    ];
    let tmp = tempfile::Builder::new()
        .prefix("rust_obj2lean_")
        .tempdir()?;
    let obj_path = tmp.path().join(format!("{}.o", krate.lib_name));
    let emit = format!("--emit=obj={}", obj_path.display());
    let base = [
        "cargo",
        "rustc",
        "-p",
        &krate.package,
        "--release",
        "--locked",
        "--lib",
        "--target",
        target,
    ];
    let mut argv = base.to_vec();
    argv.extend(["--message-format=json-render-diagnostics", "--", &emit]);
    let cargo_json = tc.run(&argv, Some(crate_dir), &build_env)?;

    let objs: Vec<PathBuf> = fs::read_dir(tmp.path())?
        .map(|e| e.map(|e| e.path()))
        .collect::<std::io::Result<Vec<_>>>()?
        .into_iter()
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    if objs.len() != 1 || objs[0] != obj_path {
        bail!(
            "`cargo rustc` for `{}` produced {} object files ({}), expected exactly `{}.o`",
            krate.package,
            objs.len(),
            objs.iter()
                .map(|p| p.file_name().unwrap_or_default().to_string_lossy())
                .join(", "),
            krate.lib_name
        );
    }
    let elf_bytes = fs::read(&obj_path)?;
    let mut display = base.to_vec();
    let display_emit = format!("--emit=obj={}.o", krate.lib_name);
    display.extend(["--", &display_emit]);
    Ok(CrateObject {
        elf_bytes,
        rlibs: cargo_artifact_rlibs(&cargo_json, target),
        build_cmd: tc.format_cmd(&display, &build_env),
    })
}

/// Crate stem of `lib<name>-<hash>.rlib` (or `<stem>` when unhashed).
pub fn rlib_crate_name(path: &Path) -> String {
    let stem = path.file_stem().unwrap_or_default().to_string_lossy();
    let stem = stem.strip_prefix("lib").unwrap_or(&stem);
    stem.rsplit_once('-')
        .map_or(stem, |(name, _)| name)
        .to_string()
}

fn cargo_artifact_rlibs(cargo_json: &str, triple: &str) -> Vec<PathBuf> {
    let needle = format!("/{triple}/");
    Message::parse_stream(Cursor::new(cargo_json))
        .flatten()
        .filter_map(|m| {
            if let Message::CompilerArtifact(a) = m {
                Some(a.filenames)
            } else {
                None
            }
        })
        .flatten()
        .filter(|f| f.extension() == Some("rlib") && f.as_str().contains(&needle))
        .map(|f| f.into_std_path_buf())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .sorted_by_key(|p| {
            (
                rlib_crate_name(p),
                p.file_name().unwrap_or_default().to_owned(),
            )
        })
        .collect()
}

/// The target's sysroot rlibs (`core`, `alloc`, `std`, ...) inside `sysroot`.
fn sysroot_rlibs(sysroot: &Path, triple: &str) -> Result<Vec<PathBuf>> {
    let lib_dir = sysroot
        .join("lib")
        .join("rustlib")
        .join(triple)
        .join("lib");
    let mut rlibs: Vec<PathBuf> = fs::read_dir(&lib_dir)
        .with_context(|| format!("failed to read sysroot lib dir {}", lib_dir.display()))?
        .map(|e| e.map(|e| e.path()))
        .collect::<std::io::Result<Vec<_>>>()?
        .into_iter()
        .filter(|p| p.extension().is_some_and(|x| x == "rlib"))
        .collect();
    rlibs.sort();
    if rlibs.is_empty() {
        bail!("no rlibs in sysroot {}", lib_dir.display());
    }
    Ok(rlibs)
}

/// The sections of `data` (a relocatable AArch64 ELF file) to keep for `roots`: the sections
/// defining the global functions `roots` (demangled names; each must be defined exactly
/// once), closed under relocations against local symbols (including section symbols).
/// Relocations against other global symbols are not followed: those stay undefined.
pub fn root_section_closure(data: &[u8], roots: &[String]) -> Result<BTreeSet<usize>> {
    let e = parse_elf_rel(data)?;
    let endian = e.endian;
    // Relocation sections by the section they apply to.
    let mut relas_of: BTreeMap<usize, Vec<&elf::SectionHeader64<object::Endianness>>> =
        BTreeMap::new();
    for sh in e.sections.iter() {
        if sh.sh_type(endian) == elf::SHT_RELA {
            relas_of
                .entry(sh.sh_info(endian) as usize)
                .or_default()
                .push(sh);
        }
    }
    let sym_sec = |i: usize| -> Result<Option<usize>> {
        let sym = e
            .symbols
            .symbol(SymbolIndex(i))
            .map_err(|err| anyhow!("symbol {i}: {err}"))?;
        Ok(e.symbols
            .symbol_section(endian, sym, SymbolIndex(i))
            .map_err(|err| anyhow!("symbol {i}: {err}"))?
            .map(|j| j.0))
    };
    let mut keep = BTreeSet::new();
    let mut work = Vec::new();
    for root in roots {
        let mut found = Vec::new();
        for (i, sym) in e.symbols.symbols().iter().enumerate() {
            if !matches!(sym.st_bind(), elf::STB_GLOBAL | elf::STB_WEAK)
                || !matches!(sym.st_type(), elf::STT_FUNC | elf::STT_OBJECT)
            {
                continue;
            }
            let Ok(raw) = e.symbols.symbol_name(endian, sym) else {
                continue;
            };
            let Ok(raw) = std::str::from_utf8(raw) else {
                continue;
            };
            if (raw == *root || demangle_rust_symbol(raw) == *root)
                && let Some(j) = sym_sec(i)?
            {
                found.push(j);
            }
        }
        match found.as_slice() {
            [j] => {
                if keep.insert(*j) {
                    work.push(*j);
                }
            }
            [] => bail!("root `{root}` is not a defined global function or object"),
            _ => bail!("root `{root}` is defined {} times", found.len()),
        }
    }
    while let Some(j) = work.pop() {
        for sh in relas_of.get(&j).into_iter().flatten() {
            if sh.sh_link(endian) as usize != e.symbols.section().0 {
                bail!("a relocation section does not use the symbol table");
            }
            let relas: &[elf::Rela64<object::Endianness>] = sh
                .data_as_array(endian, data)
                .map_err(|err| anyhow!("{err}"))?;
            for r in relas {
                let si = r.r_sym(endian, false) as usize;
                let sym = e
                    .symbols
                    .symbol(SymbolIndex(si))
                    .map_err(|err| anyhow!("symbol {si}: {err}"))?;
                if sym.st_bind() != elf::STB_LOCAL {
                    continue;
                }
                if let Some(k) = sym_sec(si)?
                    && keep.insert(k)
                {
                    work.push(k);
                }
            }
        }
    }
    Ok(keep)
}

/// The single relocatable AArch64 ELF `.o` member of `rlib` defining `roots`, with its
/// member name and kept section closure (the metadata members `lib.rmeta*` are ELF-wrapped
/// too, but are not `.o` files).
pub fn rlib_object_for_roots(
    rlib: &Path,
    roots: &[String],
) -> Result<(String, Vec<u8>, BTreeSet<usize>)> {
    let bytes = fs::read(rlib).with_context(|| format!("failed to read {}", rlib.display()))?;
    let archive = ArchiveFile::parse(&*bytes)
        .map_err(|e| anyhow!("{}: not an archive: {e}", rlib.display()))?;
    let mut objs = Vec::new();
    for member in archive.members() {
        let member = member.map_err(|e| anyhow!("{}: {e}", rlib.display()))?;
        let name = String::from_utf8_lossy(member.name()).into_owned();
        let data = member
            .data(&*bytes)
            .map_err(|e| anyhow!("{}: {e}", rlib.display()))?;
        if name.ends_with(".o") && parse_elf_rel(data).is_ok() {
            objs.push((name, data.to_vec()));
        }
    }
    if let [(name, data)] = objs.as_slice() {
        let keep = root_section_closure(data, roots)
            .with_context(|| format!("{}({name})", rlib.display()))?;
        return Ok((name.clone(), data.clone(), keep));
    }
    let matches: Vec<_> = objs
        .into_iter()
        .filter_map(|(name, data)| {
            let keep = root_section_closure(&data, roots).ok()?;
            Some((name, data, keep))
        })
        .collect();
    match <[_; 1]>::try_from(matches) {
        Ok([one]) => Ok(one),
        Err(matches) => bail!(
            "{} has {} relocatable AArch64 objects defining {:?}, expected exactly one",
            rlib.display(),
            matches.len(),
            roots
        ),
    }
}

/// Extract `cfg` from its sysroot rlib (among `sysroot`): the trimmed object and a
/// provenance line.
fn extract_sysroot_object(
    sysroot: &[PathBuf],
    cfg: &SysrootObjectConfig,
) -> Result<(ObjObject, String)> {
    let rlibs: Vec<&PathBuf> = sysroot
        .iter()
        .filter(|p| rlib_crate_name(p) == cfg.krate)
        .collect();
    let [rlib] = rlibs.as_slice() else {
        bail!(
            "expected exactly one sysroot rlib for crate `{}`, found {}",
            cfg.krate,
            rlibs.len()
        );
    };
    let obj_name = cfg.obj_name();
    let (member, elf_bytes, keep) = rlib_object_for_roots(rlib, &cfg.roots)?;
    let trim = Trim {
        keep,
        local_suffix: format!(" [lib{obj_name}]"),
    };
    let o = parse_object_with(obj_name, elf_bytes, Some(&trim))
        .with_context(|| format!("{}({member})", rlib.display()))?;
    for root in &cfg.roots {
        if !o.symbols.iter().any(|s| {
            (s.name == *root || s.raw_name == *root)
                && s.bind != SymBind::Local
                && matches!(s.sec, SymSection::Sec(_))
        }) {
            bail!("sysroot object `{obj_name}`: root `{root}` is not defined after trimming");
        }
    }
    let n_relocs: usize = o.sections.iter().map(|s| s.relocs.len()).sum();
    let prov = format!(
        "sysroot `{}` member `{member}`, {} bytes, sha256 {}; kept {} sections ({}), {} symbols, \
         {} relocations, reachable from {}",
        rlib.file_name().unwrap_or_default().to_string_lossy(),
        o.elf_bytes.len(),
        sha256_hex(&o.elf_bytes),
        o.sections.len(),
        o.sections
            .iter()
            .map(|s| format!("`{}`", s.name))
            .join(", "),
        o.symbols.len(),
        n_relocs,
        cfg.roots.iter().map(|r| format!("`{r}`")).join(", ")
    );
    Ok((o, prov))
}

/// Locate the `zig` binary via `$ZIG`, `zig` on `PATH`, or `$HOME/.local/bin/zig`.
pub fn find_zig_binary(context_what: &str) -> Result<PathBuf> {
    if let Some(p) = env::var_os("ZIG").filter(|v| !v.is_empty()) {
        return which::which(&p).map_err(|e| anyhow!("failed to find `$ZIG` ({:?}): {e}", p));
    }
    if let Ok(p) = which::which("zig") {
        return Ok(p);
    }
    if let Some(home) = env::var_os("HOME") {
        let local_zig = PathBuf::from(home).join(".local/bin/zig");
        if local_zig.is_file() {
            return Ok(local_zig);
        }
    }
    bail!(
        "{context_what} needs `zig` (`zig cc`): put `zig` on PATH, install to ~/.local/bin/zig, or set $ZIG \
         (see tools/rust-obj2lean/README.md)"
    )
}

/// The `zig` binary (`$ZIG`, `zig` on `PATH`, or `~/.local/bin/zig`), checked to report
/// exactly `version`.
pub fn resolve_zig(version: &str) -> Result<PathBuf> {
    let zig = find_zig_binary(&format!("`[[native_objects]]` need zig {version}"))?;
    let out = Command::new(&zig)
        .arg("version")
        .output()
        .with_context(|| format!("failed to invoke `{} version`", zig.display()))?;
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        bail!(
            "`{} version` failed ({}): {stderr}",
            zig.display(),
            out.status
        );
    }
    let found = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if found != version {
        bail!(
            "`{}` reports version `{found}`, but the translation config pins zig {version}",
            zig.display()
        );
    }
    Ok(zig)
}

/// Find `zig` without requiring a pinned version (returns `(zig_path, version_string)`).
fn resolve_zig_unpinned(context_what: &str) -> Result<(PathBuf, String)> {
    let zig = find_zig_binary(context_what)?;
    let out = Command::new(&zig)
        .arg("version")
        .output()
        .with_context(|| format!("failed to invoke `{} version`", zig.display()))?;
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        bail!(
            "`{} version` failed ({}): {stderr}",
            zig.display(),
            out.status
        );
    }
    let found = String::from_utf8_lossy(&out.stdout).trim().to_string();
    Ok((zig, found))
}

/// The full `zig cc` argument vector (after the `zig` binary) compiling `cfg.source` to `out`
/// with top-level `extra_cflags` plus `cfg`-specific flags (paths as given, relative to the
/// crate directory, which is the working directory).
pub fn native_cc_args_with_flags(
    cfg: &NativeObjectConfig,
    extra_cflags: &[String],
    out: &str,
) -> Vec<String> {
    let mut args: Vec<String> = vec!["cc".into()];
    args.extend(NATIVE_CFLAGS.iter().map(|s| s.to_string()));
    args.extend(extra_cflags.iter().cloned());
    args.extend(cfg.c_flags.iter().cloned());
    args.extend(
        cfg.include_dirs
            .iter()
            .map(|d| format!("-I{}", d.display())),
    );
    args.extend(cfg.defines.iter().map(|d| format!("-D{d}")));
    args.extend([
        "-c".into(),
        cfg.source.display().to_string(),
        "-o".into(),
        out.into(),
    ]);
    args
}

/// Compile `cfg` with `zig` (from `crate_dir`) and extract its entire object, a provenance
/// line and the (display) compile command.
pub fn extract_native_object(
    tc: &Toolchain,
    zig: &Path,
    crate_dir: &Path,
    cfg: &NativeObjectConfig,
    extra_cflags: &[String],
) -> Result<(ObjObject, String, String)> {
    let src_path = crate_dir.join(&cfg.source);
    let src_bytes =
        fs::read(&src_path).with_context(|| format!("failed to read {}", src_path.display()))?;
    let tmp = tempfile::Builder::new()
        .prefix("rust_obj2lean_cc_")
        .tempdir()?;
    let obj_path = tmp.path().join(format!("{}.o", cfg.name));
    let obj_str = obj_path.to_string_lossy().into_owned();
    let mut argv = vec![zig.to_string_lossy().into_owned()];
    argv.extend(native_cc_args_with_flags(cfg, extra_cflags, &obj_str));
    tc.run(&argv, Some(crate_dir), &[])?;
    let elf_bytes = fs::read(&obj_path)?;
    let o = parse_c_object(&cfg.name, elf_bytes)?;
    let n_relocs: usize = o.sections.iter().map(|s| s.relocs.len()).sum();
    let prov = format!(
        "source `{}` sha256 {}; {} bytes, sha256 {}; {} sections ({}), {} symbols, \
         {} relocations",
        cfg.source.display(),
        sha256_hex(&src_bytes),
        o.elf_bytes.len(),
        sha256_hex(&o.elf_bytes),
        o.sections.len(),
        o.sections
            .iter()
            .map(|s| format!("`{}`", s.name))
            .join(", "),
        o.symbols.len(),
        n_relocs,
    );
    let mut display = vec!["zig".to_string()];
    display.extend(native_cc_args_with_flags(
        cfg,
        extra_cflags,
        &format!("{}.o", cfg.name),
    ));
    Ok((o, prov, tc.format_cmd(&display, &[])))
}

/// Compile selected `[[native_objects]]` from `cfg` using the exact `rust-obj2lean` compiler and
/// flag pipeline (`resolve_zig` + [`extract_native_object`]), returning `(name, elf_bytes)` in
/// configuration order.
pub fn compile_native_objects(
    tc: &Toolchain,
    cfg: &ExportConfig,
    only: Option<&[String]>,
) -> Result<Vec<(String, Vec<u8>)>> {
    let zig = if let Some(nc) = &cfg.native_compiler {
        resolve_zig(&nc.zig_version)?
    } else {
        resolve_zig_unpinned("`[[native_objects]]` compilation")?.0
    };
    let selected: Vec<&NativeObjectConfig> = match only {
        None => cfg.native_objects.iter().collect(),
        Some(want) => {
            for w in want {
                if !cfg.native_objects.iter().any(|n| n.name == *w) {
                    bail!(
                        "native object `{w}` not found in `{}` (available: {})",
                        cfg.config_rel,
                        cfg.native_objects
                            .iter()
                            .map(|n| n.name.as_str())
                            .join(", ")
                    );
                }
            }
            cfg.native_objects
                .iter()
                .filter(|n| want.iter().any(|w| w == &n.name))
                .collect()
        }
    };
    let mut out = Vec::with_capacity(selected.len());
    for n in selected {
        let (o, _, _) = extract_native_object(tc, &zig, &cfg.crate_dir, n, &cfg.c_flags)
            .with_context(|| format!("native object `{}`", n.name))?;
        out.push((n.name.clone(), o.elf_bytes));
    }
    Ok(out)
}

/// Load a pre-compiled `.o` relocatable object file from `obj_rel` (relative to `crate_dir`).
fn extract_c_prebuilt_object(
    crate_dir: &Path,
    obj_rel: &Path,
    used_names: &mut BTreeSet<String>,
) -> Result<(ObjObject, String)> {
    let obj_path = crate_dir.join(obj_rel);
    let elf_bytes =
        fs::read(&obj_path).with_context(|| format!("failed to read {}", obj_path.display()))?;
    let base_name = c_stem_ident(obj_rel)?;
    let mut name = base_name.clone();
    let mut idx = 2usize;
    while !used_names.insert(name.clone()) {
        name = format!("{base_name}_{idx}");
        idx += 1;
    }
    let o = parse_c_object(&name, elf_bytes)
        .with_context(|| format!("prebuilt object `{}`", obj_rel.display()))?;
    let n_relocs: usize = o.sections.iter().map(|s| s.relocs.len()).sum();
    let prov = format!(
        "prebuilt `{}` ({} bytes, sha256 {}); {} sections ({}), {} symbols, {} relocations",
        obj_rel.display(),
        o.elf_bytes.len(),
        sha256_hex(&o.elf_bytes),
        o.sections.len(),
        o.sections.iter().map(|s| format!("`{}`", s.name)).join(", "),
        o.symbols.len(),
        n_relocs,
    );
    Ok((o, prov))
}

/// Load all `.o` relocatable ELF members from a pre-compiled `.a` static archive `arch_rel`
/// (relative to `crate_dir`).
fn extract_c_archive_objects(
    crate_dir: &Path,
    arch_rel: &Path,
    used_names: &mut BTreeSet<String>,
) -> Result<Vec<(ObjObject, String)>> {
    let arch_path = crate_dir.join(arch_rel);
    let bytes =
        fs::read(&arch_path).with_context(|| format!("failed to read {}", arch_path.display()))?;
    let archive = ArchiveFile::parse(&*bytes)
        .map_err(|e| anyhow!("{}: not a static archive: {e}", arch_path.display()))?;
    let arch_stem = c_stem_ident(arch_rel).unwrap_or_else(|_| "archive".into());
    let mut out = Vec::new();
    for member in archive.members() {
        let member = member.map_err(|e| anyhow!("{}: {e}", arch_path.display()))?;
        let raw_member_name = String::from_utf8_lossy(member.name()).into_owned();
        let member_name = raw_member_name.trim_end_matches('/');
        if member_name.is_empty()
            || member_name == "/"
            || member_name == "//"
            || member_name == "__.SYMDEF"
            || member_name == "__.SYMDEF SORTED"
        {
            continue;
        }
        let data = member
            .data(&*bytes)
            .map_err(|e| anyhow!("{}({member_name}): {e}", arch_path.display()))?;
        if !member_name.ends_with(".o") && parse_elf_rel(data).is_err() {
            continue;
        }
        let base_name = c_stem_ident(Path::new(member_name))
            .with_context(|| format!("{}({member_name})", arch_rel.display()))?;
        let mut obj_name = base_name.clone();
        if !used_names.insert(obj_name.clone()) {
            let prefixed = format!("{arch_stem}_{base_name}");
            if used_names.insert(prefixed.clone()) {
                obj_name = prefixed;
            } else {
                let mut idx = 2usize;
                loop {
                    let candidate = format!("{base_name}_{idx}");
                    if used_names.insert(candidate.clone()) {
                        obj_name = candidate;
                        break;
                    }
                    idx += 1;
                }
            }
        }
        let o = parse_c_object(&obj_name, data.to_vec())
            .with_context(|| format!("{}({member_name})", arch_rel.display()))?;
        let n_relocs: usize = o.sections.iter().map(|s| s.relocs.len()).sum();
        let prov = format!(
            "archive `{}` member `{member_name}`, {} bytes, sha256 {}; {} sections ({}), \
             {} symbols, {} relocations",
            arch_rel.display(),
            o.elf_bytes.len(),
            sha256_hex(&o.elf_bytes),
            o.sections.len(),
            o.sections.iter().map(|s| format!("`{}`", s.name)).join(", "),
            o.symbols.len(),
            n_relocs,
        );
        out.push((o, prov));
    }
    if out.is_empty() {
        bail!(
            "static archive `{}` contains no relocatable `.o` members",
            arch_rel.display()
        );
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Extraction Driver
// ---------------------------------------------------------------------------

/// The root of the git checkout that contains `dir`: its nearest ancestor (or itself) with a
/// `.git` entry (a directory, or a file in a submodule or worktree).
pub fn checkout_root(dir: &Path) -> Option<&Path> {
    dir.ancestors()
        .find(|a| !a.as_os_str().is_empty() && a.join(".git").exists())
}

/// The crate directory as shown in the generated provenance: relative to `repo_root` (this
/// repository), else, for a crate in another checkout (e.g. a repository that has this one as a
/// submodule), relative to that checkout's root, so that the text does not depend on where it
/// is checked out. Absolute only if neither applies.
pub fn crate_dir_display(repo_root: &Path, crate_dir: &Path) -> String {
    let rel = crate_dir
        .strip_prefix(repo_root)
        .ok()
        .or_else(|| crate_dir.strip_prefix(checkout_root(crate_dir)?).ok())
        .unwrap_or(crate_dir);
    if rel.as_os_str().is_empty() {
        ".".into()
    } else {
        rel.to_string_lossy().into_owned()
    }
}

/// Build, parse and resolve every crate or native object of `cfg`.
pub fn extract(cfg: &ExportConfig, tc: &mut Toolchain) -> Result<Extraction> {
    extract_with_rlibs(cfg, tc).map(|(ex, _)| ex)
}

/// Build, parse and resolve every crate or native object of `cfg`, also returning the dependency
/// and sysroot `.rlib` paths scanned during extern resolution.
pub fn extract_with_rlibs(
    cfg: &ExportConfig,
    tc: &mut Toolchain,
) -> Result<(Extraction, Vec<PathBuf>)> {
    let crate_dir = &cfg.crate_dir;
    // A crate outside this repository (e.g. in a superproject that has it as a submodule): show
    // its checkout as `$CRATE_REPO` in commands (e.g. its `target/` remap), as `$REPO` is shown.
    if !crate_dir.starts_with(&tc.repo_root)
        && let Some(root) = checkout_root(crate_dir)
    {
        tc.add_alias(root, "$CRATE_REPO");
    }
    let mut upstream_src: Option<PathBuf> = None;
    let upstream_info = if let Some(upstream) = &cfg.upstream {
        let (src, commit, tag) = resolve_upstream_src(&tc.repo_root, crate_dir, upstream)?;
        link_vendor_symlink(crate_dir, &src, upstream)?;
        let env_var = upstream
            .env_var
            .clone()
            .unwrap_or_else(|| format!("{}_SRC", upstream.name.to_uppercase()));
        if let Some(canon) = canonicalize_existing_prefix(&src)
            && canon != src
        {
            tc.add_alias(&canon, format!("${env_var}"));
        }
        tc.add_alias(&src, format!("${env_var}"));
        upstream_src = Some(src);
        Some((upstream.repo_url.clone(), commit, tag))
    } else {
        None
    };

    let mut objects = Vec::new();
    let mut commands = Vec::new();
    let mut resolved = Vec::new();
    let mut sysroot_provenance = Vec::new();
    let mut rlibs: Vec<PathBuf> = Vec::new();
    let mut n_dep_rlibs = 0;
    let mut used_names: BTreeSet<String> = BTreeSet::new();
    let mut sysroot_libs_opt: Option<Vec<PathBuf>> = None;

    if !cfg.crates.is_empty() {
        let effective_rustflags = ["-C", "codegen-units=1", "-C", "relocation-model=static"]
            .into_iter()
            .chain(DETERMINISTIC_CODEGEN_FLAGS.iter().copied())
            .chain(cfg.rustflags.iter().map(String::as_str))
            .join(" ");
        sysroot_provenance.push((
            "Compile flags (RUSTFLAGS)".into(),
            format!("`{effective_rustflags}`"),
        ));
        resolved = resolve_crates(crate_dir, &cfg.crates)?;
        // Reproducible paths (see the README): remap the host directories rustc sees, before
        // the configured flags, and check that no host path is left in an object.
        let home = cargo_home()?;
        if let Some(canon) = canonicalize_existing_prefix(&home)
            && canon != home
        {
            tc.add_alias(&canon, "$CARGO_HOME");
        }
        tc.add_alias(&home, "$CARGO_HOME");
        let sysroot = rustc_sysroot(crate_dir)?;
        if let Some(canon) = canonicalize_existing_prefix(&sysroot)
            && canon != sysroot
        {
            tc.add_alias(&canon, "$SYSROOT");
        }
        tc.add_alias(&sysroot, "$SYSROOT");
        let rustc_commit = rustc_commit_hash(&tc.rustc_version)?;
        let upstream_to = match (&cfg.upstream, &upstream_info) {
            (Some(upstream), Some((_, commit, _))) => {
                Some(upstream_remap_target(&upstream.name, commit)?)
            }
            _ => None,
        };
        let remaps = path_remaps(
            &cargo_target_dir(crate_dir)?,
            &home,
            &sysroot,
            rustc_commit,
            upstream_src.as_deref().zip(upstream_to.as_deref()),
        )?;
        let host_dirs = host_path_check_dirs(&remaps, &sysroot, crate_dir, upstream_src.as_deref());
        let rustflags: Vec<String> = remaps
            .into_iter()
            .map(|(_, flag)| flag)
            .chain(cfg.rustflags.iter().cloned())
            .collect();
        let mut dep_rlibs: BTreeSet<PathBuf> = BTreeSet::new();
        for krate in &resolved {
            let built = build_crate_object(tc, crate_dir, krate, &cfg.target, &rustflags)?;
            commands.push((format!("build `{}`", krate.lib_name), built.build_cmd));
            dep_rlibs.extend(built.rlibs);
            check_no_host_paths(&krate.lib_name, &built.elf_bytes, &host_dirs)?;
            used_names.insert(krate.lib_name.clone());
            objects.push(parse_object(&krate.lib_name, built.elf_bytes)?);
        }
        let sysroot_libs = sysroot_rlibs(&sysroot, &cfg.target)?;
        // Definitions of undefined symbols: dependency rlibs (never a stale rlib of a crate
        // being extracted) and the sysroot rlibs.
        let own: BTreeSet<&str> = resolved.iter().map(|k| k.lib_name.as_str()).collect();
        rlibs = dep_rlibs
            .into_iter()
            .filter(|p| !own.contains(rlib_crate_name(p).as_str()))
            .collect();
        n_dep_rlibs = rlibs.len();
        rlibs.extend(sysroot_libs.iter().cloned());
        sysroot_libs_opt = Some(sysroot_libs);
    }

    let has_c_inputs = cfg.native_compiler.is_some()
        || !cfg.native_objects.is_empty()
        || !cfg.c_sources.is_empty()
        || !cfg.c_objects.is_empty()
        || !cfg.c_archives.is_empty()
        || cfg.build_script.is_some()
        || cfg.build_command.is_some();

    let mut zig_used = false;
    if has_c_inputs {
        let needs_zig = cfg.native_compiler.is_some()
            || !cfg.native_objects.is_empty()
            || !cfg.c_sources.is_empty()
            || cfg.build_script.is_some()
            || cfg.build_command.is_some();
        let zig_opt = if let Some(nc) = &cfg.native_compiler {
            let zig = resolve_zig(&nc.zig_version)?;
            sysroot_provenance.push((
                "Native compiler".into(),
                format!("zig {} (`zig cc`)", nc.zig_version),
            ));
            Some(zig)
        } else if needs_zig {
            let (zig, ver) = resolve_zig_unpinned("C compilation / build script")?;
            sysroot_provenance.push(("Native compiler".into(), format!("zig {ver} (`zig cc`)")));
            Some(zig)
        } else {
            None
        };
        zig_used = zig_opt.is_some();

        if cfg.build_script.is_some() || cfg.build_command.is_some() {
            let zig = zig_opt
                .as_ref()
                .expect("zig resolved when build_script/build_command is set");
            let cflags = native_cflags_string(&cfg.c_flags);
            let zig_str = zig.to_string_lossy().into_owned();
            let path_with_zig = match (zig.parent(), env::var_os("PATH")) {
                (Some(dir), Some(old)) => format!("{}:{}", dir.display(), old.to_string_lossy()),
                (Some(dir), None) => dir.display().to_string(),
                (None, Some(old)) => old.to_string_lossy().into_owned(),
                (None, None) => String::new(),
            };
            let exec_env = [
                ("CC", "zig cc"),
                ("AR", "zig ar"),
                ("RANLIB", "zig ranlib"),
                ("CFLAGS", cflags.as_str()),
                ("ZIG", zig_str.as_str()),
                ("PATH", path_with_zig.as_str()),
            ];
            let display_env = [
                ("CC", "zig cc"),
                ("AR", "zig ar"),
                ("RANLIB", "zig ranlib"),
                ("CFLAGS", cflags.as_str()),
            ];
            if let Some(script) = &cfg.build_script {
                let script_str = script.display().to_string();
                let argv = ["sh", script_str.as_str()];
                tc.run(&argv, Some(crate_dir), &exec_env)
                    .with_context(|| format!("build_script `{script_str}`"))?;
                commands.push((
                    format!("build script `{script_str}`"),
                    tc.format_cmd(&argv, &display_env),
                ));
            }
            if let Some(cmd_vec) = &cfg.build_command {
                tc.run(cmd_vec, Some(crate_dir), &exec_env)
                    .with_context(|| format!("build_command `{}`", cmd_vec.join(" ")))?;
                commands.push((
                    "build command".into(),
                    tc.format_cmd(cmd_vec, &display_env),
                ));
            }
        }

        for n in &cfg.native_objects {
            let zig = zig_opt.as_ref().expect("zig resolved for native_objects");
            let (o, prov, cmd) = extract_native_object(tc, zig, crate_dir, n, &cfg.c_flags)
                .with_context(|| format!("native object `{}`", n.name))?;
            used_names.insert(o.name.clone());
            sysroot_provenance.push((format!("Object `{}.o` (C)", o.name), prov));
            commands.push((format!("compile `{}`", n.name), cmd));
            objects.push(o);
        }
        for src in &cfg.c_sources {
            let zig = zig_opt.as_ref().expect("zig resolved for c_sources");
            let base_name = c_stem_ident(src)?;
            let mut name = base_name.clone();
            let mut idx = 2usize;
            while !used_names.insert(name.clone()) {
                name = format!("{base_name}_{idx}");
                idx += 1;
            }
            let n = NativeObjectConfig {
                name,
                source: src.clone(),
                include_dirs: Vec::new(),
                defines: Vec::new(),
                c_flags: Vec::new(),
            };
            let (o, prov, cmd) = extract_native_object(tc, zig, crate_dir, &n, &cfg.c_flags)
                .with_context(|| format!("c_sources `{}`", src.display()))?;
            sysroot_provenance.push((format!("Object `{}.o` (C)", o.name), prov));
            commands.push((format!("compile `{}`", n.name), cmd));
            objects.push(o);
        }
        for obj_rel in &cfg.c_objects {
            if obj_rel.extension().and_then(|e| e.to_str()) == Some("a") {
                let extracted = extract_c_archive_objects(crate_dir, obj_rel, &mut used_names)?;
                for (o, prov) in extracted {
                    sysroot_provenance.push((format!("Object `{}.o` (archive)", o.name), prov));
                    objects.push(o);
                }
            } else {
                let (o, prov) = extract_c_prebuilt_object(crate_dir, obj_rel, &mut used_names)?;
                sysroot_provenance.push((format!("Object `{}.o` (prebuilt)", o.name), prov));
                objects.push(o);
            }
        }
        for arch_rel in &cfg.c_archives {
            let extracted = extract_c_archive_objects(crate_dir, arch_rel, &mut used_names)?;
            for (o, prov) in extracted {
                sysroot_provenance.push((format!("Object `{}.o` (archive)", o.name), prov));
                objects.push(o);
            }
        }
    }

    if !cfg.sysroot_objects.is_empty() {
        let sysroot_libs = match sysroot_libs_opt {
            Some(libs) => libs,
            None => {
                let sysroot = rustc_sysroot(crate_dir)?;
                if let Some(canon) = canonicalize_existing_prefix(&sysroot)
                    && canon != sysroot
                {
                    tc.add_alias(&canon, "$SYSROOT");
                }
                tc.add_alias(&sysroot, "$SYSROOT");
                let libs = sysroot_rlibs(&sysroot, &cfg.target)?;
                rlibs.extend(libs.iter().cloned());
                libs
            }
        };
        for s in &cfg.sysroot_objects {
            let (o, prov) = extract_sysroot_object(&sysroot_libs, s)
                .with_context(|| format!("sysroot object `{}`", s.obj_name()))?;
            sysroot_provenance.push((format!("Object `{}` (trimmed)", o.name), prov));
            objects.push(o);
        }
    }
    if zig_used {
        sysroot_provenance.push((
            "Compile flags (CFLAGS)".into(),
            format!("`{}`", native_cflags_string(&cfg.c_flags)),
        ));
    }
    disambiguate_symbol_names(&mut objects);
    check_name_collisions(&objects)?;

    let needed = needed_externs(&objects)?;
    let wanted: BTreeSet<String> = needed.iter().map(|n| n.raw_name.clone()).collect();
    let defs = if wanted.is_empty() || rlibs.is_empty() {
        BTreeMap::new()
    } else {
        scan_rlib_definitions(&rlibs, &wanted)?
    };
    let externs = resolve_externs_with_config(&needed, &defs, &cfg.externs)?;
    check_extern_collisions(&objects, &externs)?;

    let crate_rel = crate_dir_display(&tc.repo_root, crate_dir);
    let input_hashes = cfg
        .hashed_inputs
        .iter()
        .map(|name| {
            Ok(format!(
                "{name} sha256:{}",
                &sha256_hex(
                    fs::read(crate_dir.join(name))
                        .with_context(|| format!("hashed input `{name}`"))?
                )[..16]
            ))
        })
        .collect::<Result<Vec<_>>>()?
        .join(", ");
    let mut provenance = Vec::new();
    if let Some((upstream_url, commit, tag)) = upstream_info {
        provenance.push(("Upstream".into(), format!("{upstream_url} tag `{tag}`")));
        provenance.push(("Upstream commit".into(), commit));
    }
    provenance.push((
        "Crate directory".into(),
        format!("`{crate_rel}` ({input_hashes})"),
    ));
    for (o, krate) in objects.iter().zip(&resolved) {
        let n_relocs: usize = o.sections.iter().map(|s| s.relocs.len()).sum();
        provenance.push((
            format!("Object `{}.o`", o.name),
            format!(
                "package `{}`, {} bytes, sha256 {}; {} sections, {} symbols, {} relocations",
                krate.package,
                o.elf_bytes.len(),
                sha256_hex(&o.elf_bytes),
                o.sections.len(),
                o.symbols.len(),
                n_relocs
            ),
        ));
    }
    provenance.extend(sysroot_provenance);
    let count = |k: ExternKind| externs.iter().filter(|x| x.kind == k).count();
    provenance.push((
        "Externs".into(),
        format!(
            "{} functions, {} objects, {} TLS; definitions looked up in {} dependency rlibs \
             and {} sysroot rlibs",
            count(ExternKind::Func),
            count(ExternKind::Object),
            count(ExternKind::Tls),
            n_dep_rlibs,
            rlibs.len() - n_dep_rlibs
        ),
    ));
    provenance.extend(tc.provenance(&cfg.config_rel, &cfg.config_hash, &commands));
    Ok((
        Extraction {
            objects,
            externs,
            provenance,
        },
        rlibs,
    ))
}

// ---------------------------------------------------------------------------
// Upstream Git Source Resolution
// ---------------------------------------------------------------------------

fn resolve_upstream_src(
    repo_root: &Path,
    crate_dir: &Path,
    upstream: &UpstreamConfig,
) -> Result<(PathBuf, String, String)> {
    let tag = &upstream.tag;
    let repo_url = &upstream.repo_url;
    let name = &upstream.name;
    let env_var = upstream
        .env_var
        .clone()
        .unwrap_or_else(|| format!("{}_SRC", name.to_uppercase()));
    let no_clone_env_var = upstream
        .no_clone_env_var
        .clone()
        .unwrap_or_else(|| format!("{}_NO_CLONE", name.to_uppercase()));
    let home_subdir = upstream
        .home_subdir
        .clone()
        .unwrap_or_else(|| PathBuf::from("sw").join(name));

    let mut candidates = Vec::new();
    if let Ok(env_src) = env::var(&env_var)
        && !env_src.is_empty()
    {
        candidates.push(PathBuf::from(env_src));
    }
    let tp_dir = repo_root.join("third_party").join(format!("{name}-{tag}"));
    for tp_root in [Some(repo_root), repo_root.parent()].into_iter().flatten() {
        candidates.push(tp_root.join("third_party").join(format!("{name}-{tag}")));
        if let Some(stripped) = tag.strip_prefix('v') {
            candidates.push(
                tp_root
                    .join("third_party")
                    .join(format!("{name}-{stripped}")),
            );
        }
    }
    if let Some(rel_symlink) = &upstream.vendor_symlink {
        candidates.push(crate_dir.join(rel_symlink));
    }
    if let Ok(home) = env::var("HOME") {
        candidates.push(PathBuf::from(home).join(&home_subdir));
    }
    let clone_dir = upstream
        .vendor_symlink
        .as_ref()
        .map_or(tp_dir, |rel| crate_dir.join(rel));
    candidates.push(clone_dir.clone());

    for candidate in &candidates {
        let valid = match &upstream.probe_path {
            Some(probe) => candidate.join(probe).is_file(),
            None => candidate.join(".git").exists(),
        };
        if valid {
            let resolved = if candidate
                .symlink_metadata()
                .is_ok_and(|m| m.file_type().is_symlink())
            {
                candidate.canonicalize().unwrap_or_else(|_| candidate.clone())
            } else {
                candidate.clone()
            };
            let (commit, described) =
                describe_upstream(&resolved, name, tag, upstream.commit.as_deref(), &env_var)?;
            return Ok((resolved, commit, described));
        }
    }

    let home_disp = home_subdir.display();
    let how_to_fix = format!(
        "Point ${env_var} at a clean {tag} checkout, clone one into ~/{home_disp} \
         (`git clone --depth 1 --branch {tag} {repo_url} ~/{home_disp}`), or \
         allow this tool to clone it by unsetting ${no_clone_env_var}."
    );
    if env::var(&no_clone_env_var).is_ok_and(|v| !v.is_empty()) {
        bail!(
            "no {name} checkout found (${env_var}, ~/{home_disp}) and cloning is \
             disabled by ${no_clone_env_var}. {how_to_fix}"
        );
    }
    if which::which("git").is_err() {
        bail!("no {name} checkout found and `git` is not on PATH. {how_to_fix}");
    }

    if let Some(parent) = clone_dir.parent() {
        fs::create_dir_all(parent)?;
    }
    eprintln!(
        "Cloning {repo_url} at {tag} into {} ...",
        clone_dir.display()
    );
    let out = Command::new("git")
        .args(["clone", "--depth", "1", "--branch", tag, repo_url])
        .arg(&clone_dir)
        .output()?;
    if !out.status.success() {
        let _ = fs::remove_dir_all(&clone_dir);
        let stderr = String::from_utf8_lossy(&out.stderr);
        let detail = stderr.trim().lines().last().unwrap_or("unknown error");
        bail!("no {name} checkout found and cloning {repo_url} failed: {detail}. {how_to_fix}");
    }
    let (commit, described) =
        describe_upstream(&clone_dir, name, tag, upstream.commit.as_deref(), &env_var)?;
    Ok((clone_dir, commit, described))
}

fn describe_upstream(
    src: &Path,
    name: &str,
    tag: &str,
    pinned_commit: Option<&str>,
    env_var: &str,
) -> Result<(String, String)> {
    if !src.join(".git").exists()
        && let Some(commit) = pinned_commit
    {
        return Ok((commit.to_string(), tag.to_string()));
    }
    let commit = git_output(&["rev-parse", "HEAD"], src).ok_or_else(|| {
        anyhow!(
            "{} is not a git checkout; cannot record upstream provenance",
            src.display()
        )
    })?;
    if let Some(expected) = pinned_commit
        && commit != expected
    {
        bail!(
            "{name} checkout {} is at commit `{commit}`, expected `{expected}`",
            src.display()
        );
    }
    let described =
        git_output(&["describe", "--tags", "--always"], src).unwrap_or_else(|| "unknown".into());
    let dirty = git_output(&["status", "--porcelain"], src).unwrap_or_default();
    if !dirty.is_empty() {
        bail!(
            "{name} checkout {} has local modifications; refusing to export machine code \
             whose provenance cannot be stated exactly",
            src.display()
        );
    }
    if described != tag {
        bail!(
            "{name} checkout {} is at `{described}`, expected tag `{tag}`. \
             Check out {tag} or point ${env_var} at a checkout that is.",
            src.display()
        );
    }
    Ok((commit, described))
}

fn link_vendor_symlink(crate_dir: &Path, src: &Path, upstream: &UpstreamConfig) -> Result<()> {
    let Some(rel_symlink) = &upstream.vendor_symlink else {
        return Ok(());
    };
    let link = crate_dir.join(rel_symlink);
    if link == src
        || link
            .canonicalize()
            .ok()
            .is_some_and(|c| Some(c) == src.canonicalize().ok())
    {
        return Ok(());
    }
    if let Some(parent) = link.parent() {
        fs::create_dir_all(parent)?;
    }
    if let Ok(meta) = link.symlink_metadata() {
        if fs::read_link(&link).is_ok_and(|target| target == src) {
            return Ok(());
        }
        if meta.file_type().is_symlink() {
            fs::remove_file(&link)?;
        } else {
            return Ok(());
        }
    }
    unix_fs::symlink(src, &link)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compile a small C file with the pinned zig (skipped when it is not available) and check
    /// that the entire object is extracted and local symbols are suffixed with ` [<name>]`.
    #[test]
    fn native_object_compile() {
        let Ok(zig) = resolve_zig("0.16.0") else {
            eprintln!("skipping: zig 0.16.0 not available ($ZIG / PATH)");
            return;
        };
        let dir = tempfile::tempdir().unwrap();
        fs::write(
            dir.path().join("t.c"),
            "static const int tbl[4] = {3, 1, 4, 1};\n\
             const int gtbl[4] = {5, 9, 2, 6};\n\
             extern int ext(int);\n\
             static int helper(int x) { return tbl[x & 3] + gtbl[x & 3] + ext(x); }\n\
             int root(int x) { return helper(x) * 2 + 1; }\n\
             int unrelated(int x) { return x * 7; }\n",
        )
        .unwrap();
        let cfg = NativeObjectConfig {
            name: "t".into(),
            source: "t.c".into(),
            include_dirs: vec![],
            defines: vec![],
            c_flags: vec![],
        };
        let tc = Toolchain {
            repo_root: dir.path().to_path_buf(),
            rustc_version: String::new(),
            path_aliases: vec![],
        };
        let (o, prov, cmd) = extract_native_object(&tc, &zig, dir.path(), &cfg, &[]).unwrap();
        let names: Vec<&str> = o.sections.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&".text.root"), "{names:?}");
        assert!(names.contains(&".text.unrelated"), "{names:?}");
        assert!(names.contains(&".rodata.gtbl"), "{names:?}");
        assert!(
            o.symbols
                .iter()
                .any(|s| s.name == "root" && matches!(s.sec, SymSection::Sec(_)))
        );
        assert!(
            o.symbols
                .iter()
                .any(|s| s.name == "unrelated" && matches!(s.sec, SymSection::Sec(_)))
        );
        assert!(
            o.symbols
                .iter()
                .any(|s| s.name == "gtbl" && matches!(s.sec, SymSection::Sec(_)))
        );
        assert!(
            o.symbols
                .iter()
                .any(|s| s.name == "tbl [t]" && s.bind == SymBind::Local)
        );
        assert!(
            o.symbols
                .iter()
                .any(|s| s.name == "ext" && s.sec == SymSection::Undef)
        );
        assert!(prov.contains("source `t.c`"), "{prov}");
        assert!(
            cmd.starts_with("zig cc -target aarch64-linux-musl"),
            "{cmd}"
        );
        assert!(
            cmd.contains("-fno-jump-tables") && cmd.contains("-fno-common"),
            "{cmd}"
        );
        let n = needed_externs(std::slice::from_ref(&o)).unwrap();
        assert_eq!(
            n.iter().map(|x| x.name.as_str()).collect::<Vec<_>>(),
            ["ext"]
        );
        assert!(n[0].all_branch);
    }

    #[test]
    fn resolves_path_dependency_crates() {
        let tmp = tempfile::tempdir().unwrap();
        let dep_dir = tmp.path().join("vendor/sub");
        fs::create_dir_all(dep_dir.join("src")).unwrap();
        fs::write(
            dep_dir.join("Cargo.toml"),
            "[package]\nname = \"sub-crate\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .unwrap();
        fs::write(dep_dir.join("src/lib.rs"), "pub fn f() {}\n").unwrap();

        fs::create_dir_all(tmp.path().join("src")).unwrap();
        fs::write(
            tmp.path().join("Cargo.toml"),
            "[package]\nname = \"wrapper-crate\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\nsub-crate = { path = \"vendor/sub\" }\n",
        )
        .unwrap();
        fs::write(tmp.path().join("src/lib.rs"), "pub use sub_crate::f;\n").unwrap();

        let resolved = resolve_crates(
            tmp.path(),
            &["sub-crate".to_string(), "wrapper-crate".to_string()],
        )
        .unwrap();
        assert_eq!(resolved.len(), 2);
        assert_eq!(resolved[0].package, "sub-crate");
        assert_eq!(resolved[0].lib_name, "sub_crate");
        assert_eq!(resolved[1].package, "wrapper-crate");
        assert_eq!(resolved[1].lib_name, "wrapper_crate");
    }

    #[test]
    fn page_separate_data_config_parses_defaults_false_and_selects_layout() {
        use crate::untrusted_driver::pipeline::generate_config_with;
        use crate::untrusted_legacy_linker::{self, DataLayout};

        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        fs::write(
            root.join("sample.c"),
            "const unsigned long ro_val = 0x1122334455667788UL;\n\
             unsigned long rw_val = 0x8877665544332211UL;\n\
             unsigned long bss_arr[2];\n\
             extern unsigned long ext_obj;\n\
             unsigned long read_all(void) { return ro_val + rw_val + bss_arr[0] + ext_obj; }\n",
        )
        .unwrap();

        let write_cfg = |extra: &str, name: &str| -> PathBuf {
            let p = root.join(name);
            fs::write(
                &p,
                format!(
                    "obj_name = \"layoutSample\"\n\
                     obj_file = \"Generated/LayoutSampleObj.lean\"\n\
                     code_file = \"Generated/LayoutSampleCode.lean\"\n\
                     namespace_prefix = \"LayoutSample\"\n\
                     title = \"Layout sample\"\n\
                     legacy_linked_image = true\n\
                     c_sources = [\"sample.c\"]\n\
                     {extra}\
                     [[externs]]\n\
                     name = \"ext_obj\"\n\
                     kind = {{ data = 8 }}\n\
                     [[targets]]\n\
                     name = \"ls\"\n\
                     lean_file = \"Generated/LayoutSample.lean\"\n\
                     prog_name = \"lsProg\"\n\
                     title = \"Layout sample\"\n\
                     lemma_allowlist = [\"read_all\"]\n"
                ),
            )
            .unwrap();
            p
        };

        // 1. Default omitted == false; explicit `true` == true; non-bool rejected.
        let default_toml = write_cfg("", "default.toml");
        let false_toml = write_cfg("page_separate_data = false\n", "false.toml");
        let true_toml = write_cfg("page_separate_data = true\n", "true.toml");
        let bad_toml = write_cfg("page_separate_data = \"yes\"\n", "bad.toml");

        let cfg_default = load_config(&default_toml, root, Some(&root.join("out_def"))).unwrap();
        let cfg_false = load_config(&false_toml, root, Some(&root.join("out_false"))).unwrap();
        let cfg_true = load_config(&true_toml, root, Some(&root.join("out_true"))).unwrap();
        assert!(!cfg_default.page_separate_data);
        assert!(!cfg_false.page_separate_data);
        assert!(cfg_true.page_separate_data);

        let err = load_config(&bad_toml, root, None)
            .expect_err("non-boolean `page_separate_data` must fail deserialization");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("invalid type") || msg.contains("page_separate_data"),
            "unexpected error for non-bool `page_separate_data`: {msg}"
        );

        // 2. End-to-end export check when zig is available: default vs explicit false vs true.
        if find_zig_binary("test").is_err() {
            eprintln!("skipping end-to-end C page_separate_data test: zig not available");
            return;
        }
        let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
        let ex = extract(&cfg_default, &mut tc).unwrap();
        let li_interleaved = untrusted_legacy_linker::link_with_layout(
            &ex.objects,
            &ex.externs,
            0,
            DataLayout::Interleaved,
        )
        .unwrap();
        let li_separated = untrusted_legacy_linker::link_with_layout(
            &ex.objects,
            &ex.externs,
            0,
            DataLayout::PageSeparated,
        )
        .unwrap();
        assert_ne!(li_interleaved.got_off, li_separated.got_off);

        let files_def = generate_config_with(&cfg_default, &mut tc, false).unwrap();
        let files_false = generate_config_with(&cfg_false, &mut tc, false).unwrap();
        let files_true = generate_config_with(&cfg_true, &mut tc, false).unwrap();

        let find_bytes = |files: &[crate::untrusted_driver::pipeline::GeneratedFile], sfx: &str| {
            files
                .iter()
                .find(|f| f.path.to_string_lossy().ends_with(sfx))
                .unwrap()
                .contents
                .clone()
        };
        assert_eq!(
            find_bytes(&files_def, ".code.bin"),
            li_interleaved.code
        );
        assert_eq!(
            find_bytes(&files_def, ".data.bin"),
            li_interleaved.data
        );
        assert_eq!(
            find_bytes(&files_false, ".code.bin"),
            find_bytes(&files_def, ".code.bin")
        );
        assert_eq!(
            find_bytes(&files_false, ".data.bin"),
            find_bytes(&files_def, ".data.bin")
        );
        assert_eq!(find_bytes(&files_true, ".code.bin"), li_separated.code);
        assert_eq!(find_bytes(&files_true, ".data.bin"), li_separated.data);
    }

    #[test]
    fn target_config_defaults_to_gnu_accepts_musl_and_rejects_non_aarch64() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"alpha\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let write_cfg = |extra: &str, name: &str| -> PathBuf {
            let p = root.join(name);
            fs::write(
                &p,
                format!(
                    "obj_name = \"alpha\"\n\
                     {extra}\
                     [[targets]]\n\
                     name = \"alpha\"\n\
                     lean_file = \"Generated/Alpha.lean\"\n\
                     prog_name = \"alphaProg\"\n\
                     title = \"Alpha\"\n\
                     lemma_allowlist = [\".*\"]\n"
                ),
            )
            .unwrap();
            p
        };

        let def_cfg = load_config(&write_cfg("", "def.toml"), root, None).unwrap();
        assert_eq!(def_cfg.target, DEFAULT_TARGET);

        let musl_cfg = load_config(
            &write_cfg("target = \"aarch64-unknown-linux-musl\"\n", "musl.toml"),
            root,
            None,
        )
        .unwrap();
        assert_eq!(musl_cfg.target, "aarch64-unknown-linux-musl");

        let err = load_config(
            &write_cfg("target = \"x86_64-unknown-linux-gnu\"\n", "bad.toml"),
            root,
            None,
        )
        .expect_err("non-aarch64 target must be rejected");
        assert!(format!("{err:#}").contains("aarch64-unknown-linux-musl"));

        let json_err = load_config(
            &write_cfg("target = \"aarch64-foo.json\"\n", "json.toml"),
            root,
            None,
        )
        .expect_err("custom json target spec must be rejected");
        assert!(format!("{json_err:#}").contains("aarch64-unknown-linux-musl"));
    }
}
