// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `snapshot-link --stock` inputs for a Rust `std` binary `--main-rust` and for native objects
//! (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. Prepares link inputs for [`crate::stock::run`]; the linked
//!   executable is checked by proofs against its SHA-256-pinned bytes.
//! - **Purpose:**
//!   - [`prepare_std_bin`]: compile a safe Rust `std` binary crate under the pinned Rust `1.98.1`
//!     `-Zbuild-std=std,panic_abort` profile ([`crate::std_profile::build_std_main_objects`]) and
//!     take the C runtime from rustc's own musl `self-contained` directory (`crt1.o`, `crti.o`,
//!     `crtbegin.o`, `libc.a`, `libunwind.a`, `crtend.o`, `crtn.o`), never from `zig`. Every
//!     runtime file must have its pinned SHA-256 ([`crate::std_profile::SELF_CONTAINED_CHECKSUMS`])
//!     and is copied unmodified to `work/self-contained/`. Global symbols that `main_rust.o` and
//!     the `--config` objects both define are weakened in `main_rust.o`, so calls bind to the
//!     extracted objects the proofs are about.
//!   - [`stage_native_objects`]: copy each `--stock-native-object` (a relocatable AArch64 ELF
//!     object) to `work/native/`.
//!   - [`InputNotes`]: the extra `stock-link.json` `inputs[]` fields of these files (`kind`, and
//!     `pinnedSha256` for the self-contained runtime).
//!
//! # When to Read This File
//! - Read this file for how `--stock` links a Rust `std` binary or a native object.

use crate::link::{run_cmd, sha256};
use crate::std_profile::{
    MUSL_TARGET, PINNED_LLVM_VERSION, PINNED_RUSTC_COMMIT, PINNED_RUSTC_RELEASE,
    SELF_CONTAINED_CHECKSUMS, StdBinCrate, StdToolchain, build_std_main_objects,
};
use crate::stock::StockImage;
use anyhow::{Context, Result, ensure};
use object::{Object, ObjectSymbol};
use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Extra `stock-link.json` `inputs[]` fields, keyed by input path.
pub type InputNotes = HashMap<PathBuf, serde_json::Value>;

/// The link inputs of a `std` binary, in the slots of [`crate::stock::run`].
pub struct StdBinInputs {
    /// `crt1.o`, `crti.o`, `crtbegin.o` (before the library objects).
    pub pre: Vec<PathBuf>,
    /// `work/main_rust.o`, the `std` binary's single fat-LTO object (first in the group).
    pub main: PathBuf,
    /// `libc.a`, `compiler_builtins.a`, `libunwind.a` (in the group after `main`).
    pub libs: Vec<PathBuf>,
    /// `crtend.o`, `crtn.o` (last).
    pub post: Vec<PathBuf>,
    /// Extra `inputs[]` fields of the self-contained runtime files.
    pub notes: InputNotes,
    /// The `stdBin` object of `stock-link.json`.
    pub record: serde_json::Value,
}

/// Prepare the inputs of a `--stock` link of the `std` binary crate `std_crate` with `images`.
pub fn prepare_std_bin(
    cli: &crate::Cli,
    repo_root: &Path,
    work: &Path,
    std_crate: &StdBinCrate,
    images: &[StockImage],
) -> Result<StdBinInputs> {
    let explicit = cli
        .stock_self_contained_dir
        .as_ref()
        .map(|d| repo_root.join(d));
    let std_tc = StdToolchain::resolve_with(explicit.as_deref())?;
    let objcopy = std_tc.resolve_objcopy()?;

    // The runtime first: it is cheap to check, and a bad one must fail before the build.
    let sc_dir = work.join("self-contained");
    let mut notes = InputNotes::new();
    let mut copied = HashMap::new();
    std::fs::create_dir_all(&sc_dir)?;
    for &(file, pinned) in SELF_CONTAINED_CHECKSUMS {
        let src = std_tc.self_contained.join(file);
        let dst = sc_dir.join(file);
        let bytes = std::fs::read(&src)
            .with_context(|| format!("missing self-contained runtime input {}", src.display()))?;
        let got = sha256(&bytes);
        ensure!(
            got == pinned,
            "SHA-256 mismatch for self-contained {}: expected {pinned}, got {got}",
            src.display()
        );
        std::fs::write(&dst, &bytes)?;
        notes.insert(
            dst.clone(),
            serde_json::json!({"kind": "selfContained", "pinnedSha256": pinned}),
        );
        copied.insert(file, dst);
    }
    let sc = |f: &str| copied[f].clone();

    let (raw_main, builtins) = build_std_main_objects(
        &std_tc,
        std_crate,
        repo_root,
        work,
        &objcopy,
        // Weakened below by `weaken_image_symbols`, which also records the names.
        &Default::default(),
    )?;
    // The objects as emitted into `work/` (a trimmed sysroot object as its trim), so only names
    // the linked library really defines are weakened.
    let emitted = images
        .iter()
        .flat_map(|im| im.paths.iter())
        .map(std::fs::read)
        .collect::<std::io::Result<Vec<_>>>()?;
    let weakened = weaken_image_symbols(&objcopy, &raw_main, emitted.iter().map(Vec::as_slice))?;

    let shown_dir = match &cli.stock_self_contained_dir {
        Some(d) => d.display().to_string(),
        None => format!("<sysroot>/lib/rustlib/{MUSL_TARGET}/lib/self-contained"),
    };
    let record = serde_json::json!({
        "rustc": PINNED_RUSTC_RELEASE,
        "commit": PINNED_RUSTC_COMMIT,
        "llvm": PINNED_LLVM_VERSION,
        "selfContainedDir": shown_dir,
        "weakenedInMain": weakened,
        "rebuildKey": rebuild_key(&std_tc, std_crate, repo_root, work)?,
    });
    Ok(StdBinInputs {
        pre: vec![sc("crt1.o"), sc("crti.o"), sc("crtbegin.o")],
        main: raw_main,
        libs: vec![sc("libc.a"), builtins, sc("libunwind.a")],
        post: vec![sc("crtend.o"), sc("crtn.o")],
        notes,
        record,
    })
}

/// The `cargo` arguments of [`build_std_main_objects`] after its toolchain prefix (also run with
/// `RUSTC_BOOTSTRAP=1`, `CARGO_TARGET_DIR=work/rust-target`, and no `RUSTFLAGS`).
const STD_CARGO_ARGS: &[&str] = &[
    "rustc",
    "--manifest-path",
    "<manifest>",
    "--target",
    MUSL_TARGET,
    "--release",
    "--locked",
    "-Zbuild-std=std,panic_abort",
    "--",
    "--emit=obj",
];

/// The `stdBin.rebuildKey` of `stock-link.json`: what `main_rust.o` and `compiler_builtins.a` are
/// rebuilt from. The exact `cargo` arguments and `CARGO_ENCODED_RUSTFLAGS` (without the
/// machine-specific `--remap-path-prefix` sources, whose targets are listed), the SHA-256 of the
/// crate manifest and lockfile, and of every source file in cargo's dep-info for both outputs,
/// with paths relative to the repository (`/src`), the rust-src component (`/rustc`), the cargo
/// home (`/cargo`), the work directory (`/work`) or a crate outside the repository (`/crate`). `compilerBuiltinsSources` lists only the
/// count and the digest of its `<sha256>  <path>` lines; `std` itself is pinned by the rustc commit.
pub(crate) fn rebuild_key(
    tc: &StdToolchain,
    std_crate: &StdBinCrate,
    repo_root: &Path,
    work: &Path,
) -> Result<serde_json::Value> {
    let home = std::env::var_os("HOME").map(PathBuf::from);
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| home.as_ref().map(|h| h.join(".cargo")));
    let rustup_home = std::env::var_os("RUSTUP_HOME")
        .map(PathBuf::from)
        .or_else(|| home.as_ref().map(|h| h.join(".rustup")));
    let flags = crate::std_profile::std_encoded_rustflags(
        repo_root,
        &std_crate.crate_dir,
        work,
        cargo_home.as_deref(),
        rustup_home.as_deref(),
        &tc.sysroot,
    );
    let (remaps, rustflags): (Vec<&str>, Vec<&str>) = flags
        .split('\x1f')
        .partition(|f| f.starts_with("--remap-path-prefix="));
    let mut remap_targets: Vec<&str> = remaps
        .iter()
        .filter_map(|f| f.rsplit_once('=').map(|(_, to)| to))
        .collect();
    remap_targets.sort();
    remap_targets.dedup();

    let rust_src = tc.sysroot.join("lib/rustlib/src/rust");
    let roots: Vec<(PathBuf, &str)> = [
        Some((rust_src, "/rustc")),
        Some((work.to_path_buf(), "/work")),
        // A crate outside the repository (as in [`crate::std_profile::std_encoded_rustflags`]).
        Some((std_crate.crate_dir.clone(), "/crate"))
            .filter(|_| !std_crate.crate_dir.starts_with(repo_root)),
        Some((repo_root.to_path_buf(), "/src")),
        cargo_home.map(|c| (c, "/cargo")),
    ]
    .into_iter()
    .flatten()
    .collect();
    let shown = |p: &Path| -> String {
        roots
            .iter()
            .filter_map(|(r, to)| Some((r.as_os_str().len(), p.strip_prefix(r).ok()?, to)))
            .max_by_key(|(n, _, _)| *n)
            .map_or(p.display().to_string(), |(_, r, to)| {
                format!("{to}/{}", r.display())
            })
    };
    let hashed = |p: &Path| -> Result<serde_json::Value> {
        let bytes = std::fs::read(p)
            .with_context(|| format!("cannot read rebuild input {}", p.display()))?;
        Ok(serde_json::json!({"path": shown(p), "sha256": sha256(&bytes)}))
    };
    let lockfile = std_crate
        .crate_dir
        .ancestors()
        .take_while(|d| d.starts_with(repo_root) || *d == std_crate.crate_dir)
        .map(|d| d.join("Cargo.lock"))
        .find(|p| p.is_file())
        .context("no Cargo.lock for the --main-rust crate (it is built with --locked)")?;
    let ws_root = lockfile.parent().unwrap_or(&std_crate.crate_dir);

    let deps = work
        .join("rust-target")
        .join(MUSL_TARGET)
        .join("release")
        .join("deps");
    let sources = |prefix: &str, list: bool| -> Result<serde_json::Value> {
        let mut files = BTreeSet::new();
        let mut found = 0usize;
        for e in std::fs::read_dir(&deps)? {
            let p = e?.path();
            let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if !(name.starts_with(prefix) && name.ends_with(".d")) {
                continue;
            }
            found += 1;
            for line in std::fs::read_to_string(&p)?.lines() {
                // Each source is listed alone as an empty-prerequisite rule `<path>:`.
                if let Some(src) = line.strip_suffix(':')
                    && !src.contains(": ")
                    && !src.is_empty()
                {
                    // Cargo writes workspace sources relative to the
                    // workspace root (the directory of `Cargo.lock`).
                    files.insert(ws_root.join(src.replace("\\ ", " ")));
                }
            }
        }
        ensure!(
            found > 0,
            "no cargo dep-info `{prefix}*.d` in {}",
            deps.display()
        );
        let entries = files
            .iter()
            .map(|p| hashed(p))
            .collect::<Result<Vec<_>>>()?;
        let lines: String = entries
            .iter()
            .map(|e| {
                format!(
                    "{}  {}\n",
                    e["sha256"].as_str().unwrap_or(""),
                    e["path"].as_str().unwrap_or("")
                )
            })
            .collect();
        let mut v = serde_json::json!({"count": entries.len(), "sha256": sha256(lines.as_bytes())});
        if list {
            v["files"] = entries.into();
        }
        Ok(v)
    };
    Ok(serde_json::json!({
        "cargoArgs": STD_CARGO_ARGS
            .iter()
            .map(|a| if *a == "<manifest>" { shown(&std_crate.manifest_path) } else { a.to_string() })
            .collect::<Vec<_>>(),
        "rustflags": rustflags,
        "remapTargets": remap_targets,
        "manifest": hashed(&std_crate.manifest_path)?,
        "lockfile": hashed(&lockfile)?,
        "mainSources": sources(&format!("{}-", std_crate.bin_stem), true)?,
        "compilerBuiltinsSources": sources("compiler_builtins-", false)?,
    }))
}

/// Weaken, in place, every global symbol `main_o` defines that one of the `--config` objects
/// `image_objects` also defines (the `std` binary's LTO object carries its own copies of the
/// library functions it calls), so that the extracted definitions win. Returns the weakened
/// names, sorted.
pub(crate) fn weaken_image_symbols<'a>(
    objcopy: &Path,
    main_o: &Path,
    image_objects: impl Iterator<Item = &'a [u8]>,
) -> Result<Vec<String>> {
    let mut exported = BTreeSet::new();
    for o in image_objects {
        exported.extend(defined_globals(o)?);
    }
    let main_defs = defined_globals(&std::fs::read(main_o)?)?;
    let weaken: Vec<String> = main_defs.intersection(&exported).cloned().collect();
    if !weaken.is_empty() {
        let tmp = main_o.with_extension("unweakened.o");
        std::fs::rename(main_o, &tmp)?;
        let mut c = Command::new(objcopy);
        for s in &weaken {
            c.arg(format!("--weaken-symbol={s}"));
        }
        run_cmd(c.arg(&tmp).arg(main_o))?;
        std::fs::remove_file(&tmp)?;
    }
    Ok(weaken)
}

/// The names of the defined, non-local symbols of the ELF object `bytes`.
fn defined_globals(bytes: &[u8]) -> Result<BTreeSet<String>> {
    let f = object::File::parse(bytes).context("cannot parse object")?;
    let mut out = BTreeSet::new();
    for s in f.symbols() {
        if s.is_undefined() || s.is_local() || !s.is_definition() {
            continue;
        }
        if let Ok(n) = s.name()
            && !n.is_empty()
        {
            out.insert(n.to_string());
        }
    }
    Ok(out)
}

/// Copy every `--stock-native-object` (resolved against `repo_root`) to `work/native/<file
/// name>`, after checking that it is a relocatable little-endian AArch64 ELF64 object.
pub fn stage_native_objects(
    paths: &[PathBuf],
    repo_root: &Path,
    work: &Path,
) -> Result<(Vec<PathBuf>, InputNotes)> {
    let dir = work.join("native");
    let mut staged = Vec::with_capacity(paths.len());
    let mut notes = InputNotes::new();
    if paths.is_empty() {
        return Ok((staged, notes));
    }
    std::fs::create_dir_all(&dir)?;
    for p in paths {
        let src = repo_root.join(p);
        let bytes = std::fs::read(&src)
            .with_context(|| format!("cannot read --stock-native-object {}", src.display()))?;
        check_native_object(&bytes)
            .with_context(|| format!("--stock-native-object {}", src.display()))?;
        let name = src
            .file_name()
            .with_context(|| format!("--stock-native-object {} has no file name", p.display()))?;
        let dst = dir.join(name);
        ensure!(
            !dst.exists(),
            "two --stock-native-object inputs are named {name:?}"
        );
        std::fs::write(&dst, &bytes)?;
        notes.insert(dst.clone(), serde_json::json!({"kind": "nativeObject"}));
        staged.push(dst);
    }
    Ok((staged, notes))
}

/// Accept only a relocatable (`ET_REL`) little-endian AArch64 ELF64 object.
pub fn check_native_object(bytes: &[u8]) -> Result<()> {
    let f = object::File::parse(bytes).context("not an object file")?;
    ensure!(
        f.format() == object::BinaryFormat::Elf
            && f.architecture() == object::Architecture::Aarch64
            && f.is_64()
            && f.is_little_endian(),
        "not a little-endian AArch64 ELF64 object"
    );
    ensure!(
        f.kind() == object::ObjectKind::Relocatable,
        "not a relocatable object (ET_REL)"
    );
    Ok(())
}
