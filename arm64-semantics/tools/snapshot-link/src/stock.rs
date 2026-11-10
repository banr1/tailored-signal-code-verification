// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `snapshot-link --stock`: link the unmodified extracted objects with plain `ld.lld`
//! (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. Produces an ordinary static executable for a layout-generic
//!   proof to be checked against; nothing about its layout is assumed.
//! - **Purpose:** for each `--config`, write the exact relocatable objects `rust-obj2lean`
//!   extracts (the `.o` bytes the proofs are about, not the pinned/renamed copies the default
//!   recipe links), compile `main` (`--main-c`, or a `--main-rust` staticlib), and link them with
//!   the musl C runtime `zig cc` would use by calling `ld.lld` directly with the flags in
//!   [`LLD_FLAGS`]: no linker script, linker relaxation on (no `--no-relax`), no pinned addresses,
//!   lld's default page size and section order. Then check that the result is accepted by the
//!   static-ELF constraints of the trusted loader ([`crate::verify::check_std_elf`]) and run the
//!   relocation-site census ([`crate::census`]). Writes `<name>`, `stock-link.json` (provenance,
//!   reproducible) and `census.json` into `--out-dir`; the link wall time goes to `timing.json`.
//!   The full `ld.lld` output and its link map stay in `work/` ([`LLD_LOG`], `link.map`); when
//!   externs are traced, `stock-link.json` records each traced `definition of` line
//!   (`traceSymbolDefinitions`), including the externs of every `--config` image.
//! - A trimmed `[[sysroot_objects]]` entry is linked as the real relocatable object of its trim
//!   ([`crate::trimmed::emit`], re-parsed and compared with the trim before linking), never as the
//!   whole rlib member; `stock-link.json` records the member's SHA-256, the keep set and its digest.
//!   The trim's defined globals are `--gc-sections` roots, and the link fails if lld still removes
//!   any of its sections, so the image holds exactly the keep set.
//!   The hooked externs of such a config may not be defined by any Rust archive on the link line
//!   (except weakly, shadowed by a global stub definition), and after the link each must resolve
//!   to an allowed object, the musl runtime, or a declared export of a sibling `--config` image
//!   (lld `--trace-symbol`; see [`crate::stock_hooks`]). `stock-link.json` then also records the trim's rlib, member and roots, the
//!   engine commit, the hooked externs and the alias names exempted from the unwind-symbol audit.
//!   Files named by `--stock-lld-arg` (e.g. a `-T` linker script) are hashed there too.
//!
//! # Key Types & Functions
//! - [`run`]: the recipe. [`LLD_FLAGS`]: the `ld.lld` flags, each documented.
//! - [`crate::stock_std`]: the inputs of a Rust `std` binary `--main-rust` (rustc's pinned musl
//!   `self-contained` runtime instead of `zig`'s) and of `--stock-native-object`s.
//!
//! # When to Read This File
//! - Read this file to see exactly how a stock-linked executable is produced.

use crate::link::{
    build_rust_main_archive, musl_inputs, run_cmd, sha256, stage_runtime_inputs, tool, version,
};
use crate::{Cli, census, stock_hooks, stock_std, stock_std_audit, trimmed, verify};
use anyhow::{Context, Result, bail, ensure};
use object::read::elf::{ElfFile64, FileHeader, ProgramHeader};
use object::{Endianness, Object, ObjectSection};
use rust_obj2lean::trusted_common::{ExternDecl, ObjObject};
use rust_obj2lean::untrusted_driver::{self, Toolchain, config::load_config};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// The full `ld.lld` output, written into the work directory.
pub const LLD_LOG: &str = "lld.log";

/// The `ld.lld --trace-symbol` verbs (`<file>: <verb> <name>`).
const TRACE_VERBS: &[&str] = &[
    ": definition of ",
    ": lazy definition of ",
    ": common definition of ",
    ": reference to ",
    ": shared definition of ",
];

/// The `(file, verb, name)` of an `ld.lld --trace-symbol` line.
fn trace_line(line: &str) -> Option<(&str, &str, &str)> {
    let l = line.trim();
    TRACE_VERBS.iter().find_map(|v| {
        let (f, n) = l.split_once(v)?;
        Some((f, v.trim_start_matches(": ").trim_end(), n))
    })
}

/// `lld_log` without the `--trace-symbol` lines of the names in `names`.
pub(crate) fn without_trace_of(lld_log: &str, names: &BTreeSet<String>) -> String {
    lld_log
        .lines()
        .filter(|l| !trace_line(l).is_some_and(|(_, _, n)| names.contains(n)))
        .map(|l| format!("{l}\n"))
        .collect()
}

/// The `traceSymbolDefinitions` of `stock-link.json`: each `definition of` line of `lld_log`, with
/// its file mapped through `rel`.
pub(crate) fn trace_definitions(lld_log: &str, rel: impl Fn(&Path) -> String) -> serde_json::Value {
    lld_log
        .lines()
        .filter_map(trace_line)
        .filter(|(_, v, _)| v.ends_with("definition of"))
        .map(|(f, v, n)| {
            // An archive member `<archive>(<member>)`: map the archive path only.
            let file = match f.strip_suffix(')').and_then(|s| s.rsplit_once('(')) {
                Some((a, m)) => format!("{}({m})", rel(Path::new(a))),
                None => rel(Path::new(f)),
            };
            serde_json::json!({"symbol": n, "kind": v, "file": file})
        })
        .collect()
}

/// The `ld.lld` flags of a stock link (inputs and `-o` are appended), mirroring what `zig cc`
/// passes for a static `aarch64-linux-musl` release link minus everything that only pins the
/// layout or the toolchain:
/// - `-static`, `-no-pie`: a static `ET_EXEC` without dynamic sections (the trusted loader only
///   accepts static `ET_EXEC`).
/// - `--entry _start`: the musl `crt1.o` entry point (also lld's default).
/// - `--gc-sections`: drop unreferenced input sections, as every release link does.
/// - `--eh-frame-hdr`: emit `.eh_frame_hdr` / `PT_GNU_EH_FRAME`, as `zig cc` and `rustc` do.
/// - `-z now`: as `zig cc` passes (no effect on a static link).
/// - `--build-id=none`: no build-id note, so the output is reproducible.
/// - `--strip-debug`: drop non-allocated debug sections (they only carry toolchain paths; the
///   loaded image does not change).
///
/// Not passed (lld defaults): no `-T` linker script, no `--no-relax` (relaxation on), no `--icf`
/// (lld's default is `--icf=none`), no `-z max-page-size` / `-z common-page-size` (64 KiB on
/// AArch64), no `-z norelro`, no `--image-base`, no `-z separate-code`, and lld's default
/// optimization level `-O1` (`SHF_MERGE` deduplication only). `zig cc` passes `-O3` instead,
/// which turns on `--branch-to-branch` (a `bl f` whose target `f` starts with `b g` becomes
/// `bl g`, so a call site's word depends on the callee's code) and string tail merging; pass
/// `--stock-lld-arg=-O2` to get them.
pub const LLD_FLAGS: &[&str] = &[
    "-static",
    "-no-pie",
    "--entry",
    "_start",
    "--gc-sections",
    "--eh-frame-hdr",
    "-z",
    "now",
    "--build-id=none",
    "--strip-debug",
];

/// One `--config`: its extracted objects and the files they were written to.
pub struct StockImage {
    pub config: PathBuf,
    pub objects: Vec<ObjObject>,
    pub externs: Vec<ExternDecl>,
    pub page_separate_data: bool,
    pub paths: Vec<PathBuf>,
    /// Per object: `Some` for a trimmed `[[sysroot_objects]]` entry, whose file in `paths` is the
    /// emitted trim (its `elf_bytes` are still the whole rlib member).
    pub trimmed: Vec<Option<trimmed::Trimmed>>,
    /// Declared exports (`[placed] exports`, then `[[sysroot_objects]] roots`), raw or demangled:
    /// the names a sibling image's hooked extern may resolve to ([`crate::stock_hooks`]).
    pub exports: Vec<String>,
}

/// Run the `--stock` recipe for `cli`.
pub fn run(cli: &Cli) -> Result<()> {
    ensure!(!cli.out_dir.as_os_str().is_empty(), "--out-dir is required");
    ensure!(
        !cli.config.is_empty(),
        "--stock needs at least one --config"
    );
    ensure!(
        cli.base.is_empty()
            && cli.expect_code.is_empty()
            && cli.expect_data.is_empty()
            && cli.native_objects.is_none()
            && !cli.musl_string
            && cli.branch_stubs.is_empty()
            && !cli.page_separate_data,
        "--stock does not pin a layout: --base, --expect-code, --expect-data, --native-objects, \
         --musl-string, --branch-stubs and --page-separate-data do not apply"
    );
    let repo_root = std::fs::canonicalize(&cli.repo_root)?;
    std::fs::create_dir_all(&cli.out_dir)?;
    let out_dir = std::fs::canonicalize(&cli.out_dir)?;
    let work = out_dir.join("work");
    if work.exists() {
        std::fs::remove_dir_all(&work)?;
    }
    std::fs::create_dir_all(&work)?;

    // 1. The objects of every image, byte for byte as extracted.
    let mut tc = Toolchain::new(repo_root.clone())?;
    let mut images = Vec::with_capacity(cli.config.len());
    for (k, config) in cli.config.iter().enumerate() {
        let gen_dir = work.join(format!("gen{k}"));
        std::fs::create_dir_all(&gen_dir)?;
        let cfg = load_config(&repo_root.join(config), &repo_root, Some(&gen_dir))?;
        let ex = untrusted_driver::extract(&cfg, &mut tc)
            .with_context(|| format!("cannot extract {}", config.display()))?;
        let mut paths = Vec::with_capacity(ex.objects.len());
        let mut trims = Vec::with_capacity(ex.objects.len());
        for (i, o) in ex.objects.iter().enumerate() {
            let p = work.join(format!("lib{k}_{i}.o"));
            if let Some(s) = cfg.sysroot_objects.iter().find(|s| s.obj_name() == o.name) {
                // The trim, not the whole member: see `crate::trimmed`.
                trimmed::write(o, &s.roots, &p).with_context(|| {
                    format!("{}: sysroot object `{}`", config.display(), o.name)
                })?;
                let provenance = ex
                    .provenance
                    .iter()
                    .find(|(k, _)| *k == format!("Object `{}` (trimmed)", o.name))
                    .map(|(_, v)| v.clone())
                    .unwrap_or_default();
                trims.push(Some(trimmed::Trimmed {
                    provenance,
                    roots: s.roots.clone(),
                }));
            } else {
                std::fs::write(&p, &o.elf_bytes)?;
                trims.push(None);
            }
            paths.push(p);
        }
        let exports = cfg
            .placed
            .iter()
            .flat_map(|p| p.exports.iter())
            .chain(cfg.sysroot_objects.iter().flat_map(|s| s.roots.iter()))
            .cloned()
            .collect();
        images.push(StockImage {
            exports,
            config: config.clone(),
            objects: ex.objects,
            externs: ex.externs,
            page_separate_data: cfg.page_separate_data,
            paths,
            trimmed: trims,
        });
    }

    // 2. `main` and the C runtime: the musl runtime `zig cc` would link, or for a Rust `std`
    // binary `--main-rust` rustc's own `self-contained` musl runtime (`crate::stock_std`).
    let objcopy = tool("LLVM_OBJCOPY", "llvm-objcopy")?;
    let lld = tool("LLD", "ld.lld")?;
    let zig = untrusted_driver::find_zig_binary("snapshot-link")?;
    let std_bin = match &cli.main_rust {
        Some(m) => match crate::std_profile::classify_rust_manifest(m, &repo_root)? {
            crate::std_profile::RustMainKind::Staticlib => None,
            crate::std_profile::RustMainKind::StdBin(c) => Some(c),
        },
        None => None,
    };
    let (native, mut notes) =
        stock_std::stage_native_objects(&cli.stock_native_object, &repo_root, &work)?;
    let main_o = work.join("main.o");
    let (pre, libs, post, main_rust, std_record) = if let Some(c) = &std_bin {
        let s = stock_std::prepare_std_bin(cli, &repo_root, &work, c, &images)?;
        notes.extend(s.notes);
        (s.pre, s.libs, s.post, Some(s.main), Some(s.record))
    } else {
        ensure!(
            cli.stock_self_contained_dir.is_none(),
            "--stock-self-contained-dir needs a Rust std binary --main-rust"
        );
        let (pre, libs, post, main_rust) =
            zig_runtime(cli, &repo_root, &work, &zig, &objcopy, &tc)?;
        (pre, libs, post, main_rust, None)
    };

    // 3. Link. Inputs in `zig cc` order: startup objects, main (a C `main`), native objects, the
    // library objects, the archives (as a group, after a Rust `main`), trailing objects.
    let exe = out_dir.join(&cli.name);
    let lld_arg_files = lld_arg_files(&cli.stock_lld_arg, &work)?;
    stock_hooks::check_lld_args(&cli.stock_lld_arg)?;
    let mut args: Vec<PathBuf> = LLD_FLAGS.iter().map(PathBuf::from).collect();
    args.extend(cli.stock_lld_arg.iter().map(PathBuf::from));
    if cli.stock_keep_library {
        args.extend(library_roots(&images).map(|s| PathBuf::from(format!("--undefined={s}"))));
    }
    let trim_paths = trimmed_paths(&images);
    args.extend(trimmed_link_args(&images));
    if std_bin.is_some() {
        args.extend(stock_std_audit::lld_args().map(PathBuf::from));
    } else {
        // Always keep the link map (a `std` binary link already writes one): it gives each
        // sibling-defined extern's placed address and lets a reviewer attribute every section.
        args.push(format!("-Map={}", stock_std_audit::LINK_MAP).into());
    }
    // Hooked externs of images with trims: no archive but the C runtime may define one.
    let hooked = stock_hooks::hooked_externs(&images);
    // The other images' externs are traced too, for the record only (`traceSymbolDefinitions`);
    // the hook checks see only the hooked names' trace lines.
    let traced_only: BTreeSet<String> = if hooked.is_empty() {
        BTreeSet::new()
    } else {
        images
            .iter()
            .flat_map(|im| im.externs.iter().map(|e| e.raw_name.clone()))
            .filter(|n| !hooked.contains(n))
            .collect()
    };
    let stub_objs: Vec<&Path> = pre
        .iter()
        .chain(&post)
        .chain(std::iter::once(&main_o).filter(|_| main_rust.is_none()))
        .chain(&native)
        .chain(
            lld_arg_files
                .iter()
                .map(|(_, p)| p)
                .filter(|p| !is_archive(p)),
        )
        .map(PathBuf::as_path)
        .collect();
    // A Rust `std` binary links `compiler_builtins.a` next to the C runtime; it is a Rust archive,
    // not part of the C runtime, and `main_rust.o` is a plain object.
    let is_rust_lib = |p: &&PathBuf| {
        std_bin.is_some() && p.file_name().is_some_and(|n| n == "compiler_builtins.a")
    };
    let runtime_archives: Vec<&Path> = libs
        .iter()
        .filter(|p| !is_rust_lib(p))
        .map(PathBuf::as_path)
        .collect();
    let hook_plan = if hooked.is_empty() {
        None
    } else {
        let other_archives: Vec<&Path> = main_rust
            .iter()
            .filter(|p| is_archive(p))
            .chain(libs.iter().filter(is_rust_lib))
            .chain(
                lld_arg_files
                    .iter()
                    .map(|(_, p)| p)
                    .filter(|p| is_archive(p)),
            )
            .map(PathBuf::as_path)
            .collect();
        let plan = stock_hooks::plan(&images, &stub_objs, &other_archives)?;
        args.extend(
            hooked
                .iter()
                .chain(&traced_only)
                .map(|n| PathBuf::from(format!("--trace-symbol={n}"))),
        );
        Some(plan)
    };
    args.push("-o".into());
    args.push(exe.clone());
    args.extend(pre.iter().cloned());
    if main_rust.is_none() {
        args.push(main_o.clone());
    }
    args.extend(native.iter().cloned());
    for im in &images {
        args.extend(im.paths.iter().cloned());
    }
    args.push("--start-group".into());
    if let Some(a) = &main_rust {
        args.push(a.clone());
    }
    args.extend(libs.iter().cloned());
    args.push("--end-group".into());
    args.extend(post.iter().cloned());
    let t0 = Instant::now();
    let lld_log = run_cmd(Command::new(&lld).current_dir(&work).args(&args))?;
    let link_secs = t0.elapsed().as_secs_f64();
    // The full `ld.lld` output (`--trace-symbol`, `--print-gc-sections`), kept for review.
    std::fs::write(work.join(LLD_LOG), &lld_log)?;
    let lld_out = without_trace_of(&lld_log, &traced_only);
    let lld_out = lld_out.as_str();
    trimmed::check_none_collected(lld_out, &trim_paths)?;

    // 4. Check, census, provenance.
    let elf_bytes = std::fs::read(&exe)?;
    let hook_record = match &hook_plan {
        Some(plan) => {
            let map = if plan.siblings.is_empty() {
                None
            } else {
                let p = work.join(stock_std_audit::LINK_MAP);
                Some(
                    std::fs::read_to_string(&p)
                        .with_context(|| format!("cannot read {}", p.display()))?,
                )
            };
            Some(stock_hooks::check(
                plan,
                &lld_out,
                &stub_objs,
                &runtime_archives,
                &elf_bytes,
                map.as_deref(),
            )?)
        }
        None => {
            let bad = trimmed::disallowed_definers(&lld_out, &stub_objs, &runtime_archives);
            ensure!(
                bad.is_empty(),
                "hooked externs resolve to neither a stub nor the C runtime:\n  {}",
                bad.join("\n  ")
            );
            None
        }
    };
    let trims: Vec<(&ObjObject, &[String])> = images
        .iter()
        .flat_map(|im| im.objects.iter().zip(&im.trimmed))
        .filter_map(|(o, t)| Some((o, t.as_ref()?.roots.as_slice())))
        .collect();
    let exempt = trimmed::exempt_aliases(&elf_bytes, &trims)?;
    let parser_check = verify::check_std_elf_exempting(&elf_bytes, &exempt);
    // A `std` binary: which archive members lld extracted, and no unwinder (fails closed).
    let std_record = match std_record {
        Some(mut r) => {
            let members = stock_std_audit::archive_members(&work, &out_dir, &lld_out)?;
            let audit = stock_std_audit::unwind_audit(&elf_bytes, &members)?;
            r["archiveMembers"] = stock_std_audit::members_json(&members);
            r["unwindAudit"] = audit;
            Some(r)
        }
        None => None,
    };
    let census = census::census(&elf_bytes, &images)?;
    let rel = |p: &Path| -> String {
        match p.strip_prefix(&out_dir) {
            Ok(r) => r.display().to_string(),
            Err(_) => match p.strip_prefix(&repo_root) {
                Ok(r) => r.display().to_string(),
                Err(_) => p.display().to_string(),
            },
        }
    };
    let mut inputs = Vec::new();
    for p in pre
        .iter()
        .chain(std::iter::once(&main_o).filter(|_| main_rust.is_none()))
        .chain(&native)
        .chain(images.iter().flat_map(|im| im.paths.iter()))
        .chain(main_rust.iter())
        .chain(&libs)
        .chain(&post)
    {
        let mut e = serde_json::json!({"path": rel(p), "sha256": sha256(&std::fs::read(p)?)});
        if let (Some(m), Some(serde_json::Value::Object(extra))) = (e.as_object_mut(), notes.get(p))
        {
            m.extend(extra.clone());
        }
        inputs.push(e);
    }
    let lld_version = version(&lld, "--version")?;
    let mut configs = Vec::with_capacity(images.len());
    for im in &images {
        let mut objects = Vec::with_capacity(im.objects.len());
        for ((o, p), t) in im.objects.iter().zip(&im.paths).zip(&im.trimmed) {
            objects.push(object_json(o, &rel(p), t.as_ref())?);
        }
        configs.push(
            serde_json::json!({"config": im.config.display().to_string(), "objects": objects}),
        );
    }
    let mut manifest = serde_json::json!({
        "tool": "snapshot-link --stock",
        "configs": configs,
        "main": cli.main_c.as_ref().or(cli.main_rust.as_ref()).map(|p| p.display().to_string()),
        "elf": {"name": cli.name, "size": elf_bytes.len(), "sha256": sha256(&elf_bytes)},
        "lld": {
            "version": lld_version,
            "args": args.iter().map(|a| rel(a)).collect::<Vec<_>>(),
            "log": rel(&work.join(LLD_LOG)),
            "map": rel(&work.join(stock_std_audit::LINK_MAP)),
        },
        "zig": version(&zig, "version")?,
        "inputs": inputs,
        "segments": segments_json(&elf_bytes)?,
        "sections": sections_json(&elf_bytes)?,
        "parserCheck": match &parser_check {
            Ok(()) => serde_json::Value::String("ok".into()),
            Err(e) => serde_json::Value::String(format!("{e:#}")),
        },
    });
    // Only when some extern is traced (`--trace-symbol`), so other manifests stay unchanged.
    if !hooked.is_empty() {
        manifest["traceSymbolDefinitions"] = trace_definitions(&lld_log, |p| rel(p));
    }
    // Only when some `--stock-lld-arg` names a file, so other manifests stay unchanged.
    if !lld_arg_files.is_empty() {
        manifest["lld"]["argFiles"] = lld_arg_files
            .iter()
            .map(|(a, p)| {
                Ok(serde_json::json!({
                    "arg": a, "path": rel(p), "sha256": sha256(&std::fs::read(p)?),
                }))
            })
            .collect::<Result<Vec<_>>>()?
            .into();
    }
    // Only with trimmed sysroot objects, so other manifests stay unchanged.
    if !trims.is_empty() {
        manifest["trimmedSysrootObjects"] = serde_json::json!({
            "engineCommit": engine_commit(),
            "hookedExterns": hooked,
            "exemptedAliases": exempt,
        });
        if let (Some(r), Some(m)) = (
            hook_record,
            manifest["trimmedSysrootObjects"].as_object_mut(),
        ) {
            m.extend(r);
        }
    }
    if let (Some(r), Some(m)) = (std_record, manifest.as_object_mut()) {
        m.insert("stdBin".into(), r);
    }
    std::fs::write(
        out_dir.join("stock-link.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;
    std::fs::write(
        out_dir.join("census.json"),
        serde_json::to_string_pretty(&census)? + "\n",
    )?;
    std::fs::write(
        out_dir.join("timing.json"),
        serde_json::to_string_pretty(&serde_json::json!({"lldWallSeconds": link_secs}))? + "\n",
    )?;
    eprintln!(
        "stock link: {} ({} bytes) in {link_secs:.3}s; parser check: {}",
        exe.display(),
        elf_bytes.len(),
        manifest["parserCheck"]
    );
    parser_check.context("the stock-linked ELF violates the trusted loader's constraints")
}

/// The `stock-link.json` entry of object `o`, written to `path`; `trim` is the extractor's
/// provenance line of a trimmed sysroot object.
pub(crate) fn object_json(
    o: &ObjObject,
    path: &str,
    trim: Option<&trimmed::Trimmed>,
) -> Result<serde_json::Value> {
    let Some(t) = trim else {
        return Ok(serde_json::json!({
            "name": o.name, "path": path, "sha256": sha256(&o.elf_bytes), "size": o.elf_bytes.len(),
        }));
    };
    let bytes = trimmed::emit(o)?;
    // The provenance line names the rlib and the member as its first two `quoted` fields.
    let quoted: Vec<&str> = t.provenance.split('`').skip(1).step_by(2).collect();
    Ok(serde_json::json!({
        "name": o.name, "path": path, "sha256": sha256(&bytes), "size": bytes.len(),
        "trimmedFrom": {
            "rlib": quoted.first(),
            "member": quoted.get(1),
            "provenance": t.provenance,
            "roots": t.roots,
            "memberSha256": sha256(&o.elf_bytes),
            "memberSize": o.elf_bytes.len(),
            "keepSetSha256": trimmed::keep_set_digest(o),
            "keepSet": o.sections.iter().map(|s| format!("{}\t{}", s.elf_index, s.name)).collect::<Vec<_>>(),
        },
    }))
}

fn is_archive(p: &Path) -> bool {
    std::fs::read(p).is_ok_and(|b| b.starts_with(b"!<arch>\n"))
}

/// The engine commit `snapshot-link` was built from, or `unknown`.
fn engine_commit() -> String {
    Command::new("git")
        .args(["-C", env!("CARGO_MANIFEST_DIR"), "rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

/// The emitted files of the trimmed sysroot objects of `images`.
fn trimmed_paths(images: &[StockImage]) -> Vec<&Path> {
    images
        .iter()
        .flat_map(|im| im.paths.iter().zip(&im.trimmed))
        .filter(|(_, t)| t.is_some())
        .map(|(p, _)| p.as_path())
        .collect()
}

/// Extra `ld.lld` flags when `images` have trimmed sysroot objects (none otherwise): their
/// defined globals as `--undefined` roots, so the whole keep set is linked, and
/// `--print-gc-sections`, whose report [`trimmed::check_none_collected`] checks.
fn trimmed_link_args(images: &[StockImage]) -> Vec<PathBuf> {
    let trims: Vec<&ObjObject> = images
        .iter()
        .flat_map(|im| im.objects.iter().zip(&im.trimmed))
        .filter(|(_, t)| t.is_some())
        .map(|(o, _)| o)
        .collect();
    if trims.is_empty() {
        return Vec::new();
    }
    let roots: std::collections::BTreeSet<&str> =
        trims.iter().flat_map(|o| trimmed::roots(o)).collect();
    let mut args: Vec<PathBuf> = roots
        .into_iter()
        .map(|s| PathBuf::from(format!("--undefined={s}")))
        .collect();
    args.push("--print-gc-sections".into());
    args
}

/// The files named by the `--stock-lld-arg`s `args` (resolved against `ld.lld`'s working
/// directory `cwd`), with the argument naming each: a whole argument, the value of
/// `--opt=<file>`, `-T<file>`, or the two-token `-T <file>` / `--script <file>` (recorded as
/// `"<flag> <file>"`). Response files (`@<file>`) and library search (`-L`, `-l`,
/// `--library*`) are rejected, since the files they name would not be recorded.
pub(crate) fn lld_arg_files(args: &[String], cwd: &Path) -> Result<Vec<(String, PathBuf)>> {
    let mut out = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        ensure!(
            !a.starts_with('@'),
            "--stock-lld-arg={a}: response files are not supported"
        );
        ensure!(
            !(a.starts_with("-L") || a.starts_with("-l") || a.starts_with("--library")),
            "--stock-lld-arg={a}: library search is not supported (name the file instead)"
        );
        // Two-token forms: the next argument is the file.
        if matches!(a.as_str(), "-T" | "--script" | "-script") {
            let Some(v) = it.next() else {
                bail!("--stock-lld-arg={a} needs a file argument");
            };
            let p = cwd.join(v);
            ensure!(p.is_file(), "--stock-lld-arg={a} {v}: not a file");
            out.push((format!("{a} {v}"), p));
            continue;
        }
        let mut cands = vec![a.as_str()];
        if let Some((_, v)) = a.split_once('=') {
            cands.push(v);
        }
        if let Some(v) = a.strip_prefix("-T").filter(|v| !v.is_empty()) {
            cands.push(v);
        }
        if let Some(p) = cands.into_iter().map(|c| cwd.join(c)).find(|p| p.is_file()) {
            out.push((a.clone(), p));
        }
    }
    Ok(out)
}

/// The `zig cc` side of step 2 of [`run`]: compile the C `main` (`--main-c`, or a trivial one)
/// to `work/main.o`, stage the musl runtime a `zig cc -v` link uses under `work/runtime`, and build a
/// staticlib `--main-rust`. Returns `(startup objects, archives, trailing objects, Rust main)`.
#[allow(clippy::type_complexity)]
fn zig_runtime(
    cli: &Cli,
    repo_root: &Path,
    work: &Path,
    zig: &Path,
    objcopy: &Path,
    tc: &Toolchain,
) -> Result<(Vec<PathBuf>, Vec<PathBuf>, Vec<PathBuf>, Option<PathBuf>)> {
    let main_c = work.join("main.c");
    match &cli.main_c {
        Some(p) => std::fs::copy(repo_root.join(p), &main_c).map(|_| ())?,
        None => std::fs::write(&main_c, "int main(void) {\n  return 0;\n}\n")?,
    }
    let zcc = |c: &mut Command| {
        c.arg("cc")
            .args(["-target", "aarch64-linux-musl", "-O2", "-fno-sanitize=all"])
            .args(["-fno-pie", "-no-pie", "-static"]);
    };
    let mut c = Command::new(zig);
    zcc(&mut c);
    run_cmd(
        c.current_dir(work)
            .args(["-g0", "-c", "main.c", "-o", "main.o"]),
    )?;
    // The runtime inputs come from a `zig cc -v` link of a self-contained `main`.
    std::fs::write(work.join("probe.c"), "int main(void) {\n  return 0;\n}\n")?;
    let probe_o = work.join("probe.o");
    let mut c = Command::new(zig);
    zcc(&mut c);
    run_cmd(
        c.current_dir(work)
            .args(["-g0", "-c", "probe.c", "-o", "probe.o"]),
    )?;
    let mut c = Command::new(zig);
    zcc(&mut c);
    c.arg("-v").arg(&probe_o);
    if cli.main_rust.is_some() {
        c.arg("-lunwind");
    }
    let verbose = run_cmd(c.arg("-o").arg(work.join("probe")))?;
    let (pre, libs, post) = musl_inputs(&verbose, &probe_o)?;
    // Staged (debug-stripped, deterministic archive) copies under `work/runtime`, so that the
    // output does not depend on the zig cache location.
    let stage = work.join("runtime");
    let pre = stage_runtime_inputs(objcopy, &pre, &stage)?;
    let libs = stage_runtime_inputs(objcopy, &libs, &stage)?;
    let post = stage_runtime_inputs(objcopy, &post, &stage)?;
    let main_rust = match &cli.main_rust {
        None => None,
        Some(manifest_rel) => Some(build_rust_main_archive(
            repo_root,
            work,
            objcopy,
            manifest_rel,
            &tc.rustc_version,
        )?),
    };
    Ok((pre, libs, post, main_rust))
}

/// The global (or weak) functions and objects the library objects of `images` define, sorted and
/// deduplicated: the `--gc-sections` roots of `--stock-keep-library`.
fn library_roots(images: &[StockImage]) -> impl Iterator<Item = String> {
    use rust_obj2lean::trusted_common::{SymBind, SymKind, SymSection};
    let mut v: Vec<String> = images
        .iter()
        .flat_map(|im| im.objects.iter())
        .flat_map(|o| o.symbols.iter())
        .filter(|s| {
            matches!(s.sec, SymSection::Sec(_))
                && matches!(s.kind, SymKind::Func | SymKind::Object)
                && !matches!(s.bind, SymBind::Local)
                && !s.raw_name.is_empty()
        })
        .map(|s| s.raw_name.clone())
        .collect();
    v.sort();
    v.dedup();
    v.into_iter()
}

fn segments_json(elf_bytes: &[u8]) -> Result<serde_json::Value> {
    let elf = ElfFile64::<Endianness>::parse(elf_bytes)?;
    let e = elf.endian();
    let phdrs = elf.elf_header().program_headers(e, elf_bytes)?;
    Ok(phdrs
        .iter()
        .map(|p| {
            serde_json::json!({
                "type": format!("{:#x}", p.p_type(e)),
                "flags": p.p_flags(e),
                "offset": format!("{:#x}", p.p_offset(e)),
                "vaddr": format!("{:#x}", p.p_vaddr(e)),
                "filesz": p.p_filesz(e),
                "memsz": p.p_memsz(e),
                "align": format!("{:#x}", p.p_align(e)),
            })
        })
        .collect())
}

fn sections_json(elf_bytes: &[u8]) -> Result<serde_json::Value> {
    let elf = ElfFile64::<Endianness>::parse(elf_bytes)?;
    Ok(elf
        .sections()
        .filter(|s| s.address() != 0)
        .map(|s| {
            serde_json::json!({
                "name": s.name().unwrap_or(""),
                "addr": format!("{:#x}", s.address()),
                "size": s.size(),
            })
        })
        .collect())
}
