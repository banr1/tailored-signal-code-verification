// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Export pipeline and CLI dispatch for `rust-obj2lean` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. This module only *sequences* the pipeline and writes files
//!   to disk; it decides nothing about the bytes of the trusted outputs. Placed outputs are
//!   produced by [`crate::untrusted_placed`], while legacy `<ObjName>Obj.lean` outputs (opt-in via
//!   `--legacy-linked-image` / `legacy_linked_image = true`) are produced by
//!   [`crate::untrusted_legacy_linker::emit_obj_lean_module`].
//! - **Purpose:**
//!   1. [`generate_config`] / [`generate_config_with`]: run `untrusted_driver::extract` →
//!      `untrusted_placed::generate` (default `placed_only = true`) or, under `--legacy-linked-image`,
//!      `untrusted_legacy_linker::link` → `emit_obj_lean_module`, the untrusted `Code` module,
//!      per-target lemma modules, `*Index.json`, and DWARF hints.
//!   2. [`write_or_check`]: write a generated file or (`--check`) diff it against the on-disk
//!      copy.
//!   3. [`cli_main`]: `clap` dispatch for `export`, `fetch-decode-lemmas`, `symexec`,
//!      `print-cflags`, and `layout`.
//!
//! # When to Read This File
//! - Read this file when changing CLI subcommands, `--check` diffing, shard-file cleanup, or the
//!   order in which artefacts are generated.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result, bail};
use clap::Parser;
use similar::TextDiff;

use crate::untrusted_driver::{
    self, Cli, CommandName, ExportConfig, Toolchain, apply_module_prefix_override,
    apply_overrides, apply_perturb_layout_override, default_config_paths, load_configs,
    native_cflags_string, resolve_cli_existing_or_repo_path, resolve_cli_output_path,
    select_configs,
};
use crate::{trusted_extractor, untrusted_legacy_linker, untrusted_lemmas};

/// One generated file: its path and contents.
pub struct GeneratedFile {
    pub path: PathBuf,
    pub contents: Vec<u8>,
    /// Whether `contents` is text (diffable in `--check` mode).
    pub text: bool,
}

/// Build all files generated for `cfg`: placed-library files (default `placed_only = true`) or,
/// when `legacy_linked_image` is set, the legacy `Obj` module defining the linked image with its
/// `.code.bin`/`.data.bin` byte files, the `Code` module, and the lemma module of each target.
pub fn generate_config(cfg: &ExportConfig, tc: &mut Toolchain) -> Result<Vec<GeneratedFile>> {
    generate_config_with(cfg, tc, true)
}

std::thread_local! {
    /// Per-thread count of [`untrusted_legacy_linker::link_with_layout`] invocations (used by
    /// parallel unit tests and `RUST_OBJ2LEAN_TRACE_PIPELINE=1` runs to verify `placed_only`
    /// never invokes the legacy static linker).
    static LEGACY_LINKER_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Number of [`untrusted_legacy_linker::link_with_layout`] calls on this thread since startup or
/// [`reset_legacy_linker_calls`].
pub fn legacy_linker_calls() -> usize {
    LEGACY_LINKER_CALLS.with(std::cell::Cell::get)
}

/// Reset the current thread's [`legacy_linker_calls`] counter to `0`.
pub fn reset_legacy_linker_calls() {
    LEGACY_LINKER_CALLS.with(|c| c.set(0));
}

fn push_extracted_obj(
    files: &mut Vec<GeneratedFile>,
    cfg: &ExportConfig,
    ex: &crate::trusted_common::Extraction,
) {
    let ((lean_path, lean_src), (bin_path, bin_bytes)) =
        trusted_extractor::emit_extracted_obj_lean_module(&cfg.obj_meta(), ex);
    files.push(GeneratedFile {
        path: lean_path,
        contents: lean_src.into_bytes(),
        text: true,
    });
    files.push(GeneratedFile {
        path: bin_path,
        contents: bin_bytes,
        text: false,
    });
}

fn emit_placed_and_extracted_files(
    files: &mut Vec<GeneratedFile>,
    cfg: &ExportConfig,
    ex: &crate::trusted_common::Extraction,
) -> Result<()> {
    if cfg.placed.as_ref().is_some_and(|p| p.emit_extracted_obj) {
        push_extracted_obj(files, cfg, ex);
    }
    for (path, contents, text) in crate::untrusted_placed::generate(cfg, &ex.objects)? {
        files.push(GeneratedFile {
            path,
            contents,
            text,
        });
    }
    Ok(())
}

/// [`generate_config`], with the untrusted DWARF hints of `*Index.json` on or off (`with_dwarf`);
/// every other generated file is independent of `with_dwarf`.
pub fn generate_config_with(
    cfg: &ExportConfig,
    tc: &mut Toolchain,
    with_dwarf: bool,
) -> Result<Vec<GeneratedFile>> {
    let placed_only = cfg.placed.as_ref().is_some_and(|p| p.placed_only);
    if !placed_only && !cfg.legacy_linked_image {
        bail!(
            "`{}` does not set `[placed] placed_only = true`, and legacy `Obj.LinkedImage` \
             emission is disabled by default; set `[placed] placed_only = true`, or pass \
             `--legacy-linked-image` (`legacy_linked_image = true` in TOML) to emit deprecated \
             `Arm64.Legacy` linked-image outputs",
            cfg.config_rel
        );
    }
    let ex = untrusted_driver::extract(cfg, tc)?;
    let trace = std::env::var("RUST_OBJ2LEAN_TRACE_PIPELINE").as_deref() == Ok("1");
    let emit_raw = cfg.placed.as_ref().is_some_and(|p| p.emit_extracted_obj);
    if placed_only {
        let mut files = Vec::new();
        emit_placed_and_extracted_files(&mut files, cfg, &ex)?;
        if trace {
            eprintln!(
                "[pipeline] config={} objects={} placed_only=true emit_extracted_obj={} linker_calls={}",
                cfg.config_rel,
                ex.objects.len(),
                emit_raw,
                legacy_linker_calls()
            );
        }
        return Ok(files);
    }
    let layout = if cfg.page_separate_data {
        untrusted_legacy_linker::DataLayout::PageSeparated
    } else {
        untrusted_legacy_linker::DataLayout::Interleaved
    };
    LEGACY_LINKER_CALLS.with(|c| c.set(c.get() + 1));
    let mut li = untrusted_legacy_linker::link_with_layout(
        &ex.objects,
        &ex.externs,
        cfg.perturb_layout_bytes,
        layout,
    )
    .context("cannot link the objects")?;
    if !cfg.layout_generic_relocs {
        for o in &mut li.objects {
            o.reloc_fns.clear();
            o.data_syms.clear();
        }
    }
    // Legacy `[OUTSIDE TCB]`: the `Obj` module and its byte sidecars.
    let ((obj_path, obj_src), (code_path, code_bytes), (data_path, data_bytes)) =
        untrusted_legacy_linker::emit_obj_lean_module(&cfg.obj_meta(), &ex, &li);
    let mut files = vec![
        GeneratedFile {
            path: obj_path,
            contents: obj_src.into_bytes(),
            text: true,
        },
        GeneratedFile {
            path: code_path,
            contents: code_bytes,
            text: false,
        },
        GeneratedFile {
            path: data_path,
            contents: data_bytes,
            text: false,
        },
    ];
    // Untrusted: the canonical program and lemmas (checked by the kernel).
    let funcs = untrusted_lemmas::code::func_ranges(&ex.objects, &li);
    let ft_entries = untrusted_lemmas::index::build_func_table(cfg, &ex.objects, &li);
    let emit_hook_at_off = untrusted_lemmas::code::stub_offsets_unique(&li);
    let (fn_off_lemmas, stub_entries) = untrusted_lemmas::index::compute_symbol_lemma_names(
        &cfg.code_def_name(),
        &ex.objects,
        &li,
        emit_hook_at_off,
    );
    let mut registrations = Vec::new();
    for target in &cfg.targets {
        registrations.extend(untrusted_lemmas::code::register_fn_entry_lines(
            cfg,
            target,
            &li,
            &funcs,
            &ft_entries,
            &fn_off_lemmas,
        )?);
    }
    for (path, contents) in
        untrusted_lemmas::code::render_code_modules(cfg, &ex.objects, &li, &registrations)
    {
        files.push(GeneratedFile {
            path,
            contents: contents.into_bytes(),
            text: true,
        });
    }
    // Untrusted DWARF hints (from a `-g` companion compile; never affects the image).
    let dwarf = if with_dwarf {
        untrusted_lemmas::dwarf::companion::image_dwarf(cfg, &ex.objects)
    } else {
        Default::default()
    };
    for w in &dwarf.warnings {
        eprintln!("warning: DWARF ({}): {w}", cfg.config_rel);
    }
    let mut emitted_code_offs = std::collections::BTreeSet::new();
    let mut emitted_index_paths = std::collections::BTreeSet::new();
    for target in &cfg.targets {
        for (path, contents) in untrusted_lemmas::code::render_target_module(
            cfg,
            target,
            &li,
            &funcs,
            &ft_entries,
            &fn_off_lemmas,
            &mut emitted_code_offs,
        )? {
            files.push(GeneratedFile {
                path,
                contents: contents.into_bytes(),
                text: true,
            });
        }
        let idx_path = untrusted_lemmas::index::target_index_file(target);
        if emitted_index_paths.insert(idx_path.clone()) {
            let mut idx = untrusted_lemmas::index::build_target_index(
                cfg,
                target,
                &ex.objects,
                &li,
                &funcs,
                &ft_entries,
                &fn_off_lemmas,
                &stub_entries,
            )?;
            untrusted_lemmas::dwarf::companion::attach_to_index(&dwarf, &mut idx);
            let mut json = serde_json::to_string_pretty(&idx)?;
            json.push('\n');
            files.push(GeneratedFile {
                path: idx_path,
                contents: json.into_bytes(),
                text: true,
            });
        }
    }
    let code_idx_path = untrusted_lemmas::index::code_index_file(cfg);
    if emitted_index_paths.insert(code_idx_path.clone()) {
        let mut idx = untrusted_lemmas::index::build_combined_code_index(
            cfg,
            &ex.objects,
            &li,
            &funcs,
            &ft_entries,
            &fn_off_lemmas,
            &stub_entries,
        )?;
        untrusted_lemmas::dwarf::companion::attach_to_index(&dwarf, &mut idx);
        let mut json = serde_json::to_string_pretty(&idx)?;
        json.push('\n');
        files.push(GeneratedFile {
            path: code_idx_path,
            contents: json.into_bytes(),
            text: true,
        });
    }
    // Untrusted: the layout-generic placed library, optional ExtractedObj, and placement witness.
    emit_placed_and_extracted_files(&mut files, cfg, &ex)?;
    if let Some(reg_path) = &cfg.registry_facts_file {
        files.push(GeneratedFile {
            path: reg_path.clone(),
            contents: untrusted_lemmas::registry_facts::render_registry_facts_module(
                cfg,
                &ex.objects,
                &li,
            )
            .into_bytes(),
            text: true,
        });
    }
    Ok(files)
}

static NEXT_TMP_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Write `contents` to a temporary file in `path`'s parent directory, then rename it over `path`
/// so any existing hardlink at `path` is unlinked rather than truncated in place.
pub(crate) fn write_atomic(path: &Path, contents: &[u8]) -> Result<()> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent)
        .with_context(|| format!("failed to create {}", parent.display()))?;
    let file_name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("generated");
    let pid = std::process::id();
    let seq = NEXT_TMP_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp_path = parent.join(format!(".{file_name}.tmp.{pid}.{seq}"));
    let _ = fs::remove_file(&tmp_path);
    let write_res = (|| -> std::io::Result<()> {
        use std::io::Write;
        let mut f = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&tmp_path)?;
        f.write_all(contents)
    })();
    if let Err(e) = write_res {
        let _ = fs::remove_file(&tmp_path);
        return Err(e).with_context(|| format!("failed to write {}", tmp_path.display()));
    }
    if let Err(e) = fs::rename(&tmp_path, path) {
        let _ = fs::remove_file(&tmp_path);
        return Err(e).with_context(|| {
            format!(
                "failed to rename {} to {}",
                tmp_path.display(),
                path.display()
            )
        });
    }
    Ok(())
}

/// Write (or, with `check`, compare) `file`. Returns whether it was up to date.
pub(crate) fn write_or_check(
    file: &GeneratedFile,
    display_base: &Path,
    check: bool,
) -> Result<bool> {
    let rel = file
        .path
        .strip_prefix(display_base)
        .unwrap_or(&file.path)
        .display()
        .to_string();
    let existing = fs::read(&file.path).ok();
    let up_to_date = existing.as_deref() == Some(file.contents.as_slice());
    if check {
        if up_to_date {
            println!("[OK] {rel}");
        } else if file.text {
            let old = existing
                .as_deref()
                .map(String::from_utf8_lossy)
                .unwrap_or_default();
            let new = String::from_utf8_lossy(&file.contents);
            let diff = TextDiff::from_lines(old.as_ref(), new.as_ref());
            eprint!(
                "{}",
                diff.unified_diff()
                    .header(&rel, &format!("{rel} (expected)"))
            );
        } else {
            eprintln!("error: {rel} differs from the freshly built object");
        }
        return Ok(up_to_date);
    }
    if up_to_date {
        println!("Up to date {rel}");
    } else {
        write_atomic(&file.path, &file.contents)
            .with_context(|| format!("failed to write {}", file.path.display()))?;
        println!("Exported {rel}");
    }
    Ok(true)
}

fn run(cli: &Cli, check: bool, only: &[String]) -> Result<bool> {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("CARGO_MANIFEST_DIR must be at <repo>/tools/rust-obj2lean")
        .to_path_buf();

    let config_paths: Vec<PathBuf> = if cli.config.is_empty() {
        default_config_paths(&repo_root)
    } else {
        cli.config
            .iter()
            .map(|p| resolve_cli_existing_or_repo_path(&repo_root, p))
            .collect()
    };
    let out_dir = cli
        .out_dir
        .as_deref()
        .map(|d| resolve_cli_output_path(&repo_root, d));
    let output_file = cli
        .output
        .as_deref()
        .map(|f| resolve_cli_output_path(&repo_root, f));

    let configs = load_configs(&config_paths, &repo_root, out_dir.as_deref())?;
    let mut configs = select_configs(configs, only)?;
    apply_overrides(
        &mut configs,
        output_file.as_deref(),
        cli.namespace_prefix.as_deref(),
        cli.sub_namespace.as_deref(),
    )?;
    apply_module_prefix_override(&mut configs, cli.module_prefix.as_deref());
    apply_perturb_layout_override(&mut configs, cli.perturb_layout)?;
    if cli.emit_symbol_unique_lemmas {
        for cfg in &mut configs {
            cfg.emit_symbol_unique_lemmas = true;
        }
    }
    if cli.legacy_linked_image {
        for cfg in &mut configs {
            cfg.legacy_linked_image = true;
        }
    }
    if cli.multi_placed {
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.multi = true;
            }
        }
    }
    if cli.placed_only {
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.placed_only = true;
            }
        }
    }
    if cli.extracted_obj {
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.emit_extracted_obj = true;
            }
        }
    }
    if cli.placed_witness || cli.placed_witness_out.is_some() {
        let out_override = cli
            .placed_witness_out
            .as_deref()
            .map(|f| resolve_cli_output_path(&repo_root, f));
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.emit_placeable_witness = true;
                if let Some(ref f) = out_override {
                    p.witness_file = f.clone();
                }
            }
        }
    }

    // A config whose witnesses import a facts module emitted by another config
    // (`elf_facts_module`) reads that module from disk, so generate it after every config that
    // emits facts modules (stable, so the given order is otherwise kept).
    configs.sort_by_key(|cfg| {
        cfg.placed.as_ref().is_some_and(|p| {
            p.elf_facts_module.is_some()
                || p.extra_witnesses.iter().any(|x| x.elf_facts_module.is_some())
        })
    });
    let mut tc = Toolchain::new(repo_root.clone())?;
    let display_base = out_dir.clone().unwrap_or(repo_root);
    let mut all_ok = true;
    for cfg in &configs {
        let files = generate_config(cfg, &mut tc)
            .with_context(|| format!("cannot export `{}`", cfg.config_rel))?;
        for file in &files {
            all_ok &= write_or_check(file, &display_base, check)?;
        }
        if !check {
            let emitted_paths: std::collections::BTreeSet<&Path> =
                files.iter().map(|f| f.path.as_path()).collect();
            for i in 0..32 {
                let (shard_path, _) = cfg.code_shard_file(i);
                if !emitted_paths.contains(shard_path.as_path()) && shard_path.exists() {
                    let _ = fs::remove_file(&shard_path);
                }
            }
            for target in &cfg.targets {
                for i in 0..32 {
                    let (shard_path, _) = target.shard_file(i);
                    if !emitted_paths.contains(shard_path.as_path()) && shard_path.exists() {
                        let _ = fs::remove_file(&shard_path);
                    }
                }
            }
        }
    }
    Ok(all_ok)
}

/// Top-level CLI entry point (`export`, `fetch-decode-lemmas`, `symexec`, `print-cflags`,
/// `layout`).
pub fn cli_main() -> ExitCode {
    let mut raw_args = std::env::args();
    if let (Some(_bin), Some(sub)) = (raw_args.next(), raw_args.next())
        && (sub == "symexec" || sub == "sym-exec")
    {
        let rest: Vec<String> = raw_args.collect();
        return untrusted_lemmas::symexec::run_symexec_cli(&rest);
    }
    let mut raw_args = std::env::args().skip(1);
    if let Some(sub) = raw_args.next() {
        let rest: Vec<String> = raw_args.collect();
        if sub.as_str() == "layout" {
            return untrusted_lemmas::dwarf::cli::run_layout_cli(&rest);
        }
    }

    let cli = Cli::parse();

    if cli.print_cflags || matches!(cli.command, Some(CommandName::PrintCflags)) {
        println!("{}", native_cflags_string(&[]));
        return ExitCode::SUCCESS;
    }

    let (check, only) = match &cli.command {
        Some(CommandName::PrintCflags) => unreachable!(),
        Some(CommandName::FetchDecodeLemmas {
            check,
            prog,
            base,
            inputs,
        }) => {
            return untrusted_lemmas::run_fetch_decode_lemmas(*check, prog.clone(), base, inputs);
        }
        Some(CommandName::Export { check, only }) => {
            let mut combined = cli.only.clone();
            combined.extend(only.iter().cloned());
            (cli.check || *check, combined)
        }
        None => (cli.check, cli.only.clone()),
    };

    match run(&cli, check, &only) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
    }
}
