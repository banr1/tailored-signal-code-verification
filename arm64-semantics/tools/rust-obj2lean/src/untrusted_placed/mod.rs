// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Placed-library generator (`[OUTSIDE TCB]`).
//!
//! Emits, for a library described by a `translation.toml`:
//! - `<Obj>PlacedObj.lean`: `def <obj>Lib : Arm64.Obj.PlacedLib`, the library's relocatable text
//!   block (all `.text*` input sections in stock `ld.lld` input order), its data objects (one per
//!   data input section, or per `SHF_MERGE` piece) and its exports ([`model`], [`emit`]); with
//!   `[placed] multi = true, placed_shards = N`, the multi-block library's code blocks are split
//!   over sibling `<Obj>PlacedObjShard<k>.lean` modules that `<Obj>PlacedObj.lean` imports. The
//!   multi-block library's code blocks are emitted sorted by their address in the linked ELF
//!   ([`witness::sort_multi_blocks_by_base`]), so the witness's disjointness check is the linear
//!   sorted-chain check rather than the pairwise fallback;
//! - `<Obj>ElfObj.lean`: the SHA-256-pinned bytes of a real ELF linked by stock `ld.lld`
//!   (`<obj>ElfBytes`), independent of the placement ([`emit::render_elf`]);
//! - `<Obj>PlacedWitness.lean`: `def <obj>Placement : Arm64.Obj.Placement` read off that ELF
//!   ([`witness`], [`emit`]) and, with `[placed] linked = true`, the interned form of the library
//!   and placement and the kernel-checked `Obj.PlacedLib.LinkedIn` proof; with `[placed]
//!   chunked_check = true`, that proof is split over sibling `<…>PlacedWitnessShard<suffix>.lean`
//!   modules, one kernel fact each ([`chunked`]);
//! - `<Base>ElfFacts.lean` (linked witnesses only): the parsed ELF, its parse theorem against the
//!   bytes constant and its symbol tables, emitted once per bytes constant and imported by every
//!   linked witness about it ([`facts`]). `[placed] elf_bytes` / `elf_bytes_module` name an
//!   existing bytes constant instead of emitting `<Obj>ElfObj.lean`, and `elf_facts_module`
//!   (on `[placed]` or `[[placed.extra_witnesses]]`) imports a facts module emitted by another
//!   config instead of emitting one.
//!
//! The two `*Obj` modules are data only and have the Spec role: campaign `Spec` modules import
//! them, and the trust guard classes these gitignored build products as Spec, anchored by the
//! tracked ELF and its pinned SHA-256. The witness and facts modules are `Proof` modules.
//!
//! The ELF must be pinned by `[placed] elf_sha256` ([`check_elf_sha`], fail closed); the emitted
//! `file_bytes%` re-checks that SHA-256 when Lean elaborates `<Obj>ElfObj.lean`.
//!
//! Nothing here is trusted: the kernel checks `Arm64.Obj.PlacedLib.LinkedIn` for the emitted
//! library, placement and ELF. [`patch`] mirrors the trusted Lean patch function so that the
//! witness is checked before it is emitted (fail closed).

pub mod chunked;
pub mod emit;
pub mod facts;
pub mod model;
pub mod patch;
pub mod witness;

#[cfg(test)]
mod tests;

use std::path::PathBuf;

use anyhow::{Context, Result, bail};

use crate::trusted_common::ObjObject;
use crate::untrusted_driver::config::{ExportConfig, PlacedConfig};

/// The SHA-256 of `elf` (read from `path`), checked against the `[placed] elf_sha256` pin.
/// Fails closed when the pin is missing or does not match, so the emitted `file_bytes%` is
/// pinned to a reviewed value rather than to whatever file is on disk.
pub fn check_elf_sha(path: &std::path::Path, elf: &[u8], pinned: Option<&str>) -> Result<String> {
    let Some(pinned) = pinned else {
        bail!(
            "[placed] elf = {} needs `elf_sha256` (the pinned SHA-256 of that ELF)",
            path.display()
        );
    };
    let actual = crate::trusted_common::sha256_hex(elf);
    if !pinned.eq_ignore_ascii_case(&actual) {
        bail!(
            "{} has SHA-256 {actual}, but [placed] elf_sha256 pins {pinned}",
            path.display()
        );
    }
    Ok(pinned.to_ascii_lowercase())
}

/// The ELF bytes constant of the primary witness and its defining module: `[placed] elf_bytes` /
/// `elf_bytes_module`, or `<obj>ElfBytes` in the emitted `<ObjName>ElfObj.lean`.
fn primary_elf_bytes(cfg: &ExportConfig, p: &PlacedConfig) -> (String, String) {
    match &p.elf_bytes_override {
        Some((bytes, module)) => (bytes.clone(), module.clone()),
        None => (emit::LibNames::new(&cfg.obj_name).elf_bytes, p.elf_module.clone()),
    }
}

/// The names of the primary witness (about [`primary_elf_bytes`]).
fn primary_names(cfg: &ExportConfig, p: &PlacedConfig) -> emit::WitNames {
    let mut wn = emit::WitNames::primary(&cfg.obj_name);
    wn.elf_bytes = primary_elf_bytes(cfg, p).0;
    wn
}

/// The facts modules of `cfg`'s linked witnesses: the primary one (ELF SHA-256 `primary_sha`,
/// when it is linked), then every extra witness, in that order ([`facts::plan`]).
fn facts_plan(
    cfg: &ExportConfig,
    p: &PlacedConfig,
    primary_sha: Option<&str>,
) -> Result<facts::FactsPlan> {
    let mut uses = Vec::new();
    if let (Some(elf), Some(sha), true) = (&p.elf, primary_sha, p.linked) {
        let (elf_bytes, elf_bytes_module) = primary_elf_bytes(cfg, p);
        uses.push(facts::ElfUse {
            elf: elf.clone(),
            elf_sha256: sha.to_string(),
            elf_bytes,
            elf_bytes_module,
            namespace: cfg.namespace_prefix.clone(),
            facts_module: p.elf_facts_module.clone(),
        });
    }
    for x in &p.extra_witnesses {
        uses.push(facts::ElfUse {
            elf: x.elf.clone(),
            elf_sha256: x.elf_sha256.clone(),
            elf_bytes: x.elf_bytes.clone(),
            elf_bytes_module: x.elf_bytes_module.clone(),
            namespace: x.namespace.clone().unwrap_or_else(|| cfg.namespace_prefix.clone()),
            facts_module: x.elf_facts_module.clone(),
        });
    }
    facts::plan(p, &uses)
}

/// Appends the facts modules of `plan` to `out`.
fn push_facts(
    out: &mut Vec<(PathBuf, Vec<u8>, bool)>,
    plan: &facts::FactsPlan,
    license: &[String],
) {
    for m in &plan.emit {
        let (path, lean) = facts::facts_output(m, license);
        out.push((path, lean.into_bytes(), true));
    }
}

/// Push a witness and its shard modules (`<stem>Shard<suffix>.lean`, next to
/// `witness_file`) to `out`.
fn push_multi_witness(
    out: &mut Vec<(PathBuf, Vec<u8>, bool)>,
    witness_file: &std::path::Path,
    files: emit::MultiWitnessFiles,
) {
    let stem = witness_file
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_default()
        .to_string();
    for (suffix, lean) in files.shards {
        let path = witness_file.with_file_name(format!("{stem}Shard{suffix}.lean"));
        out.push((path, lean.into_bytes(), true));
    }
    out.push((witness_file.to_path_buf(), files.main.into_bytes(), true));
}

/// The placed-library outputs of `cfg` (empty without a `[placed]` table):
/// `(path, contents, is_text)`.
pub fn generate(cfg: &ExportConfig, objs: &[ObjObject]) -> Result<Vec<(PathBuf, Vec<u8>, bool)>> {
    let Some(p) = &cfg.placed else {
        return Ok(vec![]);
    };
    if p.multi {
        let (mut mlib, boundary) =
            model::build_multi_placed_lib_bounded(&cfg.obj_name, objs, &p.exports, &p.extern_boundary)
                .with_context(|| format!("cannot build the multi-placed library of {}", cfg.obj_name))?;
        let witness = match &p.elf {
            Some(elf_path) => {
                let elf = std::fs::read(elf_path)
                    .with_context(|| format!("cannot read {}", elf_path.display()))?;
                let sha = check_elf_sha(elf_path, &elf, p.elf_sha256.as_deref())?;
                let mut mpl = witness::extract_multi(&mlib, &elf).with_context(|| {
                    format!("cannot place {} in {}", cfg.obj_name, elf_path.display())
                })?;
                // Blocks in address order let the kernel check disjointness linearly. Re-extract
                // (and so re-check) the placement under the new block order, failing closed.
                if witness::sort_multi_blocks_by_base(&mut mlib, &mut mpl) {
                    let sorted = witness::extract_multi(&mlib, &elf).with_context(|| {
                        format!(
                            "cannot place {} in {} after sorting blocks by address",
                            cfg.obj_name,
                            elf_path.display()
                        )
                    })?;
                    anyhow::ensure!(
                        sorted.bases == mpl.bases,
                        "re-extracted block bases of {} differ after sorting",
                        cfg.obj_name
                    );
                    mpl = sorted;
                }
                if !boundary.is_empty() {
                    witness::check_extern_boundary(&boundary, &mpl, &witness::Elf::parse(&elf)?)
                        .with_context(|| format!("in {}", elf_path.display()))?;
                }
                mlib.data.sort_by_key(|d| mpl.rho(&d.sym));
                Some((elf_path, sha, mpl))
            }
            None => None,
        };
        let bin_file = p.lib_file.with_extension("bin");
        let bin_name = bin_file
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        let shard_modules: Vec<String> = if p.placed_shards > 1 {
            (0..p.placed_shards).map(|k| p.shard_module(k)).collect()
        } else {
            vec![]
        };
        let (lean, shards) = emit::render_multi_lib_sharded(
            &mlib,
            &cfg.obj_name,
            &cfg.namespace_prefix,
            &bin_name,
            &cfg.license_header,
            &shard_modules,
        );
        let mut out = vec![
            (p.lib_file.clone(), lean.into_bytes(), true),
            (bin_file, emit::sidecar_multi_bytes(&mlib), false),
        ];
        for (path, lean) in p.shard_files().into_iter().zip(shards) {
            out.push((path, lean.into_bytes(), true));
        }
        let plan = facts_plan(cfg, p, witness.as_ref().map(|(_, sha, _)| sha.as_str()))?;
        push_facts(&mut out, &plan, &cfg.license_header);
        let mut per_use = plan.per_use.into_iter();
        if let Some((elf_path, sha, mpl)) = witness {
            let wit_dir = p
                .witness_file
                .parent()
                .unwrap_or_else(|| std::path::Path::new(""));
            let elf_dir = p
                .elf_file
                .parent()
                .unwrap_or_else(|| std::path::Path::new(""));
            if p.elf_bytes_override.is_none() {
                let lean = emit::render_elf_named(
                    &mlib.name,
                    &cfg.obj_name,
                    &cfg.namespace_prefix,
                    &emit::relative_path(elf_dir, elf_path),
                    &sha,
                    &cfg.license_header,
                );
                out.push((p.elf_file.clone(), lean.into_bytes(), true));
            }
            let mut names = primary_names(cfg, p);
            if p.linked {
                names.facts = per_use.next();
                let elf = std::fs::read(elf_path)
                    .with_context(|| format!("cannot read {}", elf_path.display()))?;
                names.extern_symtab = Some(witness::extern_symtab_split(
                    &mlib,
                    &mpl,
                    &witness::Elf::parse(&elf)?,
                ));
                names.split_check = p.split_check_module.clone();
            }
            let files = emit::render_multi_witness_files(
                &mlib,
                &mpl,
                &names,
                &cfg.namespace_prefix,
                &p.witness_module,
                &p.lib_module,
                &primary_elf_bytes(cfg, p).1,
                &emit::relative_path(wit_dir, elf_path),
                p.linked,
                &cfg.license_header,
            );
            push_multi_witness(&mut out, &p.witness_file, files);
        }
        for x in &p.extra_witnesses {
            let elf = std::fs::read(&x.elf)
                .with_context(|| format!("cannot read {}", x.elf.display()))?;
            check_elf_sha(&x.elf, &elf, Some(&x.elf_sha256))?;
            let mpl = witness::extract_multi(&mlib, &elf).with_context(|| {
                format!("cannot place {} in {}", cfg.obj_name, x.elf.display())
            })?;
            if !boundary.is_empty() {
                witness::check_extern_boundary(&boundary, &mpl, &witness::Elf::parse(&elf)?)
                    .with_context(|| format!("in {}", x.elf.display()))?;
            }
            let wit_dir = x
                .witness_file
                .parent()
                .unwrap_or_else(|| std::path::Path::new(""));
            let mut names = emit::WitNames::extra(&cfg.obj_name, &x.prefix, &x.elf_bytes);
            names.facts = per_use.next();
            names.extern_symtab = Some(witness::extern_symtab_split(
                &mlib,
                &mpl,
                &witness::Elf::parse(&elf)?,
            ));
            names.split_check = p.split_check_module.clone();
            let ns = x.namespace.as_deref().unwrap_or(&cfg.namespace_prefix);
            let files = emit::render_multi_witness_files(
                &mlib,
                &mpl,
                &names,
                ns,
                &x.witness_module,
                &p.lib_module,
                &x.elf_bytes_module,
                &emit::relative_path(wit_dir, &x.elf),
                true,
                &cfg.license_header,
            );
            push_multi_witness(&mut out, &x.witness_file, files);
        }
        return Ok(out);
    }
    let mut lib = model::build_placed_lib(&cfg.obj_name, objs, &p.exports)
        .with_context(|| format!("cannot build the placed library of {}", cfg.obj_name))?;
    // With a witness ELF, list data objects in address order (the order is semantically
    // irrelevant; the kernel checker walks ELF segments fastest in address order).
    // Without an ELF, the ELF-free placement witness keeps the data objects in object-file order,
    // so enabling it does not change the emitted library (`natNodupFast` falls back to the
    // quadratic `natNodup` check when the interned symbols are not sorted).
    let (witness, synth_witness) = match &p.elf {
        Some(elf_path) => {
            let elf = std::fs::read(elf_path)
                .with_context(|| format!("cannot read {}", elf_path.display()))?;
            let sha = check_elf_sha(elf_path, &elf, p.elf_sha256.as_deref())?;
            let pl = witness::extract(&lib, &elf).with_context(|| {
                format!("cannot place {} in {}", cfg.obj_name, elf_path.display())
            })?;
            lib.data.sort_by_key(|d| pl.rho(&d.sym));
            (Some((elf_path, sha, pl)), None)
        }
        None if p.emit_placeable_witness => {
            let pl = witness::synthesize_placement(&lib)
                .with_context(|| format!("cannot synthesize placement for {}", cfg.obj_name))?;
            (None, Some(pl))
        }
        None => (None, None),
    };
    let bin_file = p.lib_file.with_extension("bin");
    let bin_name = bin_file
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .into_owned();
    let lean = emit::render_lib(
        &lib,
        &cfg.obj_name,
        &cfg.namespace_prefix,
        &bin_name,
        &cfg.license_header,
        p.noncomputable_code,
    );
    let mut out = vec![
        (p.lib_file.clone(), lean.into_bytes(), true),
        (bin_file, emit::sidecar_bytes(&lib), false),
    ];
    let plan = facts_plan(cfg, p, witness.as_ref().map(|(_, sha, _)| sha.as_str()))?;
    push_facts(&mut out, &plan, &cfg.license_header);
    let mut per_use = plan.per_use.into_iter();
    if let Some((elf_path, sha, pl)) = witness {
        let wit_dir = p
            .witness_file
            .parent()
            .unwrap_or_else(|| std::path::Path::new(""));
        let elf_dir = p
            .elf_file
            .parent()
            .unwrap_or_else(|| std::path::Path::new(""));
        if p.elf_bytes_override.is_none() {
            let lean = emit::render_elf(
                &lib,
                &cfg.obj_name,
                &cfg.namespace_prefix,
                &emit::relative_path(elf_dir, elf_path),
                &sha,
                &cfg.license_header,
            );
            out.push((p.elf_file.clone(), lean.into_bytes(), true));
        }
        let mut names = primary_names(cfg, p);
        if p.linked {
            names.facts = per_use.next();
            names.chunked = p.chunked_check;
        }
        let files = emit::render_witness_files(
            &lib,
            &pl,
            &names,
            &cfg.namespace_prefix,
            &p.witness_module,
            &p.lib_module,
            &primary_elf_bytes(cfg, p).1,
            &emit::relative_path(wit_dir, elf_path),
            p.linked,
            &cfg.license_header,
        );
        push_multi_witness(&mut out, &p.witness_file, files);
    } else if let Some(pl) = synth_witness {
        let lean = emit::render_placeable_witness(
            &lib,
            &pl,
            &emit::WitNames::primary(&cfg.obj_name),
            &cfg.namespace_prefix,
            &p.lib_module,
            &cfg.license_header,
        );
        out.push((p.witness_file.clone(), lean.into_bytes(), true));
    }
    // Extra witnesses: after the data order is fixed, so each interned library is `<obj>Lib`.
    for x in &p.extra_witnesses {
        let elf = std::fs::read(&x.elf).with_context(|| format!("cannot read {}", x.elf.display()))?;
        check_elf_sha(&x.elf, &elf, Some(&x.elf_sha256))?;
        let pl = witness::extract(&lib, &elf).with_context(|| {
            format!("cannot place {} in {}", cfg.obj_name, x.elf.display())
        })?;
        let wit_dir = x
            .witness_file
            .parent()
            .unwrap_or_else(|| std::path::Path::new(""));
        let mut names = emit::WitNames::extra(&cfg.obj_name, &x.prefix, &x.elf_bytes);
        names.facts = per_use.next();
        names.chunked = p.chunked_check;
        names.lib_ns = Some(cfg.namespace_prefix.clone());
        let ns = x.namespace.as_deref().unwrap_or(&cfg.namespace_prefix);
        let files = emit::render_witness_files(
            &lib,
            &pl,
            &names,
            ns,
            &x.witness_module,
            &p.lib_module,
            &x.elf_bytes_module,
            &emit::relative_path(wit_dir, &x.elf),
            true,
            &cfg.license_header,
        );
        push_multi_witness(&mut out, &x.witness_file, files);
    }
    Ok(out)
}
