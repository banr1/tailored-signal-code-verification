// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Resolution of the hooked externs of a `--stock` link with trimmed sysroot objects
//! (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. Checks which object of the link defines each hooked extern
//!   (an extern of an image with a trimmed `[[sysroot_objects]]` entry), and records it in
//!   `stock-link.json`; proofs check the executable against its pinned bytes.
//! - **Purpose:** before the link, [`plan`]:
//!   - rejects every archive on the link line (other than the C runtime) that defines a hooked
//!     extern, except an `STB_WEAK` archive definition of a name some stub object defines
//!     `STB_GLOBAL` (a global definition in an object always wins over a weak one, so the archive
//!     definition is shadowed; recorded as `weakArchiveShadowed`). A weak stub never shadows.
//!   - allows a sibling `--config` image to define a hooked extern only if the defining symbol is
//!     one of that image's declared exports (`[placed] exports` or `[[sysroot_objects]] roots`,
//!     raw or demangled names, each resolved to exactly one defined symbol of the image) and the
//!     image does not itself list the name as an extern (recorded as `siblingDefinedExterns`).
//!
//!   After the link, [`check`] reads the `ld.lld --trace-symbol` output:
//!   - each hooked extern has exactly one `definition of` line (a positive control: a change in
//!     the trace format cannot make the checks pass vacuously);
//!   - that definition is in a stub object, the C runtime, or the allowed sibling object;
//!   - a sibling-defined extern's executable address is the sibling's placed export address:
//!     the `-Map` address of the sibling object's defining input section plus the symbol's offset.
//!
//!   [`check_lld_args`] rejects `--stock-lld-arg`s that allow multiple definitions.
//!
//! # When to Read This File
//! - Read this file for `trimmedSysrootObjects.weakArchiveShadowed` and
//!   `trimmedSysrootObjects.siblingDefinedExterns` in `stock-link.json`.

use crate::stock::StockImage;
use crate::stock_std_audit::{MAP_COLS, MAP_HEADER};
use anyhow::{Context, Result, bail, ensure};
use object::read::archive::ArchiveFile;
use object::{Object, ObjectSection, ObjectSymbol, SymbolSection};
use rust_obj2lean::trusted_common::{SymBind, SymSection};
use rust_obj2lean::trusted_extractor::demangle_rust_symbol;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// An archive member's `STB_WEAK` definition of a hooked extern that a stub object defines
/// `STB_GLOBAL`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeakShadow {
    pub symbol: String,
    /// `<archive>(<member>)`.
    pub archive_member: String,
}

/// A hooked extern of one image defined by an export of a sibling image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SiblingDef {
    /// Raw `.symtab` name.
    pub symbol: String,
    /// The declared export it resolves from.
    pub export: String,
    /// The config listing it as an extern, and the sibling config defining it.
    pub hooked_by: PathBuf,
    pub image: PathBuf,
    /// The sibling's object file defining it.
    pub object: PathBuf,
}

/// The pre-link result of [`plan`].
#[derive(Debug, Default)]
pub struct HookPlan {
    pub hooked: BTreeSet<String>,
    pub weak_shadowed: Vec<WeakShadow>,
    pub siblings: Vec<SiblingDef>,
}

/// The names in `names` that one of the objects `stubs` defines as `STB_GLOBAL` (not weak).
/// Files that are not objects (e.g. linker scripts) define nothing here.
pub fn strong_definitions(stubs: &[&Path], names: &BTreeSet<String>) -> Result<BTreeSet<String>> {
    let mut out = BTreeSet::new();
    for p in stubs {
        let data = std::fs::read(p).with_context(|| format!("cannot read {}", p.display()))?;
        let Ok(obj) = object::File::parse(&*data) else {
            continue;
        };
        for s in obj.symbols() {
            if let Ok(n) = s.name()
                && s.is_definition()
                && s.is_global()
                && !s.is_weak()
                && names.contains(n)
            {
                out.insert(n.to_string());
            }
        }
    }
    Ok(out)
}

/// The definitions of names in `names` by members of `archives`, as
/// `(name, "<archive>(<member>)", weak)`, sorted and deduplicated.
pub fn archive_definitions(
    archives: &[&Path],
    names: &BTreeSet<String>,
) -> Result<Vec<(String, String, bool)>> {
    let mut out = Vec::new();
    for a in archives {
        let data = std::fs::read(a)?;
        let ar = ArchiveFile::parse(&*data)
            .map_err(|e| anyhow::anyhow!("{}: not an archive: {e}", a.display()))?;
        for m in ar.members() {
            let m = m.map_err(|e| anyhow::anyhow!("{}: {e}", a.display()))?;
            let Ok(obj) = object::File::parse(m.data(&*data)?) else {
                continue;
            };
            for s in obj.symbols() {
                if let Ok(n) = s.name()
                    && s.is_definition()
                    && s.is_global()
                    && names.contains(n)
                {
                    let member = String::from_utf8_lossy(m.name());
                    out.push((
                        n.to_string(),
                        format!("{}({member})", a.display()),
                        s.is_weak(),
                    ));
                }
            }
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

/// Split `defs` ([`archive_definitions`]) into the weak definitions shadowed by a name in
/// `strong` and the rejected rest (as `<archive>(<member>): <name>` lines).
pub fn classify_archive_definitions(
    defs: &[(String, String, bool)],
    strong: &BTreeSet<String>,
) -> (Vec<WeakShadow>, Vec<String>) {
    let mut shadowed = Vec::new();
    let mut rejected = Vec::new();
    for (n, am, weak) in defs {
        if *weak && strong.contains(n) {
            shadowed.push(WeakShadow {
                symbol: n.clone(),
                archive_member: am.clone(),
            });
        } else {
            let bind = if *weak { "weak" } else { "global" };
            rejected.push(format!("{am}: {n} ({bind})"));
        }
    }
    (shadowed, rejected)
}

/// The declared exports of `im` (`[placed] exports` and `[[sysroot_objects]] roots`), each
/// resolved to the raw name of the unique non-local symbol defined in `im`'s objects whose raw or
/// demangled name it is: raw name to export. Fails on an export defined 0 or ≥ 2 times.
pub fn resolve_exports(im: &StockImage) -> Result<BTreeMap<String, String>> {
    let mut out = BTreeMap::new();
    for e in &im.exports {
        let raws: BTreeSet<&str> = im
            .objects
            .iter()
            .flat_map(|o| o.symbols.iter())
            .filter(|s| {
                matches!(s.sec, SymSection::Sec(_))
                    && !matches!(s.bind, SymBind::Local)
                    && !s.raw_name.is_empty()
                    && (s.raw_name == *e || s.name == *e || demangle_rust_symbol(&s.raw_name) == *e)
            })
            .map(|s| s.raw_name.as_str())
            .collect();
        let [raw] = raws.into_iter().collect::<Vec<_>>()[..] else {
            bail!(
                "{}: declared export `{e}` does not resolve to exactly one defined symbol",
                im.config.display()
            );
        };
        out.insert(raw.to_string(), e.clone());
    }
    Ok(out)
}

/// The pre-link checks: `stubs` are the objects allowed to define hooked externs, `archives` the
/// non-runtime archives on the link line. Fails on a rejected archive definition or a sibling
/// definition that is not a declared export.
pub fn plan(images: &[StockImage], stubs: &[&Path], archives: &[&Path]) -> Result<HookPlan> {
    let hooked = hooked_externs(images);
    if hooked.is_empty() {
        return Ok(HookPlan::default());
    }
    let strong = strong_definitions(stubs, &hooked)?;
    let defs = archive_definitions(archives, &hooked)?;
    let (weak_shadowed, rejected) = classify_archive_definitions(&defs, &strong);
    ensure!(
        rejected.is_empty(),
        "archives on the link line define hooked externs, which could be fetched instead of \
         the stubs (only a weak archive definition of a name a stub object defines globally is \
         allowed):\n  {}",
        rejected.join("\n  ")
    );
    Ok(HookPlan {
        hooked,
        weak_shadowed,
        siblings: sibling_definitions(images)?,
    })
}

/// The raw names of the hooked externs: the externs of the images with trimmed sysroot objects.
pub fn hooked_externs(images: &[StockImage]) -> BTreeSet<String> {
    images
        .iter()
        .filter(|im| im.trimmed.iter().any(Option::is_some))
        .flat_map(|im| im.externs.iter().map(|e| e.raw_name.clone()))
        .collect()
}

/// For each hooked extern of each image with trims, the sibling image object defining it (none
/// for a name no sibling defines). Fails unless every such definition is a declared export of a
/// sibling that does not list the name as an extern, and is unique.
pub fn sibling_definitions(images: &[StockImage]) -> Result<Vec<SiblingDef>> {
    let mut out: Vec<SiblingDef> = Vec::new();
    let mut resolved: BTreeMap<usize, BTreeMap<String, String>> = BTreeMap::new();
    for (a, im) in images.iter().enumerate() {
        if !im.trimmed.iter().any(Option::is_some) {
            continue;
        }
        for name in im.externs.iter().map(|e| &e.raw_name) {
            let mut found = Vec::new();
            for (b, sib) in images.iter().enumerate() {
                if b == a {
                    continue;
                }
                for (o, p) in sib.objects.iter().zip(&sib.paths) {
                    let defines = o.symbols.iter().any(|s| {
                        s.raw_name == *name
                            && matches!(s.sec, SymSection::Sec(_))
                            && !matches!(s.bind, SymBind::Local)
                    });
                    if defines {
                        found.push((b, p));
                    }
                }
            }
            let [(b, p)] = found[..] else {
                ensure!(
                    found.is_empty(),
                    "hooked extern `{name}` of {} is defined by several sibling objects: {:?}",
                    im.config.display(),
                    found.iter().map(|(_, p)| p).collect::<Vec<_>>()
                );
                continue;
            };
            let sib = &images[b];
            ensure!(
                !sib.externs.iter().any(|e| e.raw_name == *name),
                "hooked extern `{name}` of {}: sibling {} both defines it and lists it as an extern",
                im.config.display(),
                sib.config.display()
            );
            let exports = match resolved.entry(b) {
                std::collections::btree_map::Entry::Occupied(e) => e.into_mut(),
                std::collections::btree_map::Entry::Vacant(e) => e.insert(resolve_exports(sib)?),
            };
            let Some(export) = exports.get(name) else {
                bail!(
                    "hooked extern `{name}` of {} is defined by sibling {} ({}), which does not \
                     declare it as an export ([placed] exports or [[sysroot_objects]] roots)",
                    im.config.display(),
                    sib.config.display(),
                    p.display()
                );
            };
            if !out.iter().any(|s| s.symbol == *name) {
                out.push(SiblingDef {
                    symbol: name.clone(),
                    export: export.clone(),
                    hooked_by: im.config.clone(),
                    image: sib.config.clone(),
                    object: p.clone(),
                });
            }
        }
    }
    out.sort_by(|x, y| x.symbol.cmp(&y.symbol));
    Ok(out)
}

/// Rejects `--stock-lld-arg`s that let `ld.lld` accept multiple definitions of a symbol
/// (`--allow-multiple-definition`, `-z muldefs`), which would defeat the single-definer checks.
pub fn check_lld_args(args: &[String]) -> Result<()> {
    let mut prev_z = false;
    for a in args {
        let a = a.as_str();
        let bad = matches!(
            a.trim_start_matches('-'),
            "allow-multiple-definition" | "zmuldefs"
        ) || (prev_z && a == "muldefs")
            || a == "-z=muldefs";
        ensure!(
            !bad,
            "--stock-lld-arg={a}: allowing multiple definitions is not supported"
        );
        prev_z = a == "-z";
    }
    Ok(())
}

/// The post-link checks of `plan` against the `ld.lld` output `lld_out`, the executable `exe` and
/// its `-Map` text `map` (required with sibling definitions). Returns the `stock-link.json`
/// fields, with each sibling-defined extern's address.
pub fn check(
    plan: &HookPlan,
    lld_out: &str,
    stubs: &[&Path],
    runtime_archives: &[&Path],
    exe: &[u8],
    map: Option<&str>,
) -> Result<serde_json::Map<String, serde_json::Value>> {
    let defs: Vec<(&str, &str)> = lld_out
        .lines()
        .filter_map(|l| l.trim().split_once(": definition of "))
        .collect();
    let miscounted: Vec<String> = plan
        .hooked
        .iter()
        .filter_map(|n| {
            let k = defs.iter().filter(|(_, s)| s == n).count();
            (k != 1).then(|| format!("{n}: {k} definitions"))
        })
        .collect();
    ensure!(
        miscounted.is_empty(),
        "each hooked extern must have exactly one `definition of` line in the ld.lld \
         --trace-symbol output:\n  {}",
        miscounted.join("\n  ")
    );
    let allowed_sibling = |file: &str, sym: &str| {
        plan.siblings
            .iter()
            .any(|s| s.symbol == sym && file == s.object.display().to_string())
    };
    let bad: Vec<String> = crate::trimmed::disallowed_definers(lld_out, stubs, runtime_archives)
        .into_iter()
        .filter(|l| {
            !defs
                .iter()
                .any(|(f, s)| *l == format!("{f}: {s}") && allowed_sibling(f, s))
        })
        .collect();
    ensure!(
        bad.is_empty(),
        "hooked externs resolve to neither a stub nor the C runtime:\n  {}",
        bad.join("\n  ")
    );
    let mut siblings = Vec::new();
    for s in &plan.siblings {
        let obj = s.object.display().to_string();
        ensure!(
            defs.iter().any(|(f, n)| *n == s.symbol && *f == obj),
            "hooked extern `{}` is not defined by its sibling export object {obj}",
            s.symbol
        );
        let map = map.context("sibling-defined hooked externs need the link map")?;
        let placed = placed_address(map, &s.object, &s.symbol)?;
        let addr = elf_address(exe, &s.symbol)?;
        ensure!(
            addr == placed,
            "hooked extern `{}`: executable address {addr:#x} is not the placed address \
             {placed:#x} of the export `{}` of {}",
            s.symbol,
            s.export,
            s.image.display()
        );
        siblings.push(serde_json::json!({
            "symbol": s.symbol,
            "export": s.export,
            "hookedBy": s.hooked_by.display().to_string(),
            "image": s.image.display().to_string(),
            "object": s.object.file_name().map(|f| f.to_string_lossy().into_owned()),
            "address": format!("{addr:#x}"),
        }));
    }
    let mut out = serde_json::Map::new();
    out.insert(
        "weakArchiveShadowed".into(),
        plan.weak_shadowed
            .iter()
            .map(|w| {
                serde_json::json!({
                    "symbol": w.symbol,
                    "archiveMember": Path::new(&w.archive_member)
                        .file_name()
                        .map(|f| f.to_string_lossy().into_owned()),
                })
            })
            .collect(),
    );
    out.insert("siblingDefinedExterns".into(), siblings.into());
    Ok(out)
}

/// The address of the unique defined symbol `name` of the executable `exe`.
pub fn elf_address(exe: &[u8], name: &str) -> Result<u64> {
    let f = object::File::parse(exe)?;
    let addrs: Vec<u64> = f
        .symbols()
        .filter(|s| s.name() == Ok(name) && s.is_definition())
        .map(|s| s.address())
        .collect();
    let [a] = addrs[..] else {
        bail!(
            "the executable defines `{name}` {} times, not once",
            addrs.len()
        );
    };
    Ok(a)
}

/// The placed address of `name` defined in the object `obj`: the `-Map` address of the input
/// section `obj:(<section>)` holding it (unique in `obj` and in the map) plus its offset.
pub fn placed_address(map: &str, obj: &Path, name: &str) -> Result<u64> {
    let data = std::fs::read(obj).with_context(|| format!("cannot read {}", obj.display()))?;
    let f = object::File::parse(&*data)?;
    let syms: Vec<_> = f
        .symbols()
        .filter(|s| s.name() == Ok(name) && s.is_definition() && s.is_global())
        .collect();
    let [s] = &syms[..] else {
        bail!("{}: `{name}` is not defined exactly once", obj.display());
    };
    let SymbolSection::Section(si) = s.section() else {
        bail!("{}: `{name}` is not in a section", obj.display());
    };
    let sec = f.section_by_index(si)?.name()?.to_string();
    ensure!(
        f.sections()
            .filter(|x| x.name() == Ok(sec.as_str()))
            .count()
            == 1,
        "{}: section {sec} of `{name}` is not unique",
        obj.display()
    );
    let mut lines = map.lines();
    ensure!(
        lines.next() == Some(MAP_HEADER),
        "link map: unrecognized header (expected {MAP_HEADER:?})"
    );
    let want = format!("{}:({sec})", obj.display());
    let vmas: Vec<u64> = lines
        .filter_map(|l| {
            let (cols, rest) = l.split_at_checked(MAP_COLS)?;
            let item = rest.strip_prefix("        ")?;
            (item == want).then(|| u64::from_str_radix(cols.split_whitespace().next()?, 16).ok())?
        })
        .collect();
    let [vma] = vmas[..] else {
        bail!(
            "link map: {} input-section lines for {want}, not one",
            vmas.len()
        );
    };
    Ok(vma + s.address())
}
