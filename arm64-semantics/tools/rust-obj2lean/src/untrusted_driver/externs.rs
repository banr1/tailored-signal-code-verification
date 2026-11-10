// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Undefined external symbol classification (`ExternDecl`) for `.rlib`/C extraction and the
//! `[OUTSIDE TCB]` legacy `LinkedImage` proof-cache exporter (`untrusted_driver::externs`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (`[infra]`). Pre-link `Obj.ExtractedObj` emission
//!   ([`crate::trusted_extractor::extracted_obj`]) and placed-library generation
//!   ([`crate::untrusted_placed`]) operate directly on [`ObjObject`]s without `ExternDecl` records;
//!   `Arm64.Obj.LabelsFromObjects` checks undefined external symbols inside the Lean kernel. This
//!   module synthesizes `ExternDecl` records (`Func` / `Object` / `Tls`, size, alignment, origin)
//!   under the Q1 rule for [`crate::untrusted_driver::extract`], the `[OUTSIDE TCB]` legacy
//!   `LinkedImage` cache ([`crate::untrusted_legacy_linker`]), and `spec-oracle`.
//! - **Key Types & Functions:** [`NeededExtern`], [`RlibDef`], [`needed_externs`],
//!   [`resolve_externs`], [`resolve_externs_with_config`], [`check_extern_collisions`].
//! - **When to Read This File:** Read when inspecting Q1 external symbol classification against
//!   `.rlib` symbol metadata or `[[externs]]` overrides in `translation.toml`.

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Result, bail};
use itertools::Itertools;

use crate::trusted_common::{
    ConfiguredExtern, ExternDecl, ExternKind, ObjObject, SymBind, SymSection,
};
use crate::trusted_extractor::{check_align, is_defined_entity};

/// An undefined symbol that no loaded object defines, with the relocation types referring
/// to it and the `STT_*` kind it has in the referring object(s).
#[derive(Clone, Debug)]
pub struct NeededExtern {
    pub raw_name: String,
    pub name: String,
    pub ref_types: BTreeSet<String>,
    pub all_branch: bool,
    pub any_ldst: bool,
    pub any_tls: bool,
    pub all_tls: bool,
    pub any_branch: bool,
    pub obj_kinds: BTreeSet<String>,
    pub max_access_end: u64,
}

/// Undefined symbols referenced by relocations of extracted sections and not defined as a
/// global in any object, in order of first reference (object, section, relocation).
pub fn needed_externs(objects: &[ObjObject]) -> Result<Vec<NeededExtern>> {
    // Global/weak definitions in extracted sections, by demangled name (what `load` consults).
    let mut globals: BTreeMap<&str, &str> = BTreeMap::new();
    for o in objects {
        for s in &o.symbols {
            if s.bind != SymBind::Local && matches!(s.sec, SymSection::Sec(_)) {
                globals.entry(&s.name).or_insert(&s.raw_name);
            }
        }
    }
    let mut order: Vec<String> = Vec::new();
    let mut needed: BTreeMap<String, NeededExtern> = BTreeMap::new();
    for o in objects {
        for sec in &o.sections {
            for r in &sec.relocs {
                let s = &o.symbols[r.sym];
                if s.sec != SymSection::Undef {
                    continue;
                }
                if r.sym == 0 || s.raw_name.is_empty() {
                    bail!(
                        "{}: relocation in `{}` against the null symbol",
                        o.name,
                        sec.name
                    );
                }
                if let Some(def_raw) = globals.get(s.name.as_str()) {
                    if *def_raw != s.raw_name {
                        bail!(
                            "{}: undefined `{}` resolves by demangled name `{}` to a different symbol `{def_raw}`",
                            o.name,
                            s.raw_name,
                            s.name
                        );
                    }
                    continue;
                }
                let entry = needed.entry(s.raw_name.clone()).or_insert_with(|| {
                    order.push(s.raw_name.clone());
                    NeededExtern {
                        raw_name: s.raw_name.clone(),
                        name: s.name.clone(),
                        ref_types: BTreeSet::new(),
                        all_branch: true,
                        any_ldst: false,
                        any_tls: false,
                        all_tls: true,
                        any_branch: false,
                        obj_kinds: BTreeSet::new(),
                        max_access_end: s.size,
                    }
                });
                entry.ref_types.insert(r.rtype.lean_ctor());
                entry.all_branch &= r.rtype.is_branch();
                entry.any_branch |= r.rtype.is_branch();
                entry.any_ldst |= r.rtype.is_ldst();
                let is_tls = r.rtype.is_tls();
                entry.any_tls |= is_tls;
                entry.all_tls &= is_tls;
                entry.obj_kinds.insert(s.kind.lean_ctor());
                let access_end = (r.addend.max(0) as u64).saturating_add(r.rtype.access_size());
                entry.max_access_end = entry.max_access_end.max(s.size).max(access_end);
            }
        }
    }
    Ok(order
        .into_iter()
        .map(|raw| needed.remove(&raw).expect("recorded above"))
        .collect())
}

/// A global definition of a needed symbol found in an rlib member.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RlibDef {
    pub kind: ExternKind,
    pub size: u64,
    pub align: u64,
    pub origin: String,
}

/// Decide the `ExternDecl` of each needed symbol (see the design's Q1 rule).
pub fn resolve_externs(
    needed: &[NeededExtern],
    defs: &BTreeMap<String, Vec<RlibDef>>,
) -> Result<Vec<ExternDecl>> {
    resolve_externs_with_config(needed, defs, &[])
}

pub fn resolve_externs_with_config(
    needed: &[NeededExtern],
    defs: &BTreeMap<String, Vec<RlibDef>>,
    configured: &[ConfiguredExtern],
) -> Result<Vec<ExternDecl>> {
    let mut out = Vec::with_capacity(needed.len());
    for n in needed {
        let refs = n.ref_types.iter().join(", ");
        if let Some(cfg_ext) = configured
            .iter()
            .find(|c| c.name == n.name || c.name == n.raw_name)
        {
            let ok = match cfg_ext.kind {
                ExternKind::Func => !n.any_ldst && !n.any_tls,
                ExternKind::Object => !n.any_branch && !n.any_tls,
                ExternKind::Tls => n.all_tls,
            };
            if !ok {
                bail!(
                    "undefined symbol `{}` is configured as {} in `[[externs]]` but is referenced by {refs}",
                    n.name,
                    cfg_ext.kind.lean_ctor()
                );
            }
            check_align(cfg_ext.align, &format!("extern `{}`", n.name))?;
            let size = match cfg_ext.size {
                Some(sz) => {
                    if matches!(cfg_ext.kind, ExternKind::Object | ExternKind::Tls)
                        && sz < n.max_access_end
                    {
                        bail!(
                            "undefined symbol `{}` is configured with size {sz} in `[[externs]]`, but relocations access up to byte {} ({refs})",
                            n.name,
                            n.max_access_end
                        );
                    }
                    sz
                }
                None => match cfg_ext.kind {
                    ExternKind::Func => 0,
                    ExternKind::Object | ExternKind::Tls => n.max_access_end.max(8),
                },
            };
            out.push(ExternDecl {
                name: n.name.clone(),
                raw_name: n.raw_name.clone(),
                kind: cfg_ext.kind,
                size,
                align: cfg_ext.align,
                origin: "configured in `[[externs]]`".into(),
            });
            continue;
        }
        let found = defs.get(&n.raw_name).map(Vec::as_slice).unwrap_or(&[]);
        let decl = match found {
            [] => {
                if !n.any_ldst
                    && !n.any_tls
                    && !n.obj_kinds.contains(".object")
                    && !n.obj_kinds.contains(".tls")
                {
                    let origin = if n.all_branch {
                        "no rlib definition; only CALL26/JUMP26 references".into()
                    } else {
                        format!("no rlib definition; function reference ({refs})")
                    };
                    ExternDecl {
                        name: n.name.clone(),
                        raw_name: n.raw_name.clone(),
                        kind: ExternKind::Func,
                        size: 0,
                        align: 1,
                        origin,
                    }
                } else if n.any_tls
                    && n.all_tls
                    && !n.obj_kinds.contains(".func")
                    && !n.obj_kinds.contains(".object")
                {
                    ExternDecl {
                        name: n.name.clone(),
                        raw_name: n.raw_name.clone(),
                        kind: ExternKind::Tls,
                        size: n.max_access_end.max(8),
                        align: 8,
                        origin: format!("no rlib definition; inferred TLS ({refs})"),
                    }
                } else if !n.any_branch
                    && !n.any_tls
                    && !n.obj_kinds.contains(".func")
                    && !n.obj_kinds.contains(".tls")
                {
                    let align = if n.ref_types.contains(".ldst128AbsLo12Nc") {
                        16
                    } else {
                        8
                    };
                    ExternDecl {
                        name: n.name.clone(),
                        raw_name: n.raw_name.clone(),
                        kind: ExternKind::Object,
                        size: n.max_access_end.max(8),
                        align,
                        origin: format!("no rlib definition; inferred object ({refs})"),
                    }
                } else {
                    bail!(
                        "undefined symbol `{}` is defined in no rlib and has incompatible relocation references ({refs})",
                        n.name
                    );
                }
            }
            [first, rest @ ..] => {
                if rest
                    .iter()
                    .any(|d| (d.kind, d.size, d.align) != (first.kind, first.size, first.align))
                {
                    bail!(
                        "undefined symbol `{}` has conflicting definitions: {}",
                        n.name,
                        found
                            .iter()
                            .map(|d| format!(
                                "{} size {} align {} in {}",
                                d.kind.lean_ctor(),
                                d.size,
                                d.align,
                                d.origin
                            ))
                            .join("; ")
                    );
                }
                let ok = match first.kind {
                    ExternKind::Func => !n.any_ldst && !n.any_tls,
                    ExternKind::Object => !n.any_branch && !n.any_tls,
                    ExternKind::Tls => n.all_tls,
                };
                if !ok {
                    bail!(
                        "undefined symbol `{}` is a {} (defined in {}) but is referenced by {refs}",
                        n.name,
                        first.kind.lean_ctor(),
                        first.origin
                    );
                }
                let obj_ok = n.obj_kinds.iter().all(|k| match k.as_str() {
                    ".notype" => true,
                    ".func" => first.kind == ExternKind::Func,
                    ".object" => first.kind == ExternKind::Object,
                    ".tls" => first.kind == ExternKind::Tls,
                    _ => false,
                });
                if !obj_ok {
                    bail!(
                        "undefined symbol `{}` has type {} in the object but is a {} in {}",
                        n.name,
                        n.obj_kinds.iter().join("/"),
                        first.kind.lean_ctor(),
                        first.origin
                    );
                }
                check_align(first.align, &format!("extern `{}`", n.name))?;
                let origin = if rest.is_empty() {
                    first.origin.clone()
                } else {
                    format!("{} (+{} identical)", first.origin, rest.len())
                };
                ExternDecl {
                    name: n.name.clone(),
                    raw_name: n.raw_name.clone(),
                    kind: first.kind,
                    size: first.size,
                    align: first.align,
                    origin,
                }
            }
        };
        out.push(decl);
    }
    Ok(out)
}

/// Fail if an extern's demangled name collides with another extern or a defined symbol.
pub fn check_extern_collisions(objects: &[ObjObject], externs: &[ExternDecl]) -> Result<()> {
    let defined: BTreeSet<&str> = objects
        .iter()
        .flat_map(|o| o.symbols.iter())
        .filter(|s| {
            is_defined_entity(s) || (s.bind != SymBind::Local && matches!(s.sec, SymSection::Sec(_)))
        })
        .map(|s| s.name.as_str())
        .collect();
    let mut seen: BTreeMap<&str, &str> = BTreeMap::new();
    for x in externs {
        if defined.contains(x.name.as_str()) {
            bail!(
                "extern `{}` (`{}`) collides with a defined symbol",
                x.name,
                x.raw_name
            );
        }
        if let Some(prev) = seen.insert(&x.name, &x.raw_name) {
            bail!(
                "externs `{prev}` and `{}` have the same demangled name `{}`",
                x.raw_name,
                x.name
            );
        }
    }
    Ok(())
}
