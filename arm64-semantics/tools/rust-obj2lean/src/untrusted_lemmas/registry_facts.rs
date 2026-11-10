// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Untrusted `.rodata` / `.data.rel.ro` Function-Pointer Registry Fact Emitter — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (every emitted theorem is checked directly by Lean's kernel
//!   via `rodataPtr_eq_fnAddr_of_loads himg (by rfl_kernel)` against the trusted `LinkedImage`).
//! - **Purpose:** Inspects `R_AARCH64_ABS64` relocations inside `.rodata` / `.data.rel.ro`
//!   sections (`SecKind::Rodata`) and emits `<ObjName>RegistryFacts.lean` containing one lemma per
//!   relocated function pointer slot:
//!   `rodataPtr img (0x<sym> + <off>) = img.fnAddr "<target>"`.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::trusted_common::{ObjObject, RelocType, SecKind, SymKind, lean_string_lit};
use crate::untrusted_legacy_linker::{DataReloc, LinkedImage};
use crate::untrusted_driver::ExportConfig;

/// A single verified `.rodata` / `.data.rel.ro` `R_AARCH64_ABS64` pointer entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistryFact {
    /// Enclosing symbol name (or `"rodata"` when anonymous).
    pub sym_name: String,
    /// Image-relative byte offset of the enclosing symbol.
    pub sym_off: u64,
    /// Byte offset of the pointer field relative to `sym_off`.
    pub field_off: u64,
    /// Target symbol name resolved by `img.fnAddr`.
    pub target_name: String,
}

/// Mirror `Arm64.Program.fnOff`: first matching offset in `li.symbols`, else `li.stubs`.
fn lookup_fn_off(li: &LinkedImage, name: &str) -> Option<u64> {
    li.symbols
        .iter()
        .find(|(s, _)| s == name)
        .map(|(_, o)| *o)
        .or_else(|| li.stubs.iter().find(|(s, _)| s == name).map(|(_, o)| *o))
}

/// Mirror `findRelocWordTarget` in `ProofLib/ObjectLoad.lean`.
fn find_reloc_word_target(relocs: &[DataReloc], data_len: u64, k: u64) -> Option<u64> {
    let mut cur: Option<u64> = None;
    for r in relocs {
        if r.off + r.width > data_len {
            return None;
        }
        if r.off == k && r.width == 8 {
            cur = Some(r.target);
        } else if r.off + r.width <= k || k + 8 <= r.off {
            // Disjoint from `[k, k + 8)`; preserves current word.
        } else {
            cur = None;
        }
    }
    cur
}

/// Sanitize an arbitrary symbol name into a clean lowercase Lean identifier stem.
fn sanitize_ident(s: &str) -> String {
    let mut out = String::new();
    let mut prev_under = false;
    for ch in s.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
            prev_under = false;
        } else if !prev_under && !out.is_empty() {
            out.push('_');
            prev_under = true;
        }
    }
    while out.ends_with('_') {
        out.pop();
    }
    if out.is_empty() {
        out.push_str("entry");
    } else if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        out.insert_str(0, "sym_");
    }
    out
}

/// Collect all kernel-checkable `.rodata` / `.data.rel.ro` `R_AARCH64_ABS64` relocation facts.
pub fn collect_registry_facts(objects: &[ObjObject], li: &LinkedImage) -> Vec<RegistryFact> {
    // Build set of defined function symbol names for tie-breaking aliases at the same offset.
    let mut func_sym_names: HashSet<String> = HashSet::new();
    let mut object_sym_names: HashSet<String> = HashSet::new();
    for obj in objects {
        for sym in &obj.symbols {
            match sym.kind {
                SymKind::Func => {
                    func_sym_names.insert(sym.name.clone());
                }
                SymKind::Object => {
                    object_sym_names.insert(sym.name.clone());
                }
                _ => {}
            }
        }
    }

    // Map each target offset to candidate symbol names whose `fnOff` in `li` equals that offset.
    let mut off_to_targets: HashMap<u64, Vec<String>> = HashMap::new();
    for (name, off) in li.symbols.iter().chain(li.stubs.iter()) {
        if lookup_fn_off(li, name) == Some(*off) {
            off_to_targets.entry(*off).or_default().push(name.clone());
        }
    }

    // Sorted map of data symbols `(sym_off -> preferred sym_name)` for `[sym + off]` decomposition.
    let mut data_syms: BTreeMap<u64, String> = BTreeMap::new();
    for (name, off) in &li.symbols {
        if *off >= li.data_off {
            data_syms
                .entry(*off)
                .and_modify(|cur| {
                    if object_sym_names.contains(name) && !object_sym_names.contains(cur) {
                        *cur = name.clone();
                    }
                })
                .or_insert_with(|| name.clone());
        }
    }

    let data_len = li.data.len() as u64 + li.bss;
    let mut seen_slots: BTreeMap<u64, RegistryFact> = BTreeMap::new();

    for (obj_idx, obj) in objects.iter().enumerate() {
        for (sec_idx, sec) in obj.sections.iter().enumerate() {
            if sec.kind() != Some(SecKind::Rodata) {
                continue;
            }
            let Some(sec_base) = li
                .sec_off
                .get(obj_idx)
                .and_then(|s| s.get(sec_idx))
                .and_then(|&x| x)
            else {
                continue;
            };
            for rel in &sec.relocs {
                if rel.rtype != RelocType::Abs64 {
                    continue;
                }
                let slot_off = sec_base + rel.offset;
                if slot_off < li.data_off {
                    continue;
                }
                let in_ro = li
                    .ro_data
                    .iter()
                    .any(|&(r_off, r_len)| r_off <= slot_off && slot_off + 8 <= r_off + r_len);
                if !in_ro {
                    continue;
                }
                let Some(rel_target) =
                    find_reloc_word_target(&li.relocs, data_len, slot_off - li.data_off)
                else {
                    continue;
                };

                // Prefer direct relocation symbol if its `fnOff` matches `rel_target`; otherwise
                // resolve any function/stub symbol in `li` at `rel_target`.
                let direct_name = obj.symbols.get(rel.sym).and_then(|s| {
                    if rel.addend == 0 && lookup_fn_off(li, &s.name) == Some(rel_target) {
                        Some(s.name.clone())
                    } else {
                        None
                    }
                });

                let target_name = direct_name.or_else(|| {
                    off_to_targets.get(&rel_target).and_then(|cands| {
                        cands
                            .iter()
                            .find(|c| func_sym_names.contains(*c))
                            .or_else(|| cands.first())
                            .cloned()
                    })
                });

                let Some(target_name) = target_name else {
                    continue;
                };

                let (sym_off, sym_name) = data_syms
                    .range(..=slot_off)
                    .next_back()
                    .map(|(&off, name)| (off, name.clone()))
                    .unwrap_or_else(|| (sec_base, "rodata".to_string()));

                seen_slots.insert(
                    slot_off,
                    RegistryFact {
                        sym_name,
                        sym_off,
                        field_off: slot_off - sym_off,
                        target_name,
                    },
                );
            }
        }
    }

    seen_slots.into_values().collect()
}

/// Render `<ObjName>RegistryFacts.lean` for `cfg` and linked image `li`.
pub fn render_registry_facts_module(
    cfg: &ExportConfig,
    objects: &[ObjObject],
    li: &LinkedImage,
) -> String {
    let facts = collect_registry_facts(objects, li);
    let image_def = format!("{}Image", cfg.obj_name);
    let ns = format!("{}.RegistryFacts", cfg.namespace_prefix.trim());

    let mut out = String::new();
    for line in &cfg.license_header {
        out.push_str(line);
        out.push('\n');
    }
    if !cfg.license_header.is_empty() {
        out.push('\n');
    }
    out.push_str("module\n\n");
    out.push_str("public import Arm64\n");
    out.push_str("public import ProofLib.Hoare.FnPtr\n");
    out.push_str(&format!("public import {}\n\n", cfg.obj_module));
    out.push_str(&format!(
        "/-!\n# Generated `.rodata` / `.data.rel.ro` Relocation Facts (`{ns}`)\n\n\
         - **Layer & Role:** Untrusted generated proof lemmas (`Role::Proof`, checked by the Lean 4\n\
           kernel against `{image_def}`).\n\
         - **Contents:** One kernel-checked equation `rodataPtr img (0x<sym> + <off>) = img.fnAddr \"<target>\"`\n\
           for each `R_AARCH64_ABS64` relocation in `.rodata` / `.data.rel.ro`.\n\
         -/\n\n"
    ));
    out.push_str("@[expose] public section\n\n");
    out.push_str("open Arm64 ProofLib ProofLib.ProgramReflection\n\n");
    out.push_str("set_option Elab.async false\n");
    out.push_str("set_option maxHeartbeats 0\n");
    out.push_str("set_option maxRecDepth 2000000\n\n");
    out.push_str(&format!("namespace {ns}\n\n"));

    let mut used_names: HashMap<String, usize> = HashMap::new();
    for f in &facts {
        let base_ident = format!(
            "rodataPtr_{}_plus_{}",
            sanitize_ident(&f.sym_name),
            f.field_off
        );
        let count = used_names.entry(base_ident.clone()).or_insert(0);
        let thm_name = if *count == 0 {
            base_ident
        } else {
            format!("{base_ident}_{count}")
        };
        *count += 1;

        out.push_str(&format!(
            "/-- Relocation at `{}+0x{:x}` (`0x{:x} + {}`) resolves to `{}`. -/\n",
            f.sym_name, f.field_off, f.sym_off, f.field_off, f.target_name
        ));
        out.push_str(&format!(
            "theorem {thm_name} {{img : Obj.Image}} (himg : Obj.Loads {image_def} img) :\n\
             \x20   rodataPtr img (0x{:x} + {}) = img.fnAddr {} :=\n\
             \x20 rodataPtr_eq_fnAddr_of_loads himg (by rfl_kernel)\n\n",
            f.sym_off,
            f.field_off,
            lean_string_lit(&f.target_name)
        ));
    }

    out.push_str(&format!("end {ns}\n"));
    out
}
