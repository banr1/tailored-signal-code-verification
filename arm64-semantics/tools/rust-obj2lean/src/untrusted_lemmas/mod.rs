// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Untrusted Proof & Lemma Generator (`untrusted_lemmas`) — `[OUTSIDE TCB]`.
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` (every Lean theorem emitted here is proved by kernel
//!   reduction against the trusted `Arm64.Obj.LinkedImage` definition and verified by Lean's
//!   kernel; a bug here can only cause `lake build` to fail, never unsoundness).
//! - **Purpose:** Generates `<ObjName>Code.lean` ([`code`]), per-target `gen_fetches` lemma modules
//!   ([`code`]), function/callee/frame metadata sidecars `<Target>Index.json`
//!   ([`index`]), symbolic execution certificates/traces ([`symexec`]), and the standalone
//!   `fetch-decode-lemmas` subcommand.
//!
//! # Key Types & Functions
//! - [`lemma_patterns`], [`name_selected`]: Compiles and matches `lemma_allowlist` regexes.
//! - [`extract`], [`bit`], [`sign_extend`], [`decode_bit_masks`], [`parse_u64_lit`], [`parse_u32_lit`]:
//!   Bitfield and integer literal helpers shared across `untrusted_lemmas`.
//! - [`format_gen_decodes_line`], [`run_fetch_decode_lemmas`]: Implements the `fetch-decode-lemmas`
//!   CLI subcommand, emitting `gen_decodes` invocations.
//! - Submodules: [`code`], [`dwarf`] (DWARF signatures/layouts/lines from an
//!   untrusted `-g` companion compile), [`index`], [`symexec`].
//!
//! # When to Read This File
//! - Read this file when modifying `lemma_allowlist` symbol matching, shared bitfield helpers, or
//!   the standalone `fetch-decode-lemmas` subcommand; otherwise jump directly to [`code.rs`](code.rs),
//!   [`index.rs`](index.rs), or [`symexec/mod.rs`](symexec/mod.rs).

pub mod code;
pub mod dwarf;
pub mod index;
pub mod index_schema;
pub mod registry_facts;
pub mod symexec;

use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::Result;
use itertools::Itertools;
use regex::Regex;

use crate::untrusted_driver::{ExportConfig, ExportTarget};

// ---------------------------------------------------------------------------
// Shared Bitfield & Literal Helpers
// ---------------------------------------------------------------------------

pub(crate) fn extract(w: u32, lsb: u32, width: u32) -> u64 {
    ((w >> lsb) & ((1u32 << width) - 1)) as u64
}

pub(crate) fn bit(w: u32, pos: u32) -> bool {
    ((w >> pos) & 1) != 0
}

pub(crate) fn sign_extend(val: u64, width: u32) -> u64 {
    if width >= 64 {
        return val;
    }
    if (val & (1u64 << (width - 1))) != 0 {
        val | (!0u64 << width)
    } else {
        val & ((1u64 << width) - 1)
    }
}

fn decode_bit_masks_levels(imm_n: bool, imms: u64) -> u64 {
    if imm_n {
        63
    } else if (imms & 0b100000) == 0 {
        31
    } else if (imms & 0b110000) == 0b100000 {
        15
    } else if (imms & 0b111000) == 0b110000 {
        7
    } else if (imms & 0b111100) == 0b111000 {
        3
    } else {
        1
    }
}

pub(crate) fn decode_bit_masks(imm_n: bool, imms: u64, immr: u64) -> Option<u64> {
    if !(imm_n || (imms & 0b111110) != 0b111110) {
        return None;
    }
    let levels = decode_bit_masks_levels(imm_n, imms);
    let s = imms & levels;
    if s == levels || (immr & (!levels & 0x3F)) != 0 {
        return None;
    }
    let r = immr & levels;
    let elem_ones = ((2u128 << s) - 1) as u64;
    let elem_mask = ((2u128 << levels) - 1) as u64;
    let elem_rotated = if r == 0 {
        elem_ones
    } else {
        let shl_amt = ((levels - r) + 1) & 0x3F;
        ((elem_ones >> r) | elem_ones.wrapping_shl(shl_amt as u32)) & elem_mask
    };
    let r2 = if levels <= 1 {
        elem_rotated | (elem_rotated << 2)
    } else {
        elem_rotated
    };
    let r4 = if levels <= 3 { r2 | (r2 << 4) } else { r2 };
    let r8 = if levels <= 7 { r4 | (r4 << 8) } else { r4 };
    let r16 = if levels <= 15 { r8 | (r8 << 16) } else { r8 };
    Some(if levels <= 31 { r16 | (r16 << 32) } else { r16 })
}

/// Parse a decimal, `0x`-prefixed hexadecimal, or `0b`-prefixed binary `u64` literal.
pub fn parse_u64_lit(s: &str) -> Result<u64> {
    let s = s.trim().replace('_', "");
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        Ok(u64::from_str_radix(hex, 16)?)
    } else if let Some(bin) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
        Ok(u64::from_str_radix(bin, 2)?)
    } else {
        Ok(s.parse::<u64>()?)
    }
}

/// Parse a decimal, hexadecimal, or binary `u32` literal.
pub fn parse_u32_lit(s: &str) -> Result<u32> {
    let v = parse_u64_lit(s)?;
    u32::try_from(v).map_err(|_| anyhow::anyhow!("32-bit word out of range: {s}"))
}

// Naming helpers for the untrusted `Code` and lemma modules (kept out of `trusted_common`,
// which only names the trusted `Obj` module and its `Image`/`ObjectInfo` definitions).

impl ExportTarget {
    /// Output path and Lean module name of shard `i` (0-based) of this target's lemmas.
    pub fn shard_file(&self, i: usize) -> (PathBuf, String) {
        let stem = self.lean_file.file_stem().and_then(|s| s.to_str()).unwrap_or("Lemmas");
        let path = self.lean_file.with_file_name(format!("{stem}Shard{i}.lean"));
        (path, format!("{}Shard{i}", self.lean_module))
    }
}

impl ExportConfig {
    /// `<obj_name>Code : Program`, the untrusted laid-out program of the image.
    pub fn code_def_name(&self) -> String {
        format!("{}Code", self.obj_name)
    }

    /// Output path and Lean module name of shard `i` (0-based) of the untrusted `Code` module.
    pub fn code_shard_file(&self, i: usize) -> (PathBuf, String) {
        let stem = self
            .code_file
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("Code");
        let path = self.code_file.with_file_name(format!("{stem}Shard{i}.lean"));
        (path, format!("{}Shard{i}", self.code_module))
    }

    /// Namespace of a target's lemma file: `prefix.sub`, dropping empty parts.
    pub fn target_namespace(&self, target: &ExportTarget) -> String {
        [
            self.namespace_prefix.trim(),
            target.sub_namespace.as_deref().unwrap_or("").trim(),
        ]
        .into_iter()
        .filter(|s| !s.is_empty())
        .join(".")
    }
}

/// Compile a target's `lemma_allowlist` into anchored regexes.
pub fn lemma_patterns(target: &ExportTarget) -> Result<Vec<Regex>> {
    target
        .lemma_allowlist
        .iter()
        .map(|p| Ok(Regex::new(&format!("^(?:{p})$"))?))
        .collect()
}

/// Whether the demangled function `name` is selected by `patterns`: the full name, its
/// last `::` component, or its base C name without trailing ` [<obj>]` / `#<n>` local
/// disambiguation suffix, matches one of them.
pub fn name_selected(name: &str, patterns: &[Regex]) -> bool {
    let leaf = name.rsplit("::").next().unwrap_or(name);
    let (no_obj, base_c) = if let Some(stripped) = name.strip_suffix(']') {
        if let Some((base, _)) = stripped.rsplit_once(" [") {
            let base_c = if let Some((raw, num)) = base.rsplit_once('#') {
                if !num.is_empty() && num.chars().all(|c| c.is_ascii_digit()) {
                    raw
                } else {
                    base
                }
            } else {
                base
            };
            (base, base_c)
        } else {
            (name, name)
        }
    } else {
        (name, name)
    };
    let base_leaf = base_c.rsplit("::").next().unwrap_or(base_c);
    patterns.iter().any(|pat| {
        pat.is_match(name)
            || pat.is_match(leaf)
            || pat.is_match(no_obj)
            || pat.is_match(base_c)
            || pat.is_match(base_leaf)
    })
}

// ---------------------------------------------------------------------------
// Standalone `fetch-decode-lemmas` Subcommand
// ---------------------------------------------------------------------------

/// Coalesce a slice of 4-byte-aligned offsets into `0x<a>` / `0x<a> → 0x<b>` range items
/// and format a `gen_decodes <prog>_tree <prog> [...]` invocation.
pub fn format_gen_decodes_line(prog_name: &str, offsets: &[u64]) -> String {
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    for &off in offsets {
        if let Some(last) = ranges.last_mut()
            && last.1 + 4 == off
        {
            last.1 = off;
        } else {
            ranges.push((off, off));
        }
    }
    let items: Vec<String> = ranges
        .into_iter()
        .map(|(a, b)| {
            if a == b {
                format!("0x{a:x}")
            } else {
                format!("0x{a:x} → 0x{b:x}")
            }
        })
        .collect();
    format!("gen_decodes {prog_name}_tree {prog_name} [{}]", items.join(", "))
}

pub fn run_fetch_decode_lemmas(
    check: bool,
    prog: Option<String>,
    base: &str,
    inputs: &[String],
) -> ExitCode {
    if check {
        for input in inputs {
            let path = std::path::Path::new(input);
            if !path.is_file() {
                continue;
            }
            match std::fs::read_to_string(path) {
                Ok(src) => {
                    if src.contains("-- BEGIN AUTO-GENERATED FETCH-DECODE LEMMAS (") {
                        eprintln!(
                            "error: {}: contains legacy inline fetch-decode block; use `gen_decodes` / `gen_fetches`",
                            path.display()
                        );
                        return ExitCode::FAILURE;
                    }
                }
                Err(e) => {
                    eprintln!("error: failed to read {}: {e}", path.display());
                    return ExitCode::FAILURE;
                }
            }
        }
        return ExitCode::SUCCESS;
    }
    let prog_name = prog.unwrap_or_else(|| "prog".into());
    let base_addr = match parse_u64_lit(base) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: invalid --base `{base}`: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut offsets = Vec::with_capacity(inputs.len());
    for (idx, tok) in inputs.iter().enumerate() {
        if let Err(e) = parse_u32_lit(tok) {
            eprintln!("error: invalid 32-bit word or offset `{tok}`: {e}");
            return ExitCode::FAILURE;
        }
        offsets.push(base_addr + (idx as u64) * 4);
    }
    println!("{}", format_gen_decodes_line(&prog_name, &offsets));
    ExitCode::SUCCESS
}
