// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Archive-member provenance and the unwind audit of a `--stock` Rust `std` binary link
//! (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. Records and checks what `ld.lld` pulled out of the archives
//!   of a [`crate::stock_std`] link; proofs check the executable against its pinned bytes.
//! - **Purpose:**
//!   - [`lld_args`]: the `--why-extract=` / `-Map=` outputs `ld.lld` writes into `work/`.
//!   - [`archive_members`]: every archive member `ld.lld` extracted, the reference and symbol
//!     that extracted it, the input sections of it that survive `--gc-sections` (with sizes), and
//!     those `--gc-sections` removed. The parser fails closed ([`parse_members`]).
//!   - [`unwind_audit`]: fails unless the executable has no unwinder. `libunwind.a` members may be
//!     extracted (`rust_eh_personality` references `_Unwind_*`), but none of their sections may
//!     be retained, and every `.symtab` name (other than `STT_FILE` source names) containing an
//!     [`UNWIND_DENY`] pattern must be an [`UNWIND_ALLOW`] entry in its allowed form (a weak
//!     undefined reference, which links no code).
//!
//! # When to Read This File
//! - Read this file for the `stdBin.archiveMembers` / `stdBin.unwindAudit` fields of
//!   `stock-link.json`.

use anyhow::{Context, Result, ensure};
use object::{Object, ObjectSymbol};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// `--why-extract=` output, relative to `work/` (`ld.lld` runs there).
pub const WHY_EXTRACT: &str = "why-extract.tsv";
/// `-Map=` output, relative to `work/`.
pub const LINK_MAP: &str = "link.map";

/// Name substrings of unwinder symbols (`libunwind`, frame registration, the `_Unwind_*` ABI).
pub const UNWIND_DENY: &[&str] = &[
    "_Unwind_",
    "__register_frame",
    "__deregister_frame",
    "unw_",
    "libunwind",
];

/// Unwinder names allowed as weak undefined references, with the reason.
pub const UNWIND_ALLOW: &[(&str, &str)] = &[
    (
        "__register_frame_info",
        "weak undefined reference of crtbegin.o; no definition is linked, so crtbegin.o skips \
         frame registration",
    ),
    (
        "__deregister_frame_info",
        "weak undefined reference of crtbegin.o; no definition is linked, so crtbegin.o skips \
         frame deregistration",
    ),
];

/// The extra `ld.lld` arguments: [`WHY_EXTRACT`], [`LINK_MAP`], and `--print-gc-sections`, whose
/// report accounts for every extracted member that retains no section.
pub fn lld_args() -> [String; 3] {
    [
        format!("--why-extract={WHY_EXTRACT}"),
        format!("-Map={LINK_MAP}"),
        "--print-gc-sections".to_string(),
    ]
}

/// The exact `--why-extract` header line.
const WHY_HEADER: &str = "reference\textracted\tsymbol";
/// The exact `-Map` header line.
pub(crate) const MAP_HEADER: &str =
    "             VMA              LMA     Size Align Out     In      Symbol";
/// Width of the `VMA LMA Size Align` columns of a `-Map` line, including the separating space.
pub(crate) const MAP_COLS: usize = 49;

/// `path` relative to `out_dir` when below it (paths in `ld.lld` outputs are as given to it).
fn rel(path: &str, out_dir: &Path) -> String {
    let prefix = format!("{}/", out_dir.display());
    path.strip_prefix(&prefix).unwrap_or(path).to_string()
}

/// `<input>:(<section>)` as `(input, section)`, with any `+0x..` piece offset removed.
fn split_input_section(s: &str) -> Option<(&str, &str)> {
    let (input, section) = s.split_once(":(")?;
    let section = section.strip_suffix(')')?;
    let section = section.split_once('+').map_or(section, |(n, _)| n);
    Some((input, section))
}

/// One extracted archive member.
#[derive(Debug, Default)]
pub struct Member {
    /// `(reference, symbol)` from `--why-extract`.
    pub extracted_by: Option<(String, String)>,
    /// Retained input section name to total size.
    pub retained: BTreeMap<String, u64>,
    /// Input sections `--gc-sections` removed.
    pub removed: BTreeSet<String>,
}

/// Parse `why` (`--why-extract` TSV), `map` (`-Map`) and `gc` (the `ld.lld` output with the
/// `--print-gc-sections` report) into members keyed by `archive(member)` (archive path relative
/// to `out_dir`).
///
/// Fails closed on any output it does not recognize, so a format change cannot make the retained
/// sets vacuously empty:
/// - both headers must match exactly, and every `-Map` line must be an output-section,
///   input-section or symbol line;
/// - at least one member must be extracted, and at least one archive input section retained;
/// - every member must be accounted for: it retains a section or `--gc-sections` removed one of
///   its sections, and every retained or removed archive section is of an extracted member.
pub fn parse_members(
    why: &str,
    map: &str,
    gc: &str,
    out_dir: &Path,
) -> Result<BTreeMap<String, Member>> {
    let mut members: BTreeMap<String, Member> = BTreeMap::new();
    let mut lines = why.lines();
    ensure!(
        lines.next() == Some(WHY_HEADER),
        "{WHY_EXTRACT}: unrecognized header (expected {WHY_HEADER:?})"
    );
    for (n, line) in lines.enumerate() {
        let f: Vec<&str> = line.split('\t').collect();
        ensure!(
            f.len() == 3 && f.iter().all(|x| !x.is_empty()) && f[1].ends_with(')'),
            "{WHY_EXTRACT} line {}: expected `reference<TAB>archive(member)<TAB>symbol`: {line:?}",
            n + 2
        );
        let m = members.entry(rel(f[1], out_dir)).or_default();
        if m.extracted_by.is_none() {
            m.extracted_by = Some((rel(f[0], out_dir), f[2].to_string()));
        }
    }
    ensure!(
        !members.is_empty(),
        "{WHY_EXTRACT}: no archive member extracted"
    );

    let mut lines = map.lines();
    ensure!(
        lines.next() == Some(MAP_HEADER),
        "{LINK_MAP}: unrecognized header (expected {MAP_HEADER:?})"
    );
    let mut archive_sections = 0usize;
    for (n, line) in lines.enumerate() {
        let bad = || format!("{LINK_MAP} line {}: unrecognized line {line:?}", n + 2);
        let (cols, rest) = line.split_at_checked(MAP_COLS).with_context(bad)?;
        let c: Vec<&str> = cols.split_whitespace().collect();
        let [vma, lma, size, align] = c.as_slice() else {
            anyhow::bail!(bad());
        };
        ensure!(
            [vma, lma, size]
                .iter()
                .all(|x| u64::from_str_radix(x, 16).is_ok())
                && align.parse::<u64>().is_ok()
                && cols.ends_with(' '),
            bad()
        );
        let indent = rest.len() - rest.trim_start_matches(' ').len();
        let item = &rest[indent..];
        ensure!(!item.is_empty(), bad());
        match indent {
            // An output section or a linker-script assignment.
            0 => {}
            // An input section.
            8 => {
                let (input, section) = split_input_section(item).with_context(bad)?;
                if !input.ends_with(')') || !input.contains(".a(") {
                    continue;
                }
                let key = rel(input, out_dir);
                let m = members.get_mut(&key).with_context(|| {
                    format!("{LINK_MAP}: section of {key}, which {WHY_EXTRACT} does not list")
                })?;
                *m.retained.entry(section.to_string()).or_default() +=
                    u64::from_str_radix(size, 16)?;
                archive_sections += 1;
            }
            // A symbol.
            16 => {}
            _ => anyhow::bail!(bad()),
        }
    }
    ensure!(
        archive_sections > 0,
        "{LINK_MAP}: no retained archive input section"
    );

    for removed in gc
        .lines()
        .filter_map(|l| l.trim().strip_prefix("removing unused section "))
    {
        let Some((input, section)) = split_input_section(removed) else {
            anyhow::bail!("--print-gc-sections: unrecognized line {removed:?}");
        };
        if !input.ends_with(')') || !input.contains(".a(") {
            continue;
        }
        let key = rel(input, out_dir);
        let m = members.get_mut(&key).with_context(|| {
            format!("--print-gc-sections: section of {key}, which {WHY_EXTRACT} does not list")
        })?;
        m.removed.insert(section.to_string());
    }
    let unaccounted: Vec<&str> = members
        .iter()
        .filter(|(_, m)| m.retained.is_empty() && m.removed.is_empty())
        .map(|(k, _)| k.as_str())
        .collect();
    ensure!(
        unaccounted.is_empty(),
        "extracted members with neither a retained ({LINK_MAP}) nor a removed \
         (--print-gc-sections) section:\n  {}",
        unaccounted.join("\n  ")
    );
    Ok(members)
}

/// The `stdBin.archiveMembers` array from the [`lld_args`] outputs in `work` and the `ld.lld`
/// output `lld_out`.
pub fn archive_members(
    work: &Path,
    out_dir: &Path,
    lld_out: &str,
) -> Result<BTreeMap<String, Member>> {
    let read = |f: &str| {
        std::fs::read_to_string(work.join(f))
            .with_context(|| format!("cannot read {}", work.join(f).display()))
    };
    parse_members(&read(WHY_EXTRACT)?, &read(LINK_MAP)?, lld_out, out_dir)
}

/// [`Member`]s as `stock-link.json` JSON.
pub fn members_json(members: &BTreeMap<String, Member>) -> serde_json::Value {
    members
        .iter()
        .map(|(k, m)| {
            serde_json::json!({
                "member": k,
                "extractedBy": m.extracted_by.as_ref().map(|(r, s)| {
                    serde_json::json!({"reference": r, "symbol": s})
                }),
                "retained": m.retained.iter().map(|(s, n)| {
                    serde_json::json!({"section": s, "size": n})
                }).collect::<Vec<_>>(),
                "removed": m.removed,
            })
        })
        .collect()
}

/// Fail unless the executable `elf` links no unwinder (see the module docs); return the
/// `stdBin.unwindAudit` object (the allowed entries present).
pub fn unwind_audit(elf: &[u8], members: &BTreeMap<String, Member>) -> Result<serde_json::Value> {
    let unwinder: Vec<String> = members
        .iter()
        .filter(|(k, m)| k.contains("libunwind.a(") && !m.retained.is_empty())
        .map(|(k, m)| format!("{k}: {:?}", m.retained.keys().collect::<Vec<_>>()))
        .collect();
    ensure!(
        unwinder.is_empty(),
        "unwind audit: libunwind.a sections are linked:\n  {}",
        unwinder.join("\n  ")
    );
    let f = object::File::parse(elf).context("unwind audit: cannot parse executable")?;
    let mut allowed = BTreeMap::new();
    let mut bad = Vec::new();
    for s in f.symbols() {
        // `STT_FILE` source names (e.g. of an extracted member whose sections were all collected)
        // name no code or data.
        if s.kind() == object::SymbolKind::File {
            continue;
        }
        let Ok(name) = s.name() else { continue };
        if !UNWIND_DENY.iter().any(|p| name.contains(p)) {
            continue;
        }
        match UNWIND_ALLOW.iter().find(|(n, _)| *n == name) {
            Some((n, why)) if s.is_undefined() && s.is_weak() => {
                allowed.insert(*n, *why);
            }
            _ => bad.push(format!(
                "{name} ({})",
                if s.is_undefined() {
                    "undefined"
                } else {
                    "defined"
                }
            )),
        }
    }
    bad.sort();
    bad.dedup();
    ensure!(
        bad.is_empty(),
        "unwind audit: unwinder symbols in .symtab without an allowed form: {}",
        bad.join(", ")
    );
    Ok(serde_json::json!({
        "allowed": allowed
            .iter()
            .map(|(n, why)| serde_json::json!({"symbol": n, "reason": why}))
            .collect::<Vec<_>>(),
    }))
}
