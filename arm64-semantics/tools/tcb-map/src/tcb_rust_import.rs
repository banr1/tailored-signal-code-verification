// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `tcb-rust-import` rule: trusted (`tcb` / `case-studies-tcb`) Rust files are self-contained
//! (`[AUDIT/LINTER]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[AUDIT/LINTER]`. The Lean side of the trust model is enforced by
//!   [`crate::Workspace::check_imports`] (trusted modules import only trusted modules). This rule
//!   is the Rust counterpart: a Rust file classified as `tcb` or `case-studies-tcb` by
//!   [`crate::policy::classify_path`] may not reference
//!   - a workspace crate under `tools/` that is not itself classified `tcb` (e.g.
//!     `repo_common::...`, `extern crate repo_common;`), or
//!   - an `[OUTSIDE TCB]` or test module of its own crate, i.e. any path segment `untrusted_*::`,
//!     `test_infra::`, `tests::`, or `*_tests::` (`crate::untrusted_driver::extract(..)`,
//!     `use super::untrusted_lemmas::..`, `tests::helper()`).
//!
//!   Declaring such a module (`pub mod untrusted_driver;`) is allowed: the crate root must name
//!   its module tree, and a declaration does not make the trusted code depend on the module's
//!   behaviour. Together with `inline-test-in-tcb` this keeps the `[tcb]` and `[case-studies-tcb]`
//!   line counts of `tcb-map --tree` honest: everything a trusted Rust file can
//!   execute is itself trusted or an external dependency named in `Cargo.toml`.
//! - The check is line-based after dropping `//` comments, so doc comments and prose that mention
//!   `untrusted_lemmas` are not flagged.
//!
//! # When to Read This File
//! - Only when changing what a trusted Rust file may reference.

use crate::Violation;
use crate::discovery::walk_repo_files;
use crate::policy::{TrustCategory, classify_path};
use anyhow::Result;
use regex::Regex;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::sync::LazyLock;

/// Rule name used in [`Violation::rule`].
pub const RULE: &str = "tcb-rust-import";

/// `untrusted_<x>::`, `test_infra::`, `tests::`, or `*_tests::` anywhere in a path
/// (optionally after `crate::`/`super::`/`self::`).
static UNTRUSTED_MODULE_PATH: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"\b(?:crate::|super::|self::)?(untrusted_[A-Za-z0-9_]*|test_infra|tests|[A-Za-z0-9_]+_tests)\s*::",
    )
    .unwrap()
});

/// Workspace crates under `tools/<name>/Cargo.toml` or `tools/dev/<name>/Cargo.toml` and whether
/// each is classified `tcb`. Crate identifiers use `_` for `-` as in Rust source.
pub fn workspace_crates(rel_paths: &[String]) -> Vec<(String, bool)> {
    let mut out = BTreeSet::new();
    for rel in rel_paths {
        let parts: Vec<&str> = rel.split('/').collect();
        if let ["tools", name, "Cargo.toml"] = parts[..]
            && name != "dev"
        {
            let tcb =
                classify_path(&format!("tools/{name}/src/lib.rs")) == Some(TrustCategory::Tcb);
            out.insert((name.replace('-', "_"), tcb));
        } else if let ["tools", "dev", name, "Cargo.toml"] = parts[..] {
            out.insert((name.replace('-', "_"), false));
        }
    }
    out.into_iter().collect()
}

/// Regex matching a reference (`ident::` or `extern crate ident`) to any of `idents`.
fn crate_ref_regex(idents: &[&str]) -> Option<Regex> {
    if idents.is_empty() {
        return None;
    }
    let alt = idents
        .iter()
        .map(|s| regex::escape(s))
        .collect::<Vec<_>>()
        .join("|");
    Some(Regex::new(&format!(r"\b(?:extern\s+crate\s+({alt})\b|({alt})\s*::)")).unwrap())
}

/// Code portion of a source line: everything before a `//` comment, or `""` for comment lines.
fn code_part(line: &str) -> &str {
    let trimmed = line.trim();
    if trimmed.starts_with("//") {
        return "";
    }
    match trimmed.find("//") {
        Some(i) => trimmed[..i].trim_end(),
        None => trimmed,
    }
}

/// References from the `tcb` Rust file `rel_path` (contents `text`) to non-`tcb` workspace
/// crates (`non_tcb_crates`, as Rust identifiers) or `untrusted_*` / `test_infra` / `tests` /
/// `*_tests` modules.
pub fn check_source(rel_path: &str, text: &str, non_tcb_crates: &[&str]) -> Vec<Violation> {
    let crate_re = crate_ref_regex(non_tcb_crates);
    let mut out = Vec::new();
    for (idx, line) in text.lines().enumerate() {
        let code = code_part(line);
        if code.is_empty() {
            continue;
        }
        let message = if let Some(m) = UNTRUSTED_MODULE_PATH.captures(code) {
            format!(
                "`tcb` file references the `[OUTSIDE TCB]` module `{}` (move the caller out of \
                 `tcb`, or move the callee into a `trusted_*` module)",
                &m[1]
            )
        } else if let Some(m) = crate_re.as_ref().and_then(|re| re.captures(code)) {
            let name = m.get(1).or_else(|| m.get(2)).map_or("", |g| g.as_str());
            format!(
                "`tcb` file references the non-`tcb` workspace crate `{name}` (a `tcb` Rust file \
                 may only use other `tcb` code and external crates)"
            )
        } else {
            continue;
        };
        out.push(Violation {
            path: rel_path.to_string(),
            line: idx + 1,
            rule: RULE.to_string(),
            text: format!("{message}: {}", line.trim()),
        });
    }
    out
}

/// [`check_source`] over every `.rs` file under `root` that is classified as trusted (`tcb` or
/// `case-studies-tcb`).
pub fn check(root: &Path) -> Result<Vec<Violation>> {
    let rel_paths = walk_repo_files(root)?;
    let crates = workspace_crates(&rel_paths);
    let non_tcb: Vec<&str> = crates
        .iter()
        .filter(|(_, tcb)| !tcb)
        .map(|(name, _)| name.as_str())
        .collect();
    let mut out = Vec::new();
    for rel in &rel_paths {
        if rel.ends_with(".rs") && classify_path(rel).is_some_and(TrustCategory::is_trusted) {
            out.extend(check_source(
                rel,
                &fs::read_to_string(root.join(rel))?,
                &non_tcb,
            ));
        }
    }
    Ok(out)
}
