// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Repository directory-hierarchy trust classification, code-size metrics, and tree/JSON views
//! (`[AUDIT/LINTER]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[AUDIT/LINTER]` (visualizes and enforces that every file and directory in
//!   the repository belongs to an explicit [`TrustCategory`]: `tcb`, `case-studies-tcb`, `proof`,
//!   `testing`, `infra`, `doc`).
//! - **Purpose:** Walks the repository ([`crate::discovery::walk_repo_files`]), classifies
//!   every file via [`crate::policy::classify_path`], computes code-size metrics (`files`,
//!   `code_lines`, and per-category `rollup` breakdowns) at every directory node, and renders
//!   either a human-readable directory hierarchy (`tcb-map --tree`) or a hierarchical
//!   JSON tree (`tcb-map --tree-json` / `--json`) suitable for interactive inspection in `fx`.

use crate::Violation;
use crate::discovery::walk_repo_files;
use crate::policy::{TrustCategory, classify_path, is_case_study_path};
use anyhow::Result;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

/// Rule reported when a repository file does not match any [`TrustCategory`] rule in
/// [`crate::policy::classify_path`].
pub const RULE: &str = "unclassified-path";

/// Code-size metrics aggregated at a file, directory, or trust-category level.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct SizeMetrics {
    pub files: usize,
    pub code_lines: usize,
}

impl SizeMetrics {
    pub fn add_assign(&mut self, other: SizeMetrics) {
        self.files += other.files;
        self.code_lines += other.code_lines;
    }
}

/// Directory-level rollup of categories, total size metrics, and per-category breakdown.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct Rollup {
    pub categories: Vec<String>,
    pub totals: SizeMetrics,
    pub by_category: BTreeMap<String, SizeMetrics>,
}

#[derive(Debug, Clone)]
pub struct FileEntry {
    pub name: String,
    pub rel_path: String,
    pub category: TrustCategory,
    pub code_lines: usize,
}

impl FileEntry {
    pub fn metrics(&self) -> SizeMetrics {
        SizeMetrics {
            files: 1,
            code_lines: self.code_lines,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct DirNode {
    pub name: String,
    /// Repo-relative path with trailing `/` (or `"."` for the repository root).
    pub rel_path: String,
    pub subdirs: BTreeMap<String, DirNode>,
    pub direct_files: Vec<FileEntry>,
    pub categories: BTreeSet<TrustCategory>,
    pub files: usize,
    pub code_lines: usize,
    pub by_category: BTreeMap<TrustCategory, SizeMetrics>,
}

/// Hierarchical JSON representation of a directory or file node for `tcb-map --tree-json`
/// (designed for interactive exploration in `fx`).
#[derive(Debug, Clone, Serialize)]
#[serde(untagged)]
pub enum JsonTreeNode {
    Dir {
        category: String,
        files: usize,
        code_lines: usize,
        rollup: Rollup,
        #[serde(skip_serializing_if = "BTreeMap::is_empty")]
        children: BTreeMap<String, JsonTreeNode>,
    },
    File {
        category: String,
        files: usize,
        code_lines: usize,
    },
}

impl DirNode {
    /// True if all files under this directory share a single [`TrustCategory`].
    pub fn is_homogeneous(&self) -> bool {
        self.categories.len() <= 1
    }

    /// True if all non-documentation (`!= TrustCategory::Doc`) files under this directory share at
    /// most one [`TrustCategory`]. Used by text `--tree` rendering so homogeneous code directories
    /// containing a `README.md` remain compact leaves.
    pub fn is_code_homogeneous(&self) -> bool {
        self.categories
            .iter()
            .filter(|&&c| c != TrustCategory::Doc)
            .count()
            <= 1
    }

    /// Plain category label (without brackets): `"tcb"`, `"case-studies-tcb"`, `"proof"`,
    /// `"testing"`, `"infra"`, `"doc"`, or `"mixed: tcb + proof + doc"`.
    pub fn category_label(&self) -> String {
        if self.categories.len() == 1 {
            let cat = *self.categories.iter().next().unwrap();
            cat.as_str().to_string()
        } else {
            let list = self
                .categories
                .iter()
                .map(|c| c.as_str())
                .collect::<Vec<_>>()
                .join(" + ");
            format!("mixed: {list}")
        }
    }

    /// Bracketed category badge: `[tcb]`, `[case-studies-tcb]`, `[proof]`, `[testing]`, `[infra]`,
    /// `[doc]`, or `[mixed: tcb + proof + doc]`.
    pub fn tag(&self) -> String {
        format!("[{}]", self.category_label())
    }

    /// Build the [`Rollup`] summary for this directory node.
    pub fn rollup(&self) -> Rollup {
        let categories = self
            .categories
            .iter()
            .map(|c| c.as_str().to_string())
            .collect();
        let by_category = self
            .by_category
            .iter()
            .filter(|(_, m)| m.files > 0)
            .map(|(cat, m)| (cat.as_str().to_string(), *m))
            .collect();
        Rollup {
            categories,
            totals: SizeMetrics {
                files: self.files,
                code_lines: self.code_lines,
            },
            by_category,
        }
    }

    /// Convert this directory and its subtree into an `fx`-friendly [`JsonTreeNode`].
    pub fn to_json_node(&self) -> JsonTreeNode {
        let mut children = BTreeMap::new();
        for (name, sub) in &self.subdirs {
            children.insert(format!("{name}/"), sub.to_json_node());
        }
        for f in &self.direct_files {
            children.insert(
                f.name.clone(),
                JsonTreeNode::File {
                    category: f.category.as_str().to_string(),
                    files: 1,
                    code_lines: f.code_lines,
                },
            );
        }
        JsonTreeNode::Dir {
            category: self.category_label(),
            files: self.files,
            code_lines: self.code_lines,
            rollup: self.rollup(),
            children,
        }
    }

    fn insert(&mut self, parts: &[&str], entry: FileEntry) {
        if parts.len() <= 1 {
            self.direct_files.push(entry);
            return;
        }
        let dir_name = parts[0];
        let child_rel = if self.rel_path == "." || self.rel_path.is_empty() {
            format!("{dir_name}/")
        } else {
            format!("{}{dir_name}/", self.rel_path)
        };
        let child = self
            .subdirs
            .entry(dir_name.to_string())
            .or_insert_with(|| DirNode {
                name: dir_name.to_string(),
                rel_path: child_rel,
                ..DirNode::default()
            });
        child.insert(&parts[1..], entry);
    }

    fn finalize(&mut self) {
        for sub in self.subdirs.values_mut() {
            sub.finalize();
        }
        self.categories.clear();
        self.files = 0;
        self.code_lines = 0;
        self.by_category.clear();
        for sub in self.subdirs.values() {
            self.categories.extend(&sub.categories);
            self.files += sub.files;
            self.code_lines += sub.code_lines;
            for (&cat, &m) in &sub.by_category {
                self.by_category.entry(cat).or_default().add_assign(m);
            }
        }
        for f in &self.direct_files {
            self.categories.insert(f.category);
            self.files += 1;
            self.code_lines += f.code_lines;
            self.by_category
                .entry(f.category)
                .or_default()
                .add_assign(f.metrics());
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TreeReport {
    pub root: DirNode,
    pub totals: BTreeMap<TrustCategory, SizeMetrics>,
    pub violations: Vec<Violation>,
    pub no_case_studies: bool,
}

impl TreeReport {
    /// Check that every repository file under `root` belongs to an explicit [`TrustCategory`],
    /// without reading file contents when `--tree` / `--tree-json` metrics are not requested.
    pub fn check_violations(root: &Path) -> Result<Vec<Violation>> {
        let mut violations = Vec::new();
        for rel in walk_repo_files(root)? {
            if classify_path(&rel).is_none() {
                violations.push(Violation {
                    path: rel.clone(),
                    line: 1,
                    rule: RULE.to_string(),
                    text: format!(
                        "`{rel}` has no trust category (add it to `policy::classify_path`)"
                    ),
                });
            }
        }
        Ok(violations)
    }

    /// Scan all repository files under `root`, classify each into a [`TrustCategory`], and build
    /// the hierarchical [`DirNode`] tree with code-size metrics.
    pub fn build(root: &Path) -> Result<Self> {
        Self::build_with_lean(root, &std::collections::HashMap::new())
    }

    /// Like [`Self::build`], optionally omitting case-study paths ([`is_case_study_path`]).
    pub fn build_filtered(root: &Path, no_case_studies: bool) -> Result<Self> {
        Self::build_with_lean_filtered(root, &std::collections::HashMap::new(), no_case_studies)
    }

    /// Like [`Self::build`], reusing already comment-stripped `code` for any `.lean` module
    /// present in `lean_code` instead of re-reading and re-lexing it from disk.
    pub fn build_with_lean(
        root: &Path,
        lean_code: &std::collections::HashMap<&str, &str>,
    ) -> Result<Self> {
        Self::build_with_lean_filtered(root, lean_code, false)
    }

    /// Like [`Self::build_with_lean`], optionally omitting case-study paths ([`is_case_study_path`]).
    pub fn build_with_lean_filtered(
        root: &Path,
        lean_code: &std::collections::HashMap<&str, &str>,
        no_case_studies: bool,
    ) -> Result<Self> {
        let mut rel_files = walk_repo_files(root)?;
        if no_case_studies {
            rel_files.retain(|rel| !is_case_study_path(rel));
        }
        let n_threads = std::thread::available_parallelism()
            .map_or(4, |n| n.get().min(8))
            .min(rel_files.len().max(1));
        let chunk_size = rel_files.len().div_ceil(n_threads).max(1);
        let entries = std::thread::scope(|s| {
            let handles: Vec<_> = rel_files
                .chunks(chunk_size)
                .map(|chunk| {
                    s.spawn(move || {
                        let mut out = Vec::with_capacity(chunk.len());
                        for rel in chunk {
                            let m = if let Some(&stripped) = lean_code.get(rel.as_str()) {
                                SizeMetrics {
                                    files: 1,
                                    code_lines: stripped
                                        .lines()
                                        .filter(|l| !l.trim().is_empty())
                                        .count(),
                                }
                            } else {
                                measure_file(&root.join(rel), rel)
                            };
                            out.push((rel.clone(), m));
                        }
                        out
                    })
                })
                .collect();
            let mut all = Vec::with_capacity(rel_files.len());
            for h in handles {
                all.extend(h.join().expect("tree worker panicked"));
            }
            all
        });
        Ok(Self::from_file_metrics_filtered(entries, no_case_studies))
    }

    /// Build a [`TreeReport`] from `(repo-relative path, code_lines)` pairs (convenience
    /// constructor for unit tests).
    pub fn from_entries(entries: impl IntoIterator<Item = (String, usize)>) -> Self {
        Self::from_file_metrics(entries.into_iter().map(|(rel, code_lines)| {
            (
                rel,
                SizeMetrics {
                    files: 1,
                    code_lines,
                },
            )
        }))
    }

    /// Build a [`TreeReport`] from `(repo-relative path, SizeMetrics)` pairs.
    pub fn from_file_metrics(entries: impl IntoIterator<Item = (String, SizeMetrics)>) -> Self {
        Self::from_file_metrics_filtered(entries, false)
    }

    /// Build a [`TreeReport`] from `(repo-relative path, SizeMetrics)` pairs, optionally omitting
    /// case-study paths ([`is_case_study_path`]).
    pub fn from_file_metrics_filtered(
        entries: impl IntoIterator<Item = (String, SizeMetrics)>,
        no_case_studies: bool,
    ) -> Self {
        let mut root = DirNode {
            name: ".".to_string(),
            rel_path: ".".to_string(),
            ..DirNode::default()
        };
        let mut violations = Vec::new();
        for (rel, m) in entries {
            if no_case_studies && is_case_study_path(&rel) {
                continue;
            }
            let Some(category) = classify_path(&rel) else {
                violations.push(Violation {
                    path: rel.clone(),
                    line: 1,
                    rule: RULE.to_string(),
                    text: format!(
                        "`{rel}` has no trust category (add it to `policy::classify_path`)"
                    ),
                });
                continue;
            };
            let parts: Vec<&str> = rel.split('/').collect();
            let name = parts.last().copied().unwrap_or(rel.as_str()).to_string();
            root.insert(
                &parts,
                FileEntry {
                    name,
                    rel_path: rel.clone(),
                    category,
                    code_lines: m.code_lines,
                },
            );
        }
        root.finalize();
        let totals: BTreeMap<TrustCategory, SizeMetrics> = TrustCategory::ALL
            .into_iter()
            .map(|c| (c, root.by_category.get(&c).copied().unwrap_or_default()))
            .collect();
        Self {
            root,
            totals,
            violations,
            no_case_studies,
        }
    }

    /// Render the directory hierarchy as pretty-printed JSON for `fx` (`tcb-map --tree-json`).
    pub fn to_json_pretty(&self) -> String {
        serde_json::to_string_pretty(&self.root.to_json_node())
            .expect("JsonTreeNode serialization cannot fail")
    }

    /// Render the directory hierarchy with `[tcb]`, `[case-studies-tcb]`, `[proof]`, `[testing]`,
    /// `[infra]`, `[doc]`, and `[mixed: ...]` badges, expanding mixed parent directories down to
    /// homogeneous code subtrees, with file count and source lines of code (`loc`), followed by per-category totals.
    pub fn render(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "Repository trust hierarchy ({} files, {} loc):",
            self.root.files, self.root.code_lines
        );
        for sub in self.root.subdirs.values() {
            render_dir(&mut out, sub, 1);
        }
        for f in &self.root.direct_files {
            if matches!(
                f.name.as_str(),
                "Arm64.lean" | "ProofLib.lean" | "lakefile.lean" | "lean-toolchain"
            ) {
                let _ = writeln!(
                    out,
                    "  {:<42} {:<38} ({:>4} file,  {:>7} loc)",
                    f.rel_path,
                    format!("[{}]", f.category),
                    1,
                    f.code_lines
                );
            }
        }
        let _ = writeln!(out, "\nTrust category totals:");
        for cat in TrustCategory::ALL {
            if self.no_case_studies && cat == TrustCategory::CaseStudiesTcb {
                continue;
            }
            let st = self.totals.get(&cat).copied().unwrap_or_default();
            let _ = writeln!(
                out,
                "  {:<20} {:>5} files, {:>8} loc",
                format!("[{cat}]"),
                st.files,
                st.code_lines
            );
        }
        out
    }
}

fn render_dir(out: &mut String, node: &DirNode, depth: usize) {
    let indent = "  ".repeat(depth);
    let label = format!("{indent}{}", node.rel_path);
    let file_word = if node.files == 1 { "file, " } else { "files," };
    let _ = writeln!(
        out,
        "{:<44} {:<38} ({:>4} {file_word} {:>7} loc)",
        label,
        node.tag(),
        node.files,
        node.code_lines
    );
    if node.is_code_homogeneous() {
        return;
    }
    for sub in node.subdirs.values() {
        render_dir(out, sub, depth + 1);
    }
    let child_indent = "  ".repeat(depth + 1);
    for cat in TrustCategory::ALL {
        let matching: Vec<&FileEntry> = node
            .direct_files
            .iter()
            .filter(|f| f.category == cat)
            .collect();
        if matching.is_empty() {
            continue;
        }
        if matching.len() == 1 {
            let f = matching[0];
            let child_label = format!("{child_indent}{}", f.rel_path);
            let _ = writeln!(
                out,
                "{:<44} {:<38} ({:>4} file,  {:>7} loc)",
                child_label,
                format!("[{cat}]"),
                1,
                f.code_lines
            );
        } else {
            let total_loc: usize = matching.iter().map(|f| f.code_lines).sum();
            let ext = matching
                .first()
                .and_then(|f| f.name.rsplit_once('.').map(|(_, e)| e))
                .unwrap_or("");
            let all_same_ext = !ext.is_empty()
                && matching
                    .iter()
                    .all(|f| f.name.ends_with(&format!(".{ext}")));
            let pattern = if all_same_ext {
                format!("*.{ext}")
            } else {
                "*".to_string()
            };
            let child_label = format!("{child_indent}{}{pattern}", node.rel_path);
            let _ = writeln!(
                out,
                "{:<44} {:<38} ({:>4} files, {:>7} loc)",
                child_label,
                format!("[{cat}]"),
                matching.len(),
                total_loc
            );
        }
    }
}

fn measure_file(path: &Path, rel_path: &str) -> SizeMetrics {
    let Ok(bytes_vec) = fs::read(path) else {
        return SizeMetrics::default();
    };
    let text = String::from_utf8_lossy(&bytes_vec);
    let code_lines = count_code_lines(rel_path, &text);
    SizeMetrics {
        files: 1,
        code_lines,
    }
}

/// Count non-empty, non-comment lines in `text`.
pub fn count_code_lines(rel_path: &str, text: &str) -> usize {
    if rel_path.ends_with(".lean") {
        let stripped = crate::lex::strip_comments_and_strings(text);
        return stripped.lines().filter(|l| !l.trim().is_empty()).count();
    }
    let ext = rel_path.rsplit('.').next().unwrap_or("");
    let is_c_or_rust = matches!(ext, "rs" | "c" | "h" | "ts" | "js");
    let is_hash_comment = matches!(ext, "sh" | "toml" | "yml" | "yaml")
        || rel_path.starts_with("scripts/")
        || rel_path.starts_with(".gitignore")
        || rel_path.starts_with(".semgrepignore");
    let mut in_block_comment = false;
    let mut count = 0;
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        if is_c_or_rust {
            if in_block_comment {
                if let Some(idx) = t.find("*/") {
                    in_block_comment = false;
                    let after = t[idx + 2..].trim();
                    if !after.is_empty() && !after.starts_with("//") {
                        count += 1;
                    }
                }
                continue;
            }
            if t.starts_with("//") {
                continue;
            }
            if t.starts_with("/*") {
                if !t.contains("*/") {
                    in_block_comment = true;
                }
                continue;
            }
        } else if is_hash_comment && t.starts_with('#') {
            continue;
        }
        count += 1;
    }
    count
}
