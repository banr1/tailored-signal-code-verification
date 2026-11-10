// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Core repository trust classification (`--tree` / `--tree-json`), import-DAG enforcement
//! (`--check-imports`), and soundness / role-purity guard (`--check`) (`[AUDIT/LINTER]`).
//!
//! # Core Soundness Invariants (Read Top-to-Bottom)
//! 1. **Explicit repository trust categories** ([`tree`], [`policy::TrustCategory`]): every file
//!    and directory in the repository is classified as `tcb`, `case-studies-tcb`, `proof`,
//!    `testing`, `infra`, or `doc` ([`Workspace::trust_tree`]).
//! 2. **Trusted specifications (`tcb` / `case-studies-tcb`) are self-contained and `Theorems` is a
//!    strict sink** ([`Workspace::check_imports`], [`Workspace::check_structure`]):
//!    - Libraries only import libraries at or below them
//!      (`Arm64 < ProofLib < VerifiedLibraries < Examples < Testing`; `Theorems` may import
//!      `Arm64`, `ProofLib`, `VerifiedLibraries`, `Examples`, and `Theorems`, and no other
//!      library may import `Theorems`).
//!    - `Role::Spec` modules (`Arm64/Trusted/`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Spec*`)
//!      only import `Role::Spec` modules—never `proof` (`ProofLib/`, `**/Proofs/`), `Theorems`, or
//!      `testing` (`*/Testing/`) modules.
//!    - Standalone case-study packages (`CaseStudies.<Pkg>.*`) are strictly pairwise independent
//!      and `VerifiedLibraries` never imports `CaseStudies`.
//! 3. **No soundness escapes** ([`Workspace::check_lines`], [`Workspace::check_attributes`]):
//!    - Zero `axiom`, `sorry`, `native_decide`, `unsafe`, `@[implemented_by]`, or `@[extern]`, and
//!      zero `theorem`/`lemma` declarations in `Role::Spec` modules.
//! 4. **`tcb` Rust files are self-contained** ([`Workspace::check_tcb_rust_imports`],
//!    [`tcb_rust_import`]): a `tcb` Rust file never references a non-`tcb` workspace crate or an
//!    `untrusted_*` / `test_infra` / `tests` / `*_tests` module.
//! 5. **Whole-process theorems do not trust library specs**
//!    ([`Workspace::check_whole_process_no_library_specs`]): the trusted `Spec`/`Theorems` closure
//!    of each [`policy::WHOLE_PROCESS_PACKAGES`] package and of `FormalRfcs/` contains no
//!    [`policy::LIBRARY_SPEC_MODULES`] module (Hoare triples, separation logic, placed-library
//!    and override-review predicates).

pub mod discovery;
pub mod lex;
pub use lex as scan;
pub mod policy;
pub mod tcb_rust_import;
pub mod tree;

/// Rule ID reported when an `Arm64/Testing` module references `VerifiedLibraries/` or
/// `CaseStudies/` (or legacy `Examples/`, `Implementation/`, `Theorems/`) file paths.
pub const ARM64_TESTING_DECOUPLING_RULE: &str = "arm64-testing-decoupling";

pub use crate::discovery::module_name_of_path;
use crate::discovery::{standalone_package_of, walk_lean_files};
pub use crate::lex::strip_comments_and_strings;
use crate::lex::{Attribute, ImportEdge, declaration_attributes, extract_imports_from_str};
use crate::policy::{
    ENGINE_INTERNAL_IMPORTS, FORBIDDEN_ATTRIBUTES, LEGACY_LINKED_IMAGE_IMPORTERS, LINE_RULES, Lib,
    ModuleClass, PRIVATE_ONLY_IMPORTS, Role, SPEC_FORBIDDEN_ATTRIBUTES, STDLIB_ROOTS, classify,
    fixture_owner, is_generated, is_spec_macro_syntax_allowed,
};
use anyhow::{Result, anyhow};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

fn has_module_header(code: &str) -> bool {
    code.split_whitespace().next() == Some("module")
}

fn strip_attributes_preserving_lines(code: &str) -> String {
    let bytes = code.as_bytes();
    let mut out = String::with_capacity(code.len());
    let mut i = 0;
    while i < bytes.len() {
        if i + 1 < bytes.len() && bytes[i] == b'@' && bytes[i + 1] == b'[' {
            out.push_str("  ");
            i += 2;
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                let ch = code[i..].chars().next().unwrap();
                if ch == '[' {
                    depth += 1;
                    out.push(' ');
                } else if ch == ']' {
                    depth -= 1;
                    out.push(' ');
                } else if ch == '\n' {
                    out.push('\n');
                } else {
                    out.push(' ');
                }
                i += ch.len_utf8();
            }
        } else {
            let ch = code[i..].chars().next().unwrap();
            out.push(ch);
            i += ch.len_utf8();
        }
    }
    out
}

fn is_theorems_cmd_keyword(tok: &str) -> bool {
    matches!(
        tok,
        "module"
            | "public"
            | "private"
            | "protected"
            | "scoped"
            | "local"
            | "noncomputable"
            | "nonrec"
            | "partial"
            | "unsafe"
            | "import"
            | "open"
            | "export"
            | "section"
            | "namespace"
            | "end"
            | "theorem"
            | "lemma"
            | "def"
            | "abbrev"
            | "structure"
            | "inductive"
            | "class"
            | "instance"
            | "axiom"
            | "opaque"
            | "example"
            | "variable"
            | "universe"
            | "set_option"
            | "attribute"
    )
}

fn has_underscore_segment(ident: &str) -> bool {
    ident.split('.').any(|seg| {
        let trimmed = seg.trim_start_matches('«').trim_end_matches('»');
        trimmed.starts_with('_')
    })
}

fn check_theorems_scopes_and_names(
    module_name: &str,
    code: &str,
    require_public_exports: bool,
) -> Vec<(usize, String)> {
    let cleaned = strip_attributes_preserving_lines(code);
    let mut tokens: Vec<(String, usize)> = Vec::new();
    let mut line = 1usize;
    let mut cur = String::new();
    let mut cur_line = 1usize;
    let is_tok_char = |c: char| {
        c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?' | '.' | '«' | '»')
    };
    for ch in cleaned.chars() {
        if is_tok_char(ch) {
            if cur.is_empty() {
                cur_line = line;
            }
            cur.push(ch);
        } else {
            if !cur.is_empty() {
                tokens.push((std::mem::take(&mut cur), cur_line));
            }
            if ch == '\n' {
                line += 1;
            }
        }
    }
    if !cur.is_empty() {
        tokens.push((cur, cur_line));
    }

    let mut violations = Vec::new();
    let mut scope_public_stack: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i < tokens.len() {
        let (tok, tok_line) = (&tokens[i].0, tokens[i].1);
        match tok.as_str() {
            "section" => {
                let is_pub = i > 0 && tokens[i - 1].0 == "public";
                scope_public_stack.push(is_pub);
                if let Some((next_tok, next_line)) = tokens.get(i + 1)
                    && *next_line == tok_line
                    && !is_theorems_cmd_keyword(next_tok)
                {
                    if has_underscore_segment(next_tok) {
                        violations.push((
                            *next_line,
                            format!(
                                "`section {next_tok}` uses `_`-prefixed internal name in Theorems module"
                            ),
                        ));
                    }
                    i += 1;
                }
            }
            "namespace" => {
                let cur_pub = scope_public_stack.last().copied().unwrap_or(false);
                if let Some((next_tok, next_line)) = tokens.get(i + 1)
                    && !is_theorems_cmd_keyword(next_tok)
                {
                    if has_underscore_segment(next_tok) {
                        violations.push((
                            *next_line,
                            format!(
                                "`namespace {next_tok}` uses `_`-prefixed internal name in Theorems module"
                            ),
                        ));
                    }
                    let depth = next_tok.split('.').filter(|s| !s.is_empty()).count().max(1);
                    for _ in 0..depth {
                        scope_public_stack.push(cur_pub);
                    }
                    i += 1;
                } else {
                    scope_public_stack.push(cur_pub);
                }
            }
            "end" => {
                let pop_count = if let Some((next_tok, next_line)) = tokens.get(i + 1)
                    && *next_line == tok_line
                    && !is_theorems_cmd_keyword(next_tok)
                {
                    let n = next_tok.split('.').filter(|s| !s.is_empty()).count().max(1);
                    i += 1;
                    n
                } else {
                    1
                };
                for _ in 0..pop_count {
                    if scope_public_stack.pop().is_none() && require_public_exports {
                        violations.push((
                            tok_line,
                            format!("unmatched `end` in Theorems module `{module_name}`"),
                        ));
                        break;
                    }
                }
            }
            "theorem" => {
                if let Some((next_tok, next_line)) = tokens.get(i + 1)
                    && has_underscore_segment(next_tok)
                {
                    violations.push((
                        *next_line,
                        format!(
                            "`theorem {next_tok}` uses `_`-prefixed internal name in Theorems module"
                        ),
                    ));
                }
                if require_public_exports {
                    let mut k = i;
                    let mut explicit_pub = false;
                    while k > 0 {
                        let prev = tokens[k - 1].0.as_str();
                        if prev == "public" {
                            explicit_pub = true;
                            break;
                        } else if matches!(
                            prev,
                            "noncomputable" | "protected" | "nonrec" | "unsafe" | "partial"
                        ) {
                            k -= 1;
                        } else {
                            break;
                        }
                    }
                    let in_pub_section = scope_public_stack.last().copied().unwrap_or(false);
                    if !explicit_pub && !in_pub_section {
                        violations.push((
                            tok_line,
                            format!(
                                "Theorems module `{module_name}` with `module` must declare `public section` covering every `theorem` (or mark it `public theorem`)"
                            ),
                        ));
                    }
                }
            }
            _ => {}
        }
        i += 1;
    }
    violations
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    pub path: String,
    pub line: usize,
    pub rule: String,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub path: String,
    pub class: ModuleClass,
    pub code: String,
    pub source: String,
    pub imports: Vec<ImportEdge>,
    pub attributes: Vec<Attribute>,
}

fn parse_module(path: &str, source: String) -> Result<(String, Module)> {
    let name = module_name_of_path(path);
    let class = classify(&name)
        .ok_or_else(|| anyhow!("{path}: not in a known library (add it to `policy::classify`)"))?;
    let code = strip_comments_and_strings(&source);
    let imports = extract_imports_from_str(&code, &source);
    let attributes = declaration_attributes(&code);
    Ok((
        name,
        Module {
            path: path.to_string(),
            class,
            code,
            source,
            imports,
            attributes,
        },
    ))
}

/// All `.lean` modules of the package, keyed by module name.
#[derive(Debug, Clone, Default)]
pub struct Workspace {
    pub modules: BTreeMap<String, Module>,
    /// Package root (set by [`Workspace::load`]; `None` for [`Workspace::from_sources`]).
    pub root: Option<PathBuf>,
    /// Optional text of the `process-inputs-top` allowlist (used by `repo-lints`).
    pub process_inputs_extras: Option<String>,
    /// Whether case-study files and modules were excluded (`--no-case-studies`).
    pub no_case_studies: bool,
}

impl Workspace {
    /// Build a workspace from `(repo-relative path, source)` pairs.
    pub fn from_sources<'a>(sources: impl IntoIterator<Item = (&'a str, &'a str)>) -> Result<Self> {
        let mut modules = BTreeMap::new();
        for (path, source) in sources {
            let (name, module) = parse_module(path, source.to_string())?;
            modules.insert(name, module);
        }
        Ok(Self {
            modules,
            root: None,
            process_inputs_extras: None,
            no_case_studies: false,
        })
    }

    /// Use `text` as the `process-inputs-top` allowlist (consumed by `repo-lints`).
    pub fn with_process_inputs_extras(mut self, text: &str) -> Self {
        self.process_inputs_extras = Some(text.to_string());
        self
    }

    /// Load every `.lean` module under the package root `root`.
    pub fn load(root: &Path) -> Result<Self> {
        Self::load_filtered(root, false)
    }

    /// Load `.lean` modules under `root`, optionally excluding case-study paths
    /// ([`policy::is_case_study_path`]).
    pub fn load_filtered(root: &Path, no_case_studies: bool) -> Result<Self> {
        let mut paths = walk_lean_files(root)?;
        if no_case_studies {
            paths.retain(|rel| !policy::is_case_study_path(rel));
        }
        paths.sort_by_cached_key(|rel| {
            std::cmp::Reverse(fs::metadata(root.join(rel)).map(|m| m.len()).unwrap_or(0))
        });
        let n_threads = std::thread::available_parallelism()
            .map(|n| n.get().min(8))
            .unwrap_or(4)
            .min(paths.len())
            .max(1);
        let next = std::sync::atomic::AtomicUsize::new(0);
        let parsed: Mutex<Vec<(String, Module)>> = Mutex::new(Vec::with_capacity(paths.len()));
        std::thread::scope(|s| -> Result<()> {
            let handles: Vec<_> = (0..n_threads)
                .map(|_| {
                    let paths = &paths;
                    let next = &next;
                    let parsed = &parsed;
                    s.spawn(move || -> Result<()> {
                        let mut local = Vec::new();
                        loop {
                            let idx = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if idx >= paths.len() {
                                break;
                            }
                            let rel = &paths[idx];
                            let text = fs::read_to_string(root.join(rel))?;
                            local.push(parse_module(rel, text)?);
                        }
                        parsed.lock().unwrap().extend(local);
                        Ok(())
                    })
                })
                .collect();
            for h in handles {
                h.join().expect("lean workspace loader thread panicked")?;
            }
            Ok(())
        })?;
        let modules: BTreeMap<String, Module> = parsed.into_inner().unwrap().into_iter().collect();
        Ok(Self {
            modules,
            root: Some(root.to_path_buf()),
            process_inputs_extras: None,
            no_case_studies,
        })
    }

    pub fn total_edges(&self) -> usize {
        self.modules.values().map(|m| m.imports.len()).sum()
    }

    /// Build the directory-hierarchy trust report (`tcb`, `case-studies-tcb`, `proof`, `testing`,
    /// `infra`, `doc`).
    pub fn trust_tree(&self) -> Result<tree::TreeReport> {
        match &self.root {
            Some(root) => {
                let lean_code: HashMap<&str, &str> = self
                    .modules
                    .values()
                    .map(|m| (m.path.as_str(), m.code.as_str()))
                    .collect();
                tree::TreeReport::build_with_lean_filtered(root, &lean_code, self.no_case_studies)
            }
            None => Ok(tree::TreeReport::from_file_metrics_filtered(
                self.modules.values().map(|m| {
                    (
                        m.path.clone(),
                        tree::SizeMetrics {
                            files: 1,
                            code_lines: m.source.lines().count(),
                        },
                    )
                }),
                self.no_case_studies,
            )),
        }
    }

    /// Check only unclassified-path violations under `self.root` without reading or counting files.
    pub fn trust_tree_violations(&self) -> Result<Vec<Violation>> {
        match &self.root {
            Some(root) => tree::TreeReport::check_violations(root),
            None => Ok(Vec::new()),
        }
    }

    /// Run Lean and Rust import-DAG checks (`check_imports` + `check_tcb_rust_imports`).
    pub fn check_imports_all(&self) -> Vec<Violation> {
        std::thread::scope(|s| {
            let imports_job = s.spawn(|| self.check_imports());
            let tcb_rust_job = s.spawn(|| self.check_tcb_rust_imports());
            let mut v = imports_job.join().expect("check_imports panicked");
            v.extend(
                tcb_rust_job
                    .join()
                    .expect("check_tcb_rust_imports panicked"),
            );
            v
        })
    }

    /// Run all core `tcb-map` soundness & role-purity checks:
    /// 1. Core TCB import self-containment & library layering (`check_imports`)
    /// 2. `Spec` / `Theorems` role structure & naming (`check_structure`)
    /// 3. Forbidden line constructs & attributes (`check_lines`, `check_attributes`)
    /// 4. No references from `tcb` Rust files to non-`tcb` crates or `untrusted_*` / test modules
    ///    (`check_tcb_rust_imports`)
    /// 5. Whole-process packages do not trust library-spec modules
    ///    (`check_whole_process_no_library_specs`)
    pub fn check_all(&self) -> Vec<Violation> {
        self.check_all_with_prefilter(true)
    }

    /// Run all core checks with literal pre-filtering either enabled (`prefilter = true`) or
    /// disabled (`prefilter = false`).
    pub fn check_all_with_prefilter(&self, prefilter: bool) -> Vec<Violation> {
        std::thread::scope(|s| {
            let imports_job = s.spawn(|| self.check_imports());
            let structure_job = s.spawn(|| self.check_structure());
            let lines_job = s.spawn(|| self.check_lines_with_prefilter(prefilter));
            let attrs_job = s.spawn(|| self.check_attributes());
            let tcb_rust_job = s.spawn(|| self.check_tcb_rust_imports());
            let arm64_testing_job = s.spawn(|| self.check_arm64_testing_decoupling());
            let whole_process_job = s.spawn(|| self.check_whole_process_no_library_specs());

            let mut v = imports_job.join().expect("check_imports panicked");
            v.extend(structure_job.join().expect("check_structure panicked"));
            v.extend(lines_job.join().expect("check_lines panicked"));
            v.extend(attrs_job.join().expect("check_attributes panicked"));
            v.extend(
                tcb_rust_job
                    .join()
                    .expect("check_tcb_rust_imports panicked"),
            );
            v.extend(
                arm64_testing_job
                    .join()
                    .expect("check_arm64_testing_decoupling panicked"),
            );
            v.extend(
                whole_process_job
                    .join()
                    .expect("check_whole_process_no_library_specs panicked"),
            );
            v
        })
    }

    /// Invariant 2a: `Role::Spec` modules only import `Role::Spec` modules, `Role::Theorems`
    /// is a sink over `Spec` and `Proof`, and libraries respect
    /// `Arm64 < ProofLib < VerifiedLibraries < Examples < Testing`.
    pub fn check_imports(&self) -> Vec<Violation> {
        let mut violations = Vec::new();
        for (name, m) in &self.modules {
            if m.class.lib == Lib::Arm64
                && m.class.role == Role::Spec
                && policy::classify_trusted_tcb_module(name).is_none()
            {
                violations.push(Violation {
                    path: m.path.clone(),
                    line: 1,
                    rule: format!(
                        "core-tcb-init-only: unclassified `Arm64` TCB module `{name}`; place semantic core modules under `Arm64/Trusted/{{ISA,Object,Process,Syscalls,Spec}}/` and surface macro/elaborator modules under `Arm64/Trusted/Surface/`"
                    ),
                    text: m.source.lines().next().unwrap_or_default().to_string(),
                });
            }
            for edge in &m.imports {
                let root = edge.imported.split('.').next().unwrap_or_default();
                let mut report = |rule: String| {
                    violations.push(Violation {
                        path: m.path.clone(),
                        line: edge.line,
                        rule,
                        text: edge.raw_line.clone(),
                    });
                };
                if STDLIB_ROOTS.contains(&root) {
                    if policy::is_core_tcb_init_only(name) && root != "Init" {
                        report(format!(
                            "core-tcb-init-only: semantic core module `{name}` must remain `Init`-only and may not import `{}` (put elaborators in `Arm64.Trusted.Surface.*` or metaprogramming instances in `ProofLib.Meta.*`)",
                            edge.imported
                        ));
                    }
                    continue;
                }
                if policy::is_core_tcb_init_only(name)
                    && !policy::is_core_tcb_init_only(&edge.imported)
                {
                    report(format!(
                        "core-tcb-init-only: semantic core module `{name}` may only import `Init` or other `Init`-only semantic core modules, not `{}`",
                        edge.imported
                    ));
                }
                let Some(target) = classify(&edge.imported) else {
                    report(format!("import of unknown library `{}`", edge.imported));
                    continue;
                };
                if !self.modules.contains_key(&edge.imported)
                    && !is_generated(&edge.imported)
                    && !(self.no_case_studies
                        && matches!(
                            target.lib,
                            Lib::Equivalence
                                | Lib::VerifiedLibraries
                                | Lib::FormalRfcs
                                | Lib::Examples
                                | Lib::Theorems
                        ))
                {
                    report(format!("unresolved import `{}`", edge.imported));
                }
                if !m.class.lib.may_import(target.lib) {
                    report(format!(
                        "layering: `{name}` ({:?}) may not import `{}` ({:?})",
                        m.class.lib, edge.imported, target.lib
                    ));
                }
                if m.class.role == Role::Spec && target.role != Role::Spec {
                    report(format!(
                        "{:?} module `{name}` may only import Spec modules, not `{}` ({target})",
                        m.class.role, edge.imported
                    ));
                }
                if m.class.role == Role::Theorems {
                    if !matches!(target.role, Role::Spec | Role::Proof | Role::Theorems) {
                        report(format!(
                            "Theorems module `{name}` may only import Spec, Proof, or Theorems modules, not `{}` ({target})",
                            edge.imported
                        ));
                    }
                    if edge.is_meta {
                        report(format!(
                            "Theorems module `{name}` may not `meta import` `{}`",
                            edge.imported
                        ));
                    }
                    if target.role == Role::Proof && edge.is_public {
                        report(format!(
                            "Theorems module `{name}` must use private `import` (not `public import`) for Proof module `{}` so Proof declarations cannot enter public theorem statement types",
                            edge.imported
                        ));
                    } else if has_module_header(&m.code)
                        && matches!(target.role, Role::Spec | Role::Theorems)
                        && !edge.is_public
                    {
                        report(format!(
                            "Theorems module `{name}` must use `public import` for {:?} module `{}`",
                            target.role, edge.imported
                        ));
                    }
                }
                if ENGINE_INTERNAL_IMPORTS.contains(&edge.imported.as_str())
                    && !(matches!(m.class.lib, Lib::Arm64 | Lib::ProofLib)
                        || name.starts_with("Arm64.Testing."))
                {
                    report(format!(
                        "`{}` may only be imported by `Arm64.*` or `ProofLib.*`, not `{name}` (use sanctioned ProofLib/SepLogic lemmas)",
                        edge.imported
                    ));
                }
                if PRIVATE_ONLY_IMPORTS.contains(&edge.imported.as_str()) && edge.is_public {
                    report(format!(
                        "`{}` must be imported privately (`import`, not `public import`) by `{name}` so its lemmas are not re-exported",
                        edge.imported
                    ));
                }
                if edge.is_all
                    && target.role != Role::Fixture
                    && !(matches!(m.class.lib, Lib::Arm64 | Lib::ProofLib)
                        || name.starts_with("Arm64.Testing."))
                {
                    report(format!(
                        "`import all` (`{}`) is only allowed in `Arm64.*` or `ProofLib.*`, not `{name}` (use sanctioned ProofLib lemmas)",
                        edge.imported
                    ));
                }
                if target.role == Role::Fixture && name != fixture_owner(&edge.imported) {
                    report(format!(
                        "fixture `{}` may only be imported by `{}`",
                        edge.imported,
                        fixture_owner(&edge.imported)
                    ));
                }
                if edge.imported.starts_with("Arm64.Testing.Tours.")
                    && edge.imported.ends_with("Tour")
                    && name != "Arm64.Testing"
                {
                    report(format!(
                        "tour `{}` may only be imported by `Arm64.Testing`, not `{name}` (use `ProofLib` lemmas)",
                        edge.imported
                    ));
                }
                if (m.path == "VerifiedLibraries.lean"
                    || m.path.starts_with("VerifiedLibraries/")
                    || name == "VerifiedLibraries"
                    || name.starts_with("VerifiedLibraries."))
                    && matches!(root, "CaseStudies" | "FormalRfcs")
                {
                    report(format!(
                        "package-isolation: VerifiedLibraries module `{name}` may not import `{}` (`VerifiedLibraries/` may only import `Arm64`, `ProofLib`, standard library, and `VerifiedLibraries.*`)",
                        edge.imported
                    ));
                }
                if (edge.imported == "Arm64.Legacy" || edge.imported.starts_with("Arm64.Legacy."))
                    && name != "Arm64.Legacy"
                    && !name.starts_with("Arm64.Legacy.")
                    && !LEGACY_LINKED_IMAGE_IMPORTERS.contains(&name.as_str())
                {
                    report(format!(
                        "legacy-linked-image-import: `{}` is deprecated `[OUTSIDE TCB]` compatibility infrastructure and may only be imported by `Arm64.Legacy.*` or `LEGACY_LINKED_IMAGE_IMPORTERS`, not `{name}` (use `Obj.PlacedLib` / `Obj.MultiPlacedLib`)",
                        edge.imported
                    ));
                }
                if let Some(own_pkg) = standalone_package_of(name)
                    && let Some(target_pkg) = standalone_package_of(&edge.imported)
                    && target_pkg != own_pkg
                {
                    report(format!(
                        "package-isolation: standalone case study `{name}` (`{}`) may not import sibling package `{}` (`{}`) (case studies and per-implementation formal RFC packages are pairwise independent; share pure specs via `VerifiedLibraries/Common/Spec/` or `FormalRfcs/<Rfc>/Spec/` and verified libraries via `VerifiedLibraries/`)",
                        own_pkg.replace('.', "/"),
                        edge.imported,
                        target_pkg.replace('.', "/")
                    ));
                }
                if name.starts_with("FormalRfcs.") {
                    let under = |prefix: &str| {
                        edge.imported == prefix
                            || edge
                                .imported
                                .strip_prefix(prefix)
                                .is_some_and(|rest| rest.starts_with('.'))
                    };
                    if let Some(own_pkg) = standalone_package_of(name) {
                        let rfc_prefix = own_pkg.rsplit_once('.').map_or("", |(rfc, _)| rfc);
                        let rfc_spec = format!("{rfc_prefix}.Spec");
                        if matches!(m.class.role, Role::Spec | Role::Theorems) {
                            if !(root == "Arm64"
                                || under("FormalRfcs.Common.Spec")
                                || under(&rfc_spec)
                                || under(&own_pkg))
                            {
                                report(format!(
                                    "package-isolation: trusted formal RFC implementation module `{name}` may only import `FormalRfcs.Common.Spec.*`, `{rfc_spec}.*`, its own package `{own_pkg}.*`, `Arm64.*`, and the standard library, not `{}`",
                                    edge.imported
                                ));
                            }
                        } else if matches!(m.class.role, Role::Proof | Role::Test | Role::Fixture)
                            && standalone_package_of(&edge.imported).is_none()
                            && (matches!(root, "CaseStudies" | "Examples")
                                || (root == "FormalRfcs"
                                    && !under("FormalRfcs.Common")
                                    && !under(rfc_prefix)))
                        {
                            report(format!(
                                "package-isolation: formal RFC implementation module `{name}` (`{own_pkg}`) may not import cross-RFC or case-study module `{}` (may only import `FormalRfcs.Common.*`, `{rfc_prefix}.*`, and shared engine/library packages)",
                                edge.imported
                            ));
                        }
                    } else {
                        let rfc = name.split('.').nth(1).unwrap_or("");
                        let rfc_prefix = format!("FormalRfcs.{rfc}");
                        if rfc == "Common" {
                            if matches!(root, "CaseStudies" | "Examples")
                                || standalone_package_of(&edge.imported).is_some()
                                || (root == "FormalRfcs" && !under("FormalRfcs.Common"))
                            {
                                report(format!(
                                    "package-isolation: FormalRfcs.Common module `{name}` may not import `{}` (`FormalRfcs/Common/` may only import `FormalRfcs.Common.*` and shared engine/library packages)",
                                    edge.imported
                                ));
                            }
                        } else if matches!(root, "CaseStudies" | "Examples")
                            || standalone_package_of(&edge.imported).is_some()
                            || (root == "FormalRfcs"
                                && !under("FormalRfcs.Common")
                                && !under(&rfc_prefix))
                        {
                            report(format!(
                                "package-isolation: formal RFC module `{name}` (`{rfc_prefix}`) may not import cross-RFC, implementation, or case-study module `{}` (may only import `FormalRfcs.Common.*`, RFC-level `{rfc_prefix}.*`, and shared engine/library packages)",
                                edge.imported
                            ));
                        }
                    }
                }
            }
        }
        if self.root.is_some() && self.modules.contains_key("Arm64.Legacy") {
            for &allowed in LEGACY_LINKED_IMAGE_IMPORTERS {
                let Some(m) = self.modules.get(allowed) else {
                    violations.push(Violation {
                        path: "tools/tcb-map/src/policy.rs".to_string(),
                        line: 1,
                        rule: format!(
                            "stale-legacy-allowlist: `{allowed}` in `LEGACY_LINKED_IMAGE_IMPORTERS` no longer exists; remove it so the allowlist shrinks monotonically"
                        ),
                        text: allowed.to_string(),
                    });
                    continue;
                };
                if !m.imports.iter().any(|e| {
                    e.imported == "Arm64.Legacy" || e.imported.starts_with("Arm64.Legacy.")
                }) {
                    violations.push(Violation {
                        path: m.path.clone(),
                        line: 1,
                        rule: format!(
                            "stale-legacy-allowlist: `{allowed}` no longer directly imports `Arm64.Legacy*`; remove it from `LEGACY_LINKED_IMAGE_IMPORTERS`"
                        ),
                        text: allowed.to_string(),
                    });
                }
            }
        }
        violations
    }

    /// Invariant 2b: `Spec` naming (`Foo/Spec.lean`), `ProofLib` `Spec` name ban, and
    /// `Role::Theorems` structural/scope/name/header checks.
    pub fn check_structure(&self) -> Vec<Violation> {
        let mut violations = Vec::new();
        for (name, m) in &self.modules {
            if m.class.role == Role::Theorems {
                let is_mod = has_module_header(&m.code);
                for (v_line, v_rule) in check_theorems_scopes_and_names(name, &m.code, is_mod) {
                    let snippet = m
                        .source
                        .lines()
                        .nth(v_line.saturating_sub(1))
                        .unwrap_or("")
                        .trim()
                        .to_string();
                    violations.push(Violation {
                        path: m.path.clone(),
                        line: v_line,
                        rule: v_rule,
                        text: snippet,
                    });
                }
            }
            let mut report = |rule: String, text: String| {
                violations.push(Violation {
                    path: m.path.clone(),
                    line: 1,
                    rule,
                    text,
                });
            };
            if name.ends_with("Spec") && !name.ends_with(".Spec") {
                report(
                    "non-uniform Spec filename (use `Foo/Spec.lean`, not `FooSpec.lean`)".into(),
                    m.path.clone(),
                );
            }
            if m.class.role == Role::Spec
                && matches!(m.class.lib, Lib::Examples | Lib::VerifiedLibraries)
                && (name.ends_with(".Spec.Cli") || name.contains(".Spec.Cli."))
            {
                report(
                    "non-uniform top-level Spec filename (use `Spec/Top.lean` as the top-level specification, not `Spec/Cli.lean`)".into(),
                    m.path.clone(),
                );
            }
            if m.class.lib == Lib::ProofLib && name.split('.').any(|p| p == "Spec") {
                report(
                    "ProofLib module named `Spec` (ProofLib is untrusted `Proof`; move trusted spec vocabulary to `Arm64/Trusted/Spec/`)".into(),
                    m.path.clone(),
                );
            }
            if m.class.role == Role::Theorems {
                if name.split('.').any(|seg| {
                    seg == "Testing"
                        || seg == "Fixtures"
                        || seg
                            .trim_start_matches('«')
                            .trim_end_matches('»')
                            .starts_with('_')
                }) {
                    report(
                        format!(
                            "Theorems module `{name}` may not contain `Testing`, `Fixtures`, or `_`-prefixed path components"
                        ),
                        m.path.clone(),
                    );
                }
                let in_repo_imports: Vec<_> = m
                    .imports
                    .iter()
                    .filter(|edge| {
                        let root = edge.imported.split('.').next().unwrap_or("");
                        !STDLIB_ROOTS.contains(&root)
                    })
                    .collect();
                if !in_repo_imports.is_empty()
                    && in_repo_imports.iter().all(|edge| {
                        self.modules
                            .get(&edge.imported)
                            .is_some_and(|imp| has_module_header(&imp.code))
                    })
                    && !has_module_header(&m.code)
                {
                    report(
                        format!(
                            "Theorems module `{name}` must start with `module` when all imported modules use `module`"
                        ),
                        m.path.clone(),
                    );
                }
            }
        }
        violations
    }

    /// Invariant 3a: forbidden line constructs (`axiom`, `sorry`, `native_decide`, `unsafe`,
    /// `theorem`/`lemma` in `Spec`, non-`theorem` declarations in `Theorems`, etc.).
    pub fn check_lines(&self) -> Vec<Violation> {
        self.check_lines_with_prefilter(true)
    }

    /// Run Invariant 3a with literal token pre-filtering enabled (`prefilter = true`) or disabled
    /// (`prefilter = false`, matching every applicable rule regex against every line directly).
    pub fn check_lines_with_prefilter(&self, prefilter: bool) -> Vec<Violation> {
        self.check_lines_with_rules(&LINE_RULES, prefilter)
    }

    /// Evaluate an arbitrary slice of [`policy::LineRule`]s across all modules in the workspace.
    pub fn check_lines_with_rules(
        &self,
        line_rules: &[policy::LineRule],
        prefilter: bool,
    ) -> Vec<Violation> {
        let mut rule_cache: HashMap<
            (u8, u8, bool, bool, bool),
            (Vec<&policy::LineRule>, regex::Regex),
        > = HashMap::new();
        let mut violations = Vec::new();
        for m in self.modules.values() {
            let is_arm64_testing = m.path.starts_with("Arm64/Testing");
            let is_prooflib_testing = m.path.starts_with("ProofLib/Testing");
            let is_surface_spec = is_spec_macro_syntax_allowed(&m.path);
            let (rules, trigger_re) = rule_cache
                .entry((
                    m.class.lib as u8,
                    m.class.role as u8,
                    is_arm64_testing,
                    is_prooflib_testing,
                    is_surface_spec,
                ))
                .or_insert_with(|| {
                    let applicable: Vec<_> = line_rules
                        .iter()
                        .filter(|r| r.scope.applies_in(m.class, &m.path))
                        .collect();
                    let mut uniq = BTreeSet::new();
                    for r in &applicable {
                        for &t in r.triggers {
                            uniq.insert(regex::escape(t));
                        }
                    }
                    let pat = uniq.into_iter().collect::<Vec<_>>().join("|");
                    let fast_re = regex::Regex::new(&pat).expect("valid literal trigger regex");
                    (applicable, fast_re)
                });
            if rules.is_empty() || (prefilter && !trigger_re.is_match(&m.code)) {
                continue;
            }
            let raw_lines: Vec<&str> = m.source.lines().collect();
            let code_lines: Vec<&str> = m.code.lines().collect();
            for (idx, &line) in code_lines.iter().enumerate() {
                if prefilter && !trigger_re.is_match(line) {
                    continue;
                }
                let joined_attr;
                let candidate_line = if line.contains("attribute") {
                    let mut buf = line.to_string();
                    let mut code_cont_lines = 0usize;
                    for (offset, &next) in code_lines[idx + 1..].iter().take(256).enumerate() {
                        let next_idx = idx + 1 + offset;
                        let next_raw = raw_lines.get(next_idx).copied().unwrap_or(next);
                        let next_raw_indent = next_raw.len() - next_raw.trim_start().len();
                        let trimmed = next.trim();
                        if next_raw.trim().is_empty() {
                            break;
                        }
                        if trimmed.is_empty() {
                            continue;
                        }
                        if !(next.starts_with(' ') || next.starts_with('\t'))
                            || [
                                "theorem ",
                                "lemma ",
                                "private ",
                                "protected ",
                                "public ",
                                "noncomputable ",
                                "def ",
                                "abbrev ",
                                "structure ",
                                "inductive ",
                                "class ",
                                "instance ",
                                "axiom ",
                                "opaque ",
                                "section ",
                                "namespace ",
                                "end ",
                                "open ",
                                "variable ",
                                "set_option ",
                                "attribute ",
                                "deriving ",
                                "@[",
                                "#",
                                "/--",
                            ]
                            .iter()
                            .any(|kw| trimmed.starts_with(kw))
                        {
                            break;
                        }
                        buf.push(' ');
                        buf.push_str(next[next_raw_indent.min(next.len())..].trim_end());
                        code_cont_lines += 1;
                        if code_cont_lines >= 32 {
                            break;
                        }
                    }
                    joined_attr = buf;
                    joined_attr.as_str()
                } else {
                    line
                };
                for rule in rules.iter() {
                    if !rule.allowlist.is_empty() && rule.allowlist.contains(&m.path.as_str()) {
                        continue;
                    }
                    if prefilter && !rule.triggers.iter().any(|t| candidate_line.contains(t)) {
                        continue;
                    }
                    if let Some(caps) = rule.pattern.captures(candidate_line) {
                        let mut msg = String::new();
                        caps.expand(rule.message, &mut msg);
                        violations.push(Violation {
                            path: m.path.clone(),
                            line: idx + 1,
                            rule: msg,
                            text: raw_lines
                                .get(idx)
                                .map(|s| s.trim().to_string())
                                .unwrap_or_default(),
                        });
                    }
                }
            }
        }
        violations
    }

    /// Invariant 3b: forbidden declaration attributes (`@[implemented_by]`, `@[extern]`, and
    /// elaborator/macro/parser attributes in `Spec` and `Theorems` modules).
    pub fn check_attributes(&self) -> Vec<Violation> {
        let mut violations = Vec::new();
        for m in self.modules.values() {
            let check_spec_attrs = matches!(m.class.role, Role::Spec | Role::Theorems)
                && !is_spec_macro_syntax_allowed(&m.path);
            for attr in &m.attributes {
                let base = attr.name.rsplit('.').next().unwrap_or(&attr.name);
                if let Some((name, reason)) = FORBIDDEN_ATTRIBUTES
                    .iter()
                    .find(|(n, _)| *n == attr.name || *n == base)
                {
                    violations.push(Violation {
                        path: m.path.clone(),
                        line: attr.line,
                        rule: format!("@[{name}] ({reason})"),
                        text: m
                            .source
                            .lines()
                            .nth(attr.line - 1)
                            .map(|s| s.trim().to_string())
                            .unwrap_or_default(),
                    });
                } else if check_spec_attrs
                    && let Some((name, reason)) = SPEC_FORBIDDEN_ATTRIBUTES
                        .iter()
                        .find(|(n, _)| *n == attr.name || *n == base)
                {
                    violations.push(Violation {
                        path: m.path.clone(),
                        line: attr.line,
                        rule: format!("@[{name}] in {:?} module ({reason})", m.class.role),
                        text: m
                            .source
                            .lines()
                            .nth(attr.line - 1)
                            .map(|s| s.trim().to_string())
                            .unwrap_or_default(),
                    });
                }
            }
        }
        violations
    }

    /// Invariant 4: `tcb` Rust files reference no non-`tcb` workspace crate and no
    /// `untrusted_*` / `test_infra` / `tests` / `*_tests` module (empty without a root).
    pub fn check_tcb_rust_imports(&self) -> Vec<Violation> {
        let Some(root) = self.root.as_deref() else {
            return Vec::new();
        };
        tcb_rust_import::check(root).unwrap_or_else(|e| {
            vec![Violation {
                path: root.display().to_string(),
                line: 0,
                rule: tcb_rust_import::RULE.to_string(),
                text: format!("failed to scan Rust sources: {e:#}"),
            }]
        })
    }

    /// Invariant 5: `Arm64/Testing` modules (`Lib::Arm64Testing`) never reference file paths under
    /// `Examples/`, `Implementation/`, `VerifiedLibraries/`, `CaseStudies/`, or `Theorems/` (so the
    /// standalone `Arm64/Testing` Lake package builds and runs with zero dependency on verified
    /// libraries, case studies, or example fixtures).
    pub fn check_arm64_testing_decoupling(&self) -> Vec<Violation> {
        const FORBIDDEN_PATH_PREFIXES: &[(&str, &str)] = &[
            ("Examples/", "Examples/"),
            ("Implementation/", "Implementation/"),
            ("VerifiedLibraries/", "VerifiedLibraries/"),
            ("CaseStudies/", "CaseStudies/"),
            ("Theorems/", "Theorems/"),
            ("../Examples/", "Examples/"),
            ("../Implementation/", "Implementation/"),
            ("../VerifiedLibraries/", "VerifiedLibraries/"),
            ("../CaseStudies/", "CaseStudies/"),
            ("../Theorems/", "Theorems/"),
        ];
        let mut violations = Vec::new();
        for m in self.modules.values() {
            if m.class.lib != Lib::Arm64Testing {
                continue;
            }
            for (idx, line) in m.source.lines().enumerate() {
                let code_part = line.split("--").next().unwrap_or("");
                for &(needle, label) in FORBIDDEN_PATH_PREFIXES {
                    if code_part.contains(needle) {
                        violations.push(Violation {
                            path: m.path.clone(),
                            line: idx + 1,
                            rule: ARM64_TESTING_DECOUPLING_RULE.to_string(),
                            text: format!(
                                "`Arm64/Testing` module `{}` references `{label}` (`{}`); keep `Arm64/Testing` self-contained or move the test to `CaseStudies/<Lib>/Testing/`",
                                m.path,
                                line.trim()
                            ),
                        });
                        break;
                    }
                }
            }
        }
        violations
    }

    /// Trusted closure of `CaseStudies/<pkg>`: every module reachable from the package's
    /// `Spec`/`Theorems` modules along trusted edges only (an edge is followed when both ends are
    /// `Role::Spec` or `Role::Theorems`, so `Theorems`' private `Proof` imports are not
    /// Trusted (`Role::Spec` or `Role::Theorems`) transitive import closure under module root
    /// `mod_root` (`CaseStudies.<Pkg>` or `FormalRfcs`; `Role::Proof` edges such as a `Theorems`
    /// module's private `import` are not followed). Generated object modules are followed through
    /// their fixed emitted header ([`policy::generated_spec_imports`]). Maps each reached module
    /// to the module that first imported it (`None` for the root's own seeds).
    fn trusted_closure_under(&self, mod_root: &str) -> BTreeMap<String, Option<String>> {
        let trusted = |name: &str| {
            classify(name).is_some_and(|c| matches!(c.role, Role::Spec | Role::Theorems))
        };
        let prefix = format!("{mod_root}.");
        let mut parent: BTreeMap<String, Option<String>> = BTreeMap::new();
        let mut stack: Vec<String> = Vec::new();
        for (name, m) in &self.modules {
            if (name.starts_with(&prefix) || name == mod_root)
                && matches!(m.class.role, Role::Spec | Role::Theorems)
            {
                parent.insert(name.clone(), None);
                stack.push(name.clone());
            }
        }
        while let Some(name) = stack.pop() {
            let imports: Vec<&str> = match self.modules.get(&name) {
                Some(m) => m.imports.iter().map(|e| e.imported.as_str()).collect(),
                None => policy::generated_spec_imports(&name)
                    .map(<[&str]>::to_vec)
                    .unwrap_or_default(),
            };
            for imp in imports {
                if trusted(imp) && !parent.contains_key(imp) {
                    parent.insert(imp.to_string(), Some(name.clone()));
                    stack.push(imp.to_string());
                }
            }
        }
        parent
    }

    /// Trusted (`Role::Spec` or `Role::Theorems`) transitive import closure of `CaseStudies.<pkg>`.
    pub fn whole_process_trusted_closure(&self, pkg: &str) -> BTreeMap<String, Option<String>> {
        self.trusted_closure_under(&format!("CaseStudies.{pkg}"))
    }

    /// Trusted (`Role::Spec` or `Role::Theorems`) transitive import closure of `FormalRfcs`.
    pub fn formal_rfcs_trusted_closure(&self) -> BTreeMap<String, Option<String>> {
        self.trusted_closure_under("FormalRfcs")
    }

    /// Line count of the `Arm64` (engine) modules in a trusted closure.
    pub fn engine_closure_lines<'a>(
        &self,
        closure: impl IntoIterator<Item = &'a String>,
    ) -> (usize, usize) {
        closure
            .into_iter()
            .filter_map(|n| self.modules.get(n))
            .filter(|m| m.class.lib == Lib::Arm64)
            .fold((0, 0), |(k, l), m| (k + 1, l + m.source.lines().count()))
    }

    /// Invariant 6: the trusted closure of each [`policy::WHOLE_PROCESS_PACKAGES`] package and of
    /// `FormalRfcs` contains no [`policy::LIBRARY_SPEC_MODULES`] module, so whole-process theorems
    /// do not trust Hoare-triple or separation-logic definitions. A listed target whose directory
    /// exists on disk with no `Spec` or `Theorems` modules fails closed (e.g. after a rename).
    pub fn check_whole_process_no_library_specs(&self) -> Vec<Violation> {
        let mut violations = Vec::new();
        let mut targets: Vec<(String, BTreeMap<String, Option<String>>, bool)> =
            policy::WHOLE_PROCESS_PACKAGES
                .iter()
                .map(|&pkg| {
                    let dir_exists = self
                        .root
                        .as_ref()
                        .is_some_and(|r| r.join("CaseStudies").join(pkg).is_dir());
                    (
                        format!("CaseStudies/{pkg}"),
                        self.whole_process_trusted_closure(pkg),
                        dir_exists,
                    )
                })
                .collect();
        let formal_rfcs_exists = self
            .root
            .as_ref()
            .is_some_and(|r| r.join("FormalRfcs").is_dir());
        targets.push((
            "FormalRfcs".to_string(),
            self.formal_rfcs_trusted_closure(),
            formal_rfcs_exists,
        ));
        for (display, closure, dir_exists) in targets {
            if closure.is_empty() {
                if dir_exists && !self.no_case_studies {
                    violations.push(Violation {
                        path: "tools/tcb-map/src/policy.rs".to_string(),
                        line: 1,
                        rule: policy::WHOLE_PROCESS_NO_LIBRARY_SPECS_RULE.to_string(),
                        text: format!(
                            "`{display}` in whole-process closure check has no `Spec`/`Theorems` modules; update the list"
                        ),
                    });
                }
                continue;
            }
            for &lib_mod in policy::LIBRARY_SPEC_MODULES {
                if !closure.contains_key(lib_mod) {
                    continue;
                }
                let mut chain = vec![lib_mod.to_string()];
                while let Some(Some(p)) = closure.get(chain.last().unwrap()) {
                    chain.push(p.clone());
                }
                chain.reverse();
                let importer = &chain[chain.len() - 2];
                let path = self
                    .modules
                    .get(importer)
                    .map_or_else(|| importer.clone(), |m| m.path.clone());
                violations.push(Violation {
                    path,
                    line: 1,
                    rule: policy::WHOLE_PROCESS_NO_LIBRARY_SPECS_RULE.to_string(),
                    text: format!(
                        "whole-process package `{display}` trusts library-spec module `{lib_mod}` via {}; import the specific whole-process modules (e.g. `Arm64.Trusted.Process`) instead",
                        chain.join(" -> ")
                    ),
                });
            }
        }
        violations
    }

    /// Format a violation list into `(stdout, stderr, ok)` streams.
    pub fn format_violations(
        &self,
        violations: &[Violation],
        tree_report: Option<&tree::TreeReport>,
        in_github_actions: bool,
    ) -> FormattedReport {
        let mut stdout = String::new();
        let mut stderr = String::new();
        if !violations.is_empty() {
            for v in violations {
                let message = if v.rule == tree::RULE
                    || v.rule == tcb_rust_import::RULE
                    || v.rule == ARM64_TESTING_DECOUPLING_RULE
                    || v.rule == "inline-test-in-tcb"
                    || v.rule == "native-cflags-sync"
                    || v.rule == "deprecated-prooflib"
                    || v.rule == "process-inputs-top"
                    || v.rule == "ctype-spec-guard"
                    || v.rule.starts_with("hook-")
                    || v.rule.starts_with("fn-")
                {
                    format!("[{}]: {}", v.rule, v.text)
                } else {
                    format!("forbidden construct [{}]: {}", v.rule, v.text)
                };
                if in_github_actions {
                    stdout.push_str(&format!(
                        "::error file={},line={}::{}\n",
                        v.path, v.line, message
                    ));
                }
                stderr.push_str(&format!("{}:{}: {}\n", v.path, v.line, message));
            }
            stderr.push_str(&format!(
                "\nTrust guard FAILED: {} violation(s) across {} Lean module(s).\n",
                violations.len(),
                self.modules.len(),
            ));
            return FormattedReport {
                stdout,
                stderr,
                ok: false,
            };
        }

        if let Some(report) = tree_report {
            stdout.push_str(&format!("{}\n", report.render()));
        }
        stdout.push_str(&format!(
            "Trust guard OK: {} Lean module(s) and {} import edge(s) checked.\n",
            self.modules.len(),
            self.total_edges(),
        ));
        FormattedReport {
            stdout,
            stderr,
            ok: true,
        }
    }

    /// Render the exact deterministic CLI output streams (`stdout`, `stderr`, exit status) for
    /// this workspace under `prefilter`.
    pub fn format_report(
        &self,
        tree: bool,
        in_github_actions: bool,
        prefilter: bool,
    ) -> Result<FormattedReport> {
        let (tree_res, mut violations) = std::thread::scope(|s| {
            let tree_job = s.spawn(|| {
                if tree {
                    self.trust_tree().map(|r| (Some(r), Vec::new()))
                } else {
                    self.trust_tree_violations().map(|v| (None, v))
                }
            });
            let v = self.check_all_with_prefilter(prefilter);
            (tree_job.join().expect("trust_tree panicked"), v)
        });
        let (tree_report, tree_violations) = tree_res?;
        if let Some(ref report) = tree_report {
            violations.extend(report.violations.clone());
        } else {
            violations.extend(tree_violations);
        }
        Ok(self.format_violations(&violations, tree_report.as_ref(), in_github_actions))
    }
}

/// Captured CLI output streams from [`Workspace::format_report`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormattedReport {
    pub stdout: String,
    pub stderr: String,
    pub ok: bool,
}

#[cfg(test)]
mod tests;
