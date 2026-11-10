// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Repository layout discovery: repo root, `.lean` / `.md` / repo file walking, and module
//! `Lib`/`Role` classification (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. [`classify`] is the single definition of which modules are
//!   trusted `Spec`, `Theorems`, or kernel-checked `Proof` (enforced by `tcb-map`).
//! - **Purpose:** Self-contained repository file discovery and Lean module classification with
//!   zero internal crate dependencies, re-exported by `repo-common` for downstream tools.

use anyhow::Result;
use std::collections::HashSet;
use std::fmt;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

// ---------------------------------------------------------------------------------------------
// Repository root
// ---------------------------------------------------------------------------------------------

/// Is `dir` the root of this repository (the Lean workspace with `lakefile.lean`, `Arm64/`, and `CaseStudies/`)?
pub fn is_repo_root(dir: &Path) -> bool {
    dir.join("lakefile.lean").is_file()
        && dir.join("Arm64").is_dir()
        && dir.join("CaseStudies").is_dir()
}

/// The nearest ancestor of `start` (inclusive) that [`is_repo_root`].
pub fn find_repo_root(start: &Path) -> Option<PathBuf> {
    start
        .ancestors()
        .find(|d| is_repo_root(d))
        .map(Path::to_path_buf)
}

/// The repository containing this crate's sources (`tools/tcb-map/../..`), else the nearest
/// repository root above the current directory, else the current directory.
pub fn default_repo_root() -> PathBuf {
    let from_manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    if is_repo_root(&from_manifest) {
        return from_manifest.canonicalize().unwrap_or(from_manifest);
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    find_repo_root(&cwd).unwrap_or(cwd)
}

// ---------------------------------------------------------------------------------------------
// Walking `.lean` files
// ---------------------------------------------------------------------------------------------

/// Directories that never contain package modules (hidden directories are skipped too).
/// `build` holds generated, never-committed build outputs.
pub const SKIP_DIRS: &[&str] = &[
    "target",
    "tools",
    "Implementation",
    "third_party",
    "docs",
    "scripts",
    "build",
];

/// Files that are `.lean` but not modules of the package.
pub const SKIP_FILES: &[&str] = &["lakefile.lean"];

/// `path` relative to `root`, with `/` separators (`None` if `path` is not under `root`).
pub fn rel_path(root: &Path, path: &Path) -> Option<String> {
    let rel = path.strip_prefix(root).ok()?;
    Some(
        rel.components()
            .map(|c| c.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/"),
    )
}

/// `CaseStudies/Alpha/Spec.lean` -> `CaseStudies.Alpha.Spec`.
pub fn module_name_of_path(rel_path: &str) -> String {
    rel_path
        .strip_suffix(".lean")
        .unwrap_or(rel_path)
        .replace('/', ".")
}

/// Repo-relative paths (sorted, `/`-separated) of every package `.lean` module under `root`,
/// skipping hidden directories, `_template`, [`SKIP_DIRS`], and [`SKIP_FILES`].
pub fn walk_lean_files(root: &Path) -> Result<Vec<String>> {
    let walker = WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            let skip = name.starts_with('.') || name == "_template" || SKIP_DIRS.contains(&&*name);
            e.depth() == 0 || !(e.file_type().is_dir() && skip)
        });
    let mut out = Vec::new();
    for entry in walker {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy();
        if entry.file_type().is_file()
            && name.ends_with(".lean")
            && !name.starts_with('.')
            && !SKIP_FILES.contains(&&*name)
        {
            out.extend(rel_path(root, entry.path()));
        }
    }
    out.sort();
    Ok(out)
}

/// Repo-relative paths (sorted) of every `.lean` file under `root/rel_dir` (empty if missing).
pub fn list_lean_files_rec(root: &Path, rel_dir: &str) -> Vec<String> {
    let mut out: Vec<String> = WalkDir::new(root.join(rel_dir))
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            e.depth() == 0
                || !(e.file_type().is_dir()
                    && (name.starts_with('.') || SKIP_DIRS.contains(&&*name)))
        })
        .filter_map(|e| e.ok())
        .filter(|e| {
            let name = e.file_name().to_string_lossy();
            e.file_type().is_file()
                && e.path().extension().and_then(|s| s.to_str()) == Some("lean")
                && !SKIP_FILES.contains(&&*name)
        })
        .filter_map(|e| rel_path(root, e.path()))
        .collect();
    out.sort();
    out
}

// ---------------------------------------------------------------------------------------------
// Walking `.md` and repository files
// ---------------------------------------------------------------------------------------------

/// Build, vendor, and cache directories never scanned for Markdown (at any depth).
pub const MARKDOWN_SKIP_DIRS: &[&str] = &[
    "target",
    "node_modules",
    "dist",
    "build",
    "out",
    "vendor",
    "cargo-vendor",
];

/// Repo-relative directories (`/`-separated) never scanned for Markdown: `.agents/shared` is an
/// external submodule that CI (`actions/checkout` without `submodules: true`) leaves empty.
pub const MARKDOWN_SKIP_REL_DIRS: &[&str] = &[".agents/shared"];

/// Repo-relative paths (sorted, `/`-separated `PathBuf`s) of every `*.md` file under `root`.
pub fn walk_markdown_files(root: &Path) -> Result<Vec<PathBuf>, String> {
    let walker = WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|e| {
            if e.depth() == 0 || !e.file_type().is_dir() {
                return true;
            }
            let name = e.file_name().to_string_lossy();
            if name.starts_with('.') && name != ".agents" {
                return false;
            }
            if MARKDOWN_SKIP_DIRS.contains(&&*name) {
                return false;
            }
            !rel_path(root, e.path()).is_some_and(|r| MARKDOWN_SKIP_REL_DIRS.contains(&r.as_str()))
        });
    let mut out = Vec::new();
    for entry in walker {
        let entry = entry.map_err(|e| format!("walking {}: {e}", root.display()))?;
        if entry.file_type().is_file() && entry.file_name().to_string_lossy().ends_with(".md") {
            out.extend(rel_path(root, entry.path()));
        }
    }
    if root.join(".git").exists() {
        if let Some(ignored) = git_ignored(root, &out) {
            out.retain(|p| !ignored.contains(p));
        }
    }
    out.sort();
    Ok(out.into_iter().map(PathBuf::from).collect())
}

/// Repo-relative paths (sorted, `/`-separated) of every repository source/config file under
/// `root`, skipping hidden directories other than `.github` and `.agents`, [`MARKDOWN_SKIP_DIRS`],
/// `.agents/shared`, `{VerifiedLibraries,CaseStudies,FormalRfcs}/**/Generated`, symlinks, and
/// git-ignored files.
pub fn walk_repo_files(root: &Path) -> Result<Vec<String>> {
    let walker = WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|e| {
            if e.depth() == 0 || !e.file_type().is_dir() {
                return true;
            }
            let name = e.file_name().to_string_lossy();
            if name.starts_with('.') && name != ".github" && name != ".agents" {
                return false;
            }
            if MARKDOWN_SKIP_DIRS.contains(&&*name) || name == "__pycache__" {
                return false;
            }
            !rel_path(root, e.path()).is_some_and(|r| {
                MARKDOWN_SKIP_REL_DIRS.contains(&r.as_str())
                    || (r.starts_with("CaseStudies/") && r.ends_with("/Generated"))
                    || (r.starts_with("VerifiedLibraries/") && r.ends_with("/Generated"))
                    || (r.starts_with("FormalRfcs/") && r.ends_with("/Generated"))
            })
        });
    let mut out = Vec::new();
    for entry in walker {
        let entry = entry?;
        let fname = entry.file_name().to_string_lossy();
        if entry.file_type().is_file() && fname != ".git" && fname != ".audit-snapshot" {
            out.extend(rel_path(root, entry.path()));
        }
    }
    if root.join(".git").exists() {
        if let Some(ignored) = git_ignored(root, &out) {
            out.retain(|p| !ignored.contains(p));
        }
    }
    out.sort();
    Ok(out)
}

/// The subset of `paths` (repo-relative) that are untracked and ignored by git, or `None` if
/// `git` cannot be run (tracked files are never reported, even if an ignore pattern matches).
fn git_ignored(root: &Path, paths: &[String]) -> Option<HashSet<String>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["check-ignore", "--stdin", "-z"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    let mut input = Vec::new();
    for p in paths {
        input.extend_from_slice(p.as_bytes());
        input.push(0);
    }
    let mut stdin = child.stdin.take()?;
    // Write on a separate thread so a full stdout pipe can never deadlock the child.
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let output = child.wait_with_output().ok()?;
    writer.join().ok()?.ok()?;
    // `git check-ignore` exits 1 when nothing is ignored; anything else is an error.
    match output.status.code() {
        Some(0) | Some(1) => {}
        _ => return None,
    }
    Some(
        output
            .stdout
            .split(|b| *b == 0)
            .filter(|s| !s.is_empty())
            .map(|s| String::from_utf8_lossy(s).into_owned())
            .collect(),
    )
}

// ---------------------------------------------------------------------------------------------
// Standalone packages
// ---------------------------------------------------------------------------------------------

/// Directory names with a fixed role inside a package (`<package>/<Role>/`) and inside a formal
/// RFC (`FormalRfcs/<Rfc>/<Role>/`), so they can never name a per-implementation package
/// `FormalRfcs/<Rfc>/<Impl>/`.
pub const PACKAGE_ROLE_DIRS: &[&str] = &[
    "Spec",
    "Proofs",
    "Testing",
    "Theorems",
    "Generated",
    "Witness",
    "Implementation",
    "Drivers",
];

/// The formal RFC directory (`FormalRfcs/Common/`) holding the shared CLI contract; it never
/// contains per-implementation packages.
pub const FORMAL_RFCS_COMMON: &str = "Common";

/// Number of leading path components (module components or `/`-separated directory components)
/// naming the per-campaign package that `parts` lies in:
/// - `2` for `CaseStudies/<Pkg>/...` and `VerifiedLibraries/<Pkg>/...`;
/// - `3` for a per-implementation formal RFC package `FormalRfcs/<Rfc>/<Impl>/...` (`<Rfc>` not
///   [`FORMAL_RFCS_COMMON`], neither `<Rfc>` nor `<Impl>` in [`PACKAGE_ROLE_DIRS`]);
/// - `None` otherwise (including the package directory's parent itself).
///
/// The components after the package prefix are classified identically for every package kind
/// (`Spec/`, `Proofs/`, `Generated/`, `Testing/`, `Theorems/`, `Implementation/`, ...).
pub fn package_depth(parts: &[&str]) -> Option<usize> {
    match parts {
        ["CaseStudies" | "VerifiedLibraries", pkg, ..] if !pkg.is_empty() => Some(2),
        ["FormalRfcs", rfc, imp, ..]
            if !rfc.is_empty()
                && *rfc != FORMAL_RFCS_COMMON
                && !PACKAGE_ROLE_DIRS.contains(rfc)
                && !imp.is_empty()
                && !PACKAGE_ROLE_DIRS.contains(imp) =>
        {
            Some(3)
        }
        _ => None,
    }
}

/// The standalone campaign package (`CaseStudies.<Pkg>` or `FormalRfcs.<Rfc>.<Impl>`, as a dotted
/// module prefix) that `module` belongs to, if any. Standalone campaign packages are pairwise
/// independent; `VerifiedLibraries.<Pkg>` packages are reusable libraries and are not included.
pub fn standalone_package_of(module: &str) -> Option<String> {
    let parts: Vec<&str> = module.split('.').collect();
    if parts[0] == "VerifiedLibraries" {
        return None;
    }
    let depth = package_depth(&parts)?;
    // A `.lean` file whose path ends at the package directory is the package umbrella.
    Some(parts[..depth].join("."))
}

/// Repo-relative directories (sorted, `/`-separated) of every standalone campaign Lake package
/// under `root`: `CaseStudies/<Pkg>/` ([`package_depth`]; no path component starting with `.` or
/// `_`, so `CaseStudies/_template` is skipped) holding a `lakefile.toml` or `lakefile.lean`.
/// (`FormalRfcs/` is a single Lake package hosting all RFC models and implementation subtrees.)
pub fn discover_campaign_package_dirs(root: &Path) -> Vec<String> {
    let subdirs = |rel: &str| -> Vec<String> {
        let Ok(rd) = std::fs::read_dir(root.join(rel)) else {
            return Vec::new();
        };
        let mut out: Vec<String> = rd
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_ok_and(|t| t.is_dir()))
            .filter_map(|e| e.file_name().into_string().ok())
            .filter(|n| !n.starts_with('.') && !n.starts_with('_'))
            .collect();
        out.sort();
        out
    };
    let candidates: Vec<String> = subdirs("CaseStudies")
        .into_iter()
        .map(|p| format!("CaseStudies/{p}"))
        .collect();
    let mut out: Vec<String> = candidates
        .into_iter()
        .filter(|d| {
            let parts: Vec<&str> = d.split('/').collect();
            package_depth(&parts) == Some(parts.len())
                && (root.join(d).join("lakefile.toml").is_file()
                    || root.join(d).join("lakefile.lean").is_file())
        })
        .collect();
    out.sort();
    out
}

// ---------------------------------------------------------------------------------------------
// Module classification
// ---------------------------------------------------------------------------------------------

/// Module roots provided by the Lean toolchain (trusted, never scanned). The package has no
/// external Lake dependencies, so any other unknown root is rejected as an unknown library.
pub const STDLIB_ROOTS: &[&str] = &["Init", "Std", "Lean", "Lake"];

/// The `lean_lib`s across the repository's Lake packages, in layering order: a library may only
/// import libraries at or below itself. `Equivalence` sits directly above `ProofLib` and may only
/// be imported by `Examples` (`CaseStudies`), `Testing`, and `Theorems` (never by `Arm64Testing`,
/// `VerifiedLibraries`, or `FormalRfcs`). `FormalRfcs` sits between `VerifiedLibraries` and
/// `Examples`: it may import `Arm64`, `ProofLib`, `VerifiedLibraries`, and `FormalRfcs`.
/// `Arm64Testing` (`Arm64.Testing.*`) is mutually incomparable with `Equivalence`,
/// `VerifiedLibraries`, `FormalRfcs`, and `Examples`: engine tests may only import `Arm64`,
/// `ProofLib`, and `Arm64Testing`. `Theorems` (trusted end-to-end theorem statements proved
/// in-repo) sits beside `Testing`: it may import `Arm64`, `ProofLib`, `Equivalence`,
/// `VerifiedLibraries`, `FormalRfcs`, `Examples`, and `Theorems` (never `Arm64Testing` or
/// `Testing`), and nothing outside `Theorems` may import it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Lib {
    /// Trusted ISA semantics, program model, and specification vocabulary (`Arm64.Trusted.*`:
    /// `c_spec` / `rust_spec` / `c_type_spec` DSLs and hook definitions).
    Arm64,
    /// Reusable proof infrastructure (entirely untrusted `Proof`).
    ProofLib,
    /// Program-equivalence package (`Equivalence.Spec.*`: `Spec`; `Equivalence.Proofs.*`:
    /// `Proof`), importing only `Arm64`, `ProofLib`, and `Equivalence`.
    Equivalence,
    /// Engine-level unit, regression, and differential tests (`Arm64.Testing.*`), decoupled
    /// from `VerifiedLibraries`, `CaseStudies`, and `Theorems`: may only import `Arm64`,
    /// `ProofLib`, and `Arm64Testing`.
    Arm64Testing,
    /// Reusable verified libraries (`VerifiedLibraries.<Pkg>.*`: `Spec` and `Proof`).
    VerifiedLibraries,
    /// Formal RFC models (`FormalRfcs.Common.*` and `FormalRfcs.<Rfc>.*` outside per-implementation
    /// packages: `Spec` for `Spec[.*]`, `Proof` for `Proofs[.*]`), importing only `Arm64`,
    /// `ProofLib`, `VerifiedLibraries`, and `FormalRfcs`. Per-implementation packages
    /// `FormalRfcs.<Rfc>.<Impl>.*` are classified like `CaseStudies.<Pkg>.*` (`Examples`).
    FormalRfcs,
    /// Standalone case-study packages (`CaseStudies.<Pkg>.*`: `Spec` and `Proof`).
    Examples,
    /// Tests and the differential-testing harness.
    Testing,
    /// Trusted end-to-end theorem statements (`VerifiedLibraries.<Pkg>.Theorems[.*]` and
    /// `CaseStudies.<Pkg>.Theorems[.*]`) importing both `Spec` and `Proof` modules, checked by the
    /// Lean kernel and `axiom-audit`.
    Theorems,
}

impl Lib {
    pub fn may_import(self, target: Lib) -> bool {
        match (self, target) {
            (Lib::Theorems, _) => {
                matches!(
                    target,
                    Lib::Arm64
                        | Lib::ProofLib
                        | Lib::Equivalence
                        | Lib::VerifiedLibraries
                        | Lib::FormalRfcs
                        | Lib::Examples
                        | Lib::Theorems
                )
            }
            (_, Lib::Theorems) => false,
            (Lib::Arm64Testing | Lib::VerifiedLibraries | Lib::FormalRfcs, Lib::Equivalence) => {
                false
            }
            (Lib::VerifiedLibraries | Lib::FormalRfcs | Lib::Examples, Lib::Arm64Testing) => false,
            _ => target <= self,
        }
    }
}

/// Whether a module is part of the trusted statement (`Spec`), checked by the kernel (`Proof`),
/// test-only (`Test`), a trusted end-to-end theorem module (`Theorems`), or a deliberately unsound
/// regression fixture for the soundness audit tooling (`Fixture`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Spec,
    Proof,
    Test,
    /// `{VerifiedLibraries,CaseStudies}.<Pkg>.Theorems[.*]`: trusted end-to-end theorem statements
    /// proved directly against `Proof` modules with zero `sorry` or non-standard axioms.
    Theorems,
    /// `<Root>.Testing.*.Fixtures`: declarations that intentionally use
    /// `sorry`/`axiom`/`native_decide` so audit tests can check they are detected. Only the
    /// parent module (e.g. `ProofLib.Testing.AxiomAudit` for
    /// `ProofLib.Testing.AxiomAudit.Fixtures`)
    /// may import a fixture module.
    Fixture,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleClass {
    pub lib: Lib,
    pub role: Role,
}

impl fmt::Display for ModuleClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}:{:?}", self.lib, self.role)
    }
}

/// Roots whose `<Root>.Testing.*` subtree (and `<Root>.Testing` umbrella) belongs to a testing
/// library (`Arm64Testing` for `Arm64`, `Testing` for the rest) rather than to `<Root>`'s own
/// library.
pub const TESTING_ROOTS: &[&str] = &["Arm64", "ProofLib", "Equivalence", "VerifiedLibraries"];

/// Is `module` part of a testing library (`Arm64.Testing[.*]`, `ProofLib.Testing[.*]`,
/// `Equivalence.Testing[.*]`, `VerifiedLibraries.Testing[.*]`, `VerifiedLibraries.<Pkg>.Testing[.*]`,
/// `CaseStudies.<Pkg>.Testing[.*]`, `FormalRfcs.<Rfc>.Testing[.*]` (including
/// `FormalRfcs.Common.Testing[.*]`), or `FormalRfcs.<Rfc>.<Impl>.Testing[.*]`)?
pub fn is_testing_module(module: &str) -> bool {
    let parts: Vec<&str> = module.split('.').collect();
    match parts.as_slice() {
        [r, "Testing", ..] if TESTING_ROOTS.contains(r) => true,
        ["FormalRfcs", rfc, "Testing", ..] => !rfc.is_empty(),
        _ => package_depth(&parts).is_some_and(|d| parts.get(d) == Some(&"Testing")),
    }
}

/// Classify a Lean module by name, failing closed (`None`) on unknown roots or non-standard
/// `{VerifiedLibraries,CaseStudies}/<Pkg>/` subdirectory paths.
///
/// - `Arm64.Testing[.*]` forms the standalone `Arm64Testing` library (which may only import
///   `Arm64`, `ProofLib`, and `Arm64Testing`); `ProofLib.Testing[.*]`,
///   `Equivalence.Testing[.*]`, `VerifiedLibraries.Testing[.*]`, `VerifiedLibraries.<Pkg>.Testing[.*]`, and
///   `CaseStudies.<Pkg>.Testing[.*]` form the `Testing` library: `<Root>.Testing.*.Fixtures`
///   (last component `Fixtures`, at depth >= 4) is `Fixture`, the rest is `Test`.
/// - `Arm64.Legacy[.*]` is `Proof` (`[OUTSIDE TCB]` deprecated `LinkedImage` compatibility
///   modules); all other non-testing `Arm64` modules (`Arm64`, `Arm64.Trusted[.*]`) are `Spec`;
///   all non-testing `ProofLib` modules are `Proof` (so a trusted spec can never import
///   `Arm64.Legacy` or `ProofLib`).
/// - `Equivalence.Spec[.*]` is `Spec` and `Equivalence.Proofs[.*]` is `Proof`; any other
///   `Equivalence[.*]` module (including a repository-root `Equivalence` umbrella) returns `None`.
/// - Outside per-implementation packages, `FormalRfcs.<Rfc>.Spec[.*]` (including
///   `FormalRfcs.Common.Spec[.*]`) is `FormalRfcs:Spec`, `FormalRfcs.<Rfc>.Proofs[.*]` is
///   `FormalRfcs:Proof`, and `FormalRfcs.<Rfc>.Testing[.*]` is `Testing`; any other module
///   returns `None`.
/// - `VerifiedLibraries.Theorems[.*]`, `VerifiedLibraries.<Pkg>.Theorems[.*]`,
///   `CaseStudies.<Pkg>.Theorems[.*]`, and `FormalRfcs.<Rfc>.<Impl>.Theorems[.*]` have role
///   `Theorems`.
/// - Inside `VerifiedLibraries.<Pkg>[.*]`, `CaseStudies.<Pkg>[.*]`, and per-implementation formal
///   RFC packages `FormalRfcs.<Rfc>.<Impl>[.*]` ([`package_depth`]; `Examples`, like
///   `CaseStudies`), classification is strictly directory-driven and fail-closed:
///   - `<Root>.<Pkg>` (package umbrella) -> `Proof`
///   - `<Root>.<Pkg>.Spec[.*]` -> `Spec`
///   - `<Root>.<Pkg>.Proofs[.*]` -> `Proof`
///   - `<Root>.<Pkg>.Witness[.*]` -> `Proof` (untrusted proofs kept out of the package's
///     default `Proofs` library, e.g. lemmas over expensive whole-image witnesses that only
///     an opt-in build target compiles)
///   - `<Root>.<Pkg>.Generated` -> `Proof`; `<Root>.<Pkg>.Generated.{*PlacedObj,*ExtractedObj,*ElfObj}`
///     and placed code shards `<Root>.<Pkg>.Generated.*PlacedObjShard<k>` -> `Spec`; all other
///     `<Root>.<Pkg>.Generated.*` (including legacy `<Name>Obj` `LinkedImage` proof-cache
///     modules) -> `Proof`
///   - Any other `<Root>.<Pkg>.<Other>[.*]` returns `None`.
pub fn classify(module: &str) -> Option<ModuleClass> {
    if module.is_empty() || module.split('.').any(str::is_empty) {
        return None;
    }
    let parts: Vec<&str> = module.split('.').collect();
    if is_testing_module(module) {
        let lib = if parts[0] == "Arm64" {
            Lib::Arm64Testing
        } else {
            Lib::Testing
        };
        let role = if parts.len() >= 4 && parts.last() == Some(&"Fixtures") {
            Role::Fixture
        } else {
            Role::Test
        };
        return Some(ModuleClass { lib, role });
    }
    let depth = package_depth(&parts);
    if (parts.len() >= 2 && parts[0] == "VerifiedLibraries" && parts[1] == "Theorems")
        || depth.is_some_and(|d| parts.get(d) == Some(&"Theorems"))
    {
        return Some(ModuleClass {
            lib: Lib::Theorems,
            role: Role::Theorems,
        });
    }
    match parts[0] {
        "Arm64" => {
            let role = if parts.get(1) == Some(&"Legacy") {
                Role::Proof
            } else {
                Role::Spec
            };
            return Some(ModuleClass {
                lib: Lib::Arm64,
                role,
            });
        }
        "ProofLib" => {
            return Some(ModuleClass {
                lib: Lib::ProofLib,
                role: Role::Proof,
            });
        }
        "Equivalence" => {
            let role = match parts.as_slice() {
                ["Equivalence", "Spec", ..] => Role::Spec,
                ["Equivalence", "Proofs", ..] => Role::Proof,
                _ => return None,
            };
            return Some(ModuleClass {
                lib: Lib::Equivalence,
                role,
            });
        }
        "FormalRfcs" if depth.is_none() => {
            let role = match parts.as_slice() {
                ["FormalRfcs", _, "Spec", ..] => Role::Spec,
                ["FormalRfcs", _, "Proofs", ..] => Role::Proof,
                _ => return None,
            };
            return Some(ModuleClass {
                lib: Lib::FormalRfcs,
                role,
            });
        }
        _ => {}
    }
    // Transitional 1-file exception pending active campaign merge before relocation to `Testing/`.
    if module == "CaseStudies.Hashbrown.SpecExamples" {
        return Some(ModuleClass {
            lib: Lib::Examples,
            role: Role::Proof,
        });
    }
    let lib = match parts[0] {
        "VerifiedLibraries" => Lib::VerifiedLibraries,
        "CaseStudies" | "FormalRfcs" => Lib::Examples,
        _ => return None,
    };
    if parts.as_slice() == ["VerifiedLibraries"] {
        return Some(ModuleClass {
            lib,
            role: Role::Proof,
        });
    }
    let depth = depth?;
    let role = match &parts[depth..] {
        [] => Role::Proof,
        ["Spec", ..] => Role::Spec,
        ["Proofs" | "Witness", ..] => Role::Proof,
        ["Generated"] => Role::Proof,
        ["Generated", ..] => {
            if is_generated_obj_name(module) {
                Role::Spec
            } else {
                Role::Proof
            }
        }
        _ => return None,
    };
    Some(ModuleClass { lib, role })
}

/// Is the last component of `module` a generated trusted object or ELF image name:
/// `<Name>PlacedObj`, `<Name>ExtractedObj`, `<Name>ElfObj`, or a code shard
/// `<Name>PlacedObjShard<k>` (decimal `k`) of a `rust-obj2lean` placed library split with
/// `[placed] placed_shards`?
///
/// Legacy `<Name>Obj` (`Arm64.Obj.LinkedImage`) exports are `[OUTSIDE TCB]` proof-cache modules
/// (`Role::Proof`) and intentionally return `false`.
pub fn is_generated_obj_name(module: &str) -> bool {
    let last = module.rsplit('.').next().unwrap_or(module);
    if (last.ends_with("PlacedObj") && last.len() > "PlacedObj".len())
        || (last.ends_with("ExtractedObj") && last.len() > "ExtractedObj".len())
        || (last.ends_with("ElfObj") && last.len() > "ElfObj".len())
    {
        return true;
    }
    let digits = last.trim_end_matches(|c: char| c.is_ascii_digit());
    digits.len() < last.len()
        && digits.ends_with("PlacedObjShard")
        && digits.len() > "PlacedObjShard".len()
}

/// The only module allowed to import the fixture module `fixture`
/// (`ProofLib.Testing.AxiomAudit.Fixtures` -> `ProofLib.Testing.AxiomAudit`).
pub fn fixture_owner(fixture: &str) -> &str {
    fixture.strip_suffix(".Fixtures").unwrap_or(fixture)
}

/// Compiler output regenerated by the lakefile (`<package>.Generated.*`, [`package_depth`]); it
/// may be absent when the checker runs.
pub fn is_generated(module: &str) -> bool {
    let parts: Vec<&str> = module.split('.').collect();
    package_depth(&parts).is_some_and(|d| parts.len() > d + 1 && parts[d] == "Generated")
}

/// Is the repo-relative `.lean` path a hand-written trusted campaign spec module: an
/// `Equivalence`, `VerifiedLibraries`, `FormalRfcs`, or `CaseStudies` module named `.../Spec.lean` or under
/// `.../Spec/`? Same rule as [`classify`], minus `Arm64` and generated `*PlacedObj` / `*ElfObj`
/// exports.
pub fn is_spec_path(rel_path: &str) -> bool {
    let module = module_name_of_path(rel_path);
    !is_generated(&module)
        && classify(&module).is_some_and(|c| {
            c.role == Role::Spec
                && matches!(
                    c.lib,
                    Lib::Equivalence | Lib::VerifiedLibraries | Lib::FormalRfcs | Lib::Examples
                )
        })
}
