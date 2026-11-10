// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Declarative trust policy for `tcb-map`: repository trust categories, module
//! classification, import layering, and forbidden Lean constructs/attributes (`[AUDIT/LINTER]`).
//!
//! # Core Soundness Invariants
//! 1. **Every repository file/directory has an explicit [`TrustCategory`]**
//!    (`tcb`, `case-studies-tcb`, `proof`, `testing`, `infra`, `doc`; see [`classify_path`]).
//! 2. **Trusted specifications are self-contained and `Theorems` is a strict sink**:
//!    - `Role::Spec` modules (`Arm64/Trusted/`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Spec*`)
//!      only import `Role::Spec` modules—never `proof` (`ProofLib/`, `**/Proofs/`) or `testing`
//!      (`*/Testing/`) modules—and contain zero theorems (`theorem`/`lemma`).
//!    - `Role::Theorems` modules (`{VerifiedLibraries,CaseStudies}/<Pkg>/Theorems*`) state and
//!      prove closed end-to-end theorems importing `Spec` and `Proof`, and no `Spec`, `Proof`, or
//!      `Testing` module may import `Theorems`.
//! 3. **No soundness escapes**: zero `axiom`, `sorry`, `native_decide`, `unsafe`,
//!    `@[implemented_by]`, or `@[extern]` in specs, proofs, and theorems (see [`LINE_RULES`] and
//!    [`FORBIDDEN_ATTRIBUTES`]).
//!
//! # Canonical Convention Table
//! <!-- BEGIN CANONICAL CONVENTION TABLE -->
//! | Pattern | Sample Path | Trust Bucket | Lean Role / Tier | Notes |
//! | --- | --- | --- | --- | --- |
//! | `**/*.md` | `README.md` | `doc` | `-` | All Markdown documentation across the repository |
//! | `Arm64/Trusted/{ISA,Object,Process,Syscalls,Spec}/**.lean`, `Arm64/Trusted/Syscalls.lean` | `Arm64/Trusted/ISA/Decode.lean` | `tcb` | `Arm64:Spec` (`CoreInitOnly`) | `Init`-only semantic core (`SepLogic.lean` is the sole notation allowlist entry) |
//! | `Arm64/Trusted/Surface/**.lean`, `Arm64.lean`, `Arm64/Trusted.lean`, `Arm64/Trusted/Process.lean` | `Arm64/Trusted/Surface/Abi.lean` | `tcb` | `Arm64:Spec` (`SurfaceMacro`) | Surface DSL macros/elaborators and package barrels |
//! | `Arm64/Legacy.lean`, `Arm64/Legacy/**.lean` | `Arm64/Legacy/Object/LinkedImage.lean` | `proof` | `Arm64:Proof` | Deprecated `[OUTSIDE TCB]` `LinkedImage` compatibility modules (shrinking importer allowlist) |
//! | `Arm64/Testing/**.lean` (`.Fixtures` at depth >= 4) | `Arm64/Testing/Audit/AxiomAudit/Fixtures.lean` | `testing` | `Arm64Testing:Fixture` | Deliberately unsound audit fixtures (importable only by parent module) |
//! | `Arm64/Testing/**` (other `.lean` and non-Lake assets) | `Arm64/Testing/AsciiTests.lean` | `testing` | `Arm64Testing:Test` | Engine-level tests decoupled from `VerifiedLibraries` and `CaseStudies` |
//! | `ProofLib.lean`, `ProofLib/**.lean` (outside `Testing/` and `TRUST_ENFORCEMENT_LEAN_FILES`) | `ProofLib/SimpAttrs.lean` | `proof` | `ProofLib:Proof` | Untrusted reusable proof automation and lemmas |
//! | `ProofLib/TrustedClosure.lean` | `ProofLib/TrustedClosure.lean` | `testing` | `ProofLib:Proof` | Trust-model enforcement: `#trusted_closure` statement-integrity checks run by `scripts/axiom-audit --strict` (`TRUST_ENFORCEMENT_LEAN_FILES`) |
//! | `Equivalence/Spec/**.lean` | `Equivalence/Spec/Basic.lean` | `case-studies-tcb` | `Equivalence:Spec` | Definition-only trusted program-equivalence vocabulary |
//! | `Equivalence/Proofs/**.lean` | `Equivalence/Proofs/Basic.lean` | `proof` | `Equivalence:Proof` | Untrusted kernel-checked equivalence lemmas (adequacy, driver linking) |
//! | `{ProofLib,Equivalence,VerifiedLibraries}/Testing/**.lean`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Testing/**.lean` (`.Fixtures` at depth >= 4) | `ProofLib/Testing/AxiomAudit/Fixtures.lean` | `testing` | `Testing:Fixture` | Deliberately unsound audit fixtures |
//! | `{ProofLib,Equivalence,VerifiedLibraries}/Testing/**`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Testing/**` (other files) | `CaseStudies/Alpha/Testing/SpecAudit.lean` | `testing` | `Testing:Test` | Spec audits, golden vectors, and unverified host test harnesses/runners |
//! | `VerifiedLibraries.lean`, `{VerifiedLibraries,CaseStudies}/<Pkg>.lean` | `CaseStudies/Alpha.lean` | `proof` | `Examples:Proof` | Package umbrella barrels (`VerifiedLibraries:Proof` under `VerifiedLibraries/`) |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Spec.lean`, `.../Spec/**.lean` | `CaseStudies/Alpha/Spec/Top.lean` | `case-studies-tcb` | `Examples:Spec` | Definition-only trusted specifications (`VerifiedLibraries:Spec` under `VerifiedLibraries/`) |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Proofs/**.lean` | `CaseStudies/Alpha/Proofs/Main.lean` | `proof` | `Examples:Proof` | Untrusted kernel-checked proofs (`VerifiedLibraries:Proof` under `VerifiedLibraries/`) |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/{*PlacedObj,*PlacedObjShard<k>,*ExtractedObj,*ElfObj}.lean` | `CaseStudies/Alpha/Generated/AlphaPlacedObj.lean` | `case-studies-tcb` | `Examples:Spec` | Generated trusted placed-library, pre-link extracted-object, and ELF object definitions (and `placed_shards` code shards) |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/*.bin` (except `*.{code,data}.bin`) | `CaseStudies/Alpha/Generated/AlphaPlacedObj.bin` | `case-studies-tcb` | `-` | Extracted target binary payloads |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated.lean`, `.../Generated/**.lean` (other) | `CaseStudies/Alpha/Generated/AlphaCode.lean` | `proof` | `Examples:Proof` | Generated instruction/decode/placement proof modules and `[OUTSIDE TCB]` legacy `*Obj` proof cache |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/*.{code,data}.bin` | `CaseStudies/Alpha/Generated/AlphaObj.code.bin` | `proof` | `-` | `[OUTSIDE TCB]` legacy `LinkedImage` proof-cache binary sidecars |
//! | `VerifiedLibraries/Theorems[.lean]`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Theorems[.lean]` | `CaseStudies/Alpha/Theorems/Top.lean` | `case-studies-tcb` | `Theorems:Theorems` | Closed `theorem`-only end-to-end statements (`Theorems` sink) |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Implementation/**` (Rust unit/integration tests) | `CaseStudies/Alpha/Implementation/src/tests.rs` | `testing` | `-` | Only `*.rs` files matching `is_test_path` (including `tests/`; never linked into verified objects); `.c`/`.h` under `tests/` stay `case-studies-tcb` |
//! | `{VerifiedLibraries,CaseStudies}/<Pkg>/Implementation/**` (target sources & build configs) | `CaseStudies/Alpha/Implementation/src/lib.rs` | `case-studies-tcb` | `-` | Verified C/Rust target inputs, translation configs, and linked ELFs |
//! | `third_party/**` | `third_party/vendor/src/lib.c` | `case-studies-tcb` | `-` | Vendored upstream sources compiled into case studies |
//! | `tools/rust-obj2lean/src/{trusted_*,lib.rs}` | `tools/rust-obj2lean/src/lib.rs` | `tcb` | `-` | Core ELF extraction TCB (`tcb-rust-import` enforced) |
//! | `tools/rust-obj2lean/src/{untrusted_lemmas,untrusted_legacy_linker}/**` (non-test) | `tools/rust-obj2lean/src/untrusted_lemmas/mod.rs` | `proof` | `-` | Untrusted Lean proof-module codegen and `[OUTSIDE TCB]` legacy `LinkedImage` proof-cache exporter |
//! | `tools/proc-snapshot/src/**` (trusted modules) | `tools/proc-snapshot/src/lib.rs` | `case-studies-tcb` | `-` | Process-snapshot dumper (`tcb-rust-import` enforced) |
//! | `tools/{rust-obj2lean,proc-snapshot}/**` (`tests`, `*_test.rs`, `test_infra`) | `tools/rust-obj2lean/src/tests.rs` | `testing` | `-` | Separated unit/integration tests of `[tcb]`/`[case-studies-tcb]` crates |
//! | `tools/{rust-obj2lean,proc-snapshot}/**` (`untrusted_*`, `src/main.rs`, `Cargo.toml`) | `tools/rust-obj2lean/src/main.rs` | `infra` | `-` | Untrusted CLI/driver orchestration and crate manifests |
//! | `tools/{isa-oracle,run-trusted-tests,sail-aarch64,unicorn-aarch64,tcb-map}/**` | `tools/tcb-map/src/lib.rs` | `testing` | `-` | Differential ISA/loader harnesses and self-contained TCB auditor |
//! | `tools/snapshot-link/**`, `tools/Cargo.{toml,lock}`, `tools/dev/**` | `tools/dev/repo-lints/src/lib.rs` | `infra` | `-` | Snapshot linker, workspace manifests, and developer/CI/review tools |
//! | `scripts/tcb-map`, `scripts/dev/check-trust-guards.sh` | `scripts/tcb-map` | `testing` | `-` | Trust-guard entrypoints |
//! | `scripts/**` (other scripts), `.github/**`, `.githooks/**`, `.agents/**`, `docs/**`, Lake/CI/git configs | `scripts/dev/pre-push-check` | `infra` | `-` | Build, CI, developer automation, and package manifests (`lakefile.*`, `ci.toml`) |
//! <!-- END CANONICAL CONVENTION TABLE -->
//!
//! # When to Read This File
//! - Read this file whenever auditing or modifying which repository paths belong to `tcb`,
//!   `case-studies-tcb`, `proof`, `testing`, `infra`, or `doc`, or which Lean
//!   constructs/imports are permitted.

use regex::Regex;
use serde::Serialize;
use std::fmt;
use std::sync::LazyLock;

pub use crate::discovery::{
    Lib, ModuleClass, Role, STDLIB_ROOTS, classify, fixture_owner, is_generated,
    module_name_of_path, package_depth,
};

/// Internal heap-model modules that may ONLY be imported by `Arm64.*`, `ProofLib.*`, or
/// `Arm64.Testing.*` (and never by `VerifiedLibraries/**`, `CaseStudies/**`, or `Theorems/**`).
pub const ENGINE_INTERNAL_IMPORTS: &[&str] = &[
    "Arm64.Trusted.Spec.SepLogicModel",
    "ProofLib.SepLogic.Model",
    "ProofLib.Hoare.Model",
];

/// Engine-internal modules that must only be imported privately (never `public import`), so their
/// declarations never become visible to the importer's own importers.
pub const PRIVATE_ONLY_IMPORTS: &[&str] = &["ProofLib.SepLogic.Model", "ProofLib.Hoare.Model"];

/// Shrinking Stage 3a allowlist of non-`Arm64.Legacy` Lean modules permitted to directly
/// `import Arm64.Legacy[.*]` while `ProofLib/` and `Arm64/Testing/` preserve temporary bump
/// compatibility for downstream consumers. Audited bidirectionally by
/// [`crate::Workspace::check_imports`] (new importers are rejected; stale entries fail closed).
pub const LEGACY_LINKED_IMAGE_IMPORTERS: &[&str] = &[
    "Arm64.Testing.Harness.ElfRegionLoad",
    "Arm64.Testing.Regression.ObjectLoad",
    "ProofLib.Library",
    "ProofLib.ObjectLoad",
];

/// Explicit two-tier classification for every non-`Testing` Lean module in `Arm64` (`[tcb]`):
/// - [`TrustedTcbTier::CoreInitOnly`]: semantic core TCB modules whose entire transitive import
///   closure must remain strictly `Init`-only (zero `Lean` or `Std` imports, and zero imports of
///   [`TrustedTcbTier::SurfaceMacro`] modules).
/// - [`TrustedTcbTier::SurfaceMacro`]: surface specification macro, attribute, binary-inclusion,
///   and umbrella modules that elaborate surface syntax into [`TrustedTcbTier::CoreInitOnly`]
///   definitions or re-export the package umbrella.
///
/// Any `Arm64` `[tcb]` module returning `None` from [`classify_trusted_tcb_module`] is
/// **unclassified** and fails closed under `core-tcb-init-only`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustedTcbTier {
    CoreInitOnly,
    SurfaceMacro,
}

/// Classify an `Arm64` `[tcb]` module by directory convention into its [`TrustedTcbTier`],
/// returning `None` (fail-closed) for any unclassified `Arm64` module path:
/// - `Arm64/Trusted/{ISA,Object,Process,Syscalls,Spec}/**` and `Arm64/Trusted/Syscalls.lean`
///   $\to$ [`TrustedTcbTier::CoreInitOnly`] (`Init`-only semantic core).
/// - `Arm64/Trusted/Surface/**` and the barrel modules `Arm64.lean`, `Arm64/Trusted.lean`, and
///   `Arm64/Trusted/Process.lean` $\to$ [`TrustedTcbTier::SurfaceMacro`].
pub fn classify_trusted_tcb_module(module: &str) -> Option<TrustedTcbTier> {
    if module == "Arm64.Trusted.Syscalls"
        || module.starts_with("Arm64.Trusted.ISA.")
        || module.starts_with("Arm64.Trusted.Object.")
        || module.starts_with("Arm64.Trusted.Process.")
        || module.starts_with("Arm64.Trusted.Syscalls.")
        || module.starts_with("Arm64.Trusted.Spec.")
    {
        Some(TrustedTcbTier::CoreInitOnly)
    } else if matches!(module, "Arm64" | "Arm64.Trusted" | "Arm64.Trusted.Process")
        || module.starts_with("Arm64.Trusted.Surface.")
    {
        Some(TrustedTcbTier::SurfaceMacro)
    } else {
        None
    }
}

/// Core semantic TCB modules whose entire transitive import closure must remain strictly
/// `Init`-only (zero `Lean` or `Std` metaprogramming/tactic libraries).
pub fn is_core_tcb_init_only(module: &str) -> bool {
    classify_trusted_tcb_module(module) == Some(TrustedTcbTier::CoreInitOnly)
}

/// Rule ID reported when a whole-process package's trusted closure reaches library-spec
/// vocabulary ([`Workspace::check_whole_process_no_library_specs`](crate::Workspace)).
pub const WHOLE_PROCESS_NO_LIBRARY_SPECS_RULE: &str = "whole-process-no-library-specs";

/// `CaseStudies/<Pkg>` packages whose public theorems are stated only over whole-process
/// semantics (`ElfRunsTo` / `ElfPartialRunsTo` on ELF bytes). Their trusted closure must not
/// contain any [`LIBRARY_SPEC_MODULES`] module.
pub const WHOLE_PROCESS_PACKAGES: &[&str] = &["Hashbrown"];

/// `Arm64` trusted modules that define library-level specification vocabulary (Hoare triples,
/// separation logic, ABI/heap contracts, placed-library and override-review predicates). They are
/// trusted only by theorems stated against library specifications, never by whole-process
/// theorems ([`WHOLE_PROCESS_PACKAGES`]).
pub const LIBRARY_SPEC_MODULES: &[&str] = &[
    "Arm64.Trusted.Spec.SepLogic",
    "Arm64.Trusted.Spec.Hoare",
    "Arm64.Trusted.Spec.GlobalAlloc",
    "Arm64.Trusted.Spec.RustAbi",
    "Arm64.Trusted.Spec.RustHeap",
    "Arm64.Trusted.Spec.Placed",
    "Arm64.Trusted.Spec.RustRuntime",
    "Arm64.Trusted.Spec.SepLogicModel",
    "Arm64.Trusted.Surface.Abi",
    "Arm64.Trusted.Surface.CType",
    "Arm64.Trusted.Process.Placed",
    "Arm64.Trusted.Process.OverrideWellBehaved",
];

/// The fixed `public import` header that `rust-obj2lean` emits for a `Spec`-role generated object
/// module (`*ElfObj`, `*PlacedObj[Shard<k>]`, `*ExtractedObj`). Generated modules are build
/// products that [`Workspace::load`](crate::Workspace) does not read, so trusted-closure walks
/// follow these edges instead. Returns `None` for modules that are not generated objects.
pub fn generated_spec_imports(module: &str) -> Option<&'static [&'static str]> {
    if !is_generated(module) || classify(module).map(|c| c.role) != Some(Role::Spec) {
        return None;
    }
    let last = module.rsplit('.').next().unwrap_or(module);
    Some(if last.ends_with("ElfObj") {
        &["Arm64.Trusted.Process"]
    } else if last.ends_with("ExtractedObj") {
        &[
            "Arm64.Trusted.Object.Labels",
            "Arm64.Trusted.Surface.IncludeBytes",
        ]
    } else {
        &[
            "Arm64.Trusted.Object.Placed",
            "Arm64.Trusted.Surface.IncludeBytes",
        ]
    })
}

// ---------------------------------------------------------------------------------------------
// 1. Repository Trust Categories (`tcb`, `case-studies-tcb`, `proof`, `testing`, `infra`, `doc`)
// ---------------------------------------------------------------------------------------------

/// Six-bucket repository trust classification assigned to every file and directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum TrustCategory {
    /// Core engine Trusted Computing Base (`[tcb]`): code whose bug could make a false claim be
    /// accepted — the Lean definitions every theorem is stated against (`Arm64/Trusted/`) and the
    /// ELF `.o` extraction that produces the relocatable object bytes the theorems are about
    /// (`tools/rust-obj2lean/src/{trusted_*,lib.rs}`). Inside that crate, test files
    /// ([`is_test_path`]) are `testing`, `untrusted_lemmas/` and `untrusted_legacy_linker/`
    /// (non-test) are `proof`, and other `untrusted_*` modules plus the `src/main.rs` entry
    /// stub ([`is_untrusted_module_path`]) are `infra`. Trusted host-tool Rust files (`tcb` and
    /// `case-studies-tcb` under `tools/`) contain no inline test code (`tcb_test_code`) and
    /// reference no non-`tcb` workspace crate or `untrusted_*` / `test_infra` module
    /// (`tcb_rust_import`).
    Tcb,
    /// Case-study Trusted Computing Base (`[case-studies-tcb]`): trusted only insofar as you want
    /// the case-study proofs (deleting the case studies leaves the core engine intact):
    /// `{VerifiedLibraries,CaseStudies}/<Pkg>/Implementation/` and `third_party/` (C/Rust sources
    /// under test), `{VerifiedLibraries,CaseStudies}/<Pkg>/Spec*`,
    /// `{VerifiedLibraries,CaseStudies}/<Pkg>/Theorems*`,
    /// `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/*.bin` (excluding legacy `.code.bin`/`.data.bin`
    /// proof-cache sidecars), and the optional process-snapshot
    /// dumper `tools/proc-snapshot/` (whose trusted Rust sources also obey `tcb_test_code` and
    /// `tcb_rust_import`).
    #[serde(rename = "case-studies-tcb")]
    CaseStudiesTcb,
    /// Untrusted machine-checked proofs & proof automation (`[proof]`): `Arm64/Legacy/`, `ProofLib/`,
    /// `{VerifiedLibraries,CaseStudies}/<Pkg>.lean`,
    /// `{VerifiedLibraries,CaseStudies}/<Pkg>/Proofs/`, `Generated/` Lean modules other than
    /// `*PlacedObj` / `*PlacedObjShard<k>` / `*ExtractedObj` / `*ElfObj` (including legacy `*Obj`
    /// proof-cache modules and `.code.bin`/`.data.bin` sidecars), and
    /// `tools/rust-obj2lean/src/{untrusted_lemmas,untrusted_legacy_linker}/`.
    Proof,
    /// Validation suites and trust-model enforcement (`[testing]`):
    /// `{Arm64,ProofLib,VerifiedLibraries}/Testing/`,
    /// `{VerifiedLibraries,CaseStudies}/<Pkg>/Testing/`, Rust unit/integration tests inside
    /// `<Pkg>/Implementation/`, `tools/{isa-oracle,run-trusted-tests,sail-aarch64,unicorn-aarch64,tcb-map}/`,
    /// test files of the `tcb` Rust crates (`tests.rs`, `*_tests.rs`, `test_infra/`, ...; see
    /// [`is_test_path`]), `scripts/{tcb-map,dev/check-trust-guards.sh}`, and the Lean
    /// trust-enforcement checks [`TRUST_ENFORCEMENT_LEAN_FILES`].
    Testing,
    /// Build configuration, scripts, CI, and developer/review tooling (`[infra]`):
    /// `lakefile.lean`, `lean-toolchain`, `.github/`, `scripts/`, `tools/snapshot-link/`, and
    /// `tools/dev/**`.
    Infra,
    /// Markdown documentation (`[doc]`): all `*.md` files across the repository.
    Doc,
}

impl TrustCategory {
    pub const ALL: [TrustCategory; 6] = [
        TrustCategory::Tcb,
        TrustCategory::CaseStudiesTcb,
        TrustCategory::Proof,
        TrustCategory::Testing,
        TrustCategory::Infra,
        TrustCategory::Doc,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            TrustCategory::Tcb => "tcb",
            TrustCategory::CaseStudiesTcb => "case-studies-tcb",
            TrustCategory::Proof => "proof",
            TrustCategory::Testing => "testing",
            TrustCategory::Infra => "infra",
            TrustCategory::Doc => "doc",
        }
    }

    /// Whether this category is part of a trusted computing base (`tcb` or `case-studies-tcb`).
    pub const fn is_trusted(self) -> bool {
        matches!(self, TrustCategory::Tcb | TrustCategory::CaseStudiesTcb)
    }
}

impl fmt::Display for TrustCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Map a classified Lean module to its [`TrustCategory`]: `Equivalence` / `VerifiedLibraries` /
/// `FormalRfcs` / `Examples` specs and `Theorems` are `case-studies-tcb`; other specs (`Arm64`)
/// are core `tcb`.
pub const fn trust_category_of_class(class: ModuleClass) -> TrustCategory {
    match class.role {
        Role::Theorems => TrustCategory::CaseStudiesTcb,
        Role::Spec
            if matches!(
                class.lib,
                Lib::Equivalence | Lib::VerifiedLibraries | Lib::FormalRfcs | Lib::Examples
            ) =>
        {
            TrustCategory::CaseStudiesTcb
        }
        Role::Spec => TrustCategory::Tcb,
        Role::Proof => TrustCategory::Proof,
        Role::Test | Role::Fixture => TrustCategory::Testing,
    }
}

/// Whether a repo-relative path belongs to verified libraries, equivalence theory, or case studies
/// rather than the verification engine (`Equivalence/`, `VerifiedLibraries.lean`,
/// `VerifiedLibraries/`, `CaseStudies/`, `third_party/`, and
/// `tools/proc-snapshot/`).
pub fn is_case_study_path(rel_path: &str) -> bool {
    let rel = rel_path.trim_matches('/');
    rel.starts_with("Equivalence/")
        || rel == "VerifiedLibraries.lean"
        || rel.starts_with("VerifiedLibraries/")
        || rel.starts_with("CaseStudies/")
        || rel.starts_with("third_party/")
        || rel.starts_with("tools/proc-snapshot/")
}

/// Lean files outside `Testing/` that enforce the trust model rather than prove anything: the
/// `#trusted_closure` statement-integrity checks that `scripts/axiom-audit --strict` runs on
/// every audited theorem and package. Their path category is `testing` (trust-model
/// enforcement, like `tools/tcb-map/`), while their Lean module class stays that of their
/// library, so import layering is unchanged.
pub const TRUST_ENFORCEMENT_LEAN_FILES: &[&str] = &["ProofLib/TrustedClosure.lean"];

/// Classify any repo-relative file path into its [`TrustCategory`].
pub fn classify_path(rel_path: &str) -> Option<TrustCategory> {
    let rel = rel_path.trim_matches('/');
    if rel.is_empty() {
        return None;
    }
    if rel.ends_with(".md") {
        return Some(TrustCategory::Doc);
    }
    if TRUST_ENFORCEMENT_LEAN_FILES.contains(&rel) {
        return Some(TrustCategory::Testing);
    }
    // `.lean` files under `scripts/`, `tools/` and `docs/` are not package modules; they are
    // classified with their directory below.
    if rel.ends_with(".lean")
        && rel != "lakefile.lean"
        && !rel.ends_with("/lakefile.lean")
        && !rel.starts_with("scripts/")
        && !rel.starts_with("tools/")
        && !rel.starts_with("docs/")
    {
        let module = module_name_of_path(rel);
        return classify(&module).map(trust_category_of_class);
    }
    let parts: Vec<&str> = rel.split('/').collect();
    // Per-package Lake configuration (`Arm64/lakefile.toml`, `Arm64/Testing/lakefile.lean`,
    // `ProofLib/lake-manifest.json`, ...) is build configuration, like the root
    // `lakefile.lean` / `lake-manifest.json`.
    if matches!(
        parts[..],
        ["Arm64" | "ProofLib", "lakefile.toml" | "lake-manifest.json"]
            | [
                "Arm64",
                "Testing",
                "lakefile.toml" | "lakefile.lean" | "lake-manifest.json"
            ]
    ) {
        return Some(TrustCategory::Infra);
    }
    match parts[0] {
        "Arm64" => {
            if parts.get(1) == Some(&"Testing") {
                Some(TrustCategory::Testing)
            } else if parts.get(1) == Some(&"Legacy") {
                Some(TrustCategory::Proof)
            } else {
                Some(TrustCategory::Tcb)
            }
        }
        "third_party" => Some(TrustCategory::CaseStudiesTcb),
        "ProofLib" => Some(TrustCategory::Proof),
        // Non-`.lean` files of the `equivalence` package: Lake configuration is build
        // configuration and `Testing/` assets are tests; anything else fails closed.
        "Equivalence" => match parts.as_slice() {
            [
                "Equivalence",
                "lakefile.toml" | "lake-manifest.json" | "ci.toml",
            ] => Some(TrustCategory::Infra),
            ["Equivalence", "Testing", ..] => Some(TrustCategory::Testing),
            _ => None,
        },
        "CaseStudies" | "VerifiedLibraries" => {
            if matches!(
                parts.as_slice(),
                [
                    "VerifiedLibraries",
                    "lakefile.toml" | "lakefile.lean" | "lake-manifest.json" | "ci.toml"
                ]
            ) {
                return Some(TrustCategory::Infra);
            }
            if parts.get(1) == Some(&"Testing") {
                return Some(TrustCategory::Testing);
            }
            // Per-package files (`CaseStudies/<Pkg>/`, `VerifiedLibraries/<Pkg>/`) are classified
            // identically below the package directory.
            let depth = package_depth(&parts)?;
            classify_package_file_path(rel, &parts[depth..])
        }
        "tools" => {
            let category = match parts.get(1).copied() {
                Some("rust-obj2lean") => match (parts.get(2).copied(), parts.get(3).copied()) {
                    (Some("src"), Some("untrusted_lemmas" | "untrusted_legacy_linker"))
                        if !is_test_path(&parts[2..]) =>
                    {
                        Some(TrustCategory::Proof)
                    }
                    (Some("src"), _) => Some(TrustCategory::Tcb),
                    _ => Some(TrustCategory::Infra),
                },
                Some("proc-snapshot") => Some(TrustCategory::CaseStudiesTcb),
                Some(
                    "isa-oracle"
                    | "run-trusted-tests"
                    | "sail-aarch64"
                    | "unicorn-aarch64"
                    | "tcb-map",
                ) => Some(TrustCategory::Testing),
                Some("dev" | "snapshot-link" | "Cargo.toml" | "Cargo.lock") => {
                    Some(TrustCategory::Infra)
                }
                _ => None,
            };
            // Inside a TCB / case-study-TCB crate, only the trusted library code carries that
            // category:
            // - tests live in their own files and are not trusted (`tcb_test_code` rejects
            //   inline test code in the remaining `tcb` files);
            // - `[OUTSIDE TCB]` orchestration lives in `untrusted_*` modules (build drivers,
            //   CLI dispatch, subprocess runners), and `src/main.rs` is a binary entry stub that
            //   only calls into them (`tcb_rust_import` keeps `tcb` files from referencing
            //   either).
            if category.is_some_and(TrustCategory::is_trusted) && is_test_path(&parts[2..]) {
                Some(TrustCategory::Testing)
            } else if category.is_some_and(TrustCategory::is_trusted)
                && (is_untrusted_module_path(&parts[2..])
                    || matches!(parts[2..], ["src", "main.rs"]))
            {
                Some(TrustCategory::Infra)
            } else {
                category
            }
        }
        "scripts" => match (parts.get(1).copied(), parts.get(2).copied()) {
            (Some("tcb-map"), None) | (Some("dev"), Some("check-trust-guards.sh")) => {
                Some(TrustCategory::Testing)
            }
            _ => Some(TrustCategory::Infra),
        },
        ".github" | ".githooks" | ".agents" | "docs" | "lakefile.lean" | "lake-manifest.json"
        | "lean-toolchain" | "LICENSE" | "copy.bara.sky" | "AGENTIC_REVIEW" | ".gitignore"
        | ".gitattributes" | ".gitmodules" | ".semgrepignore" => Some(TrustCategory::Infra),
        _ => None,
    }
}

/// Classify a non-`.lean` file of a per-campaign package (`rel` is the repo-relative path, `rest`
/// its segments below the package directory, see [`package_depth`]): Lake/CI configuration and
/// `Proofs/.gitkeep` are `infra`, `Testing/**` is `testing`, `Implementation/**` is
/// `case-studies-tcb` except Rust test sources, `Generated/*.{code,data}.bin` sidecars are
/// `proof`, other `Generated/*.bin` payloads are `case-studies-tcb`; anything else fails closed.
fn classify_package_file_path(rel: &str, rest: &[&str]) -> Option<TrustCategory> {
    match rest {
        ["lakefile.toml" | "lakefile.lean" | "lake-manifest.json"] => Some(TrustCategory::Infra),
        ["ci.toml"] => Some(TrustCategory::Infra),
        ["Proofs", .., ".gitkeep"] => Some(TrustCategory::Infra),
        ["Testing", ..] => Some(TrustCategory::Testing),
        // Only Rust test sources are untrusted: C/C++ sources and headers under a `tests/`
        // directory may still be compiled into verified objects.
        ["Implementation", tail @ ..] if rel.ends_with(".rs") && is_test_path(tail) => {
            Some(TrustCategory::Testing)
        }
        ["Implementation", ..] => Some(TrustCategory::CaseStudiesTcb),
        ["Generated", ..] if rel.ends_with(".code.bin") || rel.ends_with(".data.bin") => {
            Some(TrustCategory::Proof)
        }
        ["Generated", ..] if rel.ends_with(".bin") => Some(TrustCategory::CaseStudiesTcb),
        _ => None,
    }
}

/// Whether a path (given as its segments) names test code: some directory or the file stem is
/// `tests` or starts with `test_` or ends with `_test` / `_tests` (e.g. `tests.rs`,
/// `foo_tests.rs`, `test_infra/`).
pub fn is_test_path(parts: &[&str]) -> bool {
    parts.iter().any(|part| {
        let stem = part.split_once('.').map_or(*part, |(stem, _)| stem);
        stem == "tests"
            || stem.starts_with("test_")
            || stem.ends_with("_test")
            || stem.ends_with("_tests")
    })
}

/// Whether a path inside a TCB crate (given as its segments) names an `[OUTSIDE TCB]` module:
/// some directory or file stem starts with `untrusted_` (e.g. `untrusted_driver/mod.rs`,
/// `untrusted_driver.rs`).
pub fn is_untrusted_module_path(parts: &[&str]) -> bool {
    parts.iter().any(|part| part.starts_with("untrusted_"))
}

// ---------------------------------------------------------------------------------------------
// 2. Forbidden Lean Constructs & Attributes (`LINE_RULES`, `FORBIDDEN_ATTRIBUTES`)
// ---------------------------------------------------------------------------------------------

/// Which Lean modules a [`LineRule`] applies to.
#[derive(Debug, Clone, Copy)]
pub enum Scope {
    All,
    /// Everything except `Fixture` modules.
    NonFixture,
    /// Everything except `Fixture` modules (`Spec`, `Proof`, `Theorems`, and non-fixture `Test`).
    Proved,
    /// Everything outside the `Testing` library (which no proof module may import).
    NonTesting,
    /// Everything outside `ProofLib/` and `Arm64/Testing/`.
    OutsideProofLibAndArm64Testing,
    /// Everything outside `Arm64/Legacy*`, `ProofLib/`, and `Arm64/Testing/`.
    OutsideLegacyLinkedImage,
    Spec,
    /// `Role::Spec` modules outside [`is_spec_macro_syntax_allowed`].
    SpecNonSurface,
    SpecOrTheorems,
    Theorems,
    Examples,
    ExamplesProof,
}

impl Scope {
    pub fn applies(self, class: ModuleClass) -> bool {
        self.applies_in(class, "")
    }

    pub fn applies_in(self, class: ModuleClass, path: &str) -> bool {
        match self {
            Scope::All => true,
            Scope::NonFixture | Scope::Proved => class.role != Role::Fixture,
            Scope::NonTesting => !matches!(class.lib, Lib::Arm64Testing | Lib::Testing),
            Scope::OutsideProofLibAndArm64Testing => {
                !matches!(class.lib, Lib::ProofLib | Lib::Arm64Testing)
                    && !path.starts_with("Arm64/Testing")
            }
            Scope::OutsideLegacyLinkedImage => {
                !matches!(class.lib, Lib::ProofLib | Lib::Arm64Testing)
                    && !(class.lib == Lib::Arm64 && class.role == Role::Proof)
                    && !path.starts_with("Arm64/Legacy")
                    && !path.starts_with("Arm64/Testing")
                    && !path.starts_with("ProofLib/")
            }
            Scope::Spec => class.role == Role::Spec,
            Scope::SpecNonSurface => {
                class.role == Role::Spec && !is_spec_macro_syntax_allowed(path)
            }
            Scope::SpecOrTheorems => matches!(class.role, Role::Spec | Role::Theorems),
            Scope::Theorems => class.role == Role::Theorems,
            Scope::Examples => matches!(
                class.lib,
                Lib::Equivalence
                    | Lib::VerifiedLibraries
                    | Lib::FormalRfcs
                    | Lib::Examples
                    | Lib::Theorems
            ),
            Scope::ExamplesProof => {
                matches!(
                    class.lib,
                    Lib::Equivalence | Lib::VerifiedLibraries | Lib::FormalRfcs | Lib::Examples
                ) && class.role == Role::Proof
            }
        }
    }
}

/// A forbidden construct, matched per line after comments and strings are stripped.
/// `message` may reference capture group 1 as `$1`.
pub struct LineRule {
    pub scope: Scope,
    pub triggers: &'static [&'static str],
    pub pattern: Regex,
    pub message: &'static str,
    /// Optional repo-relative `.lean` paths exempted from this line rule while campaign-local
    /// cleanup PRs complete (audited for staleness by unit tests).
    pub allowlist: &'static [&'static str],
}

/// Characters accepted by Lean 4's `isIdFirst` (`Init/Meta/Defs.lean`: `isLetterLike` and `_`).
pub const LEAN_ID_FIRST: &str = concat!(
    r"A-Za-z_",
    r"\u{00c0}-\u{00d6}\u{00d8}-\u{00f6}\u{00f8}-\u{00ff}\u{0100}-\u{017f}",
    r"\u{0391}-\u{039f}\u{03a1}-\u{03a2}\u{03a4}-\u{03a9}",
    r"\u{03b1}-\u{03ba}\u{03bc}-\u{03c9}\u{03ca}-\u{03fb}",
    r"\u{1f00}-\u{1ffe}\u{2100}-\u{214f}\u{1d49c}-\u{1d59f}",
);

/// Characters in Lean 4's `isIdRest` that are NOT in `isIdFirst` (digits, `'`, `!`, `?`, and
/// `isSubScriptAlnum`). A contiguous `LEAN_ID_REST` run starting with one of these characters is
/// never a single Lean identifier (e.g. `1notation`, `0x1fnotation`, `1.5notation`, `1e5notation`,
/// `[1]!notation`), so a keyword at the end of such a run is lexed as a separate token by Lean.
pub const LEAN_ID_NON_FIRST: &str = concat!(
    r"0-9'!?",
    r"\u{1d62}-\u{1d6a}\u{2080}-\u{2089}\u{2090}-\u{209c}\u{2c7c}",
);

/// Characters accepted by Lean 4's `isIdRest` (`Init/Meta/Defs.lean`: `isLetterLike`,
/// `isSubScriptAlnum`, ASCII alphanumerics, and `_`, `'`, `!`, `?`).
pub const LEAN_ID_REST: &str = concat!(
    r"A-Za-z0-9_'!?",
    r"\u{00c0}-\u{00d6}\u{00d8}-\u{00f6}\u{00f8}-\u{00ff}\u{0100}-\u{017f}",
    r"\u{0391}-\u{039f}\u{03a1}-\u{03a2}\u{03a4}-\u{03a9}",
    r"\u{03b1}-\u{03ba}\u{03bc}-\u{03c9}\u{03ca}-\u{03fb}",
    r"\u{1f00}-\u{1ffe}\u{2100}-\u{214f}\u{1d49c}-\u{1d59f}",
    r"\u{1d62}-\u{1d6a}\u{2080}-\u{2089}\u{2090}-\u{209c}\u{2c7c}",
);

/// Matches any `#<ident>` command token regardless of the preceding character (`#eval`, `x#eval`,
/// `1#eval`, `0#eval`, `0#postprocess_traces`, `é#eval`, `#eval[...]`, `#eval⟨...⟩`, `#eval«...»`,
/// `#eval@...`), exempting only `#v[...]` `Vector` literal syntax.
pub fn hash_cmd_regex() -> Regex {
    let id_first_no_v = concat!(
        r"A-Za-uw-z_",
        r"\u{00c0}-\u{00d6}\u{00d8}-\u{00f6}\u{00f8}-\u{00ff}\u{0100}-\u{017f}",
        r"\u{0391}-\u{039f}\u{03a1}-\u{03a2}\u{03a4}-\u{03a9}",
        r"\u{03b1}-\u{03ba}\u{03bc}-\u{03c9}\u{03ca}-\u{03fb}",
        r"\u{1f00}-\u{1ffe}\u{2100}-\u{214f}\u{1d49c}-\u{1d59f}",
    );
    Regex::new(&format!(
        r"(#(?:[{id_first_no_v}][{LEAN_ID_REST}]*|v[{LEAN_ID_REST}]+))(?:$|[^{LEAN_ID_REST}])|(#v)(?:$|[^\[{LEAN_ID_REST}])"
    ))
    .unwrap()
}

/// Matches `word` (a regex alternation) as a whole Lean identifier, captured as group 1.
/// Also excludes a leading `.` (hierarchical name / field projection), while still matching
/// keywords glued to a preceding number literal (including `<digits>.<frac>` and `<digits>.e<exp>`)
/// or non-`isIdFirst` token.
pub fn word(word: &str) -> Regex {
    let ident = format!(r"{LEAN_ID_REST}.\-");
    Regex::new(&format!(
        r"(?:^|[^{ident}])(?:[{LEAN_ID_NON_FIRST}][{LEAN_ID_REST}.]*)?({word})(?:$|[^{ident}])"
    ))
    .unwrap()
}

/// Matches `word` (a regex alternation) as a Lean identifier segment, captured as group 1,
/// without excluding `.` or `-` boundaries (so `.kw`, `x.kw`, `0 -kw`, and number-glued forms
/// such as `1notation`, `0x1fnotation`, `1.5notation`, `1.e5notation`, `1.0e-3notation` also match).
pub fn word_no_dot(word: &str) -> Regex {
    Regex::new(&format!(
        r"(?:^|[^{LEAN_ID_REST}])(?:[{LEAN_ID_NON_FIRST}][{LEAN_ID_REST}.]*)?({word})(?:$|[^{LEAN_ID_REST}])"
    ))
    .unwrap()
}

/// Declaration and `attribute [...]` attributes forbidden in every module, with the reason.
/// Matched against each entry of every `@[...]` and `attribute [...]` list (see
/// [`crate::lex::declaration_attributes`]).
pub const FORBIDDEN_ATTRIBUTES: &[(&str, &str)] = &[
    ("implemented_by", "swaps in unverified code"),
    ("extern", "swaps in unverified foreign code"),
];

/// Declaration and `attribute [...]` attributes forbidden in `Role::Spec` and `Role::Theorems`
/// modules (outside [`is_spec_macro_syntax_allowed`]), with the reason.
pub const SPEC_FORBIDDEN_ATTRIBUTES: &[(&str, &str)] = &[
    ("term_elab", "registers a custom term elaborator in a Spec module"),
    ("builtin_term_elab", "registers a custom term elaborator in a Spec module"),
    ("command_elab", "registers a custom command elaborator in a Spec module"),
    ("builtin_command_elab", "registers a custom command elaborator in a Spec module"),
    ("tactic", "registers a custom tactic elaborator in a Spec module"),
    ("builtin_tactic", "registers a custom tactic elaborator in a Spec module"),
    ("macro", "registers a custom macro expander in a Spec module"),
    ("builtin_macro", "registers a custom macro expander in a Spec module"),
    ("term_parser", "registers a custom term parser in a Spec module"),
    ("builtin_term_parser", "registers a custom term parser in a Spec module"),
    ("command_parser", "registers a custom command parser in a Spec module"),
    ("builtin_command_parser", "registers a custom command parser in a Spec module"),
    ("tactic_parser", "registers a custom tactic parser in a Spec module"),
    ("builtin_tactic_parser", "registers a custom tactic parser in a Spec module"),
    ("attr_parser", "registers a custom attribute parser in a Spec module"),
    ("builtin_attr_parser", "registers a custom attribute parser in a Spec module"),
    ("delab", "registers a custom delaborator in a Spec module"),
    ("builtin_delab", "registers a custom delaborator in a Spec module"),
    ("app_delab", "registers a custom application delaborator in a Spec module"),
    ("builtin_app_delab", "registers a custom application delaborator in a Spec module"),
    ("app_unexpander", "registers a custom unexpander in a Spec module"),
    ("builtin_app_unexpander", "registers a custom unexpander in a Spec module"),
    ("elab_without_expected_type", "registers an elaborator hook in a Spec module"),
    ("init", "runs arbitrary initialization code in a Spec module"),
    ("builtin_init", "runs arbitrary initialization code in a Spec module"),
    ("csimp", "rewrites definitions during compilation in a Spec module"),
];

/// Reviewed non-`Arm64/Trusted/Surface/` `Role::Spec` files that define separation-logic notations
/// (self-audited in `tests.rs` alongside `Arm64/Trusted/Surface/*.lean` so stale entries fail
/// closed).
pub const SPEC_MACRO_SYNTAX_ALLOWLIST: &[&str] = &["Arm64/Trusted/Spec/SepLogic.lean"];

/// Whether `path` (repo-relative) is allowed to define surface syntax, macros, elaborators, or
/// notations: direct children `Arm64/Trusted/Surface/<Name>.lean` by directory convention (nested
/// `Arm64/Trusted/Surface/<Dir>/**` files are **not** exempt, so every exempt file is enumerated by
/// the non-recursive self-audit in `tests.rs`), plus [`SPEC_MACRO_SYNTAX_ALLOWLIST`].
pub fn is_spec_macro_syntax_allowed(path: &str) -> bool {
    path.strip_prefix("Arm64/Trusted/Surface/")
        .is_some_and(|rest| rest.ends_with(".lean") && !rest.contains('/'))
        || SPEC_MACRO_SYNTAX_ALLOWLIST.contains(&path)
}

pub static LINE_RULES: LazyLock<Vec<LineRule>> = LazyLock::new(|| {
    use Scope::*;
    let rule = |scope, triggers: &'static [&'static str], pattern: Regex, message| LineRule {
        scope,
        triggers,
        pattern,
        message,
        allowlist: &[],
    };
    vec![
        // Soundness: nothing may add axioms, leave holes, or bypass the kernel. `Fixture` modules
        // (deliberately unsound inputs for the axiom-audit regression tests) are exempt from the
        // first four rules.
        rule(
            NonFixture,
            &["axiom"],
            Regex::new(
                r"^\s*(?:(?:@\[[^\]]*\]|private|protected|public|meta|noncomputable|unsafe|nonrec|local|scoped)\s+)*axiom\b",
            )
            .unwrap(),
            "axiom",
        ),
        rule(Proved, &["sorry", "admit"], word("sorry|admit"), "$1"),
        rule(
            NonFixture,
            &["native_decide"],
            word("native_decide"),
            "native_decide (trusts the compiler)",
        ),
        rule(
            NonFixture,
            &["+native"],
            Regex::new(r"\b(decide\s*\+native)\b").unwrap(),
            "$1 (trusts the compiler)",
        ),
        // Metaprograms that build `Lean.ofReduceBool` proofs directly bypass the `native_decide`
        // keyword check; only the `Testing` audit tooling (which must name them) may mention them.
        rule(
            NonTesting,
            &["ofReduceBool", "ofReduceNat", "trustCompiler"],
            word("(?:Lean\\.)?(?:ofReduceBool|ofReduceNat|trustCompiler)"),
            "$1 (trusts the compiler)",
        ),
        rule(All, &["unsafe"], word("unsafe"), "unsafe (bypasses the kernel)"),
        // Theorems modules state and prove closed end-to-end theorems; every constant in a
        // theorem statement comes from imported Spec modules rather than local definitions or
        // opened namespaces.
        rule(
            Theorems,
            &[
                "def",
                "abbrev",
                "lemma",
                "instance",
                "structure",
                "inductive",
                "class",
                "opaque",
                "example",
                "macro",
                "macro_rules",
                "syntax",
                "elab",
                "elab_rules",
                "declare_syntax_cat",
                "declare_simp_like_tactic",
                "register_simp_attr",
                "register_option",
                "declare_config_elab",
                "unif_hint",
                "simproc",
                "builtin_simproc",
                "dsimproc",
                "builtin_dsimproc",
                "notation",
                "notation3",
                "binder_predicate",
                "infix",
                "infixl",
                "infixr",
                "prefix",
                "postfix",
                "attribute",
                "initialize",
                "builtin_initialize",
                "run_cmd",
                "run_elab",
                "run_meta",
                "run_tac",
            ],
            word_no_dot(
                "def|abbrev|lemma|instance|structure|inductive|class|opaque|example|macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|declare_simp_like_tactic|register_simp_attr|register_option|declare_config_elab|unif_hint|simproc|builtin_simproc|dsimproc|builtin_dsimproc|notation|notation3|binder_predicate|infix|infixl|infixr|prefix|postfix|attribute|initialize|builtin_initialize|run_cmd|run_elab|run_meta|run_tac",
            ),
            "`$1` in Theorems module (Theorems modules state and prove `theorem` declarations only)",
        ),
        rule(
            Theorems,
            &["#"],
            hash_cmd_regex(),
            "`$1$2` in Theorems module (Theorems modules state and prove `theorem` declarations only)",
        ),
        rule(
            Theorems,
            &["open", "export", "private", "local", "scoped"],
            word_no_dot("open|export|private|local|scoped"),
            "`$1` in Theorems module (forbid `open`/`export` so Proof namespaces and scoped notations cannot shadow Spec names, and forbid `private`/`local`/`scoped` so every theorem is publicly exported; qualify external names with `_root_.`)",
        ),
        // Spec modules state definitions only.
        rule(
            Spec,
            &["theorem", "lemma"],
            Regex::new(r"^\s*(?:(?:private|protected|public|nonrec)\s+)*(?:theorem|lemma)\b")
                .unwrap(),
            "theorem/lemma in Spec module (Spec modules contain definitions only)",
        ),
        rule(
            Spec,
            &["partial"],
            Regex::new(&format!(
                r"(?:^|[^{LEAN_ID_REST}.\-`])(?:[{LEAN_ID_NON_FIRST}][{LEAN_ID_REST}.]*)?partial\s+(?:(?:public|meta|noncomputable)\s+)*(?:def|abbrev)\b"
            ))
            .unwrap(),
            "partial def in Spec module (introduces an opaque constant)",
        ),
        rule(
            SpecOrTheorems,
            &["maxHeartbeats"],
            Regex::new(r"set_option\s+maxHeartbeats\s+0(?:$|[^0-9])").unwrap(),
            "set_option maxHeartbeats 0 in Spec/Theorems module (use a finite budget)",
        ),
        rule(
            SpecOrTheorems,
            &["autoImplicit", "relaxedAutoImplicit"],
            Regex::new(r"set_option\s+(autoImplicit|relaxedAutoImplicit)\s+true\b").unwrap(),
            "set_option $1 true in Spec/Theorems module (auto-bound typos silently alter specs)",
        ),
        rule(
            SpecNonSurface,
            &[
                "macro",
                "macro_rules",
                "syntax",
                "elab",
                "elab_rules",
                "declare_syntax_cat",
                "declare_simp_like_tactic",
                "register_option",
                "declare_config_elab",
                "unif_hint",
                "simproc",
                "builtin_simproc",
                "dsimproc",
                "builtin_dsimproc",
                "notation",
                "notation3",
                "binder_predicate",
                "run_cmd",
                "run_elab",
                "run_meta",
                "run_tac",
                "initialize",
                "builtin_initialize",
                "infix",
                "infixl",
                "infixr",
                "prefix",
                "postfix",
            ],
            word_no_dot(
                "macro_rules|elab_rules|declare_syntax_cat|declare_simp_like_tactic|register_option|declare_config_elab|unif_hint|simproc|builtin_simproc|dsimproc|builtin_dsimproc|notation3|binder_predicate|run_cmd|run_elab|run_meta|run_tac|initialize|builtin_initialize|infixl|infixr|macro|syntax|elab|notation|infix|prefix|postfix",
            ),
            "`$1` in Spec module (Spec modules state definitions only; syntax/macro/elaborator extensions can shadow spec vocabulary)",
        ),
        rule(
            Spec,
            &["register_simp_attr"],
            word_no_dot("register_simp_attr"),
            "`$1` in Spec module (Spec modules state definitions only; syntax/macro/elaborator extensions can shadow spec vocabulary)",
        ),
        rule(
            Spec,
            &["#"],
            hash_cmd_regex(),
            "`$1$2` command in Spec module (Spec modules state definitions only)",
        ),
        rule(
            ExamplesProof,
            &["notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix"],
            Regex::new(
                r"^\s*(?:(?:@\[[^\]]*\]|public|private|noncomputable)\s+)*(notation3?|infix[lr]?|prefix|postfix)\b",
            )
            .unwrap(),
            "unscoped `$1` in Examples proof module (prefix with `local` or `scoped` so Proof notations cannot leak into Theorems modules)",
        ),
    ]
});
