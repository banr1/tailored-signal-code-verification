# `tcb-map` — Repository Trust Classification & Soundness Auditor

`tcb-map` (`scripts/tcb-map`) is the self-contained auditor-facing tool (`[AUDIT/LINTER]`, classified as `[testing]`) that maps every file in the repository into one of six explicit trust buckets and enforces Lean import layering, role purity, package isolation, and core soundness invariants. It has zero internal workspace dependencies so an external auditor can read `tools/tcb-map/src/` end to end.

## Which File to Read

| Question | File |
| --- | --- |
| Which paths belong to `tcb`, `case-studies-tcb`, `proof`, `testing`, `infra`, or `doc`, and which Lean constructs/attributes are forbidden? | [`src/policy.rs`](./src/policy.rs) |
| How are `.lean` modules discovered and mapped to `(Lib, Role)` by directory convention? | [`src/discovery.rs`](./src/discovery.rs) |
| How are import-DAG layering, `CoreInitOnly` vs. `SurfaceMacro` isolation, pairwise `CaseStudies/<Pkg>/` independence, and `Theorems` purity checked? | [`src/lib.rs`](./src/lib.rs) |
| How are Lean comments, string literals, `import` headers, and `@[...]` / `attribute [...]` lists lexed? | [`src/lex.rs`](./src/lex.rs) |
| How does `tcb-map` verify that `[tcb]` and `[case-studies-tcb]` Rust files never import non-`[tcb]` workspace crates, `untrusted_*` modules, or test modules? | [`src/tcb_rust_import.rs`](./src/tcb_rust_import.rs) |
| How are `--tree` and `--tree-json` rendered and LOC totals computed? | [`src/tree.rs`](./src/tree.rs) |
| CLI flags and exit codes | [`src/main.rs`](./src/main.rs) |

## Core Soundness Invariants

1. **Exhaustive, fail-closed path classification** ([`classify_path`](./src/policy.rs)): every tracked or non-ignored repository file maps to exactly one `TrustCategory` (`tcb`, `case-studies-tcb`, `proof`, `testing`, `infra`, `doc`). Unrecognized paths fail closed with `[unclassified-path]`.
2. **Two-tier `Arm64` TCB boundary** ([`classify_trusted_tcb_module`](./src/policy.rs)):
   - `CoreInitOnly` (`Arm64/Trusted/{ISA,Object,Process,Syscalls,Spec}/**`, `Arm64/Trusted/Syscalls.lean`): `Init`-only semantic core; cannot import `Lean`, `Std`, or `SurfaceMacro` modules.
   - `SurfaceMacro` (`Arm64/Trusted/Surface/**` and barrels `Arm64.lean`, `Arm64/Trusted.lean`, `Arm64/Trusted/Process.lean`): surface DSL macros, elaborators, and binary-inclusion helpers.
   - Any non-`Testing` `Arm64` module outside these locations fails closed under `core-tcb-init-only`.
3. **Fail-closed campaign subdirectory roles & library layering** ([`classify`](./src/discovery.rs)):
   - Library DAG: `Arm64 < ProofLib < VerifiedLibraries < FormalRfcs < Examples` (`CaseStudies`), with `Equivalence` (`Equivalence/**`) directly above `ProofLib` and importable only by `Examples`, `Testing`, and `Theorems`, `Arm64Testing` (`Arm64/Testing/**`) decoupled directly above `ProofLib`, `Testing` at the top for non-engine tests, and `Theorems` as a strict sink importing `Spec`, `Proof`, and `Theorems` only.
   - Inside `Equivalence/`, every `.lean` module must reside in `Spec/` (`Role::Spec`, `case-studies-tcb`), `Proofs/` (`Role::Proof`), or `Testing/`; stray files fail closed.
   - Inside `FormalRfcs/` (`FormalRfcs` library: may import `Arm64`, `ProofLib`, and `VerifiedLibraries`, never `Equivalence` or `Arm64Testing`), every `.lean` module outside a per-implementation package must reside in `<Rfc>/Spec/` (`Role::Spec`, `case-studies-tcb`; including `Common/Spec/`), `<Rfc>/Proofs/` (`Role::Proof`), or `<Rfc>/Testing/`; stray files fail closed. A per-implementation package `FormalRfcs/<Rfc>/<Impl>/` (`<Rfc>` not `Common`, `<Impl>` not a role directory such as `Spec`/`Proofs`/`Testing`) is classified exactly like `CaseStudies/<Pkg>/` (`Examples`).
   - Inside `VerifiedLibraries/<Pkg>/` and `CaseStudies/<Pkg>/`, every `.lean` module must reside in `<Pkg>.lean`, `Spec[.lean]`, `Proofs/`, `Generated[.lean]`, `Theorems[.lean]`, or `Testing[.lean]`; stray files return `None` and fail closed.
   - `CaseStudies/<Pkg>/` and `FormalRfcs/<Rfc>/<Impl>/` packages are strictly pairwise independent (`package-isolation`): share pure specifications via `VerifiedLibraries/Common/Spec/` or `FormalRfcs/<Rfc>/Spec/` and verified libraries via `VerifiedLibraries/<Lib>/`.
4. **Role purity & no soundness escapes** ([`LINE_RULES`](./src/policy.rs), [`FORBIDDEN_ATTRIBUTES`](./src/policy.rs)):
   - Zero `axiom`, `sorry`, `admit`, `native_decide`, `decide +native`, `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`, `unsafe`, `@[implemented_by]`, or `@[extern]` outside `Role::Fixture` negative-test modules.
   - `Role::Spec` modules state definitions only (no `theorem`/`lemma`, `partial def`, `#` commands, `register_simp_attr`, or custom elaborators/notations outside `Arm64/Trusted/Surface/*.lean` and `Arm64/Trusted/Spec/SepLogic.lean`).
   - `Role::Theorems` modules state and prove public `theorem` declarations only, using `public import` for `Spec`/`Theorems` and private `import` for `Proof`, with zero `def`/`abbrev`/`open`/`export`/`private`/`local`/`scoped` declarations.
5. **Self-contained `[tcb]` Rust crates** ([`tcb_rust_import.rs`](./src/tcb_rust_import.rs)): trusted Rust files under `tools/rust-obj2lean/` and `tools/proc-snapshot/` never reference non-`[tcb]` workspace crates, `untrusted_*` modules, or test modules.
6. **Whole-process theorems do not trust library specs** (`whole-process-no-library-specs`, [`WHOLE_PROCESS_PACKAGES`](./src/policy.rs), [`LIBRARY_SPEC_MODULES`](./src/policy.rs)): the trusted closure of each whole-process case study's and `FormalRfcs/`'s `Spec`/`Theorems` modules (trusted edges only; generated `*ElfObj`/`*PlacedObj`/`*ExtractedObj` modules followed through their emitted header) contains none of the 12 library-spec modules (`Arm64.Trusted.Spec.{SepLogic,Hoare,GlobalAlloc,RustAbi,RustHeap,Placed,RustRuntime,SepLogicModel}`, `Arm64.Trusted.Surface.{Abi,CType}`, `Arm64.Trusted.Process.{Placed,OverrideWellBehaved}`). `tcb-map --whole-process-closure` prints the engine modules and line counts of these closures.

## Canonical Convention Table

Synchronized with [`src/policy.rs`](./src/policy.rs) and enforced against live [`classify_path`](./src/policy.rs) / [`classify`](./src/discovery.rs) behavior by unit tests in [`src/tests.rs`](./src/tests.rs):

<!-- BEGIN CANONICAL CONVENTION TABLE -->
| Pattern | Sample Path | Trust Bucket | Lean Role / Tier | Notes |
| --- | --- | --- | --- | --- |
| `**/*.md` | `README.md` | `doc` | `-` | All Markdown documentation across the repository |
| `Arm64/Trusted/{ISA,Object,Process,Syscalls,Spec}/**.lean`, `Arm64/Trusted/Syscalls.lean` | `Arm64/Trusted/ISA/Decode.lean` | `tcb` | `Arm64:Spec` (`CoreInitOnly`) | `Init`-only semantic core (`SepLogic.lean` is the sole notation allowlist entry) |
| `Arm64/Trusted/Surface/**.lean`, `Arm64.lean`, `Arm64/Trusted.lean`, `Arm64/Trusted/Process.lean` | `Arm64/Trusted/Surface/Abi.lean` | `tcb` | `Arm64:Spec` (`SurfaceMacro`) | Surface DSL macros/elaborators and package barrels |
| `Arm64/Legacy.lean`, `Arm64/Legacy/**.lean` | `Arm64/Legacy/Object/LinkedImage.lean` | `proof` | `Arm64:Proof` | Deprecated `[OUTSIDE TCB]` `LinkedImage` compatibility modules (shrinking importer allowlist) |
| `Arm64/Testing/**.lean` (`.Fixtures` at depth >= 4) | `Arm64/Testing/Audit/AxiomAudit/Fixtures.lean` | `testing` | `Arm64Testing:Fixture` | Deliberately unsound audit fixtures (importable only by parent module) |
| `Arm64/Testing/**` (other `.lean` and non-Lake assets) | `Arm64/Testing/AsciiTests.lean` | `testing` | `Arm64Testing:Test` | Engine-level tests decoupled from `VerifiedLibraries` and `CaseStudies` |
| `ProofLib.lean`, `ProofLib/**.lean` (outside `Testing/` and `TRUST_ENFORCEMENT_LEAN_FILES`) | `ProofLib/SimpAttrs.lean` | `proof` | `ProofLib:Proof` | Untrusted reusable proof automation and lemmas |
| `ProofLib/TrustedClosure.lean` | `ProofLib/TrustedClosure.lean` | `testing` | `ProofLib:Proof` | Trust-model enforcement: `#trusted_closure` statement-integrity checks run by `scripts/axiom-audit --strict` (`TRUST_ENFORCEMENT_LEAN_FILES`) |
| `Equivalence/Spec/**.lean` | `Equivalence/Spec/Basic.lean` | `case-studies-tcb` | `Equivalence:Spec` | Definition-only trusted program-equivalence vocabulary |
| `Equivalence/Proofs/**.lean` | `Equivalence/Proofs/Basic.lean` | `proof` | `Equivalence:Proof` | Untrusted kernel-checked equivalence lemmas (adequacy, driver linking) |
| `{ProofLib,Equivalence,VerifiedLibraries}/Testing/**.lean`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Testing/**.lean` (`.Fixtures` at depth >= 4) | `ProofLib/Testing/AxiomAudit/Fixtures.lean` | `testing` | `Testing:Fixture` | Deliberately unsound audit fixtures |
| `{ProofLib,Equivalence,VerifiedLibraries}/Testing/**`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Testing/**` (other files) | `CaseStudies/Alpha/Testing/SpecAudit.lean` | `testing` | `Testing:Test` | Spec audits, golden vectors, and unverified host test harnesses/runners |
| `VerifiedLibraries.lean`, `{VerifiedLibraries,CaseStudies}/<Pkg>.lean` | `CaseStudies/Alpha.lean` | `proof` | `Examples:Proof` | Package umbrella barrels (`VerifiedLibraries:Proof` under `VerifiedLibraries/`) |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Spec.lean`, `.../Spec/**.lean` | `CaseStudies/Alpha/Spec/Top.lean` | `case-studies-tcb` | `Examples:Spec` | Definition-only trusted specifications (`VerifiedLibraries:Spec` under `VerifiedLibraries/`) |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Proofs/**.lean` | `CaseStudies/Alpha/Proofs/Main.lean` | `proof` | `Examples:Proof` | Untrusted kernel-checked proofs (`VerifiedLibraries:Proof` under `VerifiedLibraries/`) |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/{*PlacedObj,*PlacedObjShard<k>,*ExtractedObj,*ElfObj}.lean` | `CaseStudies/Alpha/Generated/AlphaPlacedObj.lean` | `case-studies-tcb` | `Examples:Spec` | Generated trusted placed-library, pre-link extracted-object, and ELF object definitions (and `placed_shards` code shards) |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/*.bin` (except `*.{code,data}.bin`) | `CaseStudies/Alpha/Generated/AlphaPlacedObj.bin` | `case-studies-tcb` | `-` | Extracted target binary payloads |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated.lean`, `.../Generated/**.lean` (other) | `CaseStudies/Alpha/Generated/AlphaCode.lean` | `proof` | `Examples:Proof` | Generated instruction/decode/placement proof modules and `[OUTSIDE TCB]` legacy `*Obj` proof cache |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Generated/*.{code,data}.bin` | `CaseStudies/Alpha/Generated/AlphaObj.code.bin` | `proof` | `-` | `[OUTSIDE TCB]` legacy `LinkedImage` proof-cache binary sidecars |
| `VerifiedLibraries/Theorems[.lean]`, `{VerifiedLibraries,CaseStudies}/<Pkg>/Theorems[.lean]` | `CaseStudies/Alpha/Theorems/Top.lean` | `case-studies-tcb` | `Theorems:Theorems` | Closed `theorem`-only end-to-end statements (`Theorems` sink) |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Implementation/**` (Rust unit/integration tests) | `CaseStudies/Alpha/Implementation/src/tests.rs` | `testing` | `-` | Only `*.rs` files matching `is_test_path` (including `tests/`; never linked into verified objects); `.c`/`.h` under `tests/` stay `case-studies-tcb` |
| `{VerifiedLibraries,CaseStudies}/<Pkg>/Implementation/**` (target sources & build configs) | `CaseStudies/Alpha/Implementation/src/lib.rs` | `case-studies-tcb` | `-` | Verified C/Rust target inputs, translation configs, and linked ELFs |
| `third_party/**` | `third_party/vendor/src/lib.c` | `case-studies-tcb` | `-` | Vendored upstream sources compiled into case studies |
| `tools/rust-obj2lean/src/{trusted_*,lib.rs}` | `tools/rust-obj2lean/src/lib.rs` | `tcb` | `-` | Core ELF extraction TCB (`tcb-rust-import` enforced) |
| `tools/rust-obj2lean/src/{untrusted_lemmas,untrusted_legacy_linker}/**` (non-test) | `tools/rust-obj2lean/src/untrusted_lemmas/mod.rs` | `proof` | `-` | Untrusted Lean proof-module codegen and `[OUTSIDE TCB]` legacy `LinkedImage` proof-cache exporter |
| `tools/proc-snapshot/src/**` (trusted modules) | `tools/proc-snapshot/src/lib.rs` | `case-studies-tcb` | `-` | Process-snapshot dumper (`tcb-rust-import` enforced) |
| `tools/{rust-obj2lean,proc-snapshot}/**` (`tests`, `*_test.rs`, `test_infra`) | `tools/rust-obj2lean/src/tests.rs` | `testing` | `-` | Separated unit/integration tests of `[tcb]`/`[case-studies-tcb]` crates |
| `tools/{rust-obj2lean,proc-snapshot}/**` (`untrusted_*`, `src/main.rs`, `Cargo.toml`) | `tools/rust-obj2lean/src/main.rs` | `infra` | `-` | Untrusted CLI/driver orchestration and crate manifests |
| `tools/{isa-oracle,run-trusted-tests,sail-aarch64,unicorn-aarch64,tcb-map}/**` | `tools/tcb-map/src/lib.rs` | `testing` | `-` | Differential ISA/loader harnesses and self-contained TCB auditor |
| `tools/snapshot-link/**`, `tools/Cargo.{toml,lock}`, `tools/dev/**` | `tools/dev/repo-lints/src/lib.rs` | `infra` | `-` | Snapshot linker, workspace manifests, and developer/CI/review tools |
| `scripts/tcb-map`, `scripts/dev/check-trust-guards.sh` | `scripts/tcb-map` | `testing` | `-` | Trust-guard entrypoints |
| `scripts/**` (other scripts), `.github/**`, `.githooks/**`, `.agents/**`, `docs/**`, Lake/CI/git configs | `scripts/dev/pre-push-check` | `infra` | `-` | Build, CI, developer automation, and package manifests (`lakefile.*`, `ci.toml`) |
<!-- END CANONICAL CONVENTION TABLE -->

## Usage

```bash
# Render the full repository trust hierarchy and totals
./scripts/tcb-map --tree

# Render the core engine trust hierarchy only (excluding VerifiedLibraries/, CaseStudies/, third_party/, tools/proc-snapshot/)
./scripts/tcb-map --tree --no-case-studies

# Emit pretty-printed JSON hierarchy (e.g. for interactive inspection with fx)
./scripts/tcb-map --tree-json

# Run full TCB classification, import-DAG, role-purity, and soundness checks
./scripts/tcb-map --check
```
