# `tools/` — Host Rust Workspace & Verification Tooling

Shipped binary-translation, TCB-auditing, process-snapshot, and ISA differential-testing crates live in [`tools/Cargo.toml`](./Cargo.toml). Internal contributor, CI, and audit-linting crates live in the standalone developer workspace `tools/dev/Cargo.toml`; interactive Lean 4 inspection and disassembly commands are provided by `tools/dev/lean-sig/` (forwarding to `.agents/skills/lean-signatures/lean-sig`).

> **Important (`--release` Requirement):** Always invoke workspace binaries with `--release` (`cargo run --release --locked --manifest-path tools/Cargo.toml --bin <tool> -- ...`, or `tools/dev/Cargo.toml` for developer crates). Repository-wide scanners and binary translation drivers process hundreds of megabytes of generated Lean modules and ELF sections; debug builds are an order of magnitude slower and fail the CI runtime budget on `check-trust-guards`. Keep `cargo test --locked --manifest-path tools/Cargo.toml` (and `--manifest-path tools/dev/Cargo.toml`) without `--release` (`[profile.dev]` builds crate tests with `opt-level = 1` and dependencies with `opt-level = 3`).

## Quick Lookup Table: Which Tool to Run or Read for X

| Task / Question ("X") | Tool / Directory | Trust Role | Command / Entry Point |
| :--- | :--- | :--- | :--- |
| **Compile Rust/C to `.o` and emit placed `<ObjName>PlacedObj.lean` + `.bin` sidecars** | [`rust-obj2lean`](./rust-obj2lean/README.md) (`untrusted_driver` + `trusted_*` + `untrusted_placed`) | `[TCB]` / `[OUTSIDE TCB]` | `cargo run --release --locked --manifest-path tools/Cargo.toml --bin rust-obj2lean -- --config <translation.toml>` |
| **Emit `<ObjName>PlacedCode.lean`, fetch/decode lemmas, and `<Target>Index.json` sidecars** | [`rust-obj2lean`](./rust-obj2lean/README.md) (`untrusted_placed` + `untrusted_lemmas`) | `[OUTSIDE TCB]` | Same as above (or `rust-obj2lean fetch-decode-lemmas`) |
| **Run fast (<5 ms) multi-path ARM64 symbolic execution & stack-slot advisor** | [`rust-obj2lean`](./rust-obj2lean/README.md) (`symexec`) / `tools/dev/lean-sig` | `[OUTSIDE TCB]` | `tools/dev/lean-sig/lean-sig symexec <Target> <symbol>` |
| **Outline a `.lean` file, search lemmas, check live tactic goals/diagnostics, auto-fix unused simp args, disassemble, or check axioms** | `tools/dev/lean-sig` | `[OUTSIDE TCB]` / `[AUDIT/LINTER]` | `tools/dev/lean-sig/lean-sig <outline\|lookup\|query\|goal\|check\|fix-simp-args\|symexec\|disasm\|axioms> ...` |
| **Print the `[tcb]`/`[case-studies-tcb]`/`[proof]`/`[testing]`/`[infra]`/`[doc]` directory hierarchy and enforce `Spec`/`Proof`/`Theorems` import isolation, library layering, and core soundness rules (`sorry`, `axiom`, `unsafe`, `native_decide`, `@[implemented_by]`, `@[extern]`, `@[csimp]`)** | [`tcb-map`](./tcb-map/README.md) | `[AUDIT/LINTER]` | `scripts/tcb-map --tree` (or `scripts/tcb-map --check`) |
| **Enforce repository-wide campaign, `HookSat`, symbol-table, `ProcessInputs`, `c_type_spec`, SepLogic, and `ProofLib` lints (plus `tcb-map --check`)** | `tools/dev/repo-lints` | `[AUDIT/LINTER]` | `scripts/dev/check-trust-guards.sh` (or `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin repo-lints`) |
| **Check relative Markdown links, `#L<N>` line anchors, and `#<heading>` anchors across `*.md` files** | `tools/dev/repo-lints` (`check-md-links`) | `[AUDIT/LINTER]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin check-md-links` |
| **Lint PR descriptions (cited identifiers, Spec counts, `*/Testing/` `#spec_lint` & `#spec_nonvacuous!` registration, git ancestry)** | `tools/dev/pr-audit-check` | `[AUDIT/LINTER]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin pr-audit-check -- --pr-body <file-or-PR#>` |
| **Compute per-function stepped instruction coverage (`full`/`partial`/`guard-only`) and `Expr`-level precondition lints** | `tools/dev/spec-coverage` | `[AUDIT/LINTER]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin spec-coverage -- <Proof.lean> --spec <Spec.lean>` |
| **Mechanically port a static separation-logic atom (e.g. `A.pool : SepProp`) to its state-indexed form (`A.pool s0` / `A.pool sf`) in `c_spec` clauses, and count the bare sites left for hand fixes** | `tools/dev/state-index-sweep` | `[OUTSIDE TCB]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin state-index-sweep -- --atom A.pool [--dry] <File.lean>...`; per-theorem variants: `... -- p-variant <File.lean> <Spec> <thm> --extra 'Rel s0 sf'` / `... -- s-variant <File.lean> <Spec> <thm> --atom A.pool --from-ty <T> --to-ty <T'> --lift <f> --bridge <tac>` |
| **Dump an AArch64 process snapshot (memory regions + registers at exec entry and `main`) under qemu-aarch64 user mode** | [`proc-snapshot`](./proc-snapshot/README.md) | `[CASE-STUDIES TCB]` | `cargo run --release --locked --manifest-path tools/Cargo.toml --bin proc-snapshot -- snapshot --elf <bin> --qemu "$(scripts/fetch-qemu-aarch64)" --out-dir <dir>` |
| **Link a `translation.toml` build with stock `ld.lld` into a static AArch64 musl executable (input for `proc-snapshot` and whole-ELF placement witnesses)** | [`snapshot-link`](./snapshot-link/README.md) | `[OUTSIDE TCB]` | `cargo run --release --locked --manifest-path tools/Cargo.toml --bin snapshot-link -- --stock --config CaseStudies/<Campaign>/Implementation/translation.toml --out-dir <dir>` |
| **Extract ABI/stack/callee skeletons, probe AArch64 Rust type layouts in Unicorn, or validate external `Hooks` contracts (`HookSat`)** | `tools/dev/spec-oracle` | `[AUDIT/LINTER]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin spec-oracle -- <abi\|probe-layout\|validate-hooks> ...` |
| **Generate sorted Lean code-point range lists from vendored Unicode Character Database files (General_Category, `PropList.txt` properties), or `--check` that a committed table regenerates byte for byte** | `tools/dev/ucd-tables` | `[CASE-STUDIES TCB]` (trusted input generator for a campaign's `Spec/` data) | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml -p ucd-tables -- --ucd-dir <dir> --out <File.lean> --namespace <Ns> --gc Lu ... --prop Other_ID_Start ... [--check]` |
| **Run differential ISA validation of `Arm64/Trusted/` (`diff_eval`) against LLVM (`ld.lld`), Unicorn (`UC_ARCH_ARM64`), and Sail Armv9.4-A (`rems-project/sail-arm`)** | [`run-trusted-tests`](./run-trusted-tests/src/lib.rs) / [`sail-aarch64`](./sail-aarch64/README.md) | `[TEST ONLY]` | `cargo run --release --locked --manifest-path tools/Cargo.toml --bin run-trusted-tests` |
| **Extract the official ARM A-Profile A64 XML & ASL 1.0 manual or query instructions, 32-bit words, and shared ASL helpers** | `tools/dev/arm-asl-extract` | `[AUDIT/LINTER]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin arm-asl-extract -- <extract\|query> ...` |
| **Extract the official Linux `7.3` AArch64 syscall table (`unistd.h`), `SYSCALL_DEFINE*` C blocks, kernel helpers, and UAPI constants/structs** | `tools/dev/linux-syscall-extract` | `[AUDIT/LINTER]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin linux-syscall-extract -- <extract\|query> ...` |
| **Share Lean lexing/decl scanning, repo-root & campaign layout discovery, `translation.toml` / `<Target>Index.json` schemas, or the `#spec_audit_env` / `lake lean` runner across developer tools** | `tools/dev/repo-common` | `[AUDIT/LINTER]` (library) | `cargo test --locked --manifest-path tools/dev/Cargo.toml -p repo-common` |
| **Generate the dynamic CI job matrix, human-readable CI plan summary, git-ref plan diff, fail-closed coverage verification, local touch-plan, affected-shards report, or precompiled-library glob check** | `tools/dev/ci-tools` | `[OUTSIDE TCB]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin ci-tools -- <plan\|completeness-guard\|touch-plan\|affected-shards\|prune-artifacts\|rebuild-guard\|lib-globs> ...` |
| **Benchmark Lean files A/B: single core, interleaved runs, task-clock/cycles/real/user/sys, per-theorem kHB, proof size and kernel time** | `tools/dev/lean-bench` | `[OUTSIDE TCB]` | `cargo run --release --locked --manifest-path tools/dev/Cargo.toml -p lean-bench -- --per-decl --variant before=A.lean --variant after=B.lean` |

---

## Trust Boundary Classification

Every Rust source file under `tools/*/src/**/*.rs` (and `tools/dev/*/src/**/*.rs`) carries a top-of-file `//!` module header declaring its trust role:

- **`[TCB]` (Trusted Computing Base)**:
  - `tools/rust-obj2lean/src/trusted_common/`
  - `tools/rust-obj2lean/src/trusted_extractor/`
  - Not `[TCB]`: `tools/tcb-map/` (classified `[testing]`) and `tools/dev/repo-common/` (classified `[infra]`, shared Lean lexer/decl scanner, campaign layout discovery, `translation.toml` / `<Target>Index.json` schemas, `#spec_audit_env` runner) belong to the audit and developer tooling; no `[tcb]` Rust file references them (`tcb-map` rule `tcb-rust-import`).
  - The `trusted_*` modules parse in-memory relocatable ELF `.o` objects, check symbol collisions, and emit pre-link `<ObjName>ExtractedObj.lean` modules (`List Obj.ExtractedObj`). They contain **zero** subprocess invocations, static linking, archive unpacking, reachability pruning, instruction decoding, or theorem generation and never import `untrusted_*` modules.
- **`[CASE-STUDIES TCB]` (Optional Process-Snapshot Dumper)**:
  - `tools/proc-snapshot/src/{rsp,elf,snapshot}.rs` (process snapshots under qemu-aarch64 user mode, trusted only by optional snapshot-based proofs and outside the core engine `[tcb]`; the pinned runner comes from `scripts/fetch-qemu-aarch64`).
- **`[OUTSIDE TCB]` (Untrusted Build Driver, Placed Emitter, Legacy Linker, Kernel-Checked Proof & Advisor Tooling)**:
  - `tools/rust-obj2lean/src/untrusted_driver/` (CLI/`translation.toml` loader, `cargo rustc`/`zig cc` build driver, `.rlib`/`.a` archive unpacking, and `root_section_closure` reachability selector)
  - `tools/rust-obj2lean/src/untrusted_placed/` (`<ObjName>PlacedObj.lean` / `PlacedCode` / `PlacedData` / `PlacedWitness` / `ElfFacts` emission)
  - `tools/rust-obj2lean/src/untrusted_legacy_linker/` (deprecated `[OUTSIDE TCB]` legacy `LinkedImage` proof-cache exporter, gated behind `--legacy-linked-image` and classified `[proof]` by `tcb-map`)
  - `tools/rust-obj2lean/src/untrusted_lemmas/` (including `symexec/` and `dwarf/`, classified `[proof]` by `tcb-map`)
  - `tools/dev/lean-sig/` (`.agents/skills/lean-signatures/`)
  - `tools/dev/lean-bench/` (Lean A/B benchmark harness)
  - Every Lean theorem generated by `untrusted_lemmas` or `untrusted_placed` is checked by Lean's kernel against the trusted `<ObjName>PlacedObj.lean` / `<ObjName>ElfObj.lean` definitions, and `trusted_extractor` fails closed if `untrusted_driver` omits a referenced local section or symbol. Bugs here can only cause `lake build` to fail, never unsoundness.
- **`[AUDIT/LINTER]` (Static & Dynamic Policy / Spec Auditors)**:
  - `tools/tcb-map/`, `tools/dev/arm-asl-extract/`, `tools/dev/linux-syscall-extract/`, `tools/dev/repo-lints/`, `tools/dev/pr-audit-check/`, `tools/dev/spec-coverage/`, `tools/dev/spec-oracle/`
  - `tcb-map` is the self-contained trust-model auditor (`--tree`, `--check`), so `tcb-map --tree` classifies `tools/tcb-map/`, `scripts/tcb-map`, and `scripts/dev/check-trust-guards.sh` (with the differential ISA harnesses) as `[testing]`, while internal contributor/CI tools under `tools/dev/**` are classified as `[infra]`.
  - Extract the authoritative ARM A64 XML/ASL specification for ISA review, enforce repository trust guards, audit specification honesty and coverage, extract ABI/type layouts, and empirically validate external hook contracts in Unicorn.
- **`[TEST ONLY]` (Differential Test Suites)**:
  - `tools/run-trusted-tests/`
  - `tools/sail-aarch64/`
  - `tools/isa-oracle/`, `tools/unicorn-aarch64/`
  - `tools/rust-obj2lean/src/test_infra/` (`#[cfg(test)]`)
  - Unit tests of the `[TCB]` crates in separate files (`tools/rust-obj2lean/src/**/tests.rs`, `tools/proc-snapshot/tests/*.rs`; `#[cfg(test)]`). `tcb-map` classifies these as `[testing]`, classifies `untrusted_lemmas/` and `untrusted_legacy_linker/` as `[proof]` and other `untrusted_*` modules plus `src/main.rs` entry stubs of those crates as `[infra]`, and rejects references from `[tcb]` Rust files to non-`[tcb]` workspace crates, `tests`/`*_tests` modules, or `untrusted_*` / `test_infra` modules (`tcb-rust-import`); `repo-lints` also rejects inline test code (`#[test]`, `#[cfg(test)] mod tests { ... }`) in `[tcb]` Rust files (`inline-test-in-tcb`).
  - `tools/tcb-map/src/tests.rs` and `tools/dev/*/src/tests.rs` (`#[cfg(test)]`)
  - Validate the trusted Lean ISA semantics, placed-object loader (`Obj.PlacedLib`), static ELF loader, and untrusted symbolic executor against LLVM (`llvm-mc`, `ld.lld`), the Linux kernel ELF loader (`binfmt_elf`), Unicorn (`UC_ARCH_ARM64`), and the official Sail Armv9.4-A (`rems-project/sail-arm`) formal ISA semantics.

---

## Shipped Workspace Crates (`tools/Cargo.toml`)

1. **[`rust-obj2lean`](./rust-obj2lean/README.md)** — Object-level Rust/C -> Lean 4 exporter (`PlacedLib`), fetch-decode lemma generator, and `symexec` advisor (plus `[OUTSIDE TCB]` `--legacy-linked-image` proof-cache export).
2. **[`tcb-map`](./tcb-map/README.md)** — Self-contained auditor-facing TCB classification and soundness checker (`scripts/tcb-map`) with zero internal workspace dependencies: directory-hierarchy trust classification (`[tcb]`, `[case-studies-tcb]`, `[proof]`, `[testing]`, `[infra]`, `[doc]`; [`tree.rs`](./tcb-map/src/tree.rs)), `Arm64 < ProofLib < VerifiedLibraries < CaseStudies` and `Theorems`-sink layering, `Spec`/`Proof`/`Theorems` import isolation, pairwise standalone case-study package isolation, `[tcb]` Rust import isolation ([`tcb_rust_import.rs`](./tcb-map/src/tcb_rust_import.rs)), and core soundness/role-purity checks (`sorry`, `axiom`, `unsafe`, `native_decide`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, `Spec` definition-only, `Theorems` `theorem`-only).
3. **[`run-trusted-tests`](./run-trusted-tests/src/lib.rs)** — Dual-oracle differential test harness comparing Lean's `diff_eval` (`Arm64/Testing/Generators/TrustedSuite.lean`) against LLVM assembly, Unicorn AArch64 execution, and the authoritative Sail Armv9.4-A (`rems-project/sail-arm`) formal ISA semantics (via [`sail-aarch64`](./sail-aarch64/README.md)), plus standalone IEEE-754 floating-point differential testing (`--fp-only`) against Berkeley SoftFloat 3e, TestFloat 3e, and IBM FPgen.
4. **[`sail-aarch64`](./sail-aarch64/README.md)** — Standalone safe Rust interface (`CpuState`, `Simulator`, `StopReason`, `SailError`, `run_batch`) wrapping the official Sail Armv9.4-A C simulator (`armv9.c` + Sail 0.17.1 runtime). Building `sail-aarch64` requires GNU MP headers and library (`libgmp-dev` on Debian/Ubuntu: `sudo apt install libgmp-dev`) for the Sail C runtime.
5. **[`isa-oracle`](./isa-oracle/src/lib.rs)** & **[`unicorn-aarch64`](./unicorn-aarch64/src/lib.rs)** — Shared AArch64 CPU state/oracle traits and Unicorn (`UC_ARCH_ARM64`) wrapper used by `run-trusted-tests` and `tools/dev/spec-oracle`.
6. **[`proc-snapshot`](./proc-snapshot/README.md)** — `[CASE-STUDIES TCB]` process-snapshot dumper: runs a static AArch64 ELF under qemu-aarch64 user mode (GDB RSP client, no ptrace) and writes `entry`/`main` snapshots (`arm64-proc-snapshot/1` JSON + concatenated region bytes) with frozen-region consistency checks.
7. **[`snapshot-link`](./snapshot-link/README.md)** — Untrusted stock-`ld.lld` link step for static AArch64 musl/Rust executables and `proc-snapshot` inputs, checking that the linked ELF embeds each placed library (`Obj.PlacedLib`).

### Developer & CI Workspace Crates (`tools/dev/Cargo.toml`)

Internal contributor, audit-linting, and CI orchestration crates (`lean-sig`, `repo-lints` / `check-md-links` / `check-trust-guards`, `pr-audit-check`, `spec-coverage`, `spec-oracle`, `arm-asl-extract`, `linux-syscall-extract`, `repo-common`, `ci-tools`, `lean-bench`, `state-index-sweep`, and the UCD table generator `ucd-tables`) live in the standalone workspace `tools/dev/Cargo.toml`.

#### `ci-tools rebuild-guard` budget

`verify-all-examples` replays the shard artifacts, so it should compile only the cross-shard join modules. `ci-tools rebuild-guard --prefix CaseStudies --max-excess 10 --max-stale-secs 300` classifies every module the `lake build` log reports as `Built` against the CI plan (`tools/dev/ci-tools/src/rebuild_guard.rs`):

| Class | Meaning | Budget |
| --- | --- | --- |
| join | built by no builder and joins several builders' work (umbrella, `Theorems`, `join_modules`, cross-shard tops) | free (the steady-state baseline) |
| stale | inside some shard's `import` closure, so that shard's artifact should have shipped it | at most `--max-excess` (10); more only warns while their summed build time is within `--max-stale-secs` (300) |
| uncovered | built by no builder and joins nothing: a shard-coverage gap | any one fails |

The guard prints the counts per case study (`built = joins + stale + uncovered`, plus the shard that ships the stale modules) and the top module-path groups, then names the packages responsible for a failure. It blames a cross-shard cache split (with a `cache-cleanup.yml -f purge_shards=...` remedy) only on packages that `scripts/ci/check-shard-cache-coherence.sh` lists (`--incoherent`) **and** that rebuilt stale modules. Other packages with stale modules get a stale-artifact diagnosis. A coherence mismatch with no stale rebuilds is only a `::notice::`. The coherence check compares each shard's restored run token together with a chained lineage id (`scripts/ci/cache-lineage.sh`), so a split that an earlier run saved under a single run token is still reported. Without `--max-excess`, `--max N` keeps the flat cap on all rebuilt modules (default 20), which the other prefixes use.

`--max-stale-secs` makes the stale budget time-weighted, because this is a CI time guard, not a soundness check: `verify-all-examples` still compiles and checks every module it rebuilds. When the stale count exceeds `--max-excess` but the stale modules' summed build time (from the `(…s)` suffix of each `Built` line) stays within `--max-stale-secs`, every diagnosis above, remedy included, is reported as a `::warning::` and the guard passes. It fails as before when that time exceeds the limit, when a stale module's time cannot be parsed, or when any module is uncovered. The per-package line shows the stale build time next to the shipping shards.

The guard also lists each *stale root* (a stale module none of whose imports is stale) together with every import that several builders compile and that a builder other than the root's ships. Lake records imported `.olean` hashes in a trace, so such a root goes stale whenever the two compiles of the import differ byte-wise. If the shipping builder ships none of the import's direct importers (marked `SUSPECT`: it compiles the module only for another shard), the diagnosis names that module and its builders and recommends dropping it from the shipping shard's `targets` instead of a cache purge, which cannot fix the overlap. `ci-tools plan --check` reports the same pattern ahead of time as advisory `::warning::shard-overlap` lines (`tools/dev/ci-tools/src/shard_overlap.rs`); most flagged modules compile identically in practice, so the warning never fails CI.

---

## Running Tests

Always test the Rust workspaces from the repository root with `--locked` (building `run-trusted-tests` requires `libgmp-dev`, e.g., `sudo apt install libgmp-dev`):

```sh
# Run the shipped workspace unit & differential test suite:
cargo test --locked --manifest-path tools/Cargo.toml

# Run the developer/linter/CI workspace unit test suite:
cargo test --locked --manifest-path tools/dev/Cargo.toml

# Run the ignored end-to-end linker differential test across all repository crates vs ld.lld:
cargo test --locked --manifest-path tools/Cargo.toml -- --ignored repo_crates_match_lld
```
