# `Arm64/` ISA Testing, Formal Validation & Differential Conformance

[`Arm64/`](./README.md) holds the **Trusted Computing Base (TCB)** of the verification engine. By design, `Arm64.lean` and [`Arm64/Trusted/**/*.lean`](./Trusted/README.md) (the `ISA/`, `Object/`, `Process/`, `Syscalls/`, and `Spec/` sub-layers) contain **only definitions** (`Role::Spec`, enforced in CI by [`scripts/tcb-map`](../scripts/tcb-map) / [`tools/tcb-map`](../tools/tcb-map/src/lib.rs)) and **zero theorems or proof tactics**. Because every verified functional-correctness and memory-safety theorem in `CaseStudies/` ultimately states a property of `Arm64.decode`, `Arm64.execInst`, `Arm64.Step`, and `ElfImage.loadState` / `Obj.PlacedLib.Placeable`, the soundness of the entire repository rests on the faithfulness of `Arm64/Trusted/` to real AArch64 hardware and the official ARM A64 architecture specification, which we consume as ARM's machine-readable XML/ASL text (via `tools/dev/arm-asl-extract`) rather than the PDF manual. The validation layers below target the instruction-level semantics in `Arm64/Trusted/ISA/`, the whole-ELF process loader in `Arm64/Trusted/Process/`, and the layout-generic object placement model in `Arm64/Trusted/Object/`; the specification vocabulary in [`Arm64/Trusted/Spec/`](./Trusted/README.md) (Hoare triples, separation logic, `c_spec` / `rust_spec`, `c_type_spec`) is audited by review and by the spec-audit tooling (Layer 6).

This document describes the **six-layer defense-in-depth validation architecture** used to audit, formally prove, and differentially test `Arm64/Trusted/`. The Lean test modules live in [`Arm64/Testing/`](./Testing/README.md) (ISA, decoder, loader, and step-rule tests), [`ProofLib/Testing/`](../ProofLib/Testing/README.md) (`ProofLib` tactic and `SpecAudit` tests, e.g. `SymWPEval`), and `CaseStudies/<Campaign>/Testing/` (per-campaign spec audits).

---

## 1. Overview & Defense-in-Depth Validation Architecture

No single testing method suffices for an ISA specification: formal round-trip proofs catch decoder ambiguity and bit-packing bugs, concrete unit tests catch boundary cases, multi-emulator differential testing catches subtle flag/lane/memory discrepancies across thousands of instruction sequences, and systematic ASL audits verify `UNDEFINED` guards and architectural invariants directly against ARM's machine-readable specification.

| Layer | Validation Method | Key Files / Tools | What It Guarantees / Catches |
| :--- | :--- | :--- | :--- |
| **Layer 1** | **Formal Kernel-Checked Encoder/Decoder Round-Trip Proofs** | [`Arm64/Testing/Harness/Encode.lean`](Testing/Harness/Encode.lean) (untrusted encoder), [`Arm64/Testing/Proofs/EncoderDecoder.lean`](Testing/Proofs/EncoderDecoder.lean), [`Arm64/Testing/Proofs/EncoderDecoder/Common.lean`](Testing/Proofs/EncoderDecoder/Common.lean), [`Part1.lean`](Testing/Proofs/EncoderDecoder/Part1.lean)..[`Part5.lean`](Testing/Proofs/EncoderDecoder/Part5.lean) | Proves `∀ bs p, decode bs = some p → encode p = some bs` across all 80 decode branches (`encode_of_decode`), ruling out shadowed branches, bitfield overlap, and lossy decoding. |
| **Layer 2** | **Concrete & Symbolic ISA Unit Regression Suites** | [`Arm64/Testing/Regression/UnitTests.lean`](Testing/Regression/UnitTests.lean), [`Arm64/Testing/Conformance/IsaConformance.lean`](Testing/Conformance/IsaConformance.lean), [`ProofLib/Testing/SymWPEval.lean`](../ProofLib/Testing/SymWPEval.lean), [`Arm64/Testing/Regression/SimdScalarSteps.lean`](Testing/Regression/SimdScalarSteps.lean), [`Arm64/Testing/Regression/UnscaledLdurSteps.lean`](Testing/Regression/UnscaledLdurSteps.lean), [`Arm64/Testing/Regression/CondCompareSteps.lean`](Testing/Regression/CondCompareSteps.lean), [`Arm64/Testing/Regression/ObjectLoad.lean`](Testing/Regression/ObjectLoad.lean) | Verifies concrete execution (`lake exe unit_tests`), FIPS-197 AES & NEON vectors, ELF relocation/loader invariants, and `MetaM` symbolic-vs-concrete equivalence (`SymWPEval`, `IsaConformance`). |
| **Layer 3** | **Multi-Oracle Empirical Differential Testing (LLVM + Unicorn + Linux `binfmt_elf`)** | [`Arm64/Testing/Harness/TestCase.lean`](Testing/Harness/TestCase.lean), [`Arm64/Testing/Harness/Compare.lean`](Testing/Harness/Compare.lean), [`Arm64/Testing/Generators/TrustedSuite.lean`](Testing/Generators/TrustedSuite.lean), [`Arm64/Testing/Harness/DifferentialEval.lean`](Testing/Harness/DifferentialEval.lean), [`Arm64/Testing/Harness/ElfEval.lean`](Testing/Harness/ElfEval.lean), [`Arm64/Testing/Harness/PlacedEval.lean`](Testing/Harness/PlacedEval.lean), [`tools/run-trusted-tests`](../tools/run-trusted-tests/src/lib.rs), [`tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs`](../tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs) | Cross-checks `Arm64.decode`, `Arm64.execInst`, `ElfImage.loadState`, and `Placed.lean` bit-for-bit (`X0..X30`, `SP`, `PC`, `NZCV`, `V0..V31`, memory) against LLVM (`rustc`/`ld.lld`), Unicorn (`UC_ARCH_ARM64`), and the Linux kernel ELF loader. |
| **Layer 4** | **Authoritative Sail (`rems-project/sail-arm` Armv9.4-A) Formal ISA Oracle** | [`Arm64/Testing/Generators/TrustedSuite.lean`](Testing/Generators/TrustedSuite.lean), [`Arm64/Testing/Harness/Compare.lean`](Testing/Harness/Compare.lean), [`Arm64/Testing/Harness/DifferentialEval.lean`](Testing/Harness/DifferentialEval.lean), [`tools/run-trusted-tests/src/compare.rs`](../tools/run-trusted-tests/src/compare.rs) | Validates `Arm64/Testing/Generators/` and 504,435 single-instruction/FP cases against the official ARM-derived Sail AArch64 reference model (`rems-project/sail-arm` Armv9.4-A compiled C emulator) and Berkeley SoftFloat alongside Unicorn/QEMU. |
| **Layer 5** | **Official ARM Machine-Readable XML / ASL 1.0 Extraction & Audit** | `tools/dev/arm-asl-extract`, `scripts/dev/fetch-campaign-sources.sh` (`arm-isa-xml`), [`Arm64/Trusted/ISA/README.md`](Trusted/ISA/README.md) | Extracts ARM's official A-Profile Exploration Tools XML/ASL corpus (`ISA_A64_xml_A_profile-2026-06.tar.gz`) into Markdown/JSON manuals and drives line-by-line ASL audits of `Arm64/Trusted/ISA/*.lean`. |
| **Layer 6** | **End-to-End Compiled Binary Proofs & Specification Audits** | [`Arm64/Testing/Tours/Demo.lean`](Testing/Tours/Demo.lean), [`ProofLib/Testing/SpecAudit.lean`](../ProofLib/Testing/SpecAudit.lean), `CaseStudies/<Campaign>/Testing/SpecAudit.lean`, `tools/dev/spec-oracle` | Exercises the TCB across thousands of real `clang`/`rustc` `-O2` instructions in `CaseStudies/`, backed by `#spec_nonvacuous!`, `#spec_lint!`, `#spec_smoke!`, and Unicorn hook validation (`spec-oracle`). |

---

## 2. Layer 1 — Formal Kernel-Checked Encoder/Decoder Round-Trip Proofs

- **Files**:
  - [`Arm64/Testing/Harness/Encode.lean`](Testing/Harness/Encode.lean) (the untrusted encoder `Arm64.encode` / `encodeInst` / `hex32`; not part of the `Arm64/Trusted/` TCB)
  - [`Arm64/Testing/Proofs/EncoderDecoder.lean`](Testing/Proofs/EncoderDecoder.lean) (top-level theorems)
  - [`Arm64/Testing/Proofs/EncoderDecoder/Common.lean`](Testing/Proofs/EncoderDecoder/Common.lean) (`ite_some_imp` dispatcher and `decodeBitMasks` / `encodeBitMasks` round-trip lemmas)
  - [`Arm64/Testing/Proofs/EncoderDecoder/Part1.lean`](Testing/Proofs/EncoderDecoder/Part1.lean) (`NOP`, `SVC`, `BRK`, `ADR`/`ADRP`, `ADD`/`SUB` immediate, logical immediate & `DecodeBitMasks`, `MOVZ`/`MOVN`/`MOVK`, bitfields `BFM`/`SBFM`/`UBFM`, `EXTR`, branches `B`/`BL`/`CBZ`/`CBNZ`/`TBZ`/`TBNZ`/`B.cond`/`BR`/`BLR`/`RET`, logical shifted register, `ADD`/`SUB` shifted & extended register)
  - [`Arm64/Testing/Proofs/EncoderDecoder/Part2.lean`](Testing/Proofs/EncoderDecoder/Part2.lean) (`ADC`/`SBC`, `CCMP`/`CCMN`, `CSEL`/`CSINC`/`CSINV`/`CSNEG`, 1-/2-/3-source data processing, GP load/store pairs `LDP`/`STP`/`LDPSW`, unsigned-immediate `LDR`/`STR`, unscaled/indexed `LDUR`/`STUR`, literal `LDR`, acquire/release `LDAR`/`STLR`, `MRS`/`MSR`, barriers `DSB`/`DMB`/`ISB`)
  - [`Arm64/Testing/Proofs/EncoderDecoder/Part3.lean`](Testing/Proofs/EncoderDecoder/Part3.lean) (SIMD/FP load/store pairs, unsigned immediate, unscaled/indexed, `ST1` post-index, `AESE`/`AESD`/`AESMC`/`AESIMC`, `FMOV` GP↔vector, SIMD immediate shift, `INS`/`DUP`/`UMOV`/`SMOV`, SIMD three-same & two-reg-misc)
  - [`Arm64/Testing/Proofs/EncoderDecoder/Part4.lean`](Testing/Proofs/EncoderDecoder/Part4.lean) (SIMD across-lanes `ADDV`/`UMAXV`/`UMINLV`, permutes `UZP`/`TRN`/`ZIP`, `EXT`/`TBL`, scalar IEEE-754 FP 1-/2-/3-source data processing, `FCMP`/`FCMPE`, `FCCMP`, `FCSEL`, `FMOV` immediate, and fixed/integer FP conversions `SCVTF`/`UCVTF`/`FCVTZS`/`FCVTZU`)
  - [`Arm64/Testing/Proofs/EncoderDecoder/Part5.lean`](Testing/Proofs/EncoderDecoder/Part5.lean) (`HINT`, `UDF`, `DC ZVA`, `CRC32*`, `LDNP`/`STNP` (GPR + SIMD), `PRFM`/`PRFUM`, LSE atomics `LDADD`/`SWP`/…/`LDAPR`, RCpc `LDAPUR`/`STLUR`, SIMD literal `LDR`, `LDXP`/`STXP`, `CAS`/`CASP`, SIMD `LD1`/`ST1` multi-structure, `LD1R`, `TBL`/`TBX`, scalar `ADDP`)

### Key Theorems

In [`Arm64/Testing/Proofs/EncoderDecoder.lean`](Testing/Proofs/EncoderDecoder.lean):

```lean
theorem Arm64.encode_of_decode (bs : BitVec 32) (p : Instr) (h : decode bs = some p) :
    encode p = some bs

theorem Arm64.encodeInst_of_decode (bs : BitVec 32) (p : Instr) (h : decode bs = some p) :
    encodeInst p = bs

theorem Arm64.encodeHex_of_decode (bs : BitVec 32) (p : Instr) (h : decode bs = some p) :
    encodeHex p = some (hex32 bs)

theorem Arm64.encodeProg_of_decodeProg :
    ∀ (bs : List (BitVec 32)) (p : List Instr),
      decodeProg bs = some p → encodeProg p = some bs
```

### Why This Matters
1. **Injectivity of Decoding**: Because `encode : Instr → Option (BitVec 32)` is a pure function, `encode_of_decode` proves that `decode` is injective on its domain—two distinct 32-bit machine words can never decode to the same `Instr` AST node without round-tripping back to the original 32 bits.
2. **No Shadowed or Lossy Decode Branches**: Every one of the 80 sequential `if ... then ... else` branches in [`Arm64/Trusted/ISA/Decode.lean`](./Trusted/ISA/Decode.lean) is stepped through via `ite_some_imp`. If any decoder branch forgot to constrain a reserved bit or dropped a width/shift bit in the `Instr` AST, `encode p = some bs` would fail to prove.

### Runnable Command
```sh
timeout 600 lake build --no-ansi Arm64.Testing.Proofs.EncoderDecoder
```

---

## 3. Layer 2 — Concrete & Symbolic ISA Unit Regression Suites

- **Files**:
  - [`Arm64/Testing/Regression/UnitTests.lean`](Testing/Regression/UnitTests.lean) (`lake exe unit_tests`): Deterministic concrete execution test suite covering `Arm64.decode`/`Arm64.encode`, `AddWithCarry32`/`AddWithCarry64` overflow/carry edge cases, `DecodeBitMasks` and bitfield instructions (`BFM`/`SBFM`/`UBFM`/`EXTR`), multi-width loads/stores (`LDRB`/`LDRH`/`LDRW`/`LDRX`/`LDRSB`/`LDRSH`/`LDRSW`, pre-index, post-index, `LDP`/`STP`), NEON vector operations, FIPS-197 AES known-answer vectors (`AESE`/`AESD`/`AESMC`/`AESIMC`), and concrete execution of compiled Rust/C functions.
  - [`Arm64/Testing/Conformance/IsaConformance.lean`](Testing/Conformance/IsaConformance.lean) and [`ProofLib/Testing/SymWPEval.lean`](../ProofLib/Testing/SymWPEval.lean): Kernel-checked concrete (`decide`) and `MetaM` symbolic (`ProofLib.SepLogic.SymWP` / `ProofLib.VCGen`) conformance suites over `buildTrustedSuite` and randomized bitvector inputs, ensuring the untrusted symbolic execution normalizers in `ProofLib/` never diverge from the TCB evaluator in [`Arm64/Trusted/ISA/Eval.lean`](./Trusted/ISA/Eval.lean).
  - [`Arm64/Testing/Regression/SimdScalarSteps.lean`](Testing/Regression/SimdScalarSteps.lean), [`Arm64/Testing/Regression/UnscaledLdurSteps.lean`](Testing/Regression/UnscaledLdurSteps.lean), [`Arm64/Testing/Regression/CondCompareSteps.lean`](Testing/Regression/CondCompareSteps.lean): Targeted step-rule and classifier regression tests (with `#guard_msgs` negative tests) for scalar SIMD loads/stores, unscaled sub-word `LDUR`/`STUR` over byte-pair and `↦ₛ` heaps, and chained `CMP; CCMP/CCMN; CSET` sequences.
  - [`Arm64/Testing/Regression/ObjectLoad.lean`](Testing/Regression/ObjectLoad.lean) and [`Arm64/Testing/Regression/IncludeBytes.lean`](Testing/Regression/IncludeBytes.lean): Unit and theorem tests for `Arm64.Obj.LinkedImage.load`, multi-section `.text`/`.rodata`/`.data`/`.bss`/`.got` placement, and compile-time binary slice loading (`include_bytes%`).

### Runnable Commands
```sh
# Build and run the concrete ISA unit test executable:
timeout 600 lake build --no-ansi unit_tests
timeout 300 .lake/build/bin/unit_tests

# Build the symbolic-vs-concrete and step-rule regression modules:
timeout 600 lake build --no-ansi Examples.Testing.ProofLib.SymWPEval Arm64.Testing.Conformance.IsaConformance Arm64.Testing.Regression.SimdScalarSteps Arm64.Testing.Regression.UnscaledLdurSteps Arm64.Testing.Regression.CondCompareSteps Arm64.Testing.Regression.ObjectLoad Arm64.Testing.Regression.IncludeBytes
```

---

## 4. Layer 3 — Multi-Oracle Empirical Differential Testing (LLVM, Unicorn Engine, Linux ELF Loader)

- **Files**:
  - [`tools/isa-oracle`](../tools/isa-oracle/src/lib.rs), [`Arm64/Testing/Harness/TestCase.lean`](Testing/Harness/TestCase.lean), [`Arm64/Testing/Harness/Serve.lean`](Testing/Harness/Serve.lean), and [`Arm64/Testing/Harness/Compare.lean`](Testing/Harness/Compare.lean): Common `Arm64Oracle` trait (`CpuState`, `TestInput`, `Outcome`, `Policy`, `diff`), canonical test record definitions (`IsaTestCase`, `FpBatchRecord`, `UnitTestCase`), framed binary protocol server (`diff_eval --serve`), and outcome classification (`evalTestCase`, `evalFpBatchRecord`).
  - [`Arm64/Testing/Generators/TrustedSuite.lean`](Testing/Generators/TrustedSuite.lean) (assembling [`ExternalSuites.lean`](Testing/Generators/ExternalSuites.lean), [`HandWrittenVectors.lean`](Testing/Generators/HandWrittenVectors.lean), [`RandomFuzz.lean`](Testing/Generators/RandomFuzz.lean), [`CompiledBinary.lean`](Testing/Generators/CompiledBinary.lean), and [`SyscallTraces.lean`](Testing/Generators/SyscallTraces.lean)): Curated + randomized 223-vector AArch64 differential test corpus containing:
    - Ported Unicorn Engine `test_arm64.c` regression case (1) and ARM VIXL simulator instruction-level test vectors (44)
    - Multi-iteration C algorithmic loops (3), hand-written ISA surface & scalar FP cases (16), and SIMD/atomics/boundary cases (45)
    - 100 seeded randomized 8-instruction `SplitMix64` fuzz blocks (`RandomFuzz.lean`)
    - 14 compiled Rust subroutines from `Examples.Generated.ExamplesObj` (9,138 stepped words)
  - [`Arm64/Testing/Harness/DifferentialEval.lean`](Testing/Harness/DifferentialEval.lean) (`lake exe diff_eval`): CLI executable supporting `--serve`, `--dump-suite`, `--dump-random`, `--verify`, `--eval-fp`, `--batch-fp`, and `--fs-diff-trace`.
  - [`tools/run-trusted-tests`](../tools/run-trusted-tests/src/lib.rs) (`src/assembler.rs`, `src/lean_oracle.rs`, `src/unicorn.rs`, `src/sail.rs`, `src/model.rs`, `src/compare.rs`, `src/fuzz.rs`, `src/fuzz_gen.rs`, `src/main.rs`) plus [`tools/unicorn-aarch64`](../tools/unicorn-aarch64/src/lib.rs) and [`tools/sail-aarch64`](../tools/sail-aarch64/src/lib.rs): Host Rust runner that:
    1. Invokes `diff_eval --dump-suite` to export all test cases from [`Arm64/Testing/Generators/TrustedSuite.lean`](Testing/Generators/TrustedSuite.lean).
    2. Batch-assembles any symbolic assembly snippets into 32-bit AArch64 machine words using LLVM (`rustc --target aarch64-unknown-linux-gnu` + `ld.lld` in [`tools/run-trusted-tests/src/assembler.rs`](../tools/run-trusted-tests/src/assembler.rs)).
    3. Steps every test case in lockstep across `LeanOracle` (`diff_eval --serve`), `UnicornOracle` (`UC_ARCH_ARM64` / QEMU TCG in [`tools/unicorn-aarch64/src/lib.rs`](../tools/unicorn-aarch64/src/lib.rs)), and `SailOracle` (Sail Armv9.4-A C emulator in [`tools/sail-aarch64/src/lib.rs`](../tools/sail-aarch64/src/lib.rs), see Layer 4).
    4. Compares the architectural state (`X0..X30`, `SP`, `PC`, `NZCV` flags, `V0..V31`, and all watched memory bytes) bit-for-bit after every instruction via [`isa_oracle::diff`](../tools/isa-oracle/src/lib.rs) and [`tools/run-trusted-tests/src/compare.rs`](../tools/run-trusted-tests/src/compare.rs).
  - [`Arm64/Testing/Harness/PlacedEval.lean`](Testing/Harness/PlacedEval.lean) (`lake -d Arm64/Testing exe placed_eval`) and [`tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs`](../tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs): 4-layer differential placement and relocation harness comparing `Arm64.Obj.Placed` (`placed_eval`) and `untrusted_placed` against stock `ld.lld` across synthetic relocation/relaxation layouts, multi-TU C/Rust corpora, and repository `translation.toml` targets.

### Runnable Commands
```sh
# Run the full Lean vs. LLVM + Unicorn + Sail Armv9.4-A differential test suite
# (`--oracle all` is the default; `--oracle unicorn` / `--oracle sail` select one oracle;
# Sail sources come from `scripts/fetch-upstream-sources.sh sail-arm`; requires `libgmp-dev`,
# e.g., `sudo apt install libgmp-dev`):
cargo run --release --locked --manifest-path tools/Cargo.toml --bin run-trusted-tests

# Run the rust-obj2lean linker/loader differential tests against ld.lld:
cargo test --locked --manifest-path tools/Cargo.toml -p rust-obj2lean
cargo test --locked --manifest-path tools/Cargo.toml -- --ignored repo_crates_match_lld
```

---

## 5. Layer 4 — Authoritative Sail (`rems-project/sail-arm` Armv9.4-A) Formal ISA Model Differential Validation

While Unicorn Engine (`UC_ARCH_ARM64`) provides a fast QEMU TCG oracle, QEMU is a dynamic binary translator written in C rather than a formal architecture specification. To cross-check `Arm64/Trusted/` against an authoritative formal ISA specification, [`Arm64/Testing/Generators/TrustedSuite.lean`](Testing/Generators/TrustedSuite.lean) and [`Arm64/Testing/Harness/Serve.lean`](Testing/Harness/Serve.lean) are also validated against the **Sail AArch64 formal model** (`rems-project/sail-arm`, `sail-arm9.4a`), which is automatically translated from ARM's internal machine-readable ASL specification into Sail and compiled to a standalone C reference emulator:

- `run-trusted-tests --oracle all` (the default) steps every test case exported by `diff_eval --dump-suite` (223 cases / 10,503 instruction words: single-instruction vectors, multi-instruction sequences, VIXL vectors, randomized blocks, and compiled Rust subroutines) in lockstep across `LeanOracle` (`diff_eval --serve`), `UnicornOracle` ([`tools/unicorn-aarch64`](../tools/unicorn-aarch64/src/lib.rs)), and `SailOracle` ([`tools/sail-aarch64`](../tools/sail-aarch64/src/lib.rs)), diffing full state after every instruction via `isa_oracle::diff`.
- Validating against both **Unicorn/QEMU** and **Sail Armv9.4-A** eliminates single-emulator blind spots on subtle AArch64 semantics such as 32-bit `W`-register upper-bit zeroing, `AddWithCarry` signed/unsigned overflow flags (`NZCV`), `DecodeBitMasks` edge cases, and scalar SIMD upper-lane zeroing.
- A case may set `skipSail := some "<reason>"` (JSON `skip_sail`) to opt out of Sail only; Unicorn is still required. This is reserved for documented Sail-model configuration differences or bugs: currently `System/Dczid_DcZva_LinuxUserspace` (Sail's configuration reports `DCZID_EL0.DZP=1` and traps `DC ZVA`, unlike Linux EL0) and `SimdExtra/Addv_ByteLanes` (the Sail C model hits an internal assertion on byte-lane `ADDV`).

### Known Limitations

- **The Lean model's faulting and undecodable cases are never compared against Sail:**
  - In single-instruction batch fuzzing (`Arm64Oracle::run_batch` via `diff_eval --serve`), [`Serve.lean`](Testing/Harness/Serve.lean) returns `Outcome::Unmodeled` (`STATUS_UNMODELED = 1`) when `Arm64.decode w = none` and `Outcome::Fault` (`STATUS_FAULT_OTHER = 13`) when `execInst` terminates with `sf.status != .Running` (for example, misaligned `SP`, unmapped memory outside `[0x20000, 0x20040)`, or an `UNDEFINED` sub-opcode fault). On the host side, [`classify_lean_insn_batch`](../tools/run-trusted-tests/src/compare.rs) counts these outcomes in `OutcomeCounts::unmodeled_decode` and `OutcomeCounts::exec_exception` and skips them before invoking Sail and Unicorn, and [`compare_insn_batch_outcomes`](../tools/run-trusted-tests/src/compare.rs) compares post-states only when Lean returns `Outcome::Ok`.
  - In multi-step `IsaTestCase` suites (`buildTrustedSuite`), all cases are positive non-faulting traces (`sf.status == .Running`), while negative decoder (`decode w = none`) and faulting (`status = .Exception`) regression tests in [`Arm64/Testing/Regression/UnitTests.lean`](Testing/Regression/UnitTests.lean) and [`Arm64/Testing/Regression/DisproofTests.lean`](Testing/Regression/DisproofTests.lean) run only against the Lean evaluator.
  - Consequently, differential testing never queries Sail to check whether an instruction rejected by `Arm64.decode` or faulting in `Arm64.execInst` also faults in Sail Armv9.4-A (or whether the Lean model is overly restrictive on a valid A64 encoding or state). Auditing `UNDEFINED` and fault conditions against the architecture specification instead relies on Layer 5 (the systematic XML/ASL 1.0 audit below) and the negative unit tests in Layer 2.

---

## 6. Layer 5 — Official ARM Machine-Readable XML / ASL 1.0 Extraction & Systematic Semantics Review

To enable direct, repeatable human and LLM auditing of [`Arm64/Trusted/ISA/Syntax.lean`](./Trusted/ISA/Syntax.lean), [`Arm64/Trusted/ISA/Decode.lean`](./Trusted/ISA/Decode.lean), [`Arm64/Trusted/ISA/Eval.lean`](./Trusted/ISA/Eval.lean), [`Arm64/Trusted/ISA/State.lean`](./Trusted/ISA/State.lean), and [`Arm64/Trusted/ISA/Memory.lean`](./Trusted/ISA/Memory.lean) against the official ARM A64 specification (working off the structured XML/ASL text rather than PDF manuals or third-party HTML summaries), the repository provides a pure-Rust XML & ASL 1.0 extractor (`tools/dev/arm-asl-extract`) and an ASL coverage summary in [`Arm64/Trusted/ISA/README.md`](./Trusted/ISA/README.md) (paired with `.agents/skills/review-arm64-asl/SKILL.md`):

1. **SHA-256-Pinned Upstream ARM XML Specification (`scripts/dev/fetch-campaign-sources.sh`, delegated by [`scripts/fetch-upstream-sources.sh`](../scripts/fetch-upstream-sources.sh))**:
   - The `arm-isa-xml` target downloads (or reuses from `${ARM64_UPSTREAM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/arm64-verification-engine}/archives/`) ARM's official A-Profile A64 Exploration Tools archive (`ISA_A64_xml_A_profile-2026-06.tar.gz`, SHA-256 `63a01a1696483bbe2edfef9e0f0cd053d6c1c619ec0587876cb7a60bb344f354`) and unpacks it to `$CACHE/arm-isa-xml/ISA_A64_xml_A_profile-2026-06`.
2. **Pure-Rust Extractor & Query CLI (`tools/dev/arm-asl-extract`)**:
   - Parses `index.xml` (`base`), `fpsimdindex.xml` (`fpsimd`), `sveindex.xml` (`sve`), `mortlachindex.xml` (`sme`), `encodingindex.xml`, `shared_pseudocode.xml`, and all 2,291 `<instructionsection>` XML files in ~1 second.
   - Computes exact 32-bit `(mask, value)` fixed-bit patterns and negative constraints (`!= ...`) from `<regdiagram>` and `<encoding>` `<box>` elements (`bitpattern.rs`).
   - Resolves `<a link="...">` and `<anchor link="...">` cross-references between per-instruction `<ps_section secttype="Decode">` / `<ps_section secttype="Operation">` blocks and the 1,831 helper definitions in `shared_pseudocode.xml` (`AddWithCarry`, `DecodeBitMasks`, `ConditionHolds`, `ShiftReg`, `ExtendReg`, etc.).
   - Supports full reference-tree extraction (`arm-asl-extract extract`) and instant lookup (`arm-asl-extract query <mnemonic|id|hex-word|helper> --inline-shared-asl`).
3. **Seven-Point ASL Audit Workflow (`.agents/skills/review-arm64-asl/SKILL.md` / [`Arm64/Trusted/ISA/README.md`](./Trusted/ISA/README.md))**:
   - Systematic checklist covering: (1) 32-bit fixed masks/values & negative constraints, (2) `UNDEFINED` / reserved field guards, (3) register `31` (`SP` vs `XZR`) per operand, (4) 32-bit `W` and scalar SIMD write zero-extension, (5) shift/extend/bitfield/carry helpers, (6) memory addressing & writeback order, and (7) NEON/AES/IEEE-754 FP semantics.

### Runnable Commands
```sh
# 1. Fetch and SHA-256 verify the official ARM A64 XML archive:
scripts/dev/fetch-campaign-sources.sh arm-isa-xml

# 2. Extract the full Markdown & JSON reference tree to $CACHE/arm-isa-xml/extracted:
cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin arm-asl-extract -- extract --inline-shared-asl

# 3. Query an instruction mnemonic, XML ID, shared ASL helper, or 32-bit hex instruction word:
cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin arm-asl-extract -- query ADD --inline-shared-asl
cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin arm-asl-extract -- query DecodeBitMasks
cargo run --release --locked --manifest-path tools/dev/Cargo.toml --bin arm-asl-extract -- query 0x9100a820

# 4. Run arm-asl-extract unit tests:
cargo test --locked --manifest-path tools/dev/Cargo.toml -p arm-asl-extract
```

---

## 7. Layer 6 — End-to-End Compiled Binary Proof & Specification Audits

Finally, the `Arm64/Trusted/` ISA model is continuously exercised end-to-end by mechanized separation-logic proofs over real `clang` and `rustc` `-O2` AArch64 object files in `CaseStudies/<Campaign>/`:

- **Real Compiler Codegen Exerciser**: [`tools/rust-obj2lean`](../tools/rust-obj2lean/README.md) compiles production C and Rust libraries into relocatable AArch64 ELF `.o` files and extracts them into `Obj.PlacedLib` / `Obj.MultiPlacedLib` definitions (alongside whole-ELF `ElfImage` binaries). Any missing instruction, overly strict decoder guard, or wrong flag/memory transition immediately manifests as a stuck weakest-precondition step during `lake build`.
- **Specification Non-Vacuity & Smoke Execution ([`ProofLib/SpecAudit.lean`](../ProofLib/SpecAudit.lean), [`ProofLib/Testing/SpecAudit.lean`](../ProofLib/Testing/SpecAudit.lean), `CaseStudies/<Campaign>/Testing/SpecAudit.lean`)**:
  - `#spec_nonvacuous!` proves that each subroutine specification's precondition is satisfiable on a concrete `Arm64.State` with valid `Memory` permissions.
  - `#spec_lint!` statically audits AST preconditions and postconditions for overlapping stack frames, missing points-to cells, or auto-implicit typos.
  - `#spec_smoke!` executes the compiled AArch64 binary on concrete inputs via `ProofLib.execUntilPC` ([`ProofLib/Exec.lean`](../ProofLib/Exec.lean)) and checks that the post-state satisfies the specification.
- **Unicorn External Hook Validation (`tools/dev/spec-oracle`)**:
  - `spec-oracle validate-hooks` executes compiled AArch64 binaries inside Unicorn Engine to empirically validate external `Hooks` separation-logic contracts (`HookSat`) against real allocator/runtime implementations.
- **End-to-End Subroutine Contract Regression ([`Arm64/Testing/Tours/Demo.lean`](Testing/Tours/Demo.lean))**:
  - Verifies at compile time that proved subroutines compose across standalone and linked-image `subroutine_ok` / `library_ok` boundaries.
