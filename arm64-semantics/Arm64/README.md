# `Arm64`: Trusted AArch64 Semantics and Specification Model

`Arm64/` holds the **Trusted Computing Base (TCB)** of the verification engine, plus the tests that validate it. It defines what AArch64 machine code means and what it means for a compiled program to satisfy a formal specification.

| Directory | Lake library | Trusted? | Contents |
|---|---|---|---|
| [`Arm64.lean`](../Arm64.lean) + [`Arm64/Trusted/`](./Trusted/README.md) (umbrella `Arm64/Trusted.lean`) | `Arm64` (package `arm64`, [`Arm64/lakefile.toml`](./lakefile.toml)) | **Yes (TCB, `Role::Spec`)** | ISA semantics, object loading, machine-level Hoare/separation-logic foundation |
| [`Arm64/Testing/`](./Testing/README.md) (umbrella `Arm64/Testing.lean`) | `Testing` (root package, [`lakefile.lean`](../lakefile.lean)) | No (`Role::Test`) | Encoder & decode round-trip proof, unit tests, differential/ELF harnesses, ISA step-rule regressions |

**Lake package.** [`Arm64/lakefile.toml`](./lakefile.toml) defines the `arm64` Lake package, which has no dependencies and owns only `Arm64.lean` + `Arm64.Trusted.*` (`srcDir = ".."`, so module paths are resolved from the repository root). `lake -d Arm64 build` compiles the trusted library into `Arm64/.lake/build` with nothing else on `LEAN_PATH` and without a Rust toolchain. `ProofLib/lakefile.toml` (package `prooflib`) requires it, and the root `lakefile.lean` requires `prooflib`; `Arm64/Testing/` stays in the root package because some tests also import `ProofLib` and `Examples`.

> **ISA Testing, Formal Validation & Differential Conformance**: See **[`Arm64/TESTING.md`](./TESTING.md)** for the six-layer validation architecture covering formal encoder/decoder round-trip proofs (`Arm64.Testing.Arm64EncoderDecoder`), concrete & symbolic unit suites (`unit_tests`, `SymWPEval`), LLVM + Unicorn + `ld.lld` differential testing (`run-trusted-tests`, `placed_lld_diff.rs`), the Sail Armv9.4-A formal reference oracle, and official ARM A64 XML/ASL 1.0 extraction & review (`tools/arm-asl-extract`, `.agents/skills/review-arm64-asl/SKILL.md`).

## Design Principles

- **Definitions only, no proofs:** Modules in `Arm64.lean` and `Arm64/Trusted/` contain pure data types, evaluators, and propositions — never theorems, lemmas, or proof tactics (enforced in CI by `check-trust-guards`). Auditing a verified result requires reading only the definitions here and the theorem statement in a `Spec.lean` file, never any proof in `ProofLib/` or `Examples/`, nor any test in `Arm64/Testing/`.
- **Execute from memory with conservative permissions:** Instructions are fetched and decoded directly from 64-bit byte-addressable virtual memory (`Program.fetchMem`), where each byte carries read/write/execute permissions (`Perm`). Permissions are conservative: executable memory is never writable (W^X), read-only and executable bytes are frozen across every execution step, and "unmapped" means *not known to be accessible* rather than *guaranteed to fault*. A proof that code never touches unmapped memory therefore remains sound when the real process has additional sections or libraries mapped elsewhere.
- **Layout-generic placement:** Rather than verifying a binary only at a single fixed address or fixed section layout, library contracts are stated over every placement a stock static linker (`ld.lld`) may choose for the library's relocatable ELF (`ET_REL`) objects exported from Rust or C (`Obj.PlacedLib` / `Obj.MultiPlacedLib`, `Obj.Placement`, `PlacedLib.Placeable`), including per-site linker relaxations, and are then instantiated against the concrete linked ELF (`PlacedLib.InElf`). External functions and Rust `panic = abort` entry points are modeled explicitly via state hooks (`externs`, `overrides`, `Rust.withPanics`). The older fixed-layout `Obj.LinkedImage` loader lives outside the TCB in `Arm64/Legacy/`.
- **Built-in separation-logic framing and calling conventions:** Subroutine specifications (`Spec`, `subroutine_ok`) pair byte-granular partial-heap assertions (`SepProp`) with AAPCS64 calling-convention invariants (`sp` and callee-saved register preservation) and quantify universally over an arbitrary separation-logic frame (`∀ R, s₀.mem ⊨ pre ∗ R → … → sf.mem ⊨ post ∗ R`), making verified subroutines compositional across callers without manual disjointness bookkeeping.

## Sub-Layers

The trusted code lives in [`Arm64/Trusted/`](./Trusted/README.md) and is split into three sub-layers, each importing only the ones above it:

| Sub-layer | Directory | Contents |
|---|---|---|
| 1. Instruction-level semantics ([coverage \& sequential model](./Trusted/ISA/README.md)) | [`Arm64/Trusted/ISA/`](./Trusted/ISA/) | `Syntax`, `Decode`, `Memory`, `State`, `Float`, `Eval`, `Semantics` (instruction AST, decoder, memory/permissions, architectural state, `execInst`, `Step`/`Steps`) |
| 2. Object linking \& loading | [`Arm64/Trusted/Object/`](./Trusted/Object/) | `LinkedImage` (static-linker output `Obj.LinkedImage`/`Obj.Image`, `load`), `Loader` (`Program.ofImage`, `Obj.Image.Loaded`) |
| 3. Machine-level specification foundation (`Init`-only) | [`Arm64/Trusted/Spec/`](./Trusted/Spec/) | `RustRuntime`, `RustHeap`, `GlobalAlloc`, `RustAbi`, `AsciiNum`, `SepLogic`, `Hoare`, `Library` (`SepProp`, `Spec`, `subroutine_ok`, `library_ok`) |
| 4. Surface specification DSLs & literal elaborators | [`Arm64/Trusted/Surface/`](./Trusted/Surface/) | `Abi` (`c_spec`/`rust_spec`), `CType` (`c_type_spec`), `HexCode` (`hex_words%`), `Ascii` (`ascii!`/`asciic!`/`asciiCode!`), `IncludeBytes` (`include_bytes%`), `FileBytes` (`file_bytes%`) |

The higher-level specification vocabulary and surface macros that campaign specs are written in (`c_spec`/`rust_spec` in `Surface/Abi.lean`, `c_type_spec` in `Surface/CType.lean`, `ascii!` in `Surface/Ascii.lean`, subroutine hook definitions in `Spec/Hoare.lean`) are re-exported by `import Arm64` (layering: `Arm64 < ProofLib < Examples < Testing`); see [`Trusted/README.md`](Trusted/README.md).

## Quick Module Lookup Table ("Which file to read/import for X")

All `Spec.lean` files should `import Arm64` (the umbrella module), which re-exports everything below except `Arm64.Trusted.Surface.IncludeBytes` and `Arm64.Trusted.Process` (`Arm64.Trusted.Surface.FileBytes`).

| Need / Concept | Module | Key Definitions & Exports |
|---|---|---|
| Register names, operand widths, condition codes, A64 instruction AST | `Arm64/Trusted/ISA/Syntax.lean` | `Reg`, `VReg`, `MemWidth`, `RegWidth`, `CondCode`, `ShiftType`, `ExtendType`, `AddrMode`, `PairAddrMode`, `Instr` |
| Byte-addressable virtual memory, permissions (`Perm`), W^X, endian reads/writes | `Arm64/Trusted/ISA/Memory.lean` | `Perm`, `Memory`, `read8`/`16`/`32`/`64`/`128`, `write8`/`16`/`32`/`64`/`128`, `readBytes`, `writeBytes`, `canRead`, `canWrite`, `canExec`, `KeepsFrozen` |
| Architectural state (`X0..X30`, `SP`, `PC`, `NZCV`, `V0..V31`, status, hooks) | `Arm64/Trusted/ISA/State.lean` | `PState`, `RegFile`, `VRegFile`, `ExecStatus`, `State`, `readReg64`, `writeReg64`, `readReg32`, `writeReg32`, `readVReg128`, `writeVReg128` |
| IEEE-754 binary32/binary64 floating-point semantics, rounding, and conversions | `Arm64/Trusted/ISA/Float.lean` | `FpRoundMode`, `FpFormat`, `fpAbs32`/`64`, `fpNeg32`/`64`, `fpAdd32`/`64`, `fpSub32`/`64`, `fpMul32`/`64`, `fpDiv32`/`64`, `fpSqrt32`/`64`, `fpFma32`/`64`, `evalFp*`, `evalIntToFp*` |
| 32-bit machine word (`BitVec 32`) → `Instr` decoding & logical bitmasks | `Arm64/Trusted/ISA/Decode.lean` | `Arm64.decode`, `decodeBitMasks`, `decodeBitMasksValid`, `decodeBitMasksVal` |
| Single-instruction architectural execution semantics & `svc #0` syscalls | `Arm64/Trusted/ISA/Eval.lean` | `execInst`, `AddWithCarry32`/`64`, `ConditionHolds`, `evalAddrMode`, `evalBitfield`, `evalAesOp`, `execSyscall` |
| `Program` image, instruction fetch from memory, `Step` / `Steps` operational semantics | `Arm64/Trusted/ISA/Semantics.lean` | `Program`, `Program.fetchMem`, `Program.fetch`, `Program.CodeLoaded`, `Step`, `Steps`, `StepsUntil` |
| Layout-generic placed libraries, symbolic relocations, relaxation encodings, and `Obj.HoldsBytes` | `Arm64/Trusted/Object/{Reloc,Placed}.lean`, `Arm64/Trusted/{Spec,Process}/Placed.lean` | `Obj.RelocKind`, `Obj.HoldsBytes`, `Obj.CodeBlock`, `Obj.PlacedLib`, `Obj.MultiPlacedLib`, `Obj.Placement`, `PlacedLib.Placeable`, `PlacedLib.program`, `PlacedLib.dataInit`, `PlacedLib.subroutineOk`, `PlacedLib.InElf`, `PlacedLib.LinkedIn` |
| Static ELF64 (`ET_EXEC`) process loading, Linux AArch64 initial stack/auxv/fds, SHA-256-pinned file-byte literal (`file_bytes%`), and whole-binary safety/correctness contracts | `Arm64/Trusted/Process.lean` (`Arm64/Trusted/Process/`) | `file_bytes%`, `ProcessInit`, `ProcessInputs`, `ElfImage`, `ProcessOutcome`, `ElfImage.parse`, `ElfImage.loadState`, `loadElf`, `ProcessExitsWith`, `ProcessPartialRunsTo`, `ProcessRunsTo`, `ElfRunsTo`, `ElfPartialRunsTo`, `ElfCorrect`, `ElfSafe`, `ElfRunsToWithOverrides` |
| Modeling Rust `panic = abort` entry points (`core::panicking::*`, `unwrap_failed`) | `Arm64/Trusted/Spec/RustRuntime.lean` | `Rust.isPanicSymbol`, `Rust.panicked`, `Rust.withPanics` |
| Rust heap values and allocator hook contracts over an abstract `Arm64.Allocator` | `Arm64/Trusted/Spec/RustHeap.lean` | `Rust.hookFrame`, `Rust.SmallLen`, `Rust.vecOf`, `Rust.boxAt`, `Rust.allocSpec`, `Rust.deallocSpec`, `Rust.shimSpec` |
| Generic alignment-aware Rust `GlobalAlloc` contracts and verified allocator bundle | `Arm64/Trusted/Spec/GlobalAlloc.lean` | `Rust.IsPow2Align`, `Rust.LayoutOk`, `Rust.AllocStatePreserved`, `Rust.VmPreserved`, `Rust.BudgetOk`, `Rust.GlobalAllocAddrs`, `Rust.globalAllocSpec`, `Rust.globalAllocZeroedSpec`, `Rust.globalDeallocSpec`, `Rust.globalReallocSpec`, `Rust.GlobalAlloc` |
| Rust `Option`/`Result` return layouts (pinned `rustc 1.98.1`) | `Arm64/Trusted/Spec/RustAbi.lean` | `RustAbi.RetEnc`, `optionU64`/`U32`/`U16`/`U8`, `optionNonNull64`, `optionSlice`, `resultU64`, `resultU8`, `optionCapNicheAt`, `optionTagged64At` |
| Byte-granular separation logic (`SepProp`), points-to (`↦₈`..`↦₁₂₈`, `↦ₛ`), stack frames | `Arm64/Trusted/Spec/SepLogic.lean` | `Heap`, `SepProp`, `m ⊨ P`, `P ∗ Q`, `P -∗ Q`, `↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`, `↦₁₂₈`, `↦ₛ`, `↦₆₄*`, `memRegion`, `stackFrame` |
| Subroutine contracts (`Spec`), AAPCS64 preservation, total/partial Hoare triples | `Arm64/Trusted/Spec/Hoare.lean` | `Spec`, `CalleeSavedPreserved`, `CallingConventionPreserved`, `Returned`, `SubroutineOutcome`, `subroutine_ok`, `reaches_stop`, `safe_until`, `exit_ok` |
| Canonical ASCII decimal integer formatting and parsing | `Arm64/Trusted/Spec/AsciiNum.lean` | `natToDigits10`, `formatDecimalNat`, `formatDecimalInt`, `parseDecimalNat`, `parseDecimalUInt` (`parseDecimalU64`, `parseDecimalU32`), `parseDecimalInt`, `parseDecimalSInt` (`parseDecimalI64`) |
| `c_spec` / `rust_spec` contract DSLs, `c_type_spec` semantic C types, `hex_words%`, and `ascii!` literals | `Arm64/Trusted/Surface/{Abi,CType,HexCode,Ascii}.lean` | `c_spec`, `rust_spec`, `c_type_spec`, `hex_words%`, `Program.ofHex`, `ascii!`, `asciic!`, `asciiCode!` |
| Compile-time binary file slice and SHA-256-pinned file elaborators | `Arm64/Trusted/Surface/{IncludeBytes,FileBytes}.lean` | `include_bytes% "path" off len`, `IncludeBytes.read`, `IncludeBytes.toListExpr`, `file_bytes% "path" sha256 "<hex>"` |

## Navigation & Audit Rule

- **100% Theorem-Free TCB (`Role::Spec`):** `Arm64.lean` and `Arm64/Trusted/` are enforced by `check-trust-guards` to contain **0 theorems or lemmas**. All proof rules, rewrite lemmas, and tactics live in `ProofLib/`.
- **Check Top-of-File Headers or Outlines First:** Every `.lean` file in `Arm64/Trusted/` and `Arm64/Testing/` starts with a concise `/-! ... -/` summary header within the first 35 lines. Always inspect `view_file(StartLine=1, EndLine=35)` or run `.agents/skills/lean-signatures/lean-sig outline Arm64/Trusted/<SubLayer>/<Module>.lean` before reading full files, and never read large modules (`Syntax.lean`, `Decode.lean`, `Eval.lean`, `SepLogic.lean`) end-to-end.

## What Lives Outside the TCB (Untrusted Validation & Runners)

`Arm64/Trusted/` contains only what a reader must trust to believe a verified theorem: the syntax, the decoder, the evaluator, the `Step`/`Steps` relation, the loader predicates, separation logic, and the Hoare contracts. Code that merely *executes*, *tests*, or *cross-checks* these definitions lives outside `Arm64/Trusted/` (in [`Arm64/Testing/`](./Testing/README.md) or `ProofLib/`), because no theorem statement in a `Spec.lean` or `Theorems/` file mentions it. A bug there can make a test fail (or pass vacuously), but cannot make a proof unsound.

| Untrusted component | Location | Why it is not in the TCB |
|---|---|---|
| Instruction encoder (`Arm64.encode`, `encodeInst`, `encodeBitMasks`, `encodeHex`, `hex32`, `encodeProg`, `decodeProg`) | `Arm64/Testing/Harness/Encode.lean` | Specs only fetch and **decode** bytes from memory, so the decoder is trusted and the encoder is not. The encoder exists to validate the decoder and to assemble test programs. |
| Decode/encode round-trip theorem (`encode_of_decode`) | `Arm64/Testing/Proofs/EncoderDecoder.lean` (+ `Common.lean`, `Part1..5.lean`) | A kernel-checked proof that `decode bs = some p → encode p = some bs`. It shows the decoder has no shadowed branches or lossy fields, and lets the encoder serve as a more readable restatement of it. It adds confidence in `Arm64/Trusted/ISA/Decode.lean` without being an assumption. |
| Executable runners & test-memory builders (`ProofLib.stepState`, `execN`, `execUntilPC`, `Program.loadCode`, `Memory.mapRestRw`) | `ProofLib/Exec.lean` | Computable simulators that `ProofLib/Simulation.lean` proves agree with `Step`. They are used to run concrete tests and reflection proofs, and are never mentioned by specs. |
| Deprecated legacy `LinkedImage` compatibility modules (`Obj.LinkedImage`, `Obj.Loads`, `Program.ofImage`, `LibrarySpec`, `library_ok`) | `Arm64/Legacy.lean` (`Arm64/Legacy/`) | Untrusted compatibility layer (`[proof]`, shrinking importer allowlist) retained only for legacy `ProofLib/` and `Arm64/Testing/` consumers. |
| ELF region materialization (`LoadedRegion`, `Image.toLoadedRegions`, `Image.loadIntoMemory`) | `Arm64/Testing/Harness/ElfRegionLoad.lean` | Builds a concrete `Memory` from an `Obj.Image` so that `elf_eval` can be compared against `ld.lld` and the Linux ELF loader (`Obj.Image.Loaded` in `Arm64/Legacy/Object/Loader.lean`). |
| Loader & `library_ok` unit tests | `Arm64/Testing/Regression/ObjectLoad.lean` | Check `LinkedImage.load` and `library_ok` against a hand-assembled image. |
| Differential harnesses (Unicorn, Sail Armv9.4-A, SoftFloat, `ld.lld`) | `Arm64/Testing/Harness/{TestCase,Compare,DifferentialEval,ElfEval}.lean`, `Arm64/Testing/Generators/TrustedSuite.lean` | Compare `execInst` / `LinkedImage.load` against external oracles. They give empirical evidence that the trusted model matches hardware, but are not part of what is trusted. |

See [`TESTING.md`](./TESTING.md) for how these layers fit together.
