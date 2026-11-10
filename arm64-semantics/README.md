# Arm64 verification engine

This is a system for specifying and verifying Rust and C at the arm64 assembly level.

The idea is that you bring code and a specification (or, more likely, iteratively design the specification), an agent comes up with a proof, and you can have confidence that the compiled assembly of your code actually meets your specification. Such a guarantee is only possible because only minimal code is needed to define a theorem statement in Lean about the code, and the Lean kernel checks the agent-written proof. And the fact that this works at all is because AI has reached a level of performance where reasoning about assembly is within reach, and this capability is only going to get better.

> **Using the engine vs. developing the engine:** If you (or an agent) are **using** this engine to specify and verify C or Rust binaries—either in a downstream repository that consumes it as a submodule/Lake dependency (`arm64-semantics/`) or in a case study—start at [`ProofLib/README.md`](ProofLib/README.md).

## Prerequisites

- **Lean:** [elan](https://github.com/leanprover/elan). It installs the toolchain pinned in [`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.34.0`) on the first `lake` command.
- **Rust:** `rustc` and `cargo` **1.98.1** (the exact version is pinned: the `VerifiedLibraries` build scripts check the bundled musl `libc.a` byte for byte), with the `aarch64-unknown-linux-musl` and `aarch64-unknown-linux-gnu` targets and the `rust-src` and `llvm-tools` (`rust-lld`, `llvm-ar`) components:

  ```bash
  rustup toolchain install 1.98.1 --profile minimal \
    --target aarch64-unknown-linux-musl,aarch64-unknown-linux-gnu --component rust-src,llvm-tools
  ```

  Lake builds the Rust tools it needs (`tools/rust-obj2lean`) with `cargo` and uses them to regenerate the `Generated/` Lean modules from the C and Rust sources, so these modules are not checked in. The core libraries (`Arm64`, `ProofLib`) do not need Rust.
- **`ld.lld`** (LLVM linker, e.g. `sudo apt install lld`) on `PATH`, for the linker differential tests.

**Hardware.** A full build (Rust tools, generated modules, the engine tests, `VerifiedLibraries`, and `CaseStudies/Hashbrown`) takes about 35–40 minutes on 12 cores and peaks at about 25 GiB of memory. Use at least 16 GB of RAM (with `LEAN_NUM_THREADS` of 2–4 and a much longer build), 32 GB or more for 12-way parallelism, and about 6 GB of free disk. Building only the core libraries (`lake build`) takes about 13–15 minutes and stays under 6 GB.

## Building

```bash
lake build                                  # default target: the core libraries Arm64 and ProofLib
lake build ProofLib.Testing @arm64-testing  # engine tests (ProofLib/Testing and Arm64/Testing)
lake -d VerifiedLibraries build             # verified C/Rust foundation libraries (Mallocng, Musl, RustStd, ...)
lake -d CaseStudies/Hashbrown build         # the Hashbrown case study
```

`VerifiedLibraries` and each `CaseStudies/<Lib>` are separate Lake packages, so a bare `lake build` at the root does not build them. Set `LEAN_NUM_THREADS` to bound parallelism (and memory).

### Testing dependencies

The test ELFs under `Arm64/Testing/` and `VerifiedLibraries/*/Testing/` are generated from committed sources by `scripts/build-test-elfs.sh` (`--check` verifies the committed binaries are byte-identical to a fresh build). It needs Rust 1.98.1 with the targets above plus `rust-src`, zig 0.16.0 (optional: zig-built ELFs are skipped without it), and `llvm-mc`; the differential tests run under the `qemu-aarch64` pinned by `scripts/fetch-qemu-aarch64`. Tests whose ELF is missing report `SKIPPED`. See [Generated test ELFs](Arm64/Testing/README.md#7-generated-test-elfs) and [Testing dependencies](Arm64/Testing/README.md#testing-dependencies).

## High-level overview

The engine has two parts: there is _trusted code_ to define the theorem statements, and then there is _untrusted code_ that makes it easier for agents to prove the theorem statements. The split is useful for development, both the humans reviewing the work and the agents doing it - we can allow considerable freedom to experiment and test in the untrusted code with verification for free (it's provided by Lean). We keep the trusted code small and general since we want to concentrate human trust in it over time, by using this system for many tasks.

These parts roughly correspond to the two parts of the workflow: first the system produces a theorem statement with trusted code, then in part two the agent uses untrusted tools and proof libraries. However, there is a third category somewhat in between: testing infrastructure helps build confidence in the trusted code, and the way we build confidence in the testing infrastructure itself is a bit complicated.

`tcb-map --tree` (or `--tree-json`) labels every file in the repository with one of six categories: `tcb` (the core engine's trusted code: `Arm64/Trusted/` and the trusted parts of `tools/rust-obj2lean`), `case-studies-tcb` (`third_party/`, `VerifiedLibraries/**/Spec*`, `VerifiedLibraries/**/Theorems*`, `CaseStudies/**/Spec*`, `CaseStudies/**/Theorems*`, and the optional [`tools/proc-snapshot`](tools/proc-snapshot/README.md) process-snapshot dumper, which are trusted only insofar as you want the case-study or snapshot proofs; deleting them leaves the core engine intact), `proof`, `testing` (including `tools/tcb-map/` and `tools/run-trusted-tests/`), `infra`, and `doc` (all `*.md` files).

## Trusted code

The first problem we run into is that we need a **semantics** to say what the code does when executed in order to prove anything about it. The semantics have to be formal; in our case we have good reason to prefer it to be in Lean. The semantics needs to accurately reflect (or typically over-approximate) the behavior of the code when run, otherwise you can prove a property of the code that doesn't hold in the real world. Our semantics starts from the compiled code, so it also models compiler and OS features like how this code will be linked and loaded into memory, which need to happen before we can execute anything.

Next, we need the user to supply some **specification**, which is what I call something that is sufficiently mathematical to be unambiguous to the verification engine, and which makes sense to the user, so they can compare it with their intent. Note that this means natural language can’t be used as a specification on its own, since its meaning is ambiguous. The typical specification for all of our work will be pre/post conditions for the top-level API of the code, possibly in separation logic or concurrent separation logic, but there are other more esoteric options.

The verification engine then attaches the specification to the semantics of the code (what I sometimes call a model) in order to produce a **theorem statement**. The theorem is what gives the specification meaning and ought to match what the user thinks the specification means. These theorem statements will necessarily involve the semantics, since we want to prove something about what our code does when run.

Concretely the way these map to the code is that the semantics is a combination of the model of relocatable object placement ([`Arm64/Trusted/Object/Placed.lean`](Arm64/Trusted/Object/Placed.lean) and [`Arm64/Trusted/Spec/Placed.lean`](Arm64/Trusted/Spec/Placed.lean)), static ELF64 process loading ([`Arm64/Trusted/Process/`](Arm64/Trusted/Process/README.md)), the `Arm64.Steps` relation ([`Arm64/Trusted/ISA/Semantics.lean`](Arm64/Trusted/ISA/Semantics.lean), with per-instruction behavior in [`Arm64/Trusted/ISA/Eval.lean`](Arm64/Trusted/ISA/Eval.lean)), and a model of a few Linux system calls (`execSyscall`, also in `Eval.lean`); the specifications are written as pre- and post-conditions in the `c_spec`, `rust_spec`, and `c_type_spec` DSLs ([`Arm64/Trusted/Surface/Abi.lean`](Arm64/Trusted/Surface/Abi.lean) and [`Arm64/Trusted/Surface/CType.lean`](Arm64/Trusted/Surface/CType.lean)) that lower to separation-logic predicates ([`Arm64/Trusted/Spec/SepLogic.lean`](Arm64/Trusted/Spec/SepLogic.lean)) over the architecture and memory state; and the theorem statements use definitions like `subroutine_ok` ([`Arm64/Trusted/Spec/Hoare.lean`](Arm64/Trusted/Spec/Hoare.lean)) or whole-process contracts (`ElfSafe`, `ElfCorrect` in [`Arm64/Trusted/Process/Semantics.lean`](Arm64/Trusted/Process/Semantics.lean)) that define pre- and post-conditions at the assembly level. The specifications and `subroutine_ok` also formalize the ABI and calling conventions of ARM64, Linux, and the language being verified, so we incidentally prove that the compiler has implemented these conventions correctly. Each verified library or CLI binary has a trusted `Spec/*.lean` in a standalone package under `CaseStudies/<Target>/` (e.g., [`CaseStudies/Hashbrown/Spec/Top.lean`](CaseStudies/Hashbrown/Spec/Top.lean)) or [`VerifiedLibraries/`](VerifiedLibraries/README.md) with theorem statements about the program image or static ELF binary, and untrusted proofs in the corresponding `Proofs/` directory.

### Compiled libraries

We work at the level of compiled libraries, modeling the process of placing and loading code before executing it. Compilation produces relocatable ELF object files (`.o`) with symbolic references; [`tools/rust-obj2lean/`](tools/rust-obj2lean/) extracts relocatable code/data blocks and symbolic relocations into `Obj.PlacedLib` / `Obj.MultiPlacedLib` (see [`Arm64/Trusted/Object/README.md`](Arm64/Trusted/Object/README.md)), and specifications quantify over every valid linker placement (`PlacedLib.Placeable`), including `ld.lld` instruction relaxations, before tying the library to a stock-linked executable (`PlacedLib.LinkedIn`).

Any verification effort must contend with trusted code - it is difficult and undesirable to verify every single dependency, and in any case we would like to have modular proofs where the proof of a function depends only on the specifications for any libraries it depends on. Thus our infrastructure supports making assumptions over other libraries (modeling that eventually the linker will make that code available at run time) as well as dispatching those assumptions with proofs ([`Arm64/Trusted/Spec/Placed.lean`](Arm64/Trusted/Spec/Placed.lean) and [`Arm64/Trusted/Spec/Hoare.lean`](Arm64/Trusted/Spec/Hoare.lean)) and obtaining a closed proof with no trusted specifications at the interface boundary. What's especially cool about this approach in this setting is that we can verify Rust-C FFI code on both sides and connect the proofs, something which would be quite challenging at the source code level.

We only handle Linux, which uses ELF object files. We do not handle dynamic linking and only attempt to model static linking. We may in the future be able to verify shared objects themselves, though we will even then likely not support dynamic relocations (references via the PLT and GOT that the dynamic linker resolves at load time) to other shared objects.

In simple terms, the ELF object file is made up of the following sections (for our purposes):

- `.text` has the code itself
- `.rodata` has global read-only data
- `.data` and `.bss` have mutable and zero-initialized global data
- `.symtab` has a symbol table used by the linker to resolve functions and globals, and which we use to identify where in the code each function lives
- `.rela.*` sections have relocations: the symbolic references to patch. Our linker resolves these statically, except for absolute addresses, which the loader fills in (in the data or in GOT slots) once the load address is chosen. Calls to external functions go to a stub whose behavior is given by a hook rather than a PLT.

An ELF file might have other sections that we use as hints (e.g., DWARF debug info), and other sections that are irrelevant to us (e.g., note sections that aren't even loaded).

Note that Linux also uses the ELF file format for binaries. These differ from object files in that they often have a fixed load address (so all addresses in the binary can be interpreted as absolute virtual memory addresses), and the only unresolved symbols will be to shared libraries (`.so` files) resolved by the dynamic linker.

### Arm64 and Linux syscall semantics

We need to model the execution of the code after it is loaded. At its core this is actually the easy part, because Arm64 isn't too complicated (it has 2,000 instructions, many of which are vector instructions), and more importantly its semantics are well documented by official sources - ARM publishes a machine-readable XML specification giving the decoding and behavior of every instruction in a precisely defined language called ASL (Arm Specification Language). We work off this structured text rather than the PDF manual (see [`Arm64/Trusted/ISA/README.md`](Arm64/Trusted/ISA/README.md)). Furthermore instruction decoding and execution can be readily tested against emulators and hardware.

It is quite useful that we model the semantics at the level of bytes and not "high-level" textual assembly. It means we can give a uniform model of memory: it's just bytes, with no distinction between code and data. It does require that we have a trusted model of instruction decoding: the process of turning bytes into high-level, structured instructions. We do implement an (untrusted) instruction encoder ([`Arm64/Testing/Harness/Encode.lean`](Arm64/Testing/Harness/Encode.lean)) on this syntax ([`Arm64/Trusted/ISA/Syntax.lean`](Arm64/Trusted/ISA/Syntax.lean), decoded by [`Arm64/Trusted/ISA/Decode.lean`](Arm64/Trusted/ISA/Decode.lean)) and prove in [`Arm64/Testing/Proofs/EncoderDecoder.lean`](Arm64/Testing/Proofs/EncoderDecoder.lean) that $\forall bs.\, encode(decode(bs)) = bs$ - this shows that decoding is the process of finding a valid encoding and means the encoder provides a more readable version of the decoder. The encoder and its round-trip proof live under [`Arm64/Testing/Harness/Encode.lean`](Arm64/Testing/Harness/Encode.lean) and [`Arm64/Testing/Proofs/EncoderDecoder/`](Arm64/Testing/Proofs/EncoderDecoder/), outside the `Arm64/Trusted/` TCB, since specs only ever decode. See **[`Arm64/Testing/README.md`](Arm64/Testing/README.md)** and **[`Arm64/TESTING.md`](Arm64/TESTING.md)** for the complete six-layer ISA validation and differential conformance architecture (formal round-trip proofs, concrete/symbolic suites, LLVM + Unicorn + `ld.lld` differential testing, and Sail Armv9.4-A validation).

In reality the code runs as a process managed by the operating system, not on bare metal hardware, so the Arm instruction manual is insufficient to describe its behavior completely. Luckily the operating system uses _limited direct execution_ where most of the execution is directly on the hardware at an unprivileged level (EL0 on Arm64), so the hardware's ISA model handles the majority of the execution. However, there are two important exceptions: memory is actually virtual memory set up by the operating system (such as the program text itself), and the program can make _system calls_ to the operating system with the SVC instruction. We model a small subset of system calls (mainly `brk`/`sbrk` and anonymous `mmap`) needed to verify memory allocators and some other low-level systems code.

We do model virtual memory permissions ([`Arm64/Trusted/ISA/Memory.lean`](Arm64/Trusted/ISA/Memory.lean)), such as making writes to read-only memory an error, and forbidding non-executable memory. To simplify the model and proofs, we currently make self-modifying code (writes to executable memory) a runtime error of the kind that prevents proving anything about the program - it would be relatively straightforward to extend the model to support self-modifying code, but proofs would then need to maintain the invariant that the rest of the code is never modified.

The model is single-threaded: there is one PE and no other observer of memory, so memory is sequentially consistent. Load-acquire / store-release (`LDAR*`/`STLR*`) have exactly the memory effect of plain loads/stores, barriers (`DMB`/`DSB`/`ISB`/`CLREX`) are no-ops, and the load/store-exclusive instructions (`LDXR*`/`LDAXR*`/`STXR*`/`STLXR*`, [`Arm64/Trusted/ISA/Eval.lean`](Arm64/Trusted/ISA/Eval.lean)) do not model an address-granular exclusive monitor: `LDXR` is a plain load and each `STXR` draws whether it fails spuriously from the finite adversarial stream `State.exclFails` (seeded from `ProcessInputs.oracle.exclFails`; under `defaultOracle`, `exclFails = []` so `STXR` always succeeds, whereas quantifying over `Oracle` covers arbitrary finite sequences of spurious failures). In particular, a store-exclusive with no preceding `LDXR*`/`LDAXR*` that marked its address exclusive (or one after an intervening `CLREX`) *always* fails on hardware (`AArch64_ExclusiveMonitorsPass` returns FALSE), so the model's success path is not a hardware execution at all and a proof about such code says nothing about how it behaves on hardware; compilers emit `STXR` only paired with a preceding `LDXR` in the same retry loop. For the usual `LDXR`/`STXR` retry loop, quantifying over `Oracle` proves safety and termination across any finite number of spurious failures in single-threaded execution, while saying nothing about concurrent shared-memory behavior or termination under unbounded contention. All of these still require natural alignment (an unaligned access is an alignment fault), matching the architecture.

### Whole-process ELF semantics

Alongside relocatable library verification (`Obj.Loads` + `subroutine_ok`), the engine models complete, statically linked Linux AArch64 executables (`ET_EXEC`) from `_start` (`crt1.o`) through `SYS_exit` / `SYS_exit_group` in [`Arm64/Trusted/Process/`](Arm64/Trusted/Process/README.md):

- **Loading & environment inputs ([`Types.lean`](Arm64/Trusted/Process/Types.lean), [`Loader.lean`](Arm64/Trusted/Process/Loader.lean)):** `loadElf` (`ElfImage.parse` + `ElfImage.loadState`, with compile-time helper `elf_image%`) validates a static AArch64 `ET_EXEC` binary purely in Lean, maps its `PT_LOAD` segments and deterministic Linux user stack (`argc`, `argv`, `envp`, `auxv` including `AT_RANDOM`), initializes `State.fs` (`stdin`/`stdout`/`stderr` on `fd 0/1/2` plus pre-populated `files`/`dirs`), and seeds `State.oracle` / `State.exclFails` from `ProcessInputs`.
- **Whole-binary contracts ([`Semantics.lean`](Arm64/Trusted/Process/Semantics.lean), proof rules in [`ProofLib/Process.lean`](ProofLib/Process.lean)):** Under the hook-free program `Program.pureMem`, `ElfSafe`, `ElfCorrect`, and multi-exit-code `ElfRunsTo` state separation-logic-free safety (`ProcessSafeRun` / `ProcessSafeOutcome`) and total functional correctness (`ProcessExitsWith` over `ProcessOutcome`: `exitCode`, `signal`, `stdout`, `stderr`, and final `State.fs`) directly over `Arm64.Step` / `Arm64.Steps`.
- **Guided tour, examples, and QEMU validation:** Read **[`Arm64/Testing/Tours/ProcessSemanticsTour.lean`](Arm64/Testing/Tours/ProcessSemanticsTour.lean)** for a self-contained, kernel-checked tour covering `loadElf`, `ProcessInputs` quantification, syscalls/exit, proven examples (including [`CaseStudies/Hashbrown/`](CaseStudies/Hashbrown/README.md)), the trust boundary, the 12-binary `qemu-aarch64` differential test suite ([`Arm64/Testing/ProcessE2E/`](Arm64/Testing/ProcessE2E/README.md), [`Arm64/Testing/Regression/ProcessE2E.lean`](Arm64/Testing/Regression/ProcessE2E.lean)), and known modeling boundaries (fail-closed `fcntl(F_GETFD)` / `".."` paths / directory syscalls, restricted `mmap` flags, `BRK #1` $\to$ exit `101`, and single-threaded execution).

### Specifications

The top-level specifications defined in [`Arm64/Trusted/Spec/Hoare.lean`](Arm64/Trusted/Spec/Hoare.lean) are trusted in an important sense: they define what it means for a user to obtain a proof of some pre/postconditions. Even the form of these specifications is important due to a need for _Pollack consistency_: soundness here means that the user _interprets_ the specifications correctly, which means they must be self-evident, unsurprising, and standard.

Achieving readable, interpretable specifications at the assembly level is not entirely straightforward, so we have a DSL ([`Arm64/Trusted/Surface/Abi.lean`](Arm64/Trusted/Surface/Abi.lean); see [`ProofLib/Abi/README.md`](ProofLib/Abi/README.md)) to make this easier on the user. The DSL and the rest of the vocabulary that surface specs are written in (separation logic, `c_type_spec`, subroutine hook definitions) live in the trusted [`Arm64/Trusted/`](Arm64/Trusted/README.md) layer (`Spec/` and `Surface/`), separate from the untrusted lemmas and convenience combinators about them in `ProofLib/`: a bug in `c_spec` expansion could make a spec mean something weaker than the reader thinks even though the kernel accepts the proof. In Rust and C this is relatively easy as long as the data manipulated by the top-level code is straightforward (e.g., integers, arrays of bytes, and pointers are all easy to understand even at the level of the ISA). Something like a function pointer would make the specification harder to understand.

We can only specify and verify code that actually compiles to assembly. This rules out verifying generic code in Rust (anything that takes a type parameter for example), since this code isn't compiled until the parameters are instantiated. However, it is possible to specialize a generic API to a particular concrete parameter, then compile, specify, and verify the result - but note that we do not attempt to make these proofs generic in the type parameter. We would like to be able to verify at least `Vec` in a generic way, and other simple type parameterizations, but Rust's generics are quite powerful.

### Infrastructure

We use a self-contained tool [`tcb-map`](tools/tcb-map/) (run via [`scripts/tcb-map`](scripts/tcb-map)) that enforces that the trust model itself is legible: it enforces that trusted code does not import untrusted code. The library layering is `Arm64 < ProofLib < VerifiedLibraries < CaseStudies < Testing` with `Theorems` at the top: the trusted semantics and spec vocabulary in [`Arm64/Trusted/`](Arm64/Trusted/README.md) (split into `ISA/`, `Object/`, and `Spec/` sub-layers) contain only definitions, trusted `CaseStudies/<Target>/Spec*.lean` files may import only those (never `ProofLib`), and trusted `CaseStudies/<Target>/Theorems/*.lean` files state and discharge the closed top-level theorems (with zero `sorry` and nothing allowed to import `Theorems`). Tests live in the untrusted `Testing` libraries, next to what they test: [`Arm64/Testing/`](Arm64/Testing/README.md), [`ProofLib/Testing/`](ProofLib/Testing/README.md), and `CaseStudies/<Target>/Testing/` (e.g., [`CaseStudies/Hashbrown/Testing/`](CaseStudies/Hashbrown/Testing/SpecAudit.lean)). Once this guarantee is given, we can freely allow agents to modify the untrusted code and know that the soundness of our theorems cannot be compromised by a change. As a further check, [`scripts/axiom-audit`](scripts/axiom-audit) verifies in the Lean kernel that every theorem in `CaseStudies` and `Theorems` depends only on Lean's three standard axioms (`propext`, `Quot.sound`, `Classical.choice`) with zero `sorry`.

Since we rely on `tcb-map` to keep agents honest and review code, it is itself trusted in a sense. We aim to make the trusted/untrusted layout as simple as possible to make review of the trust model simple.

## Untrusted infrastructure

### Hoare logic and separation logic

The trusted definitions in [`Arm64/Trusted/Spec/Hoare.lean`](Arm64/Trusted/Spec/Hoare.lean) like `subroutine_ok` say what a proof means, but they are stated in terms of a flat byte map and the `Arm64.Steps` relation. Reasoning about those directly across hundreds of instructions would be intractable.

[`ProofLib/SepLogic/`](ProofLib/SepLogic/) and [`ProofLib/Hoare/`](ProofLib/Hoare/) build a separation logic and weakest-precondition calculus on top of the semantics: assertions are `SepProp`s built from points-to facts (`↦₆₄`, `↦ₛ`, etc., with read-only variants like `↦ᵣ`), separating conjunction `∗`, and magic wand `-∗`, and proofs go through `wp` rules for each instruction, a reflection-based entailment solver (`sep_entail`, [`ProofLib/SepLogic/Solver.lean`](ProofLib/SepLogic/Solver.lean)), and loop and control-flow-graph rules ([`ProofLib/SepLogic/CFG.lean`](ProofLib/SepLogic/CFG.lean)). Specifications also use this vocabulary, so the core definitions are trusted, but all the rules are proven down to `Arm64.Steps` and `subroutine_ok`, so they add nothing to the trusted computing base.

### Two levels of symbolic execution

Much of the proof needs to do symbolic execution over assembly code, a tedious and somewhat automatable task.

We have two levels of symbolic execution. One in Lean which is untrusted (it is verified against the semantics) and verified (tactics like `wp_steps` ([`ProofLib/SepLogic/WP.lean`](ProofLib/SepLogic/WP.lean)) and `wp_sym_steps` ([`ProofLib/SepLogic/SymWP.lean`](ProofLib/SepLogic/SymWP.lean)) step through each basic block using the generated fetch/decode lemmas and per-instruction `wp` rules, producing an ordinary proof term that the kernel checks). This is used in the final proof build for performance reasons; without reasonably efficient proof infrastructure for this, the proofs would simply take too long to build.

The other level, implemented in Rust ([`tools/rust-obj2lean/src/untrusted_lemmas/symexec/`](tools/rust-obj2lean/src/untrusted_lemmas/symexec/)), is used only during proof development for fast feedback without having to run Lean. It aims to have the same behavior as Lean, but we don't have to trust this fact: the final proof will not use this symbolic execution.

### Tools to investigate the binary

Before writing a proof, an agent needs to understand what the compiler actually emitted: where basic blocks branch, how locals are laid out in the stack frame, and what offsets correspond to C or Rust struct fields. Getting these wrong by guessing wastes a lot of proof effort.

`lean-disasm` shows a function's instructions with their offsets, basic blocks, and callees; `lean-symexec` (the Rust symbolic executor) previews memory accesses and branch conditions. These tools are part of the full contributor checkout and are not included in this distribution.

## Development process

We have a highly agentic development process, where agents are empowered to propose, create, review, and merge PRs. This is possible because there's enough scaffolding that the goals and trust model of the project are clear to frontier models, and much of the code now lies outside the trusted computing base. We still need to review the trusted infrastructure, but by design this is minimized and augmented with layers of testing and validation against the real world.

An important source of validation of the infrastructure is actually using it to do proofs, which often reveals gaps as the agent tries to reason about the code in the model and meanwhile compares it with its own understanding and actually running the code. Thus we forge ahead in doing proofs before fully trusting the infrastructure: the proofs help to build that trust.

There are some new processes we are still working on. For example, we should test that the guards and tests really work and trigger on injected bugs. The ISA semantics is already differentially tested against Unicorn, the Sail Armv9.4-A model, and LLVM ([`tools/run-trusted-tests/`](tools/run-trusted-tests/)), and relocatable object placement and static ELF loading against `ld.lld` and the Linux ELF loader, but more of the infrastructure could be tested against an external source, particularly our model of virtual memory.

Specification validation is an important area for development and research. We have some basic vacuity checks (that is, showing that a precondition is not equivalent to false) in [`ProofLib/SpecAudit.lean`](ProofLib/SpecAudit.lean), run over the campaign specs in `CaseStudies/<Target>/Testing/` (e.g., [`CaseStudies/Hashbrown/Testing/SpecAudit.lean`](CaseStudies/Hashbrown/Testing/SpecAudit.lean), with linter regressions in [`ProofLib/Testing/`](ProofLib/Testing/README.md)). Another area to explore is _verified unit tests_: proving that a unit test always succeeds using only the specification, which shows that the specification is usable.

## Structure

The dependency order `Arm64 < ProofLib < VerifiedLibraries < CaseStudies` is enforced by Lake: `Arm64/`, `ProofLib/`, and [`VerifiedLibraries/`](VerifiedLibraries/README.md) are their own Lake packages ([`Arm64/lakefile.toml`](Arm64/lakefile.toml), package `arm64`, no dependencies; [`ProofLib/lakefile.toml`](ProofLib/lakefile.toml), package `prooflib`, requires `arm64`; [`VerifiedLibraries/lakefile.lean`](VerifiedLibraries/lakefile.lean), package `«verified-libraries»`, requires `prooflib` and houses reusable placement-generic verified foundation libraries `Mallocng`, `Musl`, and `RustStd`), the root [`lakefile.lean`](lakefile.lean) requires `prooflib` and `«verified-libraries»` and defines `Testing`, and standalone campaigns live in their own pairwise-independent Lake packages under `CaseStudies/<Lib>/` (e.g., [`CaseStudies/Hashbrown/`](CaseStudies/Hashbrown/README.md), built with `lake -d CaseStudies/<Lib> build`). Each package builds into its own `.lake/build`, so `Arm64` cannot import `ProofLib`, `VerifiedLibraries` cannot import `CaseStudies`, and no `CaseStudy` can import another `CaseStudy`. `lake -d Arm64 build` and `lake -d ProofLib build` build just those libraries without a Rust toolchain; a downstream project can `require prooflib` (or `arm64` / `«verified-libraries»`) by path or git `subDir` to use the engine without the case studies. From the repository root, a bare `lake build` builds `Arm64` and `ProofLib` (see [Building](#building)). After pulling upstream changes that update vendored C/Rust sources or `.lake/build` artifacts (symptoms: `failed to read Implementation/<target>/…` or `third_party/<pkg>/…`, `failed to read file …, incompatible header`, or stale `.olean`s after editing `Arm64/` or `ProofLib/`), run `./scripts/fetch-upstream-sources.sh` then `lake run sanitize` to unpack any new upstream sources and evict out-of-sync module artifacts across `.lake/build`, `Arm64/.lake/build`, `ProofLib/.lake/build`, and `VerifiedLibraries/.lake/build` (or `lake run sanitize --clean` for a full clean rebuild) while no `lake build` is running.

- [Arm64/](Arm64/) is a self-contained Lean development (its own Lake package) that gives a semantics for arm64 assembly, relocatable object loading ([`Arm64/Trusted/Object/`](Arm64/Trusted/Object/README.md)), static ELF64 process loading ([`Arm64/Trusted/Process/`](Arm64/Trusted/Process/README.md)), and a [specification language](Arm64/Trusted/Spec/) using separation logic pre- and post-conditions, defined at the assembly level. It includes differential testing infrastructure.
- [ProofLib/](ProofLib/) (its own Lake package, depending only on `Arm64`) provides untrusted proof infrastructure to verify programs on top of Arm64. None of this infrastructure should be used to _state_ the correctness of a program.
- `CaseStudies/` (e.g., [`CaseStudies/Hashbrown/`](CaseStudies/Hashbrown/README.md)) verifies both whole-process ELF64 binaries and unmodified C and Rust libraries.
  - `CaseStudies/<Name>/Implementation/` (plus [`VerifiedLibraries/`](VerifiedLibraries/README.md) `Implementation/` dirs) has the wrapper code and `translation.toml` configs for each campaign, while [third_party/](../third_party/) holds upstream third-party code (fetched on demand by [`scripts/fetch-upstream-sources.sh`](scripts/fetch-upstream-sources.sh), plus tracked configuration headers and patches). For the unmodified libraries, in some cases we compile small wrappers around the code (for example, to monomorphize generic Rust code).
  - `CaseStudies/<Name>/Theorems/` (`Role::Theorems`) states and discharges the closed end-to-end theorems over `Spec/` and `Proofs/`, audited in-repo by the Lean kernel and [`scripts/axiom-audit`](scripts/axiom-audit).
  - There is some testing infrastructure implemented as Lean metaprograms applied to the specifications themselves.
- [tools/](tools/README.md) (release Cargo workspace `tools/Cargo.toml`):
  - [rust-obj2lean](tools/rust-obj2lean/README.md) is the most important of the tools: it compiles a Rust or C library to an object file (a `.o` file, using the ELF file format) and loads that file into a generated Lean file, where it is then modeled by the Arm64 semantics. It also produces proofs to assist with verification, but these are checked again by Lean and are untrusted.
  - [proc-snapshot](tools/proc-snapshot/README.md) and [snapshot-link](tools/snapshot-link/README.md) link target objects into static AArch64 executables and capture process memory/register snapshots under `qemu-aarch64` user mode.
  - [tcb-map](tools/tcb-map) provides automated checks to help review the code ([`scripts/tcb-map`](scripts/tcb-map)), in particular confirming that specifications (theorem statements) do not depend on proofs, which allows us to skip reviewing the proof infrastructure (it is all checked by the Lean kernel).
  - [run-trusted-tests](tools/run-trusted-tests) and [sail-aarch64](tools/sail-aarch64/README.md) run the differential test suite comparing the Lean ISA semantics against LLVM, Unicorn, and the Sail Armv9.4-A C model (building requires `libgmp-dev`, e.g., `sudo apt install libgmp-dev`).

### Building API docs

API documentation is generated on demand with [`doc-gen4`](https://github.com/leanprover/doc-gen4) (`v4.34.0`), gated behind the opt-in Lake configuration flag `-Kenv=dev` in [`lakefile.lean`](lakefile.lean) and `CaseStudies/<Lib>/lakefile.lean` (e.g., [`CaseStudies/Hashbrown/lakefile.lean`](CaseStudies/Hashbrown/lakefile.lean)) so normal `lake build` runs, CI, and `lake-manifest.json` stay untouched.

Invoke `lake` with `-R -Kenv=dev`:

```bash
# Root package (output in .lake/build/doc/index.html):
lake -R -Kenv=dev --keep-toolchain update doc-gen4
DISABLE_EQUATIONS=1 lake -R -Kenv=dev build Arm64:docs
git checkout -- lake-manifest.json && rm -f .lake/config/*/lakefile.olean.trace

# Standalone CaseStudies/<Lib> package (output in CaseStudies/<Lib>/.lake/build/doc/index.html):
lake -d CaseStudies/Hashbrown -R -Kenv=dev --keep-toolchain update doc-gen4
DISABLE_EQUATIONS=1 lake -d CaseStudies/Hashbrown -R -Kenv=dev build CaseStudies.Hashbrown:docs
git checkout -- CaseStudies/Hashbrown/lake-manifest.json && rm -f CaseStudies/Hashbrown/.lake/config/*/lakefile.olean.trace

# Serve generated HTML locally:
python3 -m http.server -d .lake/build/doc 8000
```

## License

Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
