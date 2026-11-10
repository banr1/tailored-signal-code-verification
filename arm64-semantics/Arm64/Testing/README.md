# Testing the Arm64 Execution Model

Most program verification is at the source code level, typically in a language at about the level of abstraction of C or Rust. We instead verify at the assembly level, compiled for Arm64 on Linux; this avoids having to construct a formal model of a real source language and its compiler, at the cost of longer low-level proofs.

Because the Lean kernel checks every proof down to standard axioms, proof automation (`ProofLib/`) and proof scripts (`Proofs/`) do not need human review. What *does* have to be right is the **execution model** in [`Arm64/Trusted/`](../Trusted/README.md) (and, when verifying relocatable object libraries via pre-link `.o` extraction, the pure ELF `.o` parser in [`tools/rust-obj2lean/src/trusted_extractor/`](../../tools/rust-obj2lean/README.md); static linking sits outside the TCB). A hardware instruction manual alone is not enough to describe end-to-end execution of compiled code: the code is linked into an executable or library image, loaded into virtual memory with page permissions, launched as a process under Linux with an initial user stack, and occasionally interacts with the operating system through system calls (`SVC #0`). Linux uses limited direct execution—almost all user-space instructions run directly on the processor at `EL0`—so modeling the user-space ISA alongside process initialization, virtual memory permissions, and a small set of system calls captures what happens at run time without modeling the Linux kernel itself.

Why believe that this execution model matches what actually happens when the compiled binary runs under Linux on Arm64? First, each component of the model is kept small, stays as close to the machine as possible, and **fails closed**: unsupported or `CONSTRAINED UNPREDICTABLE` encodings, dynamic ELF features, unmapped or non-executable memory accesses, writes to executable pages, and unmodeled system calls transition to halt or fault states rather than approximating behavior. Second, every layer is tested against independent external implementations—ARM's ASL-derived Sail model, Unicorn/QEMU, Berkeley SoftFloat 3e, LLVM's assembler and `ld.lld` linker, `qemu-aarch64` user-mode execution, and the host `x86_64` Linux kernel.

Real-hardware (native AArch64) testing is currently **pending**: all CI runs on `x86_64` Linux against Sail, Unicorn, SoftFloat, `ld.lld`, `qemu-aarch64`, and the host kernel, and while a native AArch64 mode exists in code (`syscall_probe.elf record-json`), it is not run anywhere yet.

## How `Arm64/Testing/` is organized

`Arm64/Testing/` is a standalone, untrusted Lake package (`arm64-testing` in [`lakefile.lean`](lakefile.lean), umbrella module [`Arm64/Testing.lean`](../Testing.lean)) that sits strictly above `Arm64` and `ProofLib`. Nothing in `Arm64/Trusted/` or in any verified theorem statement imports from `Testing/`—a dependency rule enforced on every push by `scripts/dev/check-trust-guards.sh`. Reference encoders, fast evaluators, and differential harnesses can therefore live here without adding a single line to the trusted computing base.

The package builds five CLI executables (`unit_tests`, `diff_eval`, `elf_eval`, `placed_eval`, and `elf_run`) and groups its test suites by role:

| Path | Role in validating the model |
| :--- | :--- |
| [`lakefile.lean`](lakefile.lean) | Standalone `arm64-testing` Lake package (`Arm64Testing` library plus `unit_tests`, `diff_eval`, `elf_eval`, `placed_eval`, `elf_run`). |
| [`Harness/`](Harness/) | Untrusted A64 encoder (`Encode.lean`), test formats and comparators (`TestCase.lean`, `Compare.lean`), IEEE-754 batch harness (`FpEval.lean`), binary oracle server (`Serve.lean`), ELF/loader comparators (`ElfRegionLoad.lean`, `ElfLoaderDiff.lean`), fast paged ELF runner (`FastSemantics.lean`, `ElfRun.lean`, `ElfRunCli.lean`), and CLI entry points (`DifferentialEval.lean`, `ElfEval.lean`, `PlacedEval.lean`). |
| [`Proofs/`](Proofs/) | Kernel-checked `encode_of_decode` round-trip proof across all decode branches (`EncoderDecoder.lean`, `EncoderDecoder/Part1.lean`–`Part5.lean`), plus internal support for specification tours. |
| [`Conformance/`](Conformance/) | Seven kernel-checked (`decide +kernel`) conformance theorems over `decode`, `encode`, `execInst`, `brk`, `clock_gettime`, and ASL boundary cases (`IsaConformance.lean`). |
| [`Generators/`](Generators/) & [`Fixtures/`](Fixtures/) | Multi-instruction ISA test generators (`ExternalSuites.lean`, `HandWrittenVectors.lean`, `RandomFuzz.lean`, `CompiledBinary.lean`, `TrustedSuite.lean`), host Linux VFS/`mmap` trace generators (`SyscallTraces.lean`), and compiled `rustc -O` Rust crates (`Fixtures/compiled-binary/`, `Fixtures/adequacy-tour/`). |
| [`ElfLoaderDiff/`](ElfLoaderDiff/README.md) | Multi-compiler static `ET_EXEC` corpus, linker-produced reject binaries, and `qemu-aarch64` GDB entry snapshots testing `ElfImage.parse` and `ElfImage.loadState`. |
| [`SyscallDiff/`](SyscallDiff/README.md) & [`SyscallDiff.lean`](SyscallDiff.lean) | Freestanding `#![no_std]` `syscall_probe.elf` binary and runner testing 29 of the 31 modeled Linux `7.3` syscalls against `qemu-aarch64` (`readv` / `writev` are covered by kernel-checked equivalence to `read` / `write` in [`Regression/ReadWritev.lean`](Regression/ReadWritev.lean), not by `qemu` differential probes) (plus an unexercised `record-json` mode for native AArch64 Linux). |
| [`ProcessE2E/`](ProcessE2E/README.md) | Twenty-six static `aarch64-unknown-linux-musl` Rust binaries and 99 `qemu-aarch64 -strace` reference vectors testing end-to-end process execution. |
| [`Regression/`](Regression/) & [`AsciiTests.lean`](AsciiTests.lean) | `unit_tests` driver (`UnitTests.lean`), in-Lean loader/syscall/process regressions (`ElfLoaderDiff.lean`, `SyscallDiff.lean`, `ProcessE2E.lean`, `Process*.lean`, `SyscallFamilies.lean`, `StdSyscalls.lean`, `MadvFree.lean`, `ObjectLoad.lean`, `IncludeBytes.lean`), ASCII/decimal surface-macro tests (`AsciiTests.lean`), and proof-library regressions. |
| [`Tours/`](Tours/) | Kernel-checked reader's tour of whole-process ELF semantics (`ProcessSemanticsTour.lean`, `EchoStdinFixture.lean`), alongside higher-level specification tours outside this document's scope. |

---

## 1. Arm64 ISA semantics

The majority of the execution model by lines of code is the user-space AArch64 ISA semantics in [`Arm64/Trusted/ISA/`](../Trusted/ISA/README.md). Execution is defined as a small-step transition relation `Step prog s s'` (and its multi-step closure `Steps`) over `State`: general-purpose registers `X0`–`X30`, 128-bit SIMD/FP registers `V0`–`V31`, `SP`, `PC`, condition flags `PSTATE` (`NZCV`), `TPIDR_EL0`, `FPSR`, virtual memory `mem`, file-system state `fs`, and execution `status`. At each `.Running` step, `Step.exec` fetches the 4-byte little-endian word at `s.pc` from read-execute (`Perm.rx`) memory, decodes it with `Arm64.decode`, and applies `execInst` (or halts in `.Halted` via `Step.halt_unmapped` if `s.pc` is unmapped, non-executable, misaligned, or undecodable; writes to `Perm.rx` memory fault, forbidding self-modifying code).

Our goal is soundness rather than completeness, and we model a single ARM core without concurrency. Outside of floating point, `Step` is kept a pure function by handling architectural non-determinism in three ways:
1. **Reject (`UNDEFINED` and `CONSTRAINED UNPREDICTABLE` encodings):** Where the ARM manual leaves behavior `CONSTRAINED UNPREDICTABLE`—for instance, `LDP Xt, Xt2, [Xn]!` with overlapping destination registers—`Arm64.decode` returns `none`, causing `Step` to transition to `.Halted`.
2. **Quantify (hardware and OS non-determinism via `State.exclFails` and `State.oracle`):** Run-to-run choices live in initial oracle streams on `State` (`exclFails` for spurious store-exclusive `STXR*`/`STLXR*` failures, and `oracle` for nondeterministic syscall results), so universally quantifying over the initial state covers every valid schedule while keeping `Step` deterministic.
3. **Pin (`IMPLEMENTATION DEFINED` user-space parameters and address-space profile):** Processor configuration pins standard Linux user-space defaults `FPCR = 0` (IEEE round-to-nearest-even without flush-to-zero; non-zero writes fault), `DCZID_EL0 = 4#64` (64-byte `DC ZVA` zeroing granule), and 4 KiB pages, and makes the modeling choice of an untagged 48-bit canonical user address space without pointer authentication or Top-Byte Ignore (`TBI0`; Linux user space enables `TBI0` by default).

### Formal decoder/encoder round-trip proof (`Proofs/EncoderDecoder.lean`)

Modeling execution on raw bytes means we must trust [`Arm64.decode`](../Trusted/ISA/Decode.lean). To make the decoder easier to audit and rule out silent bit-dropping bugs, [`Harness/Encode.lean`](Harness/Encode.lean) implements an untrusted AST-to-binary encoder `Arm64.encode : Instr → Option (BitVec 32)`, and [`Proofs/EncoderDecoder.lean`](Proofs/EncoderDecoder.lean) proves `encode_of_decode`: whenever `decode bs = some p`, `encode p = some bs`. Encoding from high-level syntax is much easier to read than binary bit-slicing, and the round-trip theorem guarantees that `decode` is injective across every decode branch and rejects non-canonical reserved bits. At run time, `unit_tests` also runs `reportRustExportCodec` ([`Generators/CompiledBinary.lean`](Generators/CompiledBinary.lean)), checking that all 558 instruction words compiled by `rustc -O` in `CompiledBinaryFixture.bin` round-trip identically through `decode` and `encode`.

Build and kernel-check the proof with `timeout 600 lake -d Arm64/Testing build --no-ansi Arm64.Testing.Proofs.EncoderDecoder`. A pass means Lean's kernel accepted `encode_of_decode` across all instruction classes with zero `sorry` and standard axioms only.

### Three-way lockstep differential testing against Sail and Unicorn (`diff_eval` & `run-trusted-tests`)

The main empirical check on instruction execution is three-way differential testing against the [Sail Armv9.4-A](https://github.com/rems-project/sail-arm) semantics and [Unicorn](https://www.unicorn-engine.org/) (`UC_ARCH_ARM64`). Sail is produced by the University of Cambridge REMS group and Arm by translating Arm's official machine-readable Architecture Specification Language (ASL) specification into Sail and compiling it to C (`armv9.c`). Unicorn reuses QEMU's AArch64 TCG CPU emulator as a library for stepping short instruction sequences. To compare them uniformly, our Lean semantics, Sail, and Unicorn all implement a single Rust trait, `Arm64Oracle` ([`tools/isa-oracle/src/lib.rs`](../../tools/isa-oracle/src/lib.rs)); `LeanOracle` spawns `lake -d Arm64/Testing exe diff_eval --serve` ([`Harness/Serve.lean`](Harness/Serve.lean)), which receives `TestInput` states over a persistent binary pipe and steps `Arm64.decode` and `execInst` directly, while LLVM (`llvm-mc`) assembles textual test snippets into machine words.

[`tools/run-trusted-tests`](../../tools/run-trusted-tests/src/lib.rs) runs two complementary workloads across all three evaluators:
- **Multi-instruction lockstep suite (224 `IsaTestCase`s, 10,526 instruction words in [`Generators/TrustedSuite.lean`](Generators/TrustedSuite.lean)):** combines ARM VIXL simulator vectors and Unicorn's `test_arm64.c` (`ExternalSuites.lean`, 45 cases), hand-written C loops and SIMD/SHA/AES/PMULL/LSE-atomic/RCpc/CRC32/ASL boundary vectors (`HandWrittenVectors.lean`, 65 cases), 100 seeded 8-instruction random blocks (`RandomFuzz.lean`), and 14 compiled `rustc -O` functions from `Fixtures/compiled-binary/` (`CompiledBinary.lean`), stepping Lean, Sail, and Unicorn instruction by instruction.
- **Single-instruction fuzzing (`tools/run-trusted-tests/src/fuzz.rs`, 25,000 cases per CI pass):** generates 500 edge-biased inputs for each of 49 `Arm64.decode` instruction families (24,500 cases) plus 500 Linaro RISU (`aarch64.risu`) bit-template cases via `Arm64Oracle::run_batch`. Sail serves as the architectural authority on the few SIMD/FP corner cases where QEMU 5.0's TCG translator has known quirks (tallied in `unicorn_fp_quirks_adjudicated_by_sail`).

Run the suite with:
```bash
timeout 600 lake -d Arm64/Testing build --no-ansi diff_eval
cargo run --release --locked --manifest-path tools/Cargo.toml --bin run-trusted-tests
# Targeted modes: --suite-only, --insn-fuzz-only, or --fuzz-secs 600
```
A pass (exit `0`, zero `lean_vs_sail_mismatches`) means every stepped instruction produced identical `X0`–`X30`, `V0`–`V31` (128-bit), `SP`, `PC`, `NZCV`, architectural `FPSR` bits (`0x0800009f`), and watched memory across Lean, Sail, and Unicorn (skipping Sail only on two documented cases: user-space `DC ZVA` where Sail sets `DCZID_EL0.DZP = 1`, and a Sail C assertion on byte-lane `ADDV`).

### Standalone IEEE-754 floating-point validation (`Harness/FpEval.lean`)

Scalar and vector IEEE-754 operations in [`Arm64/Trusted/ISA/Float.lean`](../Trusted/ISA/Float.lean) are also tested directly via `diff_eval --batch-fp` ([`Harness/FpEval.lean`](Harness/FpEval.lean)) against **Berkeley SoftFloat 3e** compiled with `SPECIALIZE_TYPE=ARM-VFPv2` ([`tools/run-trusted-tests/src/fp.rs`](../../tools/run-trusted-tests/src/fp.rs)). Each CI run evaluates **479,435** binary vectors across `f32`/`f64` and all five rounding modes (`RNE`, `RTP`, `RTN`, `RTZ`, `RNA`): **144,635** IBM FPgen (`*.fptest`) vectors, **324,300** Berkeley TestFloat 3e (`testfloat_gen -level 1`) vectors, and **10,500** stratified NaN, subnormal, and tie-to-even edge cases.

Run this pass on its own with `cargo run --release --locked --manifest-path tools/Cargo.toml --bin run-trusted-tests -- --fp-only` (it also runs as part of `run-trusted-tests`). A pass means bit-for-bit agreement between `Float.lean` and SoftFloat `ARM-VFPv2` on every result word (or 4-bit `NZCV` on `FCMP`/`FCMPE`) and all five IEEE-754 exception flags (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`), with legacy IEEE 754-1985 trapped overflow/underflow lines in FPgen counted and skipped and symbolic `Q` quiet-NaN tokens verified to produce quiet NaNs on both sides.

### ASL manual inspection, conformance theorems, and unit tests

Alongside differential fuzzing, each instruction's Lean decode and execute clauses are audited against ARM's official XML/ASL specification (`ISA_A64_xml_A_profile-2026-06`), extracted per instruction by `tools/dev/arm-asl-extract`. Boundary cases found during ASL review and proof campaigns are locked in permanently by 7 kernel-checked (`decide +kernel`) conformance theorems in [`Conformance/IsaConformance.lean`](Conformance/IsaConformance.lean) (`PMULL`/`PMULL2`, AdvSIMD shifts/immediates, SHA/crypto extensions, fail-closed `brk`, `clock_gettime` oracle consumption, and ASL edge cases such as `BLR X30` and `FMADD` NaN propagation), alongside concrete runtime checks in [`Regression/UnitTests.lean`](Regression/UnitTests.lean) (`./Arm64/Testing/.lake/build/bin/unit_tests --base`), compile-time byte-splicing tests in [`Regression/IncludeBytes.lean`](Regression/IncludeBytes.lean), and ASCII/decimal macro tests in [`AsciiTests.lean`](AsciiTests.lean). Building `Arm64Testing` and running `unit_tests --base` verifies that every `#guard_msgs` negative check, `decide +kernel` theorem, and runtime assertion passes.

---

## 2. Compiling, linking, loading, and external calls

We verify optimized compiled code (`--release` / `-O2`) built with deterministic codegen flags (`-C target-cpu=generic`, `-C codegen-units=1`, `panic=abort`, and LLVM auto-vectorization disabled so loops emit scalar instructions). When verifying a **relocatable library** before its final host executable is chosen, compilation produces ELF `.o` object files whose symbolic references must be linked and loaded into memory (`Perm.rx` for `.text`, `Perm.ro` for `.rodata`/GOT, `Perm.rw` for `.data`/`.bss`, and all other addresses unmapped so out-of-bounds accesses fault). [`Arm64/Trusted/Object/`](../Trusted/Object/README.md) supports two library models:
- **Stock-linker placed libraries (`Obj.PlacedLib` & `MultiPlacedLib` in [`Placed.lean`](../Trusted/Object/Placed.lean)):** the trusted library model, quantifying over every valid `Placeable` section placement and `ld.lld` `ADRP`+`ADD` relaxation encoding so a kernel-checked `LinkedIn` witness can tie the library directly to a stock-`ld.lld` executable.
- **Deprecated legacy static section linking (`Obj.LinkedImage` & `LinkedImage.load` in [`Arm64/Legacy/Object/LinkedImage.lean`](../Legacy/Object/LinkedImage.lean)):** `[OUTSIDE TCB]` compatibility model where `untrusted_legacy_linker` merges `.o` sections at fixed relative offsets and `LinkedImage.load` shifts the image to any 4 KiB-aligned base address.

Where a library calls an unverified external dependency (or overrides an internal symbol via `Program.overrides`), `Step.extern` models the call as a single-step state transition that faults if it modifies frozen code/rodata or the symbol table. In CI (`trusted-checks-core`), `spec-oracle validate-hooks` executes real compiled binaries in Unicorn to check assumed external hook behavior against actual execution, while [`Regression/ProcessOverrides.lean`](Regression/ProcessOverrides.lean) and [`Regression/ProcessOverrideWellBehaved.lean`](Regression/ProcessOverrideWellBehaved.lean) kernel-check fail-closed `.symtab` override resolution (rejecting missing, duplicate, zero-size, or non-function symbols).

A Rust differential suite drives `placed_eval` in `Harness/` to test object placement and relocation patching against stock `ld.lld` (complementing the in-Lean loader unit tests in [`Regression/ObjectLoad.lean`](Regression/ObjectLoad.lean)):
- **`Placed.lean` vs. stock `ld.lld` ([`Harness/PlacedEval.lean`](Harness/PlacedEval.lean), [`placed_lld_diff.rs`](../../tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs)):** synthesizes near (`< 1 MiB`, relaxed and unrelaxed), medium (`2–120 MiB`), high canonical ASLR, and page-boundary (`0xff8`/`0xffc`) placements across multi-TU C and Rust corpora (vtables, jump tables, `thread_local!` `.tdata`/`.tbss`) and repository `translation.toml` targets, pins those addresses in `ld.lld -T layout.lds`, and checks 100% byte-for-byte equality between stock `ld.lld` and `lake -d Arm64/Testing exe placed_eval` as well as mutual rejection of out-of-range or misaligned layouts.

Run the suite with:
```bash
timeout 600 lake -d Arm64/Testing build --no-ansi placed_eval Arm64.Testing.Regression.ObjectLoad
REQUIRE_LINK_DIFF=1 cargo test --locked --manifest-path tools/Cargo.toml -p rust-obj2lean test_infra::placed_lld_diff -- --nocapture
```
A pass (with `REQUIRE_LINK_DIFF=1` forbidding tool-missing skips) means every placed byte and relocation matches `ld.lld` across layouts and every invalid layout is rejected.

---

## 3. Loading whole ELF binaries (`ElfLoaderDiff/`)

When the verification target is a complete program, we do not need a library link model in the TCB at all. [`file_bytes%`](../Trusted/Surface/FileBytes.lean) embeds a static executable's SHA-256-pinned bytes at compile time, and the ~400-line pure-Lean loader in [`Arm64/Trusted/Process/Loader.lean`](../Trusted/Process/Loader.lean) (`ElfImage.parse` and `ElfImage.loadState`) mimics what Linux's `binfmt_elf` does for a static, non-PIE AArch64 executable (`ET_EXEC`). Each `PT_LOAD` segment becomes a 4 KiB page-aligned region with its `R`/`W`/`X` permissions: full-file segments (`p_filesz == p_memsz`) map surrounding file bytes on their first and last pages, while `.bss`-bearing segments (`p_filesz < p_memsz`) zero the fractional-page tail past `p_filesz` (`padzero`). Anything outside this static profile—PIE (`ET_DYN`), dynamic linking (`PT_INTERP`/`PT_DYNAMIC`), relocatable `.o` files, W+X segments, executable stacks, or non-writable `.bss`—is rejected fail-closed. `loadState` then zeroes registers, sets `pc := e_entry` and `brkStart`, opens `stdin`/`stdout`/`stderr` (`fd 0/1/2`) and initial files in `State.fs`, and builds the user stack (`argc`, `argv`, `envp`, `execfn`, and `auxv`).

Bugs in the loader—such as retaining file bytes past `p_filesz` that Linux zeroes—could make a proof talk about a process state that never runs. [`ElfLoaderDiff/`](ElfLoaderDiff/README.md) ([`Harness/ElfLoaderDiff.lean`](Harness/ElfLoaderDiff.lean) and [`Regression/ElfLoaderDiff.lean`](Regression/ElfLoaderDiff.lean)) therefore tests `ElfImage.parse` and `ElfImage.loadState` byte-for-byte at the first user instruction (`pc == e_entry`) against the pinned `qemu-aarch64` user-mode loader (`scripts/fetch-qemu-aarch64`, with `ADDR_NO_RANDOMIZE` and `-seed 0`). [`tools/proc-snapshot`](../../tools/proc-snapshot/README.md) (`--entry-only`) stops `qemu-aarch64` at `e_entry` over QEMU's GDB stub, probes unmapped gap pages, and dumps every mapped region, register, and stack word; `verifyPositiveCase` then checks:
- all 4,096 bytes and `rwx` permissions of every `PT_LOAD` page (including `layout_midpage_bss.elf`, which places a `0xdeadbeef` marker right after `p_offset + p_filesz` to test full-page file mapping vs. `.bss` `padzero`),
- all entry registers (`pc`, 16-byte aligned `sp`, zeroed `x0`–`x30`, `tpidr_el0`),
- every word of `[stackBase, stackTop)`, including `argc`, `argv`, `envp`, every `auxv` tag/value pair, and `[infoBase, stackTop)` bytes,
- `brkStart` and unmapped null, inter-segment, and stack guard pages, and
- fail-closed rejection on 6 real linker-produced invalid binaries (`reject_pie.elf`, `reject_dynamic.elf`, `reject_relocatable.elf`, `reject_wx_segment.elf`, `reject_exec_stack.elf`, `reject_ro_bss.elf`), also kernel-checked by `decide +kernel` in `elf_loader_diff_corpus_conformance`.

Small assembly, `zig cc` (`-O0`/`-O2` musl), and `no_std` Rust binaries (`11` positive snapshot configurations and `6` reject binaries) are committed in `ElfLoaderDiff/bin/` and `expected_snapshots.json` for fast offline testing, while `scripts/elf-loader-diff run` additionally builds and snapshots full-`std` Rust, static Go (`CGO_ENABLED=0`), and optional `gcc`+`glibc` binaries live under QEMU. The two remaining differences against `qemu-aarch64` (QEMU TCG's `CPSR.Z = 1` reset flag vs. Linux/Lean `PState.zero`, and QEMU's synthetic `[vdso]` page / `AT_SYSINFO_EHDR`) are asserted explicitly rather than masked, and known stack-padding differences vs. Linux's `fs/binfmt_elf.c` are documented in [`ElfLoaderDiff/README.md`](ElfLoaderDiff/README.md).

Run the loader tests with:
```bash
./Arm64/Testing/.lake/build/bin/unit_tests --elf-loader-diff                      # offline check vs. committed snapshots
./scripts/elf-loader-diff run                                                     # live multi-compiler build + QEMU GDB diff
./scripts/elf-loader-diff build --check && ./scripts/elf-loader-diff regen --check # zero-drift check on committed fixtures
```
A pass means every `PT_LOAD` byte, permission, register, stack word, `auxv` entry, `brk`, and unmapped boundary page matches `qemu-aarch64` (modulo the two explicitly checked QEMU quirks), all 6 unsupported ELFs fail closed, and committed snapshots regenerate without drift.

---

## 4. Linux system calls (`SyscallDiff/` & `SyscallTraces.lean`)

When user-space code issues `SVC #0`, [`Arm64/Trusted/Syscalls.lean`](../Trusted/Syscalls.lean) (`execSyscall` = `Syscall.standard`, organized along the `linux-7.3` source tree in [`Arm64/Trusted/Syscalls/`](../Trusted/Syscalls/README.md)) dispatches on `X8` across **31** modeled Linux AArch64 system calls: stdio and VFS (`read`, `write`, `readv`, `writev`, `pread64`, `lseek`, `openat`, `close`, `fstat`, `fcntl`, `ioctl`, `ppoll`), memory management (`brk`, `mmap`, `munmap`, `mremap`, `mprotect`, `madvise`, charging writable commits against `s.physMemAvail`), exit and signals (`exit`, `exit_group`, `tkill`, `tgkill`, `sigaltstack`, `rt_sigaction`, `rt_sigprocmask`), clocks and entropy (`clock_gettime`, `getrandom`), and process/thread queries (`set_tid_address`, `sched_getaffinity`, `getpid`, `gettid`). Any unmodeled syscall or unsupported flag raises `.Exception`, and nondeterministic kernel outputs (`mmap`, `mremapFail`, `getrandom`, `clockGettime`) come from `State.oracle`.

### Per-syscall `linux-7.3` & `qemu-aarch64` differential probe suite (`SyscallDiff/`)

[`SyscallDiff/`](SyscallDiff/README.md) ([`Regression/SyscallDiff.lean`](Regression/SyscallDiff.lean), re-exported by [`SyscallDiff.lean`](SyscallDiff.lean)) compiles a freestanding `#![no_std]` `#![no_main]` static AArch64 binary ([`SyscallDiff/bin/syscall_probe.elf`](SyscallDiff/src/bin/syscall_probe.rs)) issuing raw `SVC #0` probes across all 29 syscalls—normal paths, `-EINVAL` / `-EFAULT` / `-EBADF` / `-ENOENT` / `-ENOTDIR` / `-ESRCH` error returns, file writes, exit statuses, and self-sent `SIGABRT`—and compares `qemu-aarch64` against Lean's `execSyscall` across five modes (`all`, `exit_one`, `tkill_abrt`, `tgkill_abrt`, and `record-json`).

Because user-mode `qemu-aarch64` deviates from a real Linux `7.3` kernel in 13 edge cases (for instance, QEMU returns `-ENOMEM` rather than `-EINVAL` on `mremap` with `new_size == 0`, returns `0` rather than `-ENOMEM` on `madvise` over unmapped pages, uses `MINSIGSTKSZ = 2048` rather than AArch64's `5120` in `sigaltstack`, and checks the full `count` rather than `chunk.length` in `read`), `Regression/SyscallDiff.lean` records all 13 deviations in `KNOWN_QEMU_USER_DEVIATIONS` (`QEMU-DEV-1`–`QEMU-DEV-13`) and proves the kernel-checked (`decide`) theorem `all_29_syscalls_boundary_conformance` directly against `Arm64.execSyscall` on the `linux-7.3` cases of `QEMU-DEV-1`–`QEMU-DEV-9` (`QEMU-DEV-10`–`QEMU-DEV-13` are pinned by focused case binaries). `syscall_probe.elf` also implements a `record-json` mode to capture ground-truth JSON vectors for all 132 probe checks on a native AArch64 Linux `7.3` host, though this mode is not run anywhere yet.

Run the suite with `QEMU_AARCH64="$(./scripts/fetch-qemu-aarch64)" ./Arm64/Testing/.lake/build/bin/unit_tests --syscall-diff`. A pass means identical exit codes, signals, `stdout`, `stderr`, and post-run `probe_file.bin` bytes between `qemu-aarch64` and Lean across all five modes, plus kernel verification of `all_29_syscalls_boundary_conformance`.

### Host Linux kernel VFS and `mmap` guard-page traces (`Generators/SyscallTraces.lean`)

To test directly against a real Linux kernel rather than QEMU user mode, [`Generators/SyscallTraces.lean`](Generators/SyscallTraces.lean) (`diff_eval --fs-diff-trace` and `--mmap-diff-trace`) runs a 27-value CWD-relative VFS trace (`ioctl`, `clock_gettime`, `openat` with `O_TRUNC`, 128-byte `fstat`, `pread64`, `read`, `lseek`, `write`, `fcntl`, `close`) and an 11-step `mmap(MAP_FIXED, PROT_NONE)` / `mprotect` / `munmap` / `write` guard-page sequence on `Arm64.execSyscall`, while [`fs_linux_diff_tests.rs`](../../tools/run-trusted-tests/src/fs_linux_diff_tests.rs) executes the identical calls against the **host `x86_64` Linux kernel**. In-Lean kernel-checked regressions in [`Regression/SyscallFamilies.lean`](Regression/SyscallFamilies.lean), [`Regression/StdSyscalls.lean`](Regression/StdSyscalls.lean), and [`Regression/MadvFree.lean`](Regression/MadvFree.lean) additionally verify per-family dispatch equivalence, `ppoll`/`mmap`/`mremap`/`rt_sigaction` corner cases, and `MADV_FREE` lazy reclaim.

Run with `timeout 600 lake -d Arm64/Testing build --no-ansi diff_eval Arm64Testing && cargo test --locked --manifest-path tools/Cargo.toml -p run-trusted-tests`. A pass means bit-for-bit equality of every return code, file offset, `struct stat` field, and guard-page `EFAULT` between `execSyscall` and the host Linux kernel.

---

## 5. Whole-process ELF semantics (`ProcessE2E/` & `elf_run`)

Putting the loader, ISA stepper, and syscall model together, [`Arm64/Trusted/Process/`](../Trusted/Process/README.md) models complete static Linux AArch64 executables (`ET_EXEC`) from `_start` (`crt1.o`) through `SYS_exit` / `SYS_exit_group` (and fatal `SIGABRT`) under the hook-free program `Program.pureMem`: every instruction of libc startup, memory allocation, and application code steps on `Arm64.Step` to produce an observable `ProcessOutcome` (`exitCode`, `signal`, `stdout`, `stderr`, and final `State.fs`). [`Tours/ProcessSemanticsTour.lean`](Tours/ProcessSemanticsTour.lean) (with `Tours/EchoStdinFixture.lean` over `Regression/fixtures/echo_stdin.elf`) provides a self-contained, kernel-checked walkthrough of `loadElf`, `ProcessInputs`, end-to-end execution, an `STXR` retry-loop disproof under `exclFails := [true]`, and modeling boundaries, complemented by [`Regression/Process.lean`](Regression/Process.lean) (including `abort_status.elf` vs. `qemu-aarch64`) and [`Regression/ProcessAssumptions.lean`](Regression/ProcessAssumptions.lean) (`ProcessInputs.Valid`).

### End-to-end static Rust corpus against `qemu-aarch64 -strace` (`ProcessE2E/`)

[`ProcessE2E/`](ProcessE2E/README.md) ([`Regression/ProcessE2E.lean`](Regression/ProcessE2E.lean)) compiles **26** reproducibly linked `aarch64-unknown-linux-musl` `ET_EXEC` Rust binaries (`nostd_minimal`, `exit_codes`, `echo_cat`, `word_count`, `argv_envp`, `arith_sort`, `btreemap_vec`, `stderr_stdio`, `getrandom_use`, multi-step stateful `session_store`, `std_startup_probe`, zero-shim `unmodified_std_probe`, and 14 CLI-style workloads: `base64_codec`, `hexdump`, `sha256sum`, `rle_codec`, `sort_uniq`, `grep_lite`, `rpn_calc`, `file_copy`, `json_lint`, `bignum`, `matrix_mul`, `env_lookup`, `rot_cipher`, and `collatz_stats`) exercising custom and stock musl `mallocng` allocation, `BTreeMap`/`Vec` mutations, atomic directory stores, stock `std::fs` copies, `std::rt::lang_start` startup, panics, and `abort()`. [`scripts/process-e2e`](../../scripts/process-e2e) runs **99** cases under `qemu-aarch64 -strace` to capture reference outcomes and syscall censuses in `ProcessE2E/expected_vectors.json`, and `Regression/ProcessE2E.lean` replays all 99 cases through the Lean process model:
- **90 `match` cases:** exact agreement between Lean and `qemu-aarch64` on `exitCode`, fatal `signal`, `stdout` bytes, `stderr` bytes, and post-run watched files in `State.fs.files` (with `use_ref_runner` cases also cross-checked directly on the unaccelerated reference `Arm64.Process.runElf`).
- **1 `entropy_nondeterministic` case (`getrandom_use/raw_hex`):** QEMU reads live OS entropy while Lean replays both the default zero `Oracle` and a seeded `Oracle.getrandom`, verifying hex output formatting and `exit 0`.
- **5 `unmodeled_trap` cases:** `udf #1` (`unmodified_std_probe/udf1_sigill`) raises `SIGILL` under QEMU and fails closed with `.Exception "udf"`, and the 4 musl `panic!`/`abort()` probes (`stderr_stdio/panic_formatted`, `stderr_stdio/abort_after_stdout`, `unmodified_std_probe/panic_gettid`, `unmodified_std_probe/abort_sigabrt`) fail closed with `.Exception "unmodeled non-zero signal mask in rt_sigprocmask"` on musl `raise(SIGABRT)`'s non-zero `SIG_BLOCK`.
- **3 pinned `divergence` cases (`unmodified_std_probe`):** track known boundary differences explicitly so none can drift silently (`udf #0` and `brk #0` halting in `.Halted` vs. QEMU `SIGILL`/`SIGTRAP`, and Rust's `panic=immediate-abort` `brk #1` mapping to `.Exited 101` vs. QEMU `SIGTRAP`).

Run with:
```bash
./Arm64/Testing/.lake/build/bin/unit_tests --process-e2e                            # replay all 49 cases vs. committed QEMU vectors
QEMU_AARCH64="$(./scripts/fetch-qemu-aarch64)" ./scripts/process-e2e build --check  # verify bit-identical Rust ELF rebuilds
QEMU_AARCH64="$(./scripts/fetch-qemu-aarch64)" ./scripts/process-e2e regen --check  # verify zero drift vs. live qemu-aarch64 -strace
```
A pass means exact stdio, file, signal, and exit-code agreement on all 44 `match` cases, exact expected trap/divergence behavior on the 5 boundary cases, and zero build or QEMU drift.

### Validating the fast paged ELF runner (`elf_run`) against the trusted stepper

Stepping multi-million-instruction binaries (`session_store.elf`, `syscall_probe.elf`) directly on Lean's mathematical `State` representation would be too slow for routine test runs, so [`Harness/ElfRun.lean`](Harness/ElfRun.lean) (`lake -d Arm64/Testing exe elf_run`, CLI wrapper [`Harness/ElfRunCli.lean`](Harness/ElfRunCli.lean)) and [`Harness/FastSemantics.lean`](Harness/FastSemantics.lean) accelerate execution using unboxed 64-bit registers and a lazy 4 KiB paged byte store. To ensure a bug in this accelerator can never mask a bug in the trusted semantics, `FastSemantics.lean` proves `@[simp]` bridge lemmas back to `Arm64.Trusted`, `instWriteRanges` and `syscallWriteRanges` match exhaustively without wildcards (`known_syscalls_exhaustive` in `Regression/Process.lean`), `elf_run selftest 5000 1` compares 5,000 random instruction/store/syscall steps against trusted `execInst`, and `elf_run refcheck [--trusted]` / `elf_run run --trusted` cross-check real static ELFs for tens of thousands of steps against the unaccelerated trusted stepper (`Process.runStepsPure` / `runLoopTrusted`).

Run `./scripts/ci/trust-checks.sh --elf-run`; a pass means zero state or outcome discrepancies between the fast paged store and the trusted stepper.

---

## 6. Running the tests

CI (`.github/workflows/ci.yml`) runs every check above on `x86_64` Linux on each pull request across `build-testing`, `unit-tests`, `differential-harness`, `trusted-checks-core`, and `snapshot-fixtures`. To run them locally from the repository root:

```bash
# 1. Fast trust-boundary & Markdown link guards (< 10 s):
./scripts/dev/check-trust-guards.sh

# 2. Build and kernel-check all Lean test modules, round-trip proofs, tours, and CLI binaries:
lake run sanitize
timeout 600 lake -d Arm64/Testing build --no-ansi

# 3. Run the Lean unit & QEMU differential driver (codec round-trip, base ISA/FP/AES tests,
#    ElfLoaderDiff, SyscallDiff, and ProcessE2E) plus elf_run self-checks:
export QEMU_AARCH64="$(./scripts/fetch-qemu-aarch64)"
export PATH="$(dirname "$QEMU_AARCH64"):$PATH"
./Arm64/Testing/.lake/build/bin/unit_tests          # or: lake -d Arm64/Testing test
./scripts/ci/trust-checks.sh --elf-run

# 4. Run Unicorn + Sail Armv9.4-A + SoftFloat 3e + host-Linux differential suites
#    (requires CMake, pkg-config, LLVM tools, zig, and libgmp-dev):
cargo test --locked --manifest-path tools/Cargo.toml -p run-trusted-tests
cargo run --release --locked --manifest-path tools/Cargo.toml --bin run-trusted-tests

# 5. Run ld.lld placed-library differential suites and live multi-compiler QEMU checks:
REQUIRE_LINK_DIFF=1 cargo test --locked --manifest-path tools/Cargo.toml -p rust-obj2lean test_infra::placed_lld_diff -- --nocapture
./scripts/elf-loader-diff run
./scripts/process-e2e build --check && ./scripts/process-e2e regen --check
```

Or run `./scripts/ci/trust-checks.sh --full-ci-testing` and `./scripts/ci/trust-checks.sh --full-ci-core` for the bundled CI sequences.

---

## 7. Generated test ELFs

Every test ELF under `Arm64/Testing/` and `VerifiedLibraries/*/Testing/` is generated from committed
sources. The binaries are checked in so tests run without a cross toolchain, and CI
(`snapshot-fixtures`) rebuilds them all and requires byte-identical output:

```bash
scripts/build-test-elfs.sh                        # rebuild every family into its committed path
scripts/build-test-elfs.sh --check --require-all  # rebuild into temp dirs; fail on any byte drift
scripts/build-test-elfs.sh process-e2e            # one family (see --help for the list)
```

| Family | ELFs | Sources | Builder |
| --- | --- | --- | --- |
| `regression` | `Regression/fixtures/*.elf` | `*.c`, `overrides_fixture{,2}.s` + `.ld` | `scripts/dev/elf-process-fixture --elf-process` (zig) |
| `rust-std` | `VerifiedLibraries/RustStd/Testing/{empty,hello,cpstd}`, `VerifiedLibraries/Mallocng/Testing/allocsurface` | crate dirs next to each ELF | `scripts/dev/elf-process-fixture --rust-std` (Rust `-Zbuild-std`) |
| `elf-loader` | `ElfLoaderDiff/bin/*.elf` | `ElfLoaderDiff/src/` | `scripts/elf-loader-diff build` (Rust, zig) |
| `process-e2e` | `ProcessE2E/bin/*.elf` | `ProcessE2E/src/` | `scripts/process-e2e build` (Rust) |
| `syscall-cases` | `SyscallDiff/bin/<case>.elf` | `SyscallDiff/src/cases/` | `scripts/syscall-diff-cases build` (zig) |
| `syscall-probe` | `SyscallDiff/bin/syscall_probe.elf` | `SyscallDiff/src/bin/syscall_probe.rs` | `scripts/syscall-diff-cases probe` (Rust) |

When a generated ELF is missing (for example in a source-only export, or after skipping a family
because its toolchain is absent), the tests that need it report `SKIPPED` and name
`scripts/build-test-elfs.sh` instead of failing:

- Lean modules that embed an ELF at elaboration time (`file_bytes%`, `elf_image%`) wrap those
  declarations in `requires_test_files [...] ... end_requires_test_files` or select a test case with
  `if_test_files_exist% [...] then ... else ...` ([`ProofLib/TestFiles.lean`](../../ProofLib/TestFiles.lean));
  `file_bytes%` itself stays fail-closed.
- Runtime harnesses (`unit_tests --elf-loader-diff`, `--syscall-diff`, `--process-e2e`, and the
  `qemu-aarch64` abort check) report the affected cases as `SKIP` (`UnitTestCase.skipMissingFiles`
  in [`Harness/TestCase.lean`](Harness/TestCase.lean)) and count them in the summary.

### Testing dependencies

| Tool | Version | Needed for |
| --- | --- | --- |
| Rust (`rustup`) | **1.98.1** with targets `aarch64-unknown-linux-musl`, `aarch64-unknown-linux-gnu` and components `rust-src`, `llvm-tools` | `rust-std`, `elf-loader`, `process-e2e`, `syscall-probe`; the bundled `gcc-ld/ld.lld` links the hand-written corpus |
| zig | **0.16.0** | `regression`, `syscall-cases`, `elf-loader` (`c_zig_o{0,2}.elf`, and its bundled clang 21.1 assembles the hand-written `.s` corpus via `zig clang -cc1as`) |
| LLVM | `llvm-mc` (optional) | `elf-loader` assembly fallback when zig is absent; other LLVM releases may not reproduce the committed bytes |
| `qemu-aarch64` | pinned by [`scripts/fetch-qemu-aarch64`](../../scripts/fetch-qemu-aarch64) | the differential runs (`unit_tests`, `regen --check`), not the ELF builds |

```bash
rustup toolchain install 1.98.1 --profile minimal \
  --target aarch64-unknown-linux-musl,aarch64-unknown-linux-gnu --component llvm-tools,rust-src
export QEMU_AARCH64="$(./scripts/fetch-qemu-aarch64)"
```

zig is optional: without it, `scripts/build-test-elfs.sh` reports the zig families as `SKIPPED`
(and `--require-all` turns that into a failure), and the Lean tests that need those ELFs report
`SKIPPED`. CI installs zig through `scripts/ci/install-toolchain.sh --zig`.
