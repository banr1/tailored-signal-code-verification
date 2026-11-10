# `Arm64/Trusted/Process/`: Static ELF64 Process Loading & Whole-Binary Semantics

- **Layer / Role:** `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Umbrella Module:** [`Arm64/Trusted/Process.lean`](../Process.lean) (`import Arm64.Trusted.Process`). It does not re-export [`Placed.lean`](Placed.lean) or [`OverrideWellBehaved.lean`](OverrideWellBehaved.lean) (library-spec vocabulary; the latter imports `Spec.Hoare`) or [`Overrides.lean`](Overrides.lean) (symbol-keyed hook overrides, needed only by statements that use `ElfRunsToWithOverrides`); import them directly.

## Which file to read for X

| Need | File |
|---|---|
| Process inputs (`ProcessInputs`: user inputs `argv`, `envp`, `execfn`, `stdin` bytes, initial `files`/`dirs`, plus kernel/environment initialization record `init : ProcessInit` holding `AuxvConfig` incl. `AT_SECURE` and baseline `AT_HWCAP = 0x3`, `stackTop`, `8 MiB` `defaultStackSize`, and `oracle`), parsed `ElfImage`, and observable outcome (`ProcessOutcome`) | [`Types.lean`](Types.lean) |
| Shared Linux `execve(2)` input validity (`ProcessInit.Valid := AuxvValid ∧ StackValid`, `ProcessInputs.Valid := ArgsValid ∧ ProcessInit.Valid ∧ FsValid`), kernel-cited limit constants (`MAX_ARG_STRLEN`, `ARG_MAX`, `STK_LIM`, `STACK_SIZE_MAX`, `TASK_SIZE`, `STACK_BASE_MIN`, `MAX_LFS_FILESIZE`, `argLimit`, `argBytes`), boolean mirrors (`*.check`), and `Decidable` instances | [`Assumptions.lean`](Assumptions.lean) |
| Fail-closed static ELF64 `ET_EXEC` parser (`ElfImage.parse`), deterministic Linux AArch64 initial stack/auxv construction (`buildInitialStack`), initial `FsState` (`initFsState` with `fd 0/1/2`), and initial `State` construction (`ElfImage.loadState`, `loadElf`); SHA-256-pinned file-byte literal (`file_bytes%`) in [`../Surface/FileBytes.lean`](../Surface/FileBytes.lean) (re-exported by [`../Process.lean`](../Process.lean)) | [`Loader.lean`](Loader.lean) |
| Whole-binary run/exit relations (`ProcessTerminatedOutcome`, `ProcessExitsWith`, `ProcessPartialRunsTo`, `ProcessTerminates`, `ProcessRunsTo`), the top-level total-correctness contract `ElfRunsTo elfBytes pre post` (with the wrappers `ElfCorrect` and `ElfSafe`), and the partial-correctness contract `ElfPartialRunsTo elfBytes pre post` | [`Semantics.lean`](Semantics.lean) |
| A layout-generic placed library inside a parsed ELF: patched text mapped `r-x` at the placement base, data objects mapped with their patched bytes, unique `.symtab` entries for exports (`ElfMaps`, `PlacedLib.InElf`, `PlacedLib.LinkedAt`, `PlacedLib.LinkedIn`) | [`Placed.lean`](Placed.lean) |
| Whole-binary judgments that replace named functions by Lean models, selected by `.symtab` name and resolved fail-closed (`parseSymtabFull`, `resolveSym`, `resolveAddrs`, `Program.ofSites`, `ElfRunsToWithOverrides`) | [`Overrides.lean`](Overrides.lean) |
| Review predicate for an override model (`Override.WellBehaved pre fp f`: returns to `x30`, keeps `sp`/callee-saved registers/permissions and every non-register field, writes only writable bytes in the footprint `fp`); not used by the semantics, proved alongside `ElfRunsToWithOverrides` statements (theorem template `WellBehaved.hookOk` in [`ProofLib/Process/OverrideWellBehaved.lean`](../../../ProofLib/Process/OverrideWellBehaved.lean)) | [`OverrideWellBehaved.lean`](OverrideWellBehaved.lean) |

---

## Trusted ELF64 Loader Invariants & Segment Mapping (`Loader.lean`)

1. **Fail-Closed Static `ET_EXEC` Validation (`ElfImage.parse`):**
   - Requires ELF64 little-endian (`EI_CLASS = 2`, `EI_DATA = 1`), static executable (`e_type = ET_EXEC = 2`), AArch64 (`e_machine = EM_AARCH64 = 183`), `e_phentsize = 56`, and `e_phnum > 0`.
   - Rejects relocatable objects (`ET_REL = 1`), position-independent executables (`ET_DYN = 3` / PIE), dynamic linking (`PT_INTERP = 3`, `PT_DYNAMIC = 2`), W+X `PT_LOAD` segments (`PF_W && PF_X`), executable stacks (`PT_GNU_STACK` with `PF_X`), non-writable `PT_LOAD` segments with `.bss` (`p_filesz < p_memsz` without `PF_W`), misaligned `p_vaddr % 4096 != p_offset % 4096`, and overlapping or out-of-range page mappings.
   - Extracts non-local defined `STT_FUNC` symbols from `SHT_SYMTAB` + `SHT_STRTAB` when section headers are present (`symbols = []` when `e_shnum == 0` or no `SHT_SYMTAB` section is present).
   - Accepts metadata headers `PT_NULL`, `PT_PHDR`, `PT_NOTE`, `PT_TLS` (`.tdata`/`.tbss` template inside a `PT_LOAD` segment, consumed by user-space `crt` startup before setting `tpidr_el0`), `PT_GNU_EH_FRAME`, `PT_GNU_STACK` (non-executable), `PT_GNU_RELRO`, and `PT_GNU_PROPERTY`.
2. **Page-Aligned `PT_LOAD` Mapping (`parseProgramHeader` vs Linux `fs/binfmt_elf.c`, 4 KiB Pages):**
   - The loader assumes a 4 KiB AArch64 page size (`Obj.pageSize = 4096`, `AT_PAGESZ = 4096`, `AT_CLKTCK = 100`); binaries linked with 64 KiB `p_align` (`0x10000`, such as `zig cc`, `rustc`, and `go`) are supported as long as `p_vaddr % 4096 == p_offset % 4096`.
   - Each `PT_LOAD` segment with `p_memsz > 0` maps the page-aligned range `[pageStart, pageEnd)` where `pageStart = p_vaddr & ~0xfff`, `lead = p_vaddr - pageStart = p_offset & 0xfff`, and `pageEnd = alignUp4096(p_vaddr + p_memsz)`.
   - **Leading page head (`[pageStart, p_vaddr)`):** Mapped directly from the file bytes `[p_offset - lead, p_offset)` (matching Linux `elf_map` with `MAP_FIXED_NOREPLACE`).
   - **Non-`.bss` tail (`p_filesz == p_memsz`):** Linux `elf_map` `mmap`s the entire page-aligned file slice `[p_offset - lead, p_offset - lead + (pageEnd - pageStart))` without calling `padzero`. `parseProgramHeader` likewise maps the file bytes through `pageEnd` (padding with `0#8` only if the file itself ends before `fileStart + regionSize`).
   - **`.bss` tail (`p_filesz < p_memsz`, `PF_W` required):** For writable segments, Linux `load_elf_binary` / `elf_load` maps the file-backed prefix and calls `padzero(elf_bss)` / `vm_brk_flags` to zero-fill `[p_vaddr + p_filesz, pageEnd)` even if non-zero bytes follow `p_offset + p_filesz` in the file. (On Linux >= 6.7, `elf_load` ignores the `padzero` `clear_user` failure when `PROT_WRITE` is absent and leaves file bytes in the fractional page tail; `parseProgramHeader` conservatively rejects non-writable `PT_LOAD` segments with `p_filesz < p_memsz` fail-closed.) `parseProgramHeader` maps `[p_offset - lead, p_offset + p_filesz)` (when `p_filesz > 0`) and zero-fills `[p_vaddr + p_filesz, pageEnd)`.
3. **Initial Stack Info-Block Layout & `ProcessInputs.execfn` Default (`buildInitialStack`):**
   - `ProcessInputs.execfn : List (BitVec 8) := []` specifies the null-free pathname passed to `execve` for `AT_EXECFN (31)`. It defaults to `[]` (the empty string `""`) when omitted by whole-binary specs that do not inspect `AT_EXECFN` (whole-binary specs for programs that read `AT_EXECFN` should set `execfn` explicitly), in which case `buildInitialStack` pushes a single NUL terminator byte `0x00` right below the 8-byte top-of-stack zero sentinel (`stackTop - 9`) and points `AT_EXECFN` at it; differential tests against `qemu-aarch64` pass `execfn := bytesOfString snap.elf.path`.
   - From `infoBase` up to `stackTop`, `buildInitialStack` packs `randomBytes (16 B)` ++ `< 16` zero alignment bytes ++ `"aarch64\0" (8 B)` ++ `argv` strings ++ `envp` strings ++ `execfn ++ [0]` ++ 8-byte top-of-stack zero sentinel. This matches `qemu-aarch64` (`linux-user/elfload.c` `setup_arg_pages` + `create_elf_tables`) **byte-for-byte**, whereas the Linux kernel (`fs/binfmt_elf.c` `create_elf_tables`) calls `arch_align_stack(p)` before copying `"aarch64\0"` and `u_rand_bytes`, placing its `< 16` zero alignment bytes below `argv[0]` rather than between `AT_RANDOM + 16` and `AT_PLATFORM` (see Gap #3 below).

---

## Whole-Binary Judgments (`Semantics.lean`)

```lean
ElfRunsTo elfBytes (pre : ProcessInputs → Prop) (post : ProcessInputs → ProcessOutcome → Prop)
  (oom := fun _ _ => False) (prog := Program.pureMem)
```

- `elfBytes` must parse (`ElfImage.parse elfBytes = .ok img`) **outside** `∀ inputs`, so the binary
  is validated as a `WellFormed` static `ET_EXEC` image even when `pre` is unsatisfiable.
- For every `inputs` with `pre inputs`, loading succeeds and `ProcessRunsTo prog s0 (post inputs)
  (oom inputs)` holds. `ProcessRunsTo` is `ProcessTerminates ∧ ProcessPartialRunsTo`:
  - `ProcessTerminates`: some run terminates with an outcome satisfying `post` (or stops with
    `.OutOfMemory` satisfying `oom`);
  - `ProcessPartialRunsTo`: every reachable state is terminated with `post`, OOM with `oom`, or
    `.Running` with a next step.
- `ElfPartialRunsTo elfBytes pre post (oom := …) (prog := …)` has the same shape with
  `ProcessPartialRunsTo` in place of `ProcessRunsTo`. It is **partial correctness**: it makes no
  termination claim and holds vacuously for runs that never stop, but every run that does stop
  satisfies `post` (or `oom`) and no reachable state is stuck. `ElfRunsTo` implies it
  (`ElfRunsTo.toPartial` in [`ProofLib/Process/Core.lean`](../../../ProofLib/Process/Core.lean)).
- `ElfCorrect elfBytes pre post` adds `out.exitCode = 0#64 ∧ out.signal = none` to `post` and forbids
  OOM; `ElfSafe elfBytes pre` is `ElfCorrect` with a trivial `post`.
- Specs keep auxiliary parameters (`src dst`, `level oneshot`) as outer `∀` binders, put all input
  assumptions in `pre` (`fun inputs => inputs.Valid ∧ …`), and pair each statement with a
  non-vacuity `example : ∃ inputs …, inputs.Valid ∧ …`.
- Passing `(prog := Program.stdioCli)` (or another minimal bundle) keeps `Syscall.standard` out of
  the statement's constant closure (checked by `#trusted_closure!`).
- The per-image stepping stones `ElfImageRunsTo` / `ElfImageCorrect` / `ElfImageSafe` (one parsed
  image, one input) are untrusted and live in [`ProofLib/Process/Core.lean`](../../../ProofLib/Process/Core.lean).

---

## Differential Testing Against `qemu-aarch64` & Remaining Assumptions

[`Arm64/Testing/Harness/ElfLoaderDiff.lean`](../../Testing/Harness/ElfLoaderDiff.lean) and [`scripts/elf-loader-diff`](../../../scripts/elf-loader-diff) differentially test `ElfImage.parse` (via the untrusted `ByteArray` wrapper `ElfImage.parseByteArray`), `buildInitialStack`, and `ElfImage.loadState` at `pc == e_entry` against `qemu-aarch64` user mode (`tools/proc-snapshot --entry-only` with `ADDR_NO_RANDOMIZE` and `-seed 0`) across a multi-compiler corpus (`llvm-mc` + `ld.lld` assembly and custom multi-RW / mid-page `.bss` / `PT_TLS` + `PT_GNU_RELRO` layouts, `zig cc`/musl at `-O0` and `-O2`, optional `gcc`+`glibc`, Rust `no_std` and `std`, and Go `GOOS=linux GOARCH=arm64 CGO_ENABLED=0`).

### Explicit Normalizations and Modeling Assumptions at `pc == e_entry`

When `ProcessInputs` is configured with the QEMU run's `execfn` (`snap.elf.path`), `stackTop`, `stackSize`, `AT_RANDOM` 16-byte seed, `AT_HWCAP`/`AT_HWCAP2`, and `uid`/`euid`/`gid`/`egid`, the Lean initial `State` and `qemu-aarch64` agree on every `PT_LOAD` page (address, permissions, and all 4,096 bytes per page), `pc`, `x0`–`x30` (`0`), `tpidr_el0` (`0`), `argc`, `argv`, `envp`, all scalar and pointer `auxv` payloads and addresses, the entire `[infoBase, stackTop)` stack info block **byte-for-byte**, `brkStart`, and unmapped gaps, subject to two harness-asserted `qemu-aarch64` differences (Gaps #1–#2) and documented differences between `qemu-aarch64`/`loadState` and the Linux kernel (Gap #3):

1. **Gap #1 (`PState` / `CPSR` at `e_entry`)**:
   - Linux `start_thread` (`arch/arm64/include/asm/processor.h`) and Lean `ElfImage.loadState` initialize `PState` to `0` (`NZCV = 0000`).
   - QEMU user-mode TCG (`target/arm/cpu.c`) initializes `env->ZF = 0` on CPU reset, which encodes `CPSR.Z = 1` (`cpsr = 0x40000000`) when read over the GDB stub before the first flag-setting instruction. Both exact values are asserted in `compareEntryRegisters`.
2. **Gap #2 (`AT_SYSINFO_EHDR = 33` vDSO page)**:
   - Both `qemu-aarch64` and the Linux kernel map a `[vdso]` (`r-x`) page and emit `AT_SYSINFO_EHDR (33)` in `auxv`.
   - Lean intercepts `svc #0` directly via `Program.svc` (`Arm64.execSyscall`, `Arm64/Trusted/Syscalls.lean`), so `[vdso]` is not mapped. `AuxvValid` (`X3c` `no_vdso`) therefore excludes `AT_SYSINFO_EHDR` from `auxv.extra`: a vDSO pointer into unmapped memory would fault when libc dereferences it, so verified statements cover the libc `svc #0` fallback paths. The concrete loader-diff harness, which does not assume `ProcessInputs.Valid`, can still pass `AT_SYSINFO_EHDR` via `ProcessInputs.init.auxv.extra` to check stack layout (tested in `c_zig_o2_vdso_extra_auxv`, where `leanSp == qemuSp` and the entire initial stack frame `[sp, stackTop)` matches `qemu-aarch64` byte-for-byte).
3. **Gap #3 (Stack info-block 16-byte alignment padding: `qemu-aarch64` vs Linux `fs/binfmt_elf.c`)**:
   - Both Lean `buildInitialStack` and `qemu-aarch64` (`linux-user/elfload.c` `create_elf_tables`) copy `"aarch64\0"` (`AT_PLATFORM`) immediately below `argv[0]` and then align the stack pointer down to 16 bytes (`infoBase` is `0 mod 16`) when allocating the 16-byte `AT_RANDOM` buffer, placing the `< 16` zero alignment bytes between `AT_RANDOM + 16` and `AT_PLATFORM` so `[infoBase, stackTop)` matches `qemu-aarch64` byte-for-byte.
   - By contrast, the Linux kernel (`fs/binfmt_elf.c` `create_elf_tables`, `arch/arm64/kernel/process.c` `arch_align_stack`) subtracts an intra-page random offset (`0..4095` bytes when ASLR is enabled) and aligns `p &= ~0xf` *before* pushing `"aarch64\0"` (`k_platform`, 8 bytes) and `u_rand_bytes` (16 bytes), so on Linux the random offset and the `< 16` zero alignment bytes (only the latter under `ADDR_NO_RANDOMIZE`) sit between `argv[0]` (above) and `AT_PLATFORM` (below). Consequently, for the same `stackTop` the `argv`, `envp`, and `execfn` string addresses are identical in both layouts, whereas Linux's `AT_PLATFORM` and `AT_RANDOM` addresses (under `ADDR_NO_RANDOMIZE`, `(argv[0] & ~0xf) - 8` and `(argv[0] & ~0xf) - 24`; always `8 mod 16` rather than 16-byte-aligned) — and hence `sp` — differ, alongside other unmodeled kernel details documented in `docs/trust-story/trust-story.md` (`AT_PHDR` edge cases, post-`.bss` `brk` guard/ASLR gap, `auxv` ordering and `AT_HWCAP3`/`AT_MINSIGSTKSZ`/`AT_RSEQ_*`, and `PT_GNU_PROPERTY`).

---

## Symbol-Keyed Overrides (`Overrides.lean`)

`ElfRunsToWithOverrides svc os elfBytes pre post` runs the binary with each function named in
`os : List (String × (State → State))` replaced by its Lean model. The model fires when `pc` equals
the function's entry address. Names are resolved through a full parse of the first `SHT_SYMTAB`
section (`parseSymtabFull`, local and global entries). The judgment is `False` unless resolution
succeeds (`resolveAddrs`); parsing and resolution sit outside `∀ inputs`, so they are checked
even when `pre` is unsatisfiable. For each name, resolution requires:

- **exactly one** `.symtab` entry with that name, of any type or binding (so duplicate local
  symbols, such as two `static` functions with the same name, fail);
- `STT_FUNC` (`st_info & 0xf = 2`), `st_size ≠ 0`, and `st_value % 4 = 0`;
- a regular section index (`0 < st_shndx < SHN_LORESERVE`) that names an `SHT_PROGBITS` section with
  `SHF_ALLOC | SHF_EXECINSTR`, and `[st_value, st_value + st_size)` inside that section;
- `[st_value, st_value + st_size)` inside one executable (`PF_X`) `PT_LOAD` segment of the parsed
  image (any executable segment, not only the one containing `e_entry`);
- pairwise distinct names and pairwise distinct resolved addresses.

Hooks are address-keyed (`Program.ofSites`, `base = 0`), so a model fires exactly at its resolved
address and nowhere else. `ElfImage.symbols` (non-local functions only) is not used. Process steps fetch instructions from memory, so the hook
program's empty `code` is never read.

---

## Untrusted Counterparts

- **Per-image stepping stones (`ElfImageRunsTo`, `ElfImageCorrect`, `ElfImageSafe`), `ElfRunsTo.intro` / `ElfRunsTo.image` / `ElfRunsTo.mono`, `ByteArray` helpers (`ElfImage.parseByteArray`), proof rules, `ProcessInputs.check_iff_valid`, loader/filesystem consequences (`buildInitialStack_ok_of_valid`, `loadState_ok_of_valid`, `initFsState_*`), concrete ELF elaboration (`elf_image%`), kernel-speed `fastParse` (`fastParse_eq_parse` / `ElfImage.parse_of_fastParse`), & executable runners:** [`ProofLib/Process.lean`](../../../ProofLib/Process.lean) and [`ProofLib/Process/Assumptions.lean`](../../../ProofLib/Process/Assumptions.lean).
- **Override resolution lemmas (`overrideProgram_externAt_iff`, `overrideProgram_externAt_none`), kernel-speed checker (`checkOverrides`, `resolveAddrs_of_check`), and constructors (`ElfRunsToWithOverrides.intro`, `ElfRunsToWithOverrides.not_of_check`):** [`ProofLib/Process/Overrides.lean`](../../../ProofLib/Process/Overrides.lean); tests in [`Arm64/Testing/Regression/ProcessOverrides.lean`](../../Testing/Regression/ProcessOverrides.lean).
- **Entry-state differential harness & corpus against `qemu-aarch64`:** [`Arm64/Testing/ElfLoaderDiff/README.md`](../../Testing/ElfLoaderDiff/README.md), [`Arm64/Testing/Harness/ElfLoaderDiff.lean`](../../Testing/Harness/ElfLoaderDiff.lean), and [`Arm64/Testing/Regression/ElfLoaderDiff.lean`](../../Testing/Regression/ElfLoaderDiff.lean).
- **Unit & conformance tests:** [`Arm64/Testing/Regression/Process.lean`](../../Testing/Regression/Process.lean) (`checkElfParserFailClosed`, `checkInitialStackAndAuxv`) and [`Arm64/Testing/Regression/ProcessAssumptions.lean`](../../Testing/Regression/ProcessAssumptions.lean) (`ProcessInputs.Valid` positive/negative `decide +kernel` tests).
- **Examples (`echo_stdin.elf`):** [`Arm64/Testing/Tours/EchoStdinFixture.lean`](../../Testing/Tours/EchoStdinFixture.lean) and [`Arm64/Testing/Tours/ProcessSemanticsTour.lean`](../../Testing/Tours/ProcessSemanticsTour.lean) (fixture [`echo_stdin.c`](../../Testing/Regression/fixtures/echo_stdin.c)).
