# `Arm64/Testing/ElfLoaderDiff/`: Static ELF64 Loader vs `qemu-aarch64` Differential Corpus

- **Layer / Role:** Untrusted differential test corpus (`Lib::Testing`, `Role::Test`).
- **Trusted Target Under Test:** [`Arm64/Trusted/Process/Loader.lean`](../../Trusted/Process/Loader.lean) (`ElfImage.parse`, `ElfImage.parseByteArray`, `buildInitialStack`, `ElfImage.loadState`).
- **Comparison Harness:** [`Arm64/Testing/Harness/ElfLoaderDiff.lean`](../Harness/ElfLoaderDiff.lean) and [`Arm64/Testing/Regression/ElfLoaderDiff.lean`](../Regression/ElfLoaderDiff.lean).
- **Host Orchestrator & CLI:** [`tools/run-trusted-tests/src/elf_loader_diff/`](../../../tools/run-trusted-tests/src/elf_loader_diff/mod.rs) via [`scripts/elf-loader-diff`](../../../scripts/elf-loader-diff).

---

## 1. What Is Compared at `pc == e_entry`

For each binary and `(argv, envp, stdin, files)` configuration, `tools/proc-snapshot --entry-only` launches the binary under the pinned `qemu-aarch64` (`scripts/fetch-qemu-aarch64`) with `personality(ADDR_NO_RANDOMIZE)` and `-seed 0`, stops at the first user instruction (`pc == e_entry`) over the GDB RSP stub, probes unmapped gap pages, and writes `entry.snapshot.{json,bin}`.

[`Testing.ElfLoaderDiff.verifyPositiveCase`](../Harness/ElfLoaderDiff.lean) then parses the same ELF binary with `ElfImage.parse` / `ElfImage.parseByteArray`, constructs `s0 ← img.loadState inputs`, and compares Lean's initial `State` against the QEMU entry snapshot:

1. **Every `PT_LOAD` segment and every 4 KiB page** (`comparePtLoadRegions`):
   - Segment count, page-aligned start address `p_vaddr & ~0xfff`, page-aligned size, and `rwx` permission (`Perm.ro`, `Perm.rx`, `Perm.rw`).
   - Every byte of every 4 KiB page (`0..4096`) between `img.segments` / `s0.mem` and QEMU's dumped memory image (`entry.snapshot.bin`), including:
     - non-bss file tail bytes after `p_vaddr + p_filesz` when `p_filesz == p_memsz` (Linux `elf_map` maps the full file page), and
     - zeroed fractional-page `.bss` tail bytes (`padzero` / `zero_bss`) when `p_filesz < p_memsz` (even when non-zero bytes follow `p_offset + p_filesz` in the ELF file).
2. **All architectural registers at `e_entry`** (`compareEntryRegisters`):
   - `s0.status == .Running`, `s0.pc == img.entry == snap.regs.pc`.
   - `s0.sp % 16 == 0`, `snap.regs.sp % 16 == 0`, and both inside the top stack page `[stackBase, stackTop)`.
   - General-purpose registers `x0`–`x30`: all 31 equal `0` in both Lean and QEMU (`ELF_PLAT_INIT`).
   - Thread pointer `tpidr_el0 == 0` in both Lean and QEMU.
   - `PState` / `CPSR`: verifies Lean's `PState.zero` (`0`, matching Linux `start_thread`) and QEMU TCG's reset `cpsr == 0x40000000` (`CPSR.Z = 1`; see Documented Gap #1 below).
3. **Whole initial stack frame `[stackBase, stackTop)`** (`compareInitialStack`):
   - Every byte below `sp` (`[stackBase, sp)`) is `0x00` and mapped `Perm.rw`.
   - `argc` at `sp`, `argv[0..argc]` pointers and dereferenced NUL-terminated strings, and `argv[argc] == 0`.
   - `envp[0..envc]` pointers and dereferenced NUL-terminated strings, and `envp[envc] == 0`.
   - Every `auxv` `(a_type, a_val)` pair up to `(AT_NULL = 0, 0)`:
     - Exact scalar equality on `AT_PHDR (3)`, `AT_PHENT (4)`, `AT_PHNUM (5)`, `AT_PAGESZ (6)`, `AT_BASE (7)`, `AT_FLAGS (8)`, `AT_ENTRY (9)`, `AT_UID (11)`, `AT_EUID (12)`, `AT_GID (13)`, `AT_EGID (14)`, `AT_HWCAP (16)`, `AT_CLKTCK (17)`, `AT_SECURE (23)`, and `AT_HWCAP2 (26)`.
     - Exact pointer address and payload equality on `AT_PLATFORM (15)` (`"aarch64\0"`), `AT_RANDOM (25)` (16-byte seed), and `AT_EXECFN (31)` (`snap.elf.path`).
     - Bidirectional tag-set check ensuring no unmodeled `auxv` tags exist (and checking `AT_SYSINFO_EHDR (33)` when `AuxvConfig.extra` is populated).
   - Exact byte-for-byte equality of `[infoBase, stackTop)` (`randomBytes (16 B)` ++ `< 16` zero alignment bytes ++ `"aarch64\0"` ++ `argv` strings ++ `envp` strings ++ `execfn` string ++ 8-byte top-of-stack sentinel) between `s0.mem` and `qemu-aarch64`'s dumped stack memory, plus optional 8-byte `0#64` table alignment word after `AT_NULL` (see Documented Gap #3 below for how `qemu-aarch64`'s padding placement compares to Linux `fs/binfmt_elf.c`).
4. **`brk` and unmapped gap pages** (`compareBrkAndUnmappedGaps`):
   - `s0.brkStart == s0.brk == img.brkStart == snap.brkStart`, with `brkStart` unmapped at entry.
   - Null page `[0x0, 0x1000)` unmapped (`s0.mem.perm 0x0#64 == none`).
   - Boundary pages outside `[loads[0].start, brk_start)` (`0x0`, `loads[0].start - PAGE`, `brk_start`, and `stack_top`) probed unmapped in both Lean (`s0.mem.perm`) and QEMU (`proc-snapshot` GDB RSP `m` probes); inter-segment gap pages inside `[loads[0].start, brk_start)` (which `qemu-aarch64` reserves with an anonymous `PROT_NONE` VMA that GDB RSP's `/proc/self/mem` `FOLL_FORCE` fallback reads as `0x00`) verified unmapped in `s0.mem` and absent from `snap.regions`.
   - Guard pages below `stackBase` and at `stackTop` unmapped.
5. **Fail-closed rejection of unsupported/invalid ELFs** (`runRejectedCaseIO` & `#guard_msgs`):
   - Verifies that `ElfImage.parse` and `ElfImage.parseByteArray` cleanly reject PIE (`ET_DYN`), dynamic (`PT_INTERP` / `PT_DYNAMIC`), relocatable (`ET_REL`), W+X (`PF_R | PF_W | PF_X`), executable-stack (`PT_GNU_STACK` with `PF_X`), and non-writable `.bss` (`p_filesz < p_memsz` without `PF_W`) binaries.

---

## 2. Corpus (`src/` & `bin/`)

Small (< 18 KiB) binaries are checked into `bin/` alongside `expected_snapshots.json` so `lake test` / `unit_tests` runs without invoking external compilers or QEMU. In the table, `as` is the pinned zig's integrated assembler (`zig clang -cc1as`, LLVM 21.1; `llvm-mc` is a fallback that other LLVM releases may not reproduce byte-for-byte) and `ld.lld` is the one bundled with the pinned Rust toolchain. Larger multi-compiler binaries (`rust_tls_bss.elf` with full `std`, `go_static.elf`, optional `c_gcc_glibc.elf`, and `zig cc` PIE/dynamic binaries) are compiled and snapshotted on the fly by `./scripts/elf-loader-diff run`.

| Binary | Toolchain / Linker | Key Layout Features Tested | Committed in `bin/`? |
|---|---|---|---|
| `tiny_asm.elf` | `as` + `ld.lld -static` | Minimal hand-written AArch64 assembly (`r-x` text, no `.data`/`.bss`) | Yes (`1.0 KiB`) |
| `layout_multi_rw.elf` | `as` + `ld.lld -T layout_multi_rw.ld` | 5 `PT_LOAD` segments: `r--`, `r-x`, and **3 distinct `rw-` segments** (`p_filesz == p_memsz`, mixed data+bss, and pure `p_filesz == 0 < p_memsz`) separated by an unmapped multi-page gap `[0x432000, 0x445000)` | Yes (`17 KiB`) |
| `layout_midpage_bss.elf` | `as` + `ld.lld -T layout_midpage_bss.ld` | Both `PT_LOAD` segments start **mid-page** (`0x400200`, `0x402380`) and end mid-page; `.file_tail_marker` (`0xdeadbeef`) immediately follows `p_offset + p_filesz` in the file to test non-bss file tail mapping vs `.bss` `padzero` | Yes (`2.5 KiB`) |
| `layout_tls_relro.elf` | `as` + `ld.lld -T layout_tls_relro.ld` | Explicit `PT_PHDR`, `PT_NOTE`, `PT_TLS` (`.tdata` + `.tbss`), `PT_GNU_RELRO`, and `PT_GNU_STACK` | Yes (`13 KiB`) |
| `layout_text_only.elf` | `as` + `ld.lld -T layout_text_only.ld` | A single `r-x` `PT_LOAD` (ELF header + program headers + `.rodata` + `.text`) and **no writable segment**, so `brk` starts right after the only text page; `e_entry` is in the middle of the segment. Also tested with 201 `argv` + 120 `envp` entries (~21 KiB info block spanning 6+ stack pages) | Yes (`0.6 KiB`) |
| `layout_entry_deep.elf` | `as` + `ld.lld -T layout_entry_deep.ld` | 3-page `r-x` segment with `e_entry` on its **third page**; a separate `r--` header + `.rodata` segment shares file page 0 with the text segment at a different virtual page | Yes (`11 KiB`) |
| `layout_bss_page_end.elf` | `as` + `ld.lld -T layout_bss_page_end.ld` | Mid-page `rw-` segment whose `.bss` is padded so `p_vaddr + p_memsz` ends **exactly on a page boundary** | Yes (`0.8 KiB`) |
| `layout_filesz_page_end.elf` | `as` + `ld.lld -T layout_filesz_page_end.ld` | `rw-` segment whose non-zero `.data` ends **exactly on a page boundary** (`p_vaddr + p_filesz` page-aligned) with 24 B of `.bss` just past it (no fractional `padzero` page) | Yes (`4.3 KiB`) |
| `layout_large_bss.elf` | `as` + `ld.lld -T layout_large_bss.ld` | Mid-page `rw-` segment with 0x58 B `.data` and **1 MiB + 0x234 B `.bss`** (258 pages, 257 anonymous) ending mid-page | Yes (`0.8 KiB`) |
| `layout_palign_4k.elf`, `layout_palign_16k.elf`, `layout_palign_2m.elf` | `as` + `ld.lld -z max-page-size=0x1000` / `0x4000` / `0x200000` (no linker script) | The same source in `ld.lld`'s default `r--`/`r-x`/`rw-` layout with `p_align` `0x1000`, `0x4000`, and `0x200000`: segments on consecutive pages, 3-page gaps, and 2 MiB-apart segments that all share one file page | Yes (`1.6 KiB` each) |
| `layout_unaligned_straddle.elf` | `as` + `ld.lld -T layout_unaligned_straddle.ld` | `r-x`, `r--`, `rw-` `PT_LOAD`s at **non-page-aligned `p_vaddr`/`p_offset`** (congruent mod 4 KiB), each **straddling a page boundary**; the `rw-` `p_filesz` and `p_memsz` cross different boundaries, so `padzero` clears a mid-page tail | Yes (`13 KiB`) |
| `layout_phdr_unmapped.elf` | `as` + `ld.lld -T layout_phdr_unmapped.ld` | ELF header and program header table **not covered by any `PT_LOAD`** (no `FILEHDR`/`PHDRS`, no `PT_PHDR`); page-aligned `r-x`, then a separate `r--` `.rodata` segment **after** text, then `rw-` | Yes (`12 KiB`) |
| `layout_pure_bss_midpage.elf` | `as` + `ld.lld -T layout_pure_bss_midpage.ld` | **Pure `.bss` `PT_LOAD` (`p_filesz == 0`) starting and ending mid-page** (`0xb03a40`), separate from a `p_filesz == p_memsz` `rw-` segment with an unmapped page between them | Yes (`2.9 KiB`) |
| `layout_many_loads.elf` | `as` + `ld.lld -T layout_many_loads.ld` | **Eight `PT_LOAD`s** (`r--`, `r-x`, `r--`, `rw-`, `r--`, `r-x`, `rw-` data+bss, `rw-` pure bss) on distinct pages sharing file pages, with unmapped gaps; `e_entry` in the second `r-x` segment | Yes (`4.8 KiB`) |
| `layout_many_sections.elf` | `as` + `ld.lld` (no linker script, unstripped) | 70+ small output sections (40 `.fnNN` functions with `STT_FUNC` symbols in `.symtab`, 30 odd-sized `.dNN` data/rodata sections with mixed alignment) | Yes (`14 KiB`) |
| `layout_high_vaddr.elf` | `as` + `ld.lld -T layout_high_vaddr.ld` | `r-x` text at `0x10000` (the usual `mmap_min_addr`) and `rw-` data + `.bss` **above 4 GiB** (`0x100002110`), leaving a ~4 GiB unmapped gap; `brk` above 4 GiB | Yes (`0.7 KiB`) |
| `layout_rw_file_tail.elf` | `as` + `ld.lld -T layout_rw_file_tail.ld` | `rw-` `PT_LOAD` with `p_filesz == p_memsz` ending mid-page, followed in the file by a non-alloc `0xfeedface` marker that Linux maps into the **writable** page (no `padzero`) | Yes (`1.3 KiB`) |
| `c_zig_o0.elf` | `zig cc -target aarch64-linux-musl -static -O0` | Stock musl `crt1.o` + C at `-O0` with `.rodata`, `.data`, and 8 KiB `.bss` | Yes (`3.8 KiB`) |
| `c_zig_o2.elf` | `zig cc -target aarch64-linux-musl -static -O2` | Stock musl `crt1.o` + C at `-O2`; tested with default args, `AT_SYSINFO_EHDR` in `AuxvConfig.extra`, 49 `argv` + 32 `envp` entries (> 6 KiB info block), and `stdin` + regular files | Yes (`3.6 KiB`) |
| `rust_nostd_tls_bss.elf` | `rustc --target=aarch64-unknown-linux-musl -O` (`no_std`) | Static Rust with `PT_TLS` (`.tdata` + `.tbss`) and 64 KiB `.bss` (`16` zero pages) | Yes (`1.8 KiB`) |
| `rust_tls_bss.elf` | `rustc --target=aarch64-unknown-linux-musl -O` (`std`) | Full Rust `std` runtime (`std::thread_local!` `PT_TLS`, `PT_GNU_RELRO`, 64 KiB `.bss`) | Built by `elf-loader-diff run` |
| `go_static.elf` | `GOOS=linux GOARCH=arm64 CGO_ENABLED=0 go build` | Go static binary (`0x10000` text segment, `PT_NOTE` `.note.go.buildid`, embedded section headers, large `.noptrdata`/`.bss`) | Built by `elf-loader-diff run` |
| `c_gcc_glibc.elf` | `aarch64-linux-gnu-gcc -static -O2` | Optional static `gcc` + `glibc` binary (run automatically when `aarch64-linux-gnu-gcc` is installed) | Built by `elf-loader-diff run` |
| `reject_pie.elf`, `reject_dynamic.elf`, `reject_relocatable.elf`, `reject_wx_segment.elf`, `reject_exec_stack.elf`, `reject_ro_bss.elf` | `ld.lld` / header mutation | Real linker-produced `ET_DYN` (PIE), `PT_INTERP`/`PT_DYNAMIC`, `ET_REL` (`.o`), `--omagic` W+X, `-z execstack`, and non-writable `p_filesz < p_memsz` binaries | Yes (`0.8–17 KiB`) |

---

## 3. Explicit `ProcessInputs` Alignment & Documented Normalizations / Gaps

Rather than masking away host-dependent fields, `verifyPositiveCase` configures `ProcessInputs` to match the QEMU run (`execfn = bytesOfString snap.elf.path` — overriding the `ProcessInputs.execfn := []` default that writes a single NUL byte `"\0"` when callers do not specify a pathname — along with `stackTop`, `stackSize`, `auxv.randomBytes`, `auxv.hwcap`, `auxv.hwcap2`, `auxv.uid`, `auxv.euid`, `auxv.gid`, `auxv.egid`, and optional `auxv.extra = [(AT_SYSINFO_EHDR, vdso)]`).

Every remaining difference between `ElfImage.loadState` and `qemu-aarch64` is listed and checked explicitly in [`Arm64/Testing/Harness/ElfLoaderDiff.lean`](../Harness/ElfLoaderDiff.lean) (Gaps #1–#2 and #4), alongside documented differences between `qemu-aarch64`/`loadState` and the Linux kernel (Gap #3; see [`Arm64/Trusted/Process/README.md`](../../Trusted/Process/README.md)):

1. **Gap #1 (`PState` / `CPSR` at `e_entry`)**: Linux `start_thread` and Lean `loadState` initialize `PState.zero` (`NZCV = 0000`), whereas QEMU TCG's CPU reset leaves `env->ZF = 0` (`CPSR.Z = 1`, `cpsr = 0x40000000`). Both exact values are asserted in `compareEntryRegisters`.
2. **Gap #2 (`AT_SYSINFO_EHDR = 33` vDSO page)**: Both `qemu-aarch64` and the Linux kernel map a `[vdso]` (`r-x`) page and emit `AT_SYSINFO_EHDR (33)`. Lean models syscalls directly in `execSyscall` and omits `[vdso]` by default, and `AuxvValid` (`X3c`) excludes `AT_SYSINFO_EHDR` from verified statements; this harness does not assume `ProcessInputs.Valid` and still supports `AT_SYSINFO_EHDR` via `AuxvConfig.extra` for stack-layout checks (tested in `c_zig_o2_vdso_extra_auxv`, where `leanSp == qemuSp` and the entire initial stack frame `[sp, stackTop)` matches `qemu-aarch64` byte-for-byte).
3. **Gap #3 (Stack info-block 16-byte alignment padding: `qemu-aarch64` vs Linux `fs/binfmt_elf.c`)**: Both Lean `buildInitialStack` and `qemu-aarch64` (`linux-user/elfload.c` `create_elf_tables`) push `"aarch64\0"` (`AT_PLATFORM`) immediately below `argv[0]` and align down to 16 bytes (`infoBase` is `0 mod 16`) when reserving the 16-byte `AT_RANDOM` buffer, placing the `< 16` zero alignment bytes between `AT_RANDOM + 16` and `AT_PLATFORM` so `[infoBase, stackTop)` matches `qemu-aarch64` **byte-for-byte**. By contrast, the Linux kernel (`fs/binfmt_elf.c` `create_elf_tables`) calls `arch_align_stack(p)` (`p &= ~0xf`) *before* pushing `"aarch64\0"` (`k_platform`, 8 bytes) and `u_rand_bytes` (16 bytes), so on Linux the `< 16` zero alignment bytes sit below `argv[0]` (between `argv[0]` and `AT_PLATFORM`) rather than above `AT_RANDOM`. Thus the `argv`, `envp`, and `execfn` string addresses are identical in both layouts, whereas Linux's `AT_PLATFORM` (`(argv[0] & ~0xf) - 8`) and `AT_RANDOM` (`(argv[0] & ~0xf) - 24`, which is `8 mod 16`) addresses — and hence `sp` — differ (documented, not asserted by the `qemu-aarch64` harness, alongside other Linux kernel differences such as `auxv` tag ordering and newer tags like `AT_MINSIGSTKSZ` / `AT_RSEQ_*`).
4. **Gap #4 (`AT_PHDR` when no `PT_LOAD` maps the program headers: `qemu-aarch64` vs Lean/Linux)**: Linux `load_elf_binary` (`third_party/linux-7.3/fs/binfmt_elf.c`) sets `phdr_addr` only for a `PT_LOAD` with `p_offset <= e_phoff < p_offset + p_filesz`; otherwise it stays `0`, so a static `ET_EXEC` gets `AT_PHDR = 0`. Lean `loadState` (`ElfImage.phdrVaddr`) also reports `0` when no page-rounded `PT_LOAD` file mapping (`[p_offset - p_vaddr % 4096, p_offset + p_filesz)`) contains the whole table. `qemu-aarch64` instead reports `pageAlignDown(min PT_LOAD p_vaddr) + e_phoff`, an address with no program headers behind it. The harness recognizes this layout from the raw ELF bytes (`qemuUncoveredPhdrAddr?`, using the same page-rounded rule as the Lean loader) and asserts both exact values (Lean `0`, QEMU the formula above), so a change on either side fails the case. The `layout_phdr_unmapped_default` case exercises this. Every other case still requires equal Lean and QEMU `AT_PHDR`, including `layout_midpage_bss` and `layout_unaligned_straddle`: there the table sits in the page-alignment lead bytes, before `p_offset`, so Lean and QEMU agree and Linux would report `0`. That separate Lean-vs-Linux difference is tracked in `docs/trust-story/trust-story.md`.

---

## 4. Commands

```bash
# Recompile the committed small binaries in Arm64/Testing/ElfLoaderDiff/bin/
./scripts/elf-loader-diff build

# Regenerate (or check zero drift on) Arm64/Testing/ElfLoaderDiff/expected_snapshots.json
# Note: `regen --check` compares all PT_LOAD region descriptors and bytes, brkStart, pc, x0..x30,
# cpsr, tpidr_el0, argv, envp, elf.sha256, runner.sha256, stack size/perm/binOff, and stack_top - sp,
# while skipping stack.start, regs.sp, and raw stack/auxv bytes (which depend on host UID/GID and
# stack base; full stack and auxv bytes are checked against `loadState` by `run` and `unit_tests`).
./scripts/elf-loader-diff regen
./scripts/elf-loader-diff regen --check

# Build all live multi-compiler binaries (including Go and full-std Rust), snapshot under QEMU,
# and run the full Lean comparison harness (`elf_eval --loader-diff`)
./scripts/elf-loader-diff run

# Run the committed snapshot comparison suite via `unit_tests` (no QEMU or compilers required)
./Arm64/Testing/.lake/build/bin/unit_tests --elf-loader-diff
```
