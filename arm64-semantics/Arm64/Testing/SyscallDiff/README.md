# `Arm64/Testing/SyscallDiff`: Per-Syscall Linux `7.3` & QEMU Differential Probe Suite

- **Layer / Role**: Untrusted differential test suite (`Lib::Testing`, `Role::Test`, outside the TCB).
- **Covers**:
  - [`src/bin/syscall_probe.rs`](src/bin/syscall_probe.rs): Freestanding `#![no_std]` `#![no_main]` static AArch64 (`ET_EXEC`) binary issuing raw `svc #0` probes across all 29 modeled Linux AArch64 syscalls (`include/uapi/asm-generic/unistd.h` in `linux-7.3`).
  - `bin/syscall_probe.elf`: Deterministically compiled static AArch64 ELF binary executed against both `qemu-aarch64` user-mode and Lean's `runElfImageFastMmap` (`Arm64.execSyscall`).
  - [`../Regression/SyscallDiff.lean`](../Regression/SyscallDiff.lean) (and re-export [`../SyscallDiff.lean`](../SyscallDiff.lean)):
    - Structured `KNOWN_QEMU_USER_DEVIATIONS` table (`QEMU-DEV-1` .. `QEMU-DEV-13`) documenting every case where `qemu-aarch64` user-mode deviates from real Linux `7.3`.
    - Kernel-checked boundary conformance theorem `all_29_syscalls_boundary_conformance` testing `Arm64.execSyscall` across all 29 modeled syscalls, including the `linux-7.3` edge cases where `qemu-aarch64` deviates.
    - Differential test runner (`checkSyscallProbeVsQemuIO`, `runSyscallDiffSuiteIO`) comparing `syscall_probe.elf` across modes `all`, `exit_one`, `tkill_abrt`, `tgkill_abrt`, and `record-json` between `qemu-aarch64` and `Arm64.execSyscall`.
    - Focused per-behavior case table `syscallCaseTable` (`checkSyscallCaseIO`), described below.
  - [`src/cases/`](src/cases/): one small freestanding C source per behavior (`<syscall>_<behavior>.c`, `seq_<family>_<behavior>.c`) plus the shared runtime [`src/cases/sd_rt.h`](src/cases/sd_rt.h), compiled to `bin/<case>.elf`.

## Focused Per-Behavior Case Binaries

Each `src/cases/<case>.c` exercises one behavior of one syscall family (success path, one modeled
error path, a boundary argument, or a short sequence) with raw `svc #0` calls. For every call it
prints `label=<raw return>` on `stdout`; when the return differs from the Linux `7.3` result the
case expects, it also prints a `FAIL` line on `stderr` and exits `1`. Host-dependent values
(addresses, PIDs, clocks, random bytes) are checked by property and never printed.

`syscallCaseTable` in [`../Regression/SyscallDiff.lean`](../Regression/SyscallDiff.lean) lists every
case with its expected exit status / signal (and optional `argv` / `stdin`). For each case,
`unit_tests --syscall-diff` runs the binary under `qemu-aarch64` (`-0 <case>`, fresh empty working
directory, empty environment) and under `runElfImageFastMmap`, and requires identical exit status,
signal, `stdout` and `stderr` (`stderr` is not compared on signal deaths, where `qemu-aarch64`
prints its own message), plus the exit status / signal from the table.
`syscallCaseTableMatchesSources` fails if the table and `src/cases/*.c` drift apart.

A case whose runners differ is not hidden: its entry carries a `gap : Option CaseGap` that pins the
divergence and fails once it closes:

| `CaseGap` | Lean model | `qemu-aarch64` |
|---|---|---|
| `leanFailsClosed needle` | ends in a non-exit status (`.Exception` / `.OutOfMemory`) containing `needle`; `stdout` so far is a prefix of QEMU's | matches the table (Linux) |
| `leanDiverges leanExit` | exits `leanExit` (wrong value: model bug or documented scope limit) | matches the table (Linux) |
| `qemuDeviates devId qemuExit` | matches the table (Linux) | exits `qemuExit` (`devId` in `KNOWN_QEMU_USER_DEVIATIONS`) |
| `bothDifferFromLinux` | plain check: both runners agree byte for byte, but the table status records that both differ from Linux | |

`qemu-aarch64` keeps some host file descriptors (for example `3`) open inside the guest, so guest
`openat` results differ from Lean and Linux. Cases never print or compare absolute fd numbers; they
check `fd >= 3`, monotonicity, and lowest-free reuse instead, and use fd `99` / `-1` for `EBADF`.

```bash
scripts/syscall-diff-cases build [<case>...]   # rebuild bin/<case>.elf (pinned zig 0.16.0)
scripts/syscall-diff-cases check               # fresh rebuild must match the checked-in ELFs
scripts/syscall-diff-cases probe [--check]     # rebuild or check bin/syscall_probe.elf (Rust 1.98.1)
scripts/syscall-diff-cases diff <case>         # developer loop: qemu-aarch64 vs `elf_run`
Arm64/Testing/.lake/build/bin/unit_tests --syscall-diff
```

To add a case: write `src/cases/<case>.c` (copy an existing case), run
`scripts/syscall-diff-cases build <case>` and `diff <case>`, add a `syscallCaseTable` entry, and run
`unit_tests --syscall-diff`.

## Standalone Native AArch64 Linux Runner Mode

The same static `syscall_probe.elf` binary can be copied onto any native AArch64 Linux `7.3` host (or full-system VM) and run with `record-json` to emit a ground-truth JSON vector of all 132 probe outcomes:

```bash
./Arm64/Testing/SyscallDiff/bin/syscall_probe.elf record-json > native_linux_7_3_vectors.json
```

## Rebuilding `bin/syscall_probe.elf`

```bash
scripts/syscall-diff-cases probe           # rebuild from src/bin/syscall_probe.rs (pinned Rust 1.98.1)
scripts/syscall-diff-cases probe --check   # fresh rebuild must match the checked-in ELF
```

The probe is a freestanding `#![no_std]` binary: one `rustc --target aarch64-unknown-linux-gnu
-C opt-level=s -C panic=abort -C strip=symbols --emit=obj` with paths remapped, linked by `rust-lld`
against that target's `libcore` and `compiler_builtins` rlibs. `scripts/build-test-elfs.sh` rebuilds
it together with every other generated test ELF; see
[Testing dependencies](../README.md#testing-dependencies) for the toolchains.
