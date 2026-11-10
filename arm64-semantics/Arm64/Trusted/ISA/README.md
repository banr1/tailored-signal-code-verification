# `Arm64/Trusted/ISA/` — A64 instruction set model (TCB)

This directory is the trusted model of the AArch64 (A64) user-mode ISA. Every
verified theorem in the repository is ultimately a statement about
[`Step`/`Steps`](Semantics.lean). Those are defined by fetching 4 bytes from
memory, decoding them with [`Arm64.decode`](Decode.lean), and executing the
resulting `Instr` with [`execInst`](Eval.lean). A bug in any of these files can
make a proof meaningless, so the files are kept theorem-free (enforced by
`check-trust-guards`). They are cross-checked against Unicorn, Sail and the
ARM ASL specification by the untrusted harnesses in
[`Arm64/Testing/`](../../Testing/README.md).

## Which file to read for X

| Need | File |
|---|---|
| Instruction AST (`Instr`, `Reg`, `AddrMode`, `MemWidth`, `AtomicOp`, `SimdMemSize`, …) | [`Syntax.lean`](Syntax.lean) |
| 32-bit word → `Option Instr` (`Arm64.decode`), grouped by encoding class | [`Decode.lean`](Decode.lean) |
| Byte-addressed memory, `Perm`, `canRead`/`canWrite`/`canExec`, `readSized`/`writeSized` | [`Memory.lean`](Memory.lean) |
| Registers, `NZCV`, `V0..V31`, `TPIDR_EL0`, `FPSR`, `brkStart`/`brk`, `sigActions`, `sigAltStack`, `Oracle`, `ExecStatus` | [`State.lean`](State.lean) |
| IEEE-754 binary32/binary64 arithmetic and cumulative `FPSR` exception flags | [`Float.lean`](Float.lean) |
| `execInstWithSvc`, `noSyscalls`, atomics/CRC/SIMD helpers (Linux `SVC #0` handlers live in [`../Syscalls/`](../Syscalls/README.md)) | [`Eval.lean`](Eval.lean) |
| `Program` (including `svc`), fetch, `Step`, `Steps`, `StepsUntil` | [`Semantics.lean`](Semantics.lean) |

## Execution model in one paragraph

The model is a **single hardware thread at EL0 running Linux user code**.
State is the 31 GPRs plus `SP`/`PC`, `NZCV`, 32 128-bit vector registers,
`TPIDR_EL0`, `FPSR`, the program break, per-signal dispositions (`sigActions`),
alternate signal stack configuration (`sigAltStack`), and a byte-addressed
memory with per-byte `Perm` (read/write/exec). Each `Step` executes one instruction
deterministically. Faults are not traps: they set `status := .Exception msg`
and stop execution. Faults include permission faults, SP misalignment when
`Rn = SP`, required-alignment faults, unmodeled system registers and syscalls,
and `UDF`. Since no proof can make progress past an `Exception`, the
conservative choice for anything not modeled is to fault rather than guess.
Instruction words that decode to `none` (unallocated, reserved, or
CONSTRAINED UNPREDICTABLE register overlaps) likewise cannot step.

## Supported instruction families

**Integer data processing**
- `ADD`/`SUB`/`ADDS`/`SUBS` with immediate, shifted-register and extended-register forms.
- `ADC`/`SBC` (and their flag-setting forms).
- Logical operations with immediate (`decodeBitMasks`) or shifted register:
  `AND`/`ORR`/`EOR`/`ANDS`/`BIC`/`ORN`/`EON`/`BICS`.
- Moves `MOVZ`/`MOVN`/`MOVK`, and `ADR`/`ADRP`.
- Bitfield `BFM`/`SBFM`/`UBFM` (covering all their aliases) and `EXTR`.
- Variable shifts `LSLV`/`LSRV`/`ASRV`/`RORV`.
- `CLZ`/`CLS`/`RBIT`/`REV*`.
- Multiply/divide: `MADD`/`MSUB`, `SMADDL`/`UMADDL`, `SMSUBL`/`UMSUBL`, `SMULH`/`UMULH`, `SDIV`/`UDIV`.
- Conditional `CSEL`/`CSINC`/`CSINV`/`CSNEG` and `CCMP`/`CCMN`.
- **CRC32**: `CRC32{B,H,W,X}` and `CRC32C{B,H,W,X}`, computed as bit-reflected
  polynomial division over GF(2) with polynomials `0x04C11DB7` and
  `0x1EDC6F41` (`evalCrc32`).

**Branches**: `B`, `BL`, `BR`, `BLR`, `RET`, `B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`.

**GPR loads and stores**
- `LDR`/`STR` at every width and sign-extension variant.
- Addressing modes: unsigned scaled offset, unscaled (`LDUR`), pre-/post-index,
  register offset with extend/shift, and PC-relative literal.
- Pairs: `LDP`/`STP`/`LDPSW` in signed-offset, pre- and post-index forms.
- **`LDNP`/`STNP`**: non-temporal pairs, treated sequentially as signed-offset
  `LDP`/`STP`. `LDNP` with `Rt = Rt2` decodes to `none`.

**SIMD&FP loads and stores**
- `LDR`/`STR`/`LDP`/`STP` for `B/H/S/D/Q`.
- **`LDR St/Dt/Qt, label`**: PC-relative literal.
- **`LDNP`/`STNP`** for `S/D/Q`.
- `ST1` single-lane post-index.
- **`LD1`/`ST1` (multiple structures, 1–4 consecutive registers, no offset /
  post-index immediate / post-index register)**.
- **`LD1R`**.

**SIMD and floating point**
- `FMOV` between general-purpose and vector registers, and FP data processing
  with 1, 2 or 3 sources.
- `FCMP`, `FCCMP`, `FCSEL`, `FMOV #imm`, and fixed/integer conversions. Every
  scalar FP instruction and saturating integer SIMD operation updates the
  cumulative flags in `State.fpsr` (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, `QC`)
  under pinned `FPCR = 0` (round-to-nearest-even, no flush-to-zero, `DN = 0`,
  `AH = 0`, trap enables disabled).
- Vector ops:
  - Immediate shifts & modified immediates (`simdImmShift`): `MOVI` (`LSL` & `MSL`), `MVNI` (`LSL` & `MSL`), `ORR`/`BIC #imm`, vector `FMOV #imm8`, `SHL`, `SLI`, `SRI`, `USHR`/`SSHR`, `USRA`/`SSRA`, `URSHR`/`SRSHR`, `URSRA`/`SRSRA`, `SQSHL`/`UQSHL`/`SQSHLU` (immediate), narrowing shifts `SHRN`/`RSHRN`/`SQSHRN`/`UQSHRN`/`SQSHRUN`/`SQRSHRN`/`UQRSHRN`/`SQRSHRUN` (`+2`), and widening shifts `USHLL`/`SSHLL` (`+2`, `UXTL`/`SXTL`).
  - Lane insert/duplicate/extract (`simdInsDup`): `INS`, `DUP`, `UMOV`, `SMOV`.
  - Three-same integer (`simdThreeSame`): `AND`/`BIC`/`ORR`/`ORN`/`EOR`/`BSL`/`BIT`/`BIF`, `ADD`/`SUB`/`ADDP`, `CMGT`/`CMHI`/`CMGE`/`CMHS`/`CMEQ`/`CMTST`, `SHADD`/`UHADD`/`SRHADD`/`URHADD`/`SHSUB`/`UHSUB`, `SQADD`/`UQADD`/`SQSUB`/`UQSUB`, `SSHL`/`USHL`/`SRSHL`/`URSHL`/`SQSHL`/`UQSHL`/`SQRSHL`/`UQRSHL`, `SMAX`/`UMAX`/`SMIN`/`UMIN`/`SMAXP`/`UMAXP`/`SMINP`/`UMINP`, `SABD`/`UABD`/`SABA`/`UABA`, `MUL`/`MLA`/`MLS`/`PMUL`, `SQDMULH`/`SQRDMULH`.
  - Two-register miscellaneous (`simdTwoRegMisc`): `REV64`/`REV32`/`REV16`, `SADDLP`/`UADDLP`/`SADALP`/`UADALP`, `SUQADD`/`USQADD`, `CLS`/`CLZ`/`CNT`/`NOT`/`RBIT`, `SQABS`/`SQNEG`/`ABS`/`NEG`, zero-comparisons `CMGT`/`CMGE`/`CMEQ`/`CMLE`/`CMLT #0`, `XTN`/`SQXTUN`/`SQXTN`/`UQXTN` (`+2`), `SHLL`/`SHLL2`, `URECPE`/`URSQRTE`.
  - Across-lanes (`ADDV`, `UADDLV`, `SADDLV`, `UMAXV`, `UMINV`, `SMAXV`, `SMINV`), permutes (`ZIP`/`UZP`/`TRN1`/`TRN2`), `EXT`, `TBL`/`TBX` (1–4 table registers), scalar `ADDP Dd, Vn.2D`, and polynomial multiply long `PMULL`/`PMULL2` (`8H <- 8B/16B` and `1Q <- 1D/2D`).
- Cryptographic extensions: AES (`AESE`/`AESD`/`AESMC`/`AESIMC`), SHA-1 (`SHA1C`/`SHA1P`/`SHA1M`/`SHA1H`/`SHA1SU0`/`SHA1SU1`), SHA-256 (`SHA256H`/`SHA256H2`/`SHA256SU0`/`SHA256SU1`), SHA-512 (`SHA512H`/`SHA512H2`/`SHA512SU0`/`SHA512SU1`), and SHA-3 (`EOR3`/`BCAX`/`RAX1`/`XAR`).

Any SIMD sub-opcode inside a decoded group that is not implemented (such as vector floating-point) or is architecturally `UNDEFINED` evaluates to `.Exception` with a descriptive message naming the encoding class, fields, and mnemonic when known. It never produces a silently wrong value.

**System**
- `NOP`, and **`HINT #imm`**: `YIELD`, `WFE`, `WFI`, `SEV`, `SEVL`, `BTI`,
  `PACIASP`/`AUTIASP` and the other hint-space encodings.
- Barriers `DMB`/`DSB`/`ISB`, and `CLREX`.
- `MRS`/`MSR` for `TPIDR_EL0`, **`NZCV`**, **`FPSR`**, **`FPCR`** (pinned to `0`), and **`DCZID_EL0`** (read-only).
- **`DC ZVA`**, **`PRFM`** (immediate, unscaled, register and literal forms),
  **`UDF`**, `SVC #0`, `BRK #imm16` (`HLT` is not decoded).

## Sequential (single-threaded) semantics of atomics, ordering and hints

The model has exactly one observer of memory: no other cores, no DMA, no
signal handlers. Under that assumption every memory-ordering annotation is
unobservable, and every atomic read-modify-write is just a read followed by a
write. Each instruction below executes **deterministically and atomically in
one `Step`**.

| Family | Instructions | Sequential meaning |
|---|---|---|
| Load-acquire / store-release | `LDAR*`, `STLR*`, `LDAPR{,B,H}`, `LDAPUR*`, `LDAPURS*`, `STLUR*` | A plain load (zero- or, for `LDAPURS*`, sign-extending) or store. The access must be naturally aligned, otherwise alignment fault. The model is stricter than the architecture here: with `FEAT_LSE2`, or with `SCTLR.nAA = 1`, unaligned accesses that stay within a 16-byte granule are allowed. Acquire/release/RCpc ordering is not modeled. |
| Load exclusive | `LDXR`, `LDAXR` (`W8`–`W64`), `LDXP`, `LDAXP` (`W32`, `W64`) | A naturally aligned load. A pair must be aligned to its total size: 8 bytes for a `W32` pair, 16 bytes for a `W64` pair. This matches the ASL `Mem` check, which aligns exclusive pairs to the full access size. **The exclusive monitor is not modeled**, though spurious store-exclusive failures are modeled via the `exclFails` oracle below. |
| Store exclusive | `STXR`, `STLXR` (`W8`–`W64`), `STXP`, `STLXP` (`W32`, `W64`) | Checks SP alignment, natural alignment, and write permission (`s.mem.canWrite`), then consults the store-exclusive failure oracle `s.exclWillFail` (`s.exclFails.headD false`, advancing `s.exclFails := s.exclFails.tail`): on `true`, **spurious failure** (`Ws := 1`, memory unchanged); on `false`, **success** (`Ws := 0`, stores `Rt` and `Rt2`). **Fairness assumption**: every execution has finitely many spurious failures, adversarially placed (`exclFails : List Bool`, defaulting to `false` once exhausted). This models eventual LL/SC progress without an exclusive monitor; a retry-less `stxr`/`stxp` is unprovable because `exclFails = [true]` is a valid initial state. Overlaps that are CONSTRAINED UNPREDICTABLE (`Ws = Rt`/`Rt2`, or `Ws = Rn` with `Rn ≠ SP`) decode to `none`. |
| Compare-and-swap | `CAS{,A,L,AL}{B,H,}` and `CASP{,A,L,AL}` | `old := mem[Xn]`. If `old = Rs` (truncated to the access width), then `mem[Xn] := Rt`. Finally `Rs := old`, zero-extended. **Read and write permission are required even when the compare fails.** This is architectural: the ASL `CreateAccDescAtomicOp` sets `write = TRUE`, and `MemAtomic` translates the address before comparing. The access must be naturally aligned (stricter than `FEAT_LSE2`). `CASP` with odd `Rs`/`Rt` is UNDEFINED and decodes to `none`. |
| Atomic RMW | `SWP*`, `LD{ADD,CLR,EOR,SET,SMAX,SMIN,UMAX,UMIN}{,A,L,AL}{B,H,}`, and the `ST<op>` aliases (`Rt = XZR`) | `old := mem[Xn]`, then `mem[Xn] := op(old, Rs)`, then `Rt := old` (discarded when `Rt = XZR`). `SMAX`/`SMIN` compare signed at the access width. The access must be naturally aligned (stricter than `FEAT_LSE2`). |
| Barriers | `DMB`, `DSB`, `ISB`, `CLREX` | No-op: `PC += 4`. |
| Hints | `NOP`, `HINT #imm` (incl. `YIELD`, `WFE`, `WFI`, `SEV`, `SEVL`, `CSDB`, `BTI`, `PACIASP`, `AUTIASP`, `XPACLRI`, `CHKFEAT`) | No-op: `PC += 4`. With a single thread, `WFE`/`WFI` wake up immediately, and `SEV`/`CSDB` have no modeled state. **The model is a PE without `FEAT_PAuth`, `FEAT_BTI`, `FEAT_GCS` or `FEAT_CHK`.** For those, the ASL takes `EndOfDecode(Decode_NOP)`: `PACIASP`/`AUTIASP` leave `X30` unchanged, and `CHKFEAT` leaves `X16` unchanged (the "feature absent" answer). Unallocated hints are NOPs. |
| Prefetch | `PRFM` (all forms) | No-op: `PC += 4`. Per the ASL, no permission, alignment or SP check is done, because prefetches never fault. |
| Cache zero | `DC ZVA, Xt` | Zeroes the 64-byte block containing `Xt` (`Xt & ~63`). Write permission is required on the whole block. Consistent with `DCZID_EL0`. |
| System registers | `MRS`/`MSR TPIDR_EL0`; `MRS`/`MSR NZCV`; `MRS`/`MSR FPSR`; `MRS`/`MSR FPCR`; `MRS DCZID_EL0` | `TPIDR_EL0` is a plain 64-bit register used for TLS. `NZCV` reads/writes bits `[31:28]`. `FPSR` reads/writes the cumulative floating-point exception and SIMD saturation flags masked to `fpsrMask = 0x0800009f` (`IOC` bit 0, `DZC` bit 1, `OFC` bit 2, `UFC` bit 3, `IXC` bit 4, `IDC` bit 7, `QC` bit 27; AArch32-only `NZCV[31:28]` and reserved bits are `RES0` / RAZ-WI). `FPCR` is pinned to `0#64` (round-to-nearest-even `RNE`, `FZ = 0`, `DN = 0`, `AH = 0`, all exception trap enables `IOE..IDE = 0`): `MRS Xt, FPCR` reads `0`, `MSR FPCR, Xt` is a no-op when `Xt = 0`, and any nonzero write faults (`.Exception "unsupported FPCR value"`). FP semantics assume `FPCR = 0` at entry and on return from unverified code. `DCZID_EL0` reads `0x4`: `BS = 4`, i.e. 64-byte blocks, and `DZP = 0`. Writing `DCZID_EL0`, or accessing any other system register, faults. |
| Traps | `UDF #imm16` (`imm16 ≠ 0`); `SVC #imm ≠ 0` | `.Exception` (`"udf"` / `"unmodeled syscall (svc)"`). The all-zero word (`UDF #0`) deliberately decodes to `none`, because zero-filled extern-stub slots and padding rely on `decode 0 = none`. Both outcomes stop execution. |
| Linux syscalls | `SVC #0` with `X8` ∈ {`fcntl` (`F_GETFD = 1` returns `1` if `cloexec` else `0` and `F_SETFD = 2` sets `cloexec := (arg &&& 1) != 0` and returns `0` on open `.localFile` or `.localDir` descriptors; `-EBADF` on negative/closed fds; `.Exception` fail-closed on any other `cmd`, unmodeled stdio, or other descriptor kinds), `ioctl` (`FIOCLEX` / `FIONCLEX` set / clear `cloexec` and return `0` on open `.localFile` or `.localDir` descriptors; `FIONREAD` stores the 32-bit `i_size - f_pos` at `arg` on `.localFile` or returns `-EFAULT` if `arg` is not writable; terminal-only `'T'` commands outside the generic `do_vfs_ioctl` set (`isTtyOnlyIoctl`, e.g. `TCGETS`) return `-ENOTTY` on `.localFile`; `-EBADF` on negative/closed fds; `.Exception` fail-closed on every other command (`FIONBIO`, `FIOASYNC`, `FIOQSIZE`, `FIGETBSZ`, `FS_IOC_*`, ...), unmodeled stdio, or other descriptor kinds), `openat` (`dfd = AT_FDCWD` only; validates `flags` via `checkOpenFlags` before reading the path string, normalizes relative `.` and repeated `'/'` segments into canonical `FsPath` keys via `normalizePath`, fails closed with `.Exception` on non-`AT_FDCWD` `dfd`, leading `'/'`, `".."` segments, or missing-file `O_CREAT` without `0600` (`S_IRUSR \| S_IWUSR`) mode bits, treats `"."` as a directory, walks strict ancestor components left-to-right via `strictAncestorWalkErrno?` so missing parent/ancestor directories return `-ENOENT`, regular-file parent/ancestor components return `-ENOTDIR`, and any component longer than `NAME_MAX = 255` bytes returns `-ENAMETOOLONG` (checking `O_CREAT` + trailing `'/'` → `-EISDIR` before final-segment `NAME_MAX` per `fs/namei.c:4707`), opens existing `.dir` entries with `O_RDONLY` and without `O_CREAT`/`O_TRUNC` as `.localDir` descriptors while returning `-EISDIR` on write/`O_CREAT`/`O_TRUNC` and `-EEXIST` on `O_CREAT \| O_EXCL` without trailing slash, and logs `TraceEvent.fileChanged` on regular-file `O_CREAT`/`O_TRUNC`, including `O_RDONLY \| O_TRUNC`), `close` (closes `.localFile` and `.localDir` descriptors), `lseek` (`SEEK_SET`/`SEEK_CUR`/`SEEK_END` below `FS_SAFE_MAX_FILESIZE = 0xffffffff` and past-EOF `SEEK_DATA`/`SEEK_HOLE` returning `-ENXIO` when `offset ≥ i_size` on `.localFile` descriptors, failing closed with `.Exception` on `newOff ≥ FS_SAFE_MAX_FILESIZE`, negative or in-bounds `SEEK_DATA`/`SEEK_HOLE` `offset < i_size`, `.stdio`, or `.localDir`), `read` (`.localFile` and `.stdio` `stdin` up to `MAX_RW_COUNT = 0x7ffff000`, enforcing `access_ok` within `USER_VA_LIMIT` including `count = 0`, `-EINVAL` via `rw_verify_area` on `.localFile` when `desc.offset + count > MAX_LFS_FILESIZE`, and lazy page-fault checks on the `chunk.length` bytes transferred so EOF returns `0` without faulting, plus `-EISDIR` on `.localDir` after `access_ok`; `count > MAX_RW_COUNT` returns a short `MAX_RW_COUNT`-clamped transfer; `.Exception` when `chunk` faults after a writable prefix), `write` (up to `MAX_RW_COUNT = 0x7ffff000`, enforcing `access_ok` within `USER_VA_LIMIT` including `count = 0` no-op without file padding, `-EINVAL` via `rw_verify_area` when `count > 0` and `desc.offset + count.toNat > MAX_LFS_FILESIZE`, `-EFAULT` when the first byte is unreadable (`!allPerm (·.r) buf 1`), `count > MAX_RW_COUNT` returns a short `MAX_RW_COUNT`-clamped transfer; `.Exception` when `buf` faults after a readable prefix or a file write exceeds `FS_SAFE_MAX_FILESIZE = 0xffffffff` or `MAX_LFS_FILESIZE`, and `-EBADF` on `.localDir`), `readv` / `writev` (sequential `read` / `write` per `iovec` segment; `-EINVAL` on `iovcnt > UIO_MAXIOV` or a negative `iov_len`, `-EFAULT` on an unreadable `iovec` array; `.Exception` when the total exceeds `MAX_RW_COUNT` or a later segment fails after partial progress), `pread64` (`.localFile` only up to `MAX_RW_COUNT = 0x7ffff000`, enforcing `access_ok` within `USER_VA_LIMIT` before `-EINVAL` via `rw_verify_area` when `pos + count > MAX_LFS_FILESIZE`, and lazy page-fault checks on `chunk.length`, clamping `count > MAX_RW_COUNT` to a short transfer; `.Exception` on partial-fault short reads or `.stdio`/`.localDir`), `ppoll` (**`std`-startup `POLLNVAL` probe only** on `fd ∈ {0, 1, 2}` with `events = 0`, zero timeout, null `sigmask`, and fixed `nfds ≤ 1024`; writes `POLLNVAL` for closed fds and `revents = 0` for open `.stdio`/`.localFile` fds without modeling `POLLHUP`/`POLLERR`, failing closed on other fds/events/timeouts/sigmasks), `fstat` (`encodeLinuxStat` on `.localFile` and `.localDir` with `0644` regular file / `0755` empty-`tmpfs` directory metadata), `exit`, `exit_group`, `set_tid_address`, `getpid`, `gettid` (return `SIM_TID = 1`), `rt_sigprocmask` (`sigsetsize == 8`, `how ∈ {0, 1, 2}`; validates non-wrapping memory access, zero-fills `oldset` when the effective blocked mask stays `0`, and fails closed with `.Exception` on `SIG_BLOCK`/`SIG_SETMASK` with any blockable signal bit set), `sigaltstack` (`__NR_sigaltstack = 132`: queries and updates the 24-byte `stack_t` in `State.sigAltStack` with 32-bit `ss_flags` at `+8` ignoring caller padding at `+12..+15` and zeroing `+12..+15` in `uoss`, `(sp, sp + size]` `onSigStack` `-EPERM` suppressed under `SS_AUTODISARM`, `SS_DISABLE` skipping `MINSIGSTKSZ` even with non-zero `ss_size`, AArch64 `MINSIGSTKSZ = 5120` `-ENOMEM` except for the Linux unchanged-settings early return when the raw recorded `(sp, size, ss_flags)` already equals the request (so a fresh process's `sigaltstack(&{0, 0, 0}, _)` returns `0`), and post-commit `uoss` `-EFAULT` ordering), `rt_sigaction` (per-signal `SIG_DFL` / `SIG_IGN` queries and updates across signals `1..64` in `State.sigActions`, plus recording custom user-space handlers strictly for synchronous fault signals `SIGBUS = 7` and `SIGSEGV = 11` without signal delivery—hardware faults always trap directly to `.Exception`; returns `-EINVAL` on invalid `sigsetsize`, out-of-range signal, or attempts to change `SIGKILL`/`SIGSTOP`, strips `SIG_UNBLOCKABLE_MASK` from `sa_mask`, masks stored `sa_flags` with the AArch64 `UAPI_SA_FLAGS = 0xDC000807`, and fails closed on custom handlers for all other signals), `tkill`, `tgkill` (`tid = 1` / `tgid = 1` with `SIGABRT = 6` sets fatal `ExecStatus.Signaled 6#7` under `SIG_DFL`—reported as exit status `134` with `signal = some 6`—or returns `0` under `SIG_IGN` without consulting the unmodeled signal mask; invalid arguments return `-EINVAL`; any other target, signal, or handler fails closed), `clock_gettime` (clocks `0..7`: queries `ts := s.oracle.clockGettime s.oracleIdx`, writes 16-byte little-endian `struct timespec` with `0 ≤ tv_nsec < 1_000_000_000` and arbitrary 64-bit `tv_sec`, advances `s.nextOracle`, and returns `0` with no cross-call monotonicity; `-EFAULT` if `!s.mem.canWrite tp 16`; `.Exception` if `clk.toNat > 7`), `sched_getaffinity`, `brk` (`addr = 0` queries `s.brk`; otherwise deterministic: returns old `s.brk` with memory unchanged if `addr < s.brkStart`, shrinking `[newPage, oldPage)` is not fully mapped, `newPage + BRK_GUARD_GAP > 2 ^ 48`, or `!s.mem.canMap` on `[oldPage, newPage + BRK_GUARD_GAP)`, transitions to `.OutOfMemory` if growing by `newPage - oldPage > s.physMemAvail`, and otherwise maps/unmaps whole 4 KiB pages via `mapZero`/`unmapWritable` while charging/refunding `s.physMemAvail`; note that `unmapWritable` conservatively leaves any `PROT_NONE` pages in the shrunk region as `some Perm.protNone`), `munmap` (deterministic success on page-aligned non-frozen ranges within `2 ^ 48`, allowing unmapped holes and refunding `s.mem.countRw addr size` to `s.physMemAvail`; `-EINVAL` on misalignment/`len = 0`/overflow; `.Exception` on frozen memory; **modeling caveat**: does not model Linux's possible `-ENOMEM` when an interior `munmap` splits a VMA and `mm->map_count` reaches `vm.max_map_count`, whereas whole-VMA unmaps and one-sided trims never increase `map_count`), `mremap` (`MREMAP_MAYMOVE` on a uniform `Perm.rw` range within `2 ^ 48`: returns `-EINVAL` on misalignment/`new_size = 0`/overflow and `-EFAULT` on completely unmapped ranges, fails closed on `old_size = 0`, other flags, frozen bytes, or mixed permissions, returns `-ENOMEM` when `s.oracle.mremapFail s.oracleIdx` holds or no free gap of `pageAlignUp new_size` bytes exists after unmapping the old range, transitions to `.OutOfMemory` if `newAligned > s.physMemAvail + oldAligned`, and otherwise places the resized mapping via `sanitizeMmapAddr` on `s.oracle.mmap s.oracleIdx`, preserving `min oldAligned newAligned` bytes, zero-filling growth, and updating `s.physMemAvail`; **modeling caveat**: treats `[oldAddr, oldAddr + oldAligned)` as a single VMA, whereas Linux returns `-EFAULT` across adjacent unmerged VMAs, does not model VMA-split `vm.max_map_count` refusal on shrink, and re-places shrunk ranges via `sanitizeMmapAddr` rather than shrinking strictly in place), `mmap` (anonymous private `MAP_PRIVATE \| MAP_ANONYMOUS` (`0x22`), `MAP_PRIVATE \| MAP_ANONYMOUS \| MAP_STACK` (`0x20022`, mapped to advisory `VM_NOHUGEPAGE`, keeping `MAP_FIXED \| MAP_STACK = 0x20032` fail-closed), or `MAP_PRIVATE \| MAP_ANONYMOUS \| MAP_FIXED` (`0x32`) with `PROT_READ \| PROT_WRITE` or `PROT_NONE` within the 48-bit Linux user VA space `base + size ≤ 2 ^ 48`, charging `size` from `s.physMemAvail` for `PROT_READ \| PROT_WRITE` and `0` for `PROT_NONE`; without `MAP_FIXED`, sanitizes `s.oracle.mmap s.oracleIdx` via `sanitizeMmapAddr`—falling back to `findUnmappedArea` in `[MMAP_MIN_ADDR, 2 ^ 48)` when the oracle candidate is invalid or collides—and transitions to `.OutOfMemory` when no free gap of `size` bytes exists or `s.physMemAvail < size`; with `MAP_FIXED` (`0x32`), replaces the non-frozen range at a page-aligned `addr ≥ MMAP_MIN_ADDR = 65536` without consulting the oracle—installing zero-filled `PROT_NONE` pages (refunding `reclaimed := s.mem.countRw addr size` to `s.physMemAvail`) or zero-filled `PROT_READ \| PROT_WRITE` pages (transitioning to `.OutOfMemory` if `size > s.physMemAvail + reclaimed`, else setting `s.physMemAvail := s.physMemAvail + reclaimed - size`)—and raises `.Exception` on frozen memory or invalid fixed addresses; **modeling caveat**: `Oracle` has no `mmapFail` bit, so non-`MAP_FIXED` `mmap` assumes `RLIMIT_AS` and `vm.max_map_count` are not reached), `mprotect` (`PROT_NONE` (`some Perm.protNone = some ⟨false, false, false⟩`) ↔ `PROT_READ \| PROT_WRITE` (`some Perm.rw`) on mapped non-frozen ranges within `2 ^ 48`, charging `size - s.mem.countRw addr size` from `s.physMemAvail` on `PROT_READ \| PROT_WRITE` promotion—or transitioning to `.OutOfMemory` if insufficient—and refunding `0` on `PROT_NONE` demotion; `-EINVAL` on misalignment; `-ENOMEM` on completely unmapped (`canMap`) ranges; `.Exception` on partially mapped ranges mixing mapped and unmapped bytes, ranges past `2 ^ 48`, frozen memory, or other `prot`), `madvise` (`MADV_DONTNEED` zero-fills mapped non-frozen private anonymous ranges and clears `lazyFree`; `MADV_FREE` marks mapped non-frozen private anonymous ranges `lazyFree := true`; `MADV_NORMAL`/`RANDOM`/`SEQUENTIAL`/`WILLNEED`/`HUGEPAGE`/`NOHUGEPAGE`/`DONTDUMP`/`DODUMP` are no-ops, with `[INTENTIONAL_SCOPE]` assuming `CONFIG_TRANSPARENT_HUGEPAGE=y` on normal user memory for `MADV_HUGEPAGE = 14` / `MADV_NOHUGEPAGE = 15`; `-EINVAL` on misalignment or 64-bit wrap; `-ENOMEM` on completely unmapped ranges; `.Exception` on partially mapped ranges, non-anonymous `MADV_DONTNEED`/`MADV_FREE`, ranges past `2 ^ 48`, frozen memory, or other `advice`), `getrandom` (reads low 32-bit `W2` as `unsigned int flags`; returns `-EINVAL` with no buffer write and no `oracleIdx` advance if `flags &&& ~~~0x7#32 != 0#32`, `flags &&& 0x6#32 == 0x6#32` (`GRND_INSECURE \| GRND_RANDOM`), or `count.toNat > MAX_RW_COUNT` (`0x7ffff000`); returns `-EFAULT` if `count > 0` and `!s.mem.canWrite buf count.toNat`; otherwise fills all `count` bytes from `s.oracle.getrandom s.oracleIdx`, advances `s.nextOracle`, and returns `count`, assuming an initialized kernel CRNG so `GRND_NONBLOCK` never returns `-EAGAIN`; **modeling deviation**: real Linux clamps `count` to `MAX_RW_COUNT`, whereas the model rejects `count > MAX_RW_COUNT` with `-EINVAL` to avoid short reads, affecting only requests ≥ ~2 GiB)} | Cooperative local-disk `State.fs` (`FsState` / `FdEntry` / `FdKind`: `.localFile` and `.localDir` entries in `entries` plus out-of-band `FsState.stdin` for `.stdio` descriptors `0..2`, keeping `"<stdin>"` / `"<stdout>"` / `"<stderr>"` out of the `openat` path namespace) for file-system syscalls, trace output for `stdout`/`stderr` and `TraceEvent.fileChanged`, `-EINVAL` for invalid syscall flags (e.g. `getrandom`) or `write` past `MAX_LFS_FILESIZE`, and fail-closed `.Exception` traps on unmodeled syscalls (`newfstatat`, etc.), `fcntl` commands, non-`AT_FDCWD` `dfd` / leading `'/'` / `".."` paths, `pread64`/`lseek` on `.localDir`, `mmap`/`mprotect`/`madvise` modes, clock IDs, unmodeled stdio descriptors, or unsupported non-`.localFile` descriptor operations. See [`../Syscalls/README.md`](../Syscalls/README.md). |

**What this buys and what it does not.** A theorem proved against this
model holds for single-threaded executions of the code, or more generally
for executions in which no other agent touches the memory the proof is
about. It does **not** establish data-race freedom, lock correctness under
contention, or anything about weak-memory reordering.

## ASL Coverage Table (Implemented / Fail-Closed / Not Decoded)

The table below summarizes all 49 instruction groups (80 sequential decode branches) in [`Decode.lean`](Decode.lean) and [`Eval.lean`](Eval.lean) against the official ARM A-Profile A64 Machine-Readable XML & ASL 1.0 specification (`ISA_A64_xml_A_profile-2026-06`).

| Group | Family / Mnemonics | Representative XML IDs | Status (`Implemented` / `Fail-Closed` / `Not Decoded`) |
| :--- | :--- | :--- | :--- |
| **1, 1b, 1c, 1d** | `NOP`, `HINT #imm7`, `SVC #imm16`, `BRK #imm16`, `UDF #imm16`, `DC ZVA` | `NOP_HI_hints`, `SVC_EX_exception`, `BRK_EX_exception`, `UDF_only_perm_undef`, `DC_SYS_cr_systeminstrs` | **Implemented** (`NOP`/`HINT` advance `PC`; `DC ZVA` zeroes 64B cacheline; `SVC #0` runs `execSyscall`; `BRK #1` sets `.Exited 101#64` and `BRK #imm16 ≠ 1` sets `.Halted`); **Fail-Closed** (`UDF #imm16 ≠ 0` and `SVC #imm16 ≠ 0` set `.Exception`; `UDF #0` = `0x00000000` is **Not Decoded** (`none`)) |
| **2–6** | PC-rel `ADR`/`ADRP`, `ADD`/`ADDS`/`SUB`/`SUBS` (imm), Logical (imm), `MOVN`/`MOVZ`/`MOVK`, Bitfield `SBFM`/`BFM`/`UBFM`, `EXTR` | `ADR_only_pcreladdr`, `ADD_32_addsub_imm`, `AND_32_log_imm`, `MOVZ_32_movewide`, `SBFM_32M_bitfield`, `EXTR_32_extract` | **Implemented**; reserved bitmask triples (`DecodeBitMasks`), `sh = 1` in `MOV*`, and 32-bit `N = 1` / `imms<5> = 1` / `immr<5> = 1` are **Not Decoded** (`none`) |
| **7–11** | Branches `B`/`BL`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`, `B.cond`, `BR`/`BLR`/`RET` | `B_only_branch_imm`, `BL_only_branch_imm`, `CBZ_32_compbranch`, `TBZ_only_testbranch`, `B_only_condbranch`, `BR_64_branch_reg` | **Implemented**; `B.cond` with `o1 = 1` or `o0 = 1`, and `BR`/`BLR`/`RET` with non-zero `op2`/`op3`/`op4` (including non-hint `PAC`/`RETAA`/`RETAB`) are **Not Decoded** (`none`) |
| **12–17** | Shifted/Extended `AND`/`BIC`/`ORR`/`ORN`/`EOR`/`EON`/`ANDS`/`BICS`, `ADD`/`ADDS`/`SUB`/`SUBS`, `ADC`/`ADCS`/`SBC`/`SBCS`, `CCMN`/`CCMP`, `CSEL`/`CSINC`/`CSINV`/`CSNEG` | `AND_32_log_shift`, `ADD_32_addsub_shift`, `ADD_32_addsub_ext`, `ADC_32_addsub_carry`, `CCMP_32_condcmp_reg`, `CSEL_32_condsel` | **Implemented**; 32-bit `imm6 ≥ 32`, `ADD`/`SUB` shifted `ROR` (`shift = 11`), `ADD`/`SUB` extended `imm3 > 4`, and reserved `o2`/`o3` bits are **Not Decoded** (`none`) |
| **18–21** | 1-Source (`RBIT`, `REV16`, `REV32`, `REV`, `CLZ`, `CLS`), `CRC32{B,H,W,X}`/`CRC32C*`, 2-Source (`UDIV`, `SDIV`, `LSLV`, `LSRV`, `ASRV`, `RORV`), 3-Source (`MADD`, `MSUB`, `SMADDL`, `SMSUBL`, `SMULH`, `UMADDL`, `UMSUBL`, `UMULH`) | `RBIT_32_dp_1src`, `CRC32B_32C_dp_2src`, `UDIV_32_dp_2src`, `MADD_32A_dp_3src`, `SMADDL_64WA_dp_3src`, `SMULH_64_dp_3src` | **Implemented**; 32-bit `REV64`, 64-bit `CRC32B`/`H`/`W`, and unallocated `opcode` values are **Not Decoded** (`none`) |
| **21b, 22, 23–25** | GPR Pairs (`LDNP`/`STNP`, `LDP`/`STP`/`LDPSW`), `LDR*`/`STR*` (unsigned imm, unscaled `LDUR`/`STUR`, pre/post-index, register offset), Literal `LDR`/`LDRSW`/`PRFM` | `LDNP_32_ldstnapair_offs`, `LDP_32_ldstpair_post`, `LDR_32_ldst_pos`, `LDUR_32_ldst_unscaled`, `LDR_32_ldst_immpost`, `LDR_32_ldst_regoff`, `LDR_32_ldst_pcrel` | **Implemented**; `CONSTRAINED UNPREDICTABLE` load-pair overlap (`Rt == Rt2`) and writeback base overlap (`Rn == Rt`/`Rt2` with `Rn ≠ 31`), `option<1> = 0`, and unallocated `size:opc` combinations are **Not Decoded** (`none`) |
| **22b–22f, 26–26f** | Prefetch (`PRFM` imm/reg/lit, `PRFUM`), Exclusives (`LDXR*`/`LDAXR*`, `STXR*`/`STLXR*`, `LDXP*`/`LDAXP*`, `STXP*`/`STLXP*`), Ordered (`LDAR*`/`STLR*`, `LDAPR*`, `LDAPUR*`/`STLUR*`), LSE Atomics (`CAS*`, `CASP*`, `LD<OP>*`, `SWP*`, `ST<OP>*`) | `PRFM_P_ldst_pos`, `LDXR_LR32_ldstexcl`, `STXR_SR32_ldstexcl`, `LDXP_LP32_ldstexcl`, `CAS_C32_comswap`, `CASP_CP32_comswappr`, `LDADD_32_memop`, `LDAPUR_32_ldapstl_unscaled` | **Implemented** (deterministic single-thread atomic semantics); `CONSTRAINED UNPREDICTABLE` overlaps (`Rs == Rt`/`Rt2`, `Rs == Rn && Rn ≠ 31`, `LDXP Rt == Rt2`, odd `CASP` registers) are **Not Decoded** (`none`) |
| **27–28** | System Registers (`MRS`/`MSR` `TPIDR_EL0`, `NZCV`, `FPSR`, `FPCR`, `DCZID_EL0`) & Barriers (`CLREX`, `DSB`, `DMB`, `ISB`) | `MRS_RS_systemmove`, `MSR_SR_systemmove`, `CLREX_BN_barriers`, `DSB_BO_barriers`, `DMB_BO_barriers`, `ISB_BI_barriers` | **Implemented** for `TPIDR_EL0`, `NZCV`, `FPSR` (masked to `0x0800009f`), `FPCR` (reads `0`; writes succeed iff `Xt = 0`, else **Fail-Closed** `.Exception`), `DCZID_EL0` (read-only), and barriers; **Fail-Closed** (`.Exception`) for all other `MRS`/`MSR` system registers |
| **25b, 28b, 29–32** | SIMD&FP Loads/Stores (`LDR` lit, `LDNP`/`STNP`, `LDP`/`STP`, `LDR`/`STR`/`LDUR`/`STUR` `B`/`H`/`S`/`D`/`Q`, multi-structure `LD1`/`ST1` 1–4 regs, `LD1R`, single-lane `ST1` post-index) | `LDR_S_ldst_pcrel`, `LDNP_S_ldstnapair_offs`, `LDP_S_ldstpair_post`, `LDR_B_ldst_pos`, `LD1_asisdlse_R1_1v`, `LD1R_asisdlso_R1`, `ST1_asisdlso_B1_1b` | **Implemented**; `CONSTRAINED UNPREDICTABLE` load-pair overlap (`Vt == Vt2`) is **Not Decoded** (`none`); reserved `LD1` single-reg `size<1> = 1 && S = 1` or `ST1` single-lane reserved bits are **Fail-Closed** (`.Exception`); interleaved `LD2`–`LD4`/`ST2`–`ST4` are **Not Decoded** (`none`) |
| **33, 41b–41h** | Crypto & Hash (`AESE`, `AESD`, `AESMC`, `AESIMC`, `PMULL`/`PMULL2`, `SHA1C`/`P`/`M`/`H`/`SU0`/`SU1`, `SHA256H`/`H2`/`SU0`/`SU1`, `SHA512H`/`H2`/`SU0`/`SU1`, `EOR3`, `BCAX`, `RAX1`, `XAR`) | `AESE_B_cryptoaes`, `PMULL_asimddiff_L`, `SHA1C_QSV_cryptosha3`, `SHA256H_QQV_cryptosha3`, `SHA512H_QQV_cryptosha512_3`, `EOR3_VVV16_crypto4`, `XAR_VVV2_crypto3_imm6` | **Implemented**; SM3/SM4 cryptographic encodings are **Not Decoded** (`none`) |
| **34, 42–49** | Scalar IEEE-754 Binary32/Binary64 FP (`FMOV` GPR↔vec/imm, `FABS`, `FNEG`, `FSQRT`, `FCVT`, `FRINTN`/`P`/`M`/`Z`/`A`/`X`/`I`, `FMUL`, `FDIV`, `FADD`, `FSUB`, `FMAX`, `FMIN`, `FMAXNM`, `FMINNM`, `FNMUL`, `FCMP`/`FCMPE`, `FCCMP`/`FCCMPE`, `FCSEL`, `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB`, fixed/int `SCVTF`/`UCVTF`/`FCVT*S`/`FCVT*U`) | `FMOV_32S_float2int`, `FADD_S_floatdp2`, `FMADD_S_floatdp3`, `FCMP_S_floatcmp`, `FCCMP_S_floatccmp`, `FCSEL_S_floatsel`, `FCVTZS_32S_float2int`, `SCVTF_S32_float2fix` | **Implemented** for `binary32` (`ftype = 00`) and `binary64` (`ftype = 01`) plus `FMOV Xd, Vn.D[1]` / `Vd.D[1], Xn`, including cumulative `FPSR` exception flags (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`); **Fail-Closed** (`.Exception`) for `FP16` (`ftype = 11`), reserved `ftype = 10`, same-size `FCVT`, `FJCVTZS`, and reserved sub-opcodes |
| **35–41** | AdvSIMD Vector Integer, Shifts, Modified Imm, Permutes & Reductions (`simdImmShift`, `simdInsDup`, `simdThreeSame`, `simdTwoRegMisc`, `simdAcrossLanes`, `simdPermute`, `simdExt`, `simdTbl`, `simdAddpScalar`) | `MOVI_asimdimm_N_b`, `SHL_asimdshf_R`, `INS_asimdins_IV_v`, `ADD_asimdsame_only`, `REV64_asimdmisc_R`, `ADDV_asimdall_only`, `ZIP1_asimdperm_only`, `EXT_asimdext_only`, `TBL_asimdtbl_L1_1` | **Implemented** across all integer lane widths (`8B`/`16B`/`4H`/`8H`/`2S`/`4S`/`1D`/`2D`), including cumulative `FPSR.QC` (`bit 27`) saturation updates; **Fail-Closed** (`.Exception`) on architecturally `UNDEFINED` `Q`/`size`/`imm` combinations and unmodeled vector FP (`FADD`, `FMUL`, `FCMEQ`, etc.) |

### Codec Canonicalization & Fail-Closed Guard Conventions

To maintain the kernel-checked decoder/encoder round-trip theorem (`Arm64.encode_of_decode : decode bs = some p → encode p = some bs`), `Arm64.decode` enforces two canonicalization guards where the ARM encoding permits redundant bit encodings of the same architectural operation:
1. **Logical Immediate Bitmasks (`decodeBitMasksValid`)**: Requires canonical rotate `immr < esize` so that each 32-bit or 64-bit periodic bitmask has a unique `(N, immr, imms)` representation.
2. **8-Bit Register-Offset Addressing (`LDRB`/`STRB`/`LDRSB` and SIMD `LDR`/`STR B`)**: When `size = 00` (`scale = 0`), `S = 0` (omitted shift) and `S = 1` (explicit `#0` shift) both compute `shift = 0`. `Decode.lean` accepts canonical `S = 0` (which compilers and assemblers emit when no `#0` shift is written) and rejects `S = 1` (`none`, fail-closed) so `MemExtendAmount.E0` / `amount = 0` has a unique 32-bit encoding.
3. **Hint-Space Prefetch Overlap (`PRFM (register)` / `RPRFM`)**: In group 22d (`0xf8a00800`), `Rt = 11xxx` with `option = 011, S = 0` is `RPRFM` (`RPRFM_R_ldst_regoff`), which like `PRFM (register)` (`PRFM_P_ldst_regoff`) is an architectural prefetch hint (`PC += 4` with no memory or alignment side effects).

## Out of scope (intentionally)

- Concurrency and the Arm weak memory model: multi-copy atomicity, barrier
  ordering, exclusive-monitor loss, ordering of `LDAPR` vs `LDAR`.
- EL1–EL3 / privileged ISA: page tables, exception vectors, `ERET`, privileged
  system registers, and `DC`/`IC`/`TLBI` other than `DC ZVA`.
- SVE/SVE2/SME.
- SM3/SM4 cryptographic instructions, and actual pointer authentication
  signing/authentication (`PACIA`/`AUTIA` outside hint space, `RETAA`, …).
- Half-precision/BF16 arithmetic, vector floating-point instructions,
  non-default `FPCR` control modes (directed rounding modes `RMode ≠ 0`,
  flush-to-zero `FZ`/`FZ16`, default-NaN `DN`, alternate half-precision `AHP`,
  `FEAT_AFP`), and trapped floating-point exceptions
  (`FPCR.IOE`/`DZE`/`OFE`/`UFE`/`IXE`/`IDE`). All scalar FP semantics assume
  `FPCR = 0` at entry and on return from unverified code, and `MSR FPCR` with
  any nonzero value fails closed (`.Exception "unsupported FPCR value"`). FPSR
  cumulative flags (`IOC`, `DZC`, `OFC`, `UFC`, `IXC`, `IDC`, `QC`) are modeled
  exactly under untrapped `FPCR = 0`.

Gaps that are *not* listed above are simply not implemented yet. Add them
following the pattern in [`Decode.lean`](Decode.lean) and [`Eval.lean`](Eval.lean):
- Append new `Instr` constructors and `execInst` arms at the end, so the
  case indices in `ProofLib/Invariant.lean` stay stable.
- Extend the untrusted encoder and the `encode_of_decode` round-trip proof in
  `Arm64/Testing/Arm64EncoderDecoder/`.
- Add golden or differential tests in [`Arm64/Testing/`](../../Testing/README.md).
