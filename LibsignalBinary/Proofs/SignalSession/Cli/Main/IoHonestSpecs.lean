/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Honest `write_file` / `write_stdout` Hook Contracts
(`LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs`)

- **Role**: `Role::Proof` (outside the TCB). Untrusted groundwork for #1255 (HOOKS-PREP); nothing
  here is used by a headline statement yet, and no trusted file changes.
- **Overview**:
  The active budget-threaded consumer specs `SpecsPlacedBudget.writeFileSpecPlaced` and
  `SpecsPlacedBudget.writeStdoutSpecPlaced` are proved only for the idealized hooks
  `CliRun.writeFileHook` / `CliRun.writeStdoutHook` (`HookOk`, via `H sym = some <hook>`). The
  compiled `signal_session_io::write_file` / `write_stdout` (`third_party/libsignal/
  libsignal-session/cli/io/src/lib.rs:222`, `:285`) does not meet them as stated: it uses a
  `4096`-byte stack path buffer, opens a file descriptor, and is bounded by the kernel's
  `MAX_LFS_FILESIZE`. This file states the honest twins the real code is expected to meet, so that
  consumers can later depend only on `HookSat H sym <honestSpec>`:
  1. `writeFileHonestCore` / `writeFileSpecPlacedSat` (row 1a of the HOOKS-PREP plan);
  2. `writeStdoutHonestCore` / `writeStdoutSpecPlacedSat` (row 1b).
  Each honest spec adds premises to `pre` (stack floor, closed descriptors, length bound) and only
  ADDS conjuncts to `post` (every old `post` conjunct is kept verbatim), so the honest `post`
  projects onto the old one and only the new `pre` premises need re-anchoring at call sites.
- **Real-bytes status**: NO whole-function real-bytes proof of either function exists yet (today's
  ELF reaches `write_file` / `write_stdout` through zero stubs; real-code proofs require the stock
  relink, same as `memset` / `memcpy`). Only the musl syscall pieces are proved on rustc
  `self-contained/libc.a` bytes in the engine:
  `VerifiedLibraries/Musl/Proofs/SyscallProof.lean` (`muslClose48Spec` `:686`,
  `muslWriteFile32Spec` `:879`, `muslOpenCreateTruncSpec` `:1477`) and
  `VerifiedLibraries/RustStd/Proofs/StdoutRaw.lean` (`muslWriteStdout32Spec` `:46`).
- **Statement skeletons** for the follow-up proofs are in the comment block at the end of the file.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession.Cli.MainHops (IoModel WriteFileGhost WriteStdoutGhost)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (allocFailedEvent)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (WriteFileEnv WriteStdoutEnv withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)

/-! ## 1. Stack floors -/

/-- Conservative stack floor (bytes below `sp`) for the compiled `write_file`.
    The real code keeps a `4096`-byte NUL-terminated copy of the path on its stack (`cpath`,
    `lib.rs:222`) plus its own frame and the musl `open` / `write` / `close` / `__errno_location`
    frames; the HOOKS-PREP plan estimates about `4304` bytes in total [E, not measured]. `8192` is a
    deliberately conservative named value over that estimate, still `≤ extHookStack` (`16384`), the
    hook stack every current consumer passes. A whole-function real-bytes proof will pin the exact
    figure; lowering this constant later only weakens the premise, and raising it up to
    `extHookStack` is also free for consumers. -/
def writeFileStackFloor : Nat := 8192

/-- Conservative stack floor (bytes below `sp`) for the compiled `write_stdout`
    (`write_all_fd::<true>(1, bytes)` plus musl `write` and `__errno_location`); the HOOKS-PREP plan
    estimates about `96` bytes [E, not measured]. `1024` is a deliberately conservative named value,
    `≤ extHookStack`. -/
def writeStdoutStackFloor : Nat := 1024

theorem writeFileStackFloor_le_extHookStack : writeFileStackFloor ≤ extHookStack := by decide

theorem writeStdoutStackFloor_le_extHookStack : writeStdoutStackFloor ≤ extHookStack := by decide

/-! ## 2. `write_file` (row 1a) -/

/-- **Honest core contract of the compiled `signal_session_io::write_file(path, bytes)`**
(`x0..x3`; `Result<(), IoError>` in `x0`: `0` Ok, `1` Err), the twin of
`SpecsPlacedBudget.writeFileSpecPlaced` with exactly these deltas.

What the real code does (`lib.rs:222-282`): it copies the path byte by byte (through `black_box`)
into a `4096`-byte stack buffer, returns `Err` if the path is `≥ 4096` bytes or contains an
interior NUL, then calls musl `open(cpath, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0o666)` with an
`EINTR` retry loop, writes all bytes with `write_all_fd::<false>` (`EINTR` retry, chunks of
`0x7fff_f000` bytes, `n == 0` is `Err`), and closes the descriptor on every exit after `open`. It
makes no allocation. Errors are read with `__errno_location` (thread-local `errno`).

`pre` deltas (absent from the idealized hook's spec):
* `writeFileStackFloor ≤ stk`: the `4096`-byte stack path buffer and the musl frames
  (`writeFileStackFloor`); the old spec allows any `stk`, including `0`.
* `FdsGe3Closed s.fs`: musl `open` takes the lowest free descriptor `≥ 3`
  (`FsState.allocFd`). With every slot in `[3, 2^31)` closed it gets descriptor `3`
  (`allocFd_eq_three_of_fds3_none`), so `open` cannot fail with `EMFILE` (which the old spec's
  `io.wr` outcome does not model). This premise is honest but stronger than the minimum the real
  code needs (`s.fs.allocFd.isSome`); `FdsGe3Closed` is kept for simplicity to match the Spine-B
  descriptor invariant.
* `x.bs.length < 2 ^ 63`: after `O_TRUNC` the offset is `0`, and the engine's regular-file
  `write` rejects `offset + count > MAX_LFS_FILESIZE = 2^63 - 1` with `EINVAL`
  (`Arm64/Trusted/ISA/State.lean:291`, `Syscalls/Fs/ReadWrite.lean`), which the old spec's `io.wr`
  outcome does not model.

`post` deltas (all additive; the old conjuncts are kept verbatim and first):
* `sf.fs.fds = s0.fs.fds`: `open` allocates descriptor `3` and `close` sets it back to `none` (and
  a failed `open` allocates nothing), so the descriptor table is unchanged on every return.
* `FsTraced (·.isFsChange) s0 sf`: the trace only grows, and `fs.files` changes only together
  with a file event (`openat`'s `fileChanged` on create/truncate, the `writeByte (.fd 3)` bytes of
  the regular-file `write`). The trace stays prefix-only (no exact event list) for two reasons:
  first, the idealized `writeFileHook` logs `fileChanged p` before its ancestor / directory checks,
  i.e. also on the `ENOENT` / `EISDIR` error paths where the real `openat` logs nothing; second,
  the real `write` also logs `writeByte (.fd fd)` events for `x.bs`, which the hook never emits.
* `allocFailedEvent ∉ s0.trace → allocFailedEvent ∉ sf.trace`: the function makes no allocation,
  so it never logs `rust_alloc_failed`.
* `VmPreserved s0 sf` is added by `writeFileSpecPlacedSat` (`withVmPreserved`).

Unchanged on purpose:
* `WriteFileEnv` (`SpecBudget.lean:840`) still over-approximates the allocation events (the real
  code has `evs = []`), so consumers' `FitsEnv` premises keep their shape.
* `x0 = 0#64` / `1#64` is kept as a full 64-bit value. That the compiled code clears the upper bits
  of `x0` for `Result<(), IoError>` is NOT verified yet [unverified]; the real-bytes proof must
  confirm it or this conjunct must weaken to the low byte.
* `errno`: on error paths the real code writes the thread-local `errno` cell. For an abstract
  `A : RustCliAllocBudget M` this spec cannot name that cell; in the concrete mallocng
  instantiation it is owned by `A.pool` (`CliIo/BridgePlaced.lean:161`, `pool_split_errno`), so no
  extra premise is added here (adding one would double-own the cell). Consequently, the real-bytes
  `HookSat` is proved per concrete `A` whose `A.pool` owns the `errno` cell, not for an arbitrary
  abstract `A`.

Not proved on real bytes yet (see the module docstring). -/
def writeFileHonestCore {M : AllocCostModel} (io : IoModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteFileGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ io.pathOk x.path ∧
      FitsEnv M lim st (WriteFileEnv x.path.length) ∧
      writeFileStackFloor ≤ stk ∧ FdsGe3Closed s.fs ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteFileEnv x.path.length evs ∧
        (match io.wr s0.fs.files x.path x.bs with
         | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
         | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
        s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ∧
        sf.fs.fds = s0.fs.fds ∧
        FsTraced (fun e => e.isFsChange = true) s0 sf ∧
        (allocFailedEvent ∉ s0.trace → allocFailedEvent ∉ sf.trace)⌝ ∗
        (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗
        A.pool lim (M.stepEvents evs st) sf

/-- **Honest `write_file` consumer contract**: `writeFileHonestCore` with `VmPreserved s0 sf` on
the normal return (`withVmPreserved`). The real code does not move `brk`, `tpidr_el0`,
`physMemAvail` or page permissions (no allocation, no `mmap`), and the descriptor table is
unchanged on return (so `FdsHiFrame` holds). Intended carrier shape:
`HookSat H lsWriteFileSym (writeFileSpecPlacedSat io A lim hookStack)`.
NOT proved on real bytes yet (module docstring). -/
def writeFileSpecPlacedSat {M : AllocCostModel} (io : IoModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteFileGhost × M.σ) :=
  withVmPreserved (writeFileHonestCore io A lim stk)

/-! ## 3. `write_stdout` (row 1b) -/

/-- **Honest core contract of the compiled `signal_session_io::write_stdout(bytes)`**
(`x0, x1`; `Result<(), IoError>` in `x0`), the twin of `SpecsPlacedBudget.writeStdoutSpecPlaced`
with exactly these deltas.

What the real code does (`lib.rs:285` = `write_all_fd::<true>(1, bytes)`, `lib.rs:133`): it calls
musl `write(1, …)` in chunks of at most `0x7fff_f000` bytes until all bytes are written (`EINTR`
retry, `n == 0` is `Err`, `EBADF` counts as `Ok`), with no allocation. The engine's `execWrite`
(`Syscalls/Fs/ReadWrite.lean:111`) on descriptor `1` does not consult the descriptor table: it
appends `TraceEvent.ofBytes .stdout chunk` and returns the count, leaving `fs` unchanged. So the
real loop appends exactly `TraceEvent.ofBytes .stdout x.bs` (chunk-wise concatenation; nothing for
an empty slice) and returns `Ok`.

`pre` deltas:
* `writeStdoutStackFloor ≤ stk`: the real frames need stack (about `96` bytes [E]); the old spec
  allows any `stk`, including `0`.
* `x.bs.length < 2 ^ 63`: Rust slice bound (`≤ isize::MAX`). Not required by the real loop (which
  chunks at `≤ 0x7fff_f000`, so the per-chunk `< 2 ^ 63` bound in `muslWriteStdout32Spec`,
  `StdoutRaw.lean:46`, always holds and `execWrite` on fd `1` has no size check); kept because it
  is harmless and free at M6 (`ownedBytes_unpack`, `outCap.toNat < 2 ^ 63`).

`post` deltas (additive; the old conjuncts are kept verbatim and first):
* `sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout x.bs` (exact trace) and `sf.fs = s0.fs`
  (the whole file system, not only `files`). Both hold for the engine's `write(1, …)` above and
  for `CliRun.writeStdoutHook`; together they imply the old prefix / stdout-stream conjuncts and
  also that no `rust_alloc_failed` event is logged.
* `VmPreserved s0 sf` is added by `writeStdoutSpecPlacedSat` (`withVmPreserved`).

Unchanged on purpose: `WriteStdoutEnv` (`SpecBudget.lean:889`) still over-approximates the
allocation events (the real code has `evs = []`); `x0 = 0#64` is kept as a full 64-bit value, and
that the compiled code clears the upper bits of `x0` is NOT verified yet [unverified]. On the paths
reachable here the real code does not write `errno` (no `EINTR` / `EBADF` arises for `write(1, …)`
in the engine), but `__errno_location` may still be called; see the `errno` note on
`writeFileHonestCore`.

Not proved on real bytes yet (see the module docstring). -/
def writeStdoutHonestCore {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteStdoutGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      FitsEnv M lim st WriteStdoutEnv ∧
      writeStdoutStackFloor ≤ stk ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteStdoutEnv evs ∧
        sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs ∧
        sf.trace = s0.trace ++ TraceEvent.ofBytes .stdout x.bs ∧
        sf.fs = s0.fs⌝ ∗
        (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

/-- **Honest `write_stdout` consumer contract**: `writeStdoutHonestCore` with `VmPreserved s0 sf`
on the normal return (`withVmPreserved`). Intended carrier shape:
`HookSat H lsWriteStdoutSym (writeStdoutSpecPlacedSat A lim hookStack)`.
NOT proved on real bytes yet (module docstring). -/
def writeStdoutSpecPlacedSat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (WriteStdoutGhost × M.σ) :=
  withVmPreserved (writeStdoutHonestCore A lim stk)

/-! ## 4. Statement skeletons for the follow-up proofs (comments only, nothing is assumed)

(a) Exact → Sat bridges (the idealized hooks meet the honest specs; note that the real-bytes
`HookSat` will instead be proved per concrete `A` whose `A.pool` owns the thread-local `errno`
cell via `pool_split_errno`, `CliIo/BridgePlaced.lean:161`):

```
theorem writeFileHook_ok_honestCore {M} (A : RustCliAllocBudget M) (lim) (stk) :
    HookOk writeFileHook (writeFileHonestCore cliIo A lim stk)
-- Weaken `pre` into `F3.HRead.ReadStdinBudgetPlaced.writeFileHook_ok_placed`, then strengthen the
-- `post` (merely dropping the 3 new `pre` conjuncts is not enough because the honest `post` is
-- stronger): on `writeFileHook s0` (`CliRun.lean:373`), the three extra `post` facts hold for
-- every `s0` (`fds` untouched via `setFile` / `appendTrace` / `unitResult`; `FsTraced` with
-- `d = []` or `d = [.fileChanged p]`; `allocFailedEvent ≠ .fileChanged p`).

theorem writeStdoutHook_ok_honestCore {M} (A : RustCliAllocBudget M) (lim) (stk) :
    HookOk writeStdoutHook (writeStdoutHonestCore A lim stk)
-- Weaken `pre` into `ReadStdinBudgetPlaced.writeStdoutHook_ok_placed`, and strengthen `post` using
-- `s0.mem.readBytes x.buf n = x.bs` derived from `x.buf ↦ₛ x.bs` in `pre` (`writeStdoutHook s0 =
-- unitResult true (s0.appendTrace (TraceEvent.ofBytes .stdout x.bs))`, `CliRun.lean:428`).

theorem hookSat_writeFileSpecPlacedSat_of_hook {M} {A} {lim} {stk} {H : LibsignalHooks}
    (h : H lsWriteFileSym = some writeFileHook) :
    HookSat H lsWriteFileSym (writeFileSpecPlacedSat cliIo A lim stk)
-- `SpecBudget.hookSat_withVmPreserved ⟨_, h, writeFileHook_ok_honestCore A lim stk⟩
--   (fun f hf s => by cases h.symm.trans hf; exact vmPreserved_writeFileHook s)`.
-- Same for `writeStdoutSpecPlacedSat` with `vmPreserved_writeStdoutHook`.
```

(b) Carrier twin and what the two live carriers need:

```
structure MainIoPlacedSat [LibsignalPlacement] {M} (A) (lim) (H) (io) (hookStack) : Prop where
  readStdin        -- unchanged from `SpecsPlacedBudget.MainIoPlaced`
  readFile         -- unchanged
  writeFile        : subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
                       (withLsRoCl lsmpl (writeFileSpecPlacedSat io A lim hookStack))
  writeStdout      : subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
                       (withLsRoCl lsmpl (writeStdoutSpecPlacedSat A lim hookStack))
  hWriteFileStack  : writeFileStackFloor ≤ hookStack
  hWriteStdoutStack : writeStdoutStackFloor ≤ hookStack
```
* `F3.HRead.ReadStdinBudgetPlaced.mainIoOfPlaced_withReadHooks` (`:2038`) and
  `Cli/Main/MainOkA1Placed.lean:101-127` (`writeFile_rocl_ok_of_lookup`, `IoHooksPlaced.lean:274`,
  `:283`): Sat twins take `HookSat H0 lsWriteFileSym (writeFileSpecPlacedSat …)` (resp. stdout)
  instead of `H0 lsWriteFileSym = some writeFileHook` (plus the stack-floor bounds when `stk` is
  generic, discharged by `decide` at `stk = extHookStack`), and build `writeFile` / `writeStdout`
  with `subroutine_ok_rocl_of_plain (ls_hook_ok_ultra_of_mem hsat …)` exactly as today
  (`ls_hook_placed_rocl_ok`, `ReadStdinBudgetPlaced.lean:2027`). The exact case is recovered with
  `hookSat_writeFileSpecPlacedSat_of_hook`.
* There is NO projection `MainIoPlacedSat → MainIoPlaced`: the honest `pre` is stronger. The honest
  `post` is never weaker (every old conjunct is kept), so post-side continuations (`hnext`) are
  unchanged; only the new `pre` premises re-anchor.

Consumer lemmas that must re-anchor the new `pre` premises (none needs a weaker `post`):
* `Main/Proofs/M5CallsPlacedBudget.m5_call_write_file_placed` (`:799`): needs
  `FdsGe3Closed s.fs`, `bs.length < 2 ^ 63`, `writeFileStackFloor ≤ hookStack`.
  - `writeFileStackFloor ≤ hookStack`: read from `MainIoPlacedSat.hWriteFileStack` (`m5` is generic
    in `hookStack`; concrete `hookStack = extHookStack` constructors discharge it by `decide` via
    `writeFileStackFloor_le_extHookStack`).
  - `FdsGe3Closed s.fs` after `run`: NOT available today. `Main/Proofs/M4PlacedBudgetFd.lean`
    threads `FdsGe3Closed` into `run`'s `pre` only (`runSpecTightPlacedPreFd`), and
    `SpecsPlacedBudget.runSpecPlaced`'s `post` states `sf.fs.files = s0.fs.files` but nothing on
    `fs.fds`. Needed: a `run` post twin carrying `FdsGe3Closed sf.fs` (or `FdsHiFrame`), or an
    equivalent fact from the M5 entry state.
  - `bs.length < 2 ^ 63`: the bytes are a Rust `Vec<u8>` / slice (`≤ isize::MAX`); the exact
    source in the M5 state (`runResAt` / `callAt` ownership) is not checked yet [unverified].
* `Main/Proofs/M6PlacedBudget.main_m6_of_pool_proof_placed` (`hio.writeStdout`, `:709`): needs
  `bs.length < 2 ^ 63` (from `ownedBytes_unpack`, `outCap.toNat < 2 ^ 63`) and
  `writeStdoutStackFloor ≤ hookStack` (from `MainIoPlacedSat.hWriteStdoutStack`).
* `Main/Proofs/IoSitesPlacedBudget.main_writeFile_placed_ok` / `main_writeStdout_placed_ok`
  (`:62`, `:70`): one-line `MainIoPlacedSat` projections.
* Field copies of `MainIoPlaced` that need Sat twins (no new premise): `M24/MainIoBoundedPlaced`
  (`:352`, `:362`, `:431`), `Main/Proofs/M3PlacedBudgetFd` (`:164`).
-/

end LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHonestSpecs
