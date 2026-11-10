/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.IoCommon

/-!
# Specification of `std::fs::write`

Specifies `std::fs::write::inner(path_ptr = x0, path_len = x1, buf = x2, n = x3) -> io::Result<()>`.
The routine copies `path` into a NUL-terminated buffer (on the stack when `path_len < 384`, or in a
temporary heap `CString` freed before `open` returns), rejects interior NUL bytes with `NUL_ERR`
prior to any syscall, calls `openat(AT_FDCWD, path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC |
O_LARGEFILE)`, writes `contents` in `MAX_RW_COUNT`-clamped chunks, and closes the descriptor.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-- Outcome of `std::fs::write` on `fs` for path bytes `bs` (excluding the trailing NUL):
    `nul` when `bs` contains `0#8`, `err e` when `openat` fails with errno `e`, `trap` when the
    `openat` model fails closed (leading `/` or `..`), or `ok segs fd ev` when `openat` opens
    regular file `segs` as `fd` and emits `ev`. -/
inductive WriteOutcome where
  | nul
  | err (e : BitVec 64)
  | trap
  | ok (segs : FsPath) (fd : BitVec 64) (ev : List TraceEvent)
  deriving Inhabited

/-- Evaluates the `std::fs::write` outcome for path bytes `bs` on `fs`: checks for interior NUL
    bytes first, returns `ENAMETOOLONG` when `PATH_MAX ≤ bs.length`, and otherwise dispatches to
    `Arm64.openatPure` with `stdCreateTruncOpenFlags` at `normalizePath (cPathOf bs)`. -/
def fsWriteOutcome (fs : FsState) (bs : List (BitVec 8)) : WriteOutcome :=
  if 0#8 ∈ bs then .nul
  else if PATH_MAX ≤ bs.length then .err ENAMETOOLONG
  else
    match Arm64.openatPure fs AT_FDCWD_W32 (cPathOf bs) stdCreateTruncOpenFlags with
    | .trap _ => .trap
    | .errno e => .err e
    | .opened fd _ cp? =>
      .ok (normalizePath (cPathOf bs)) fd
        (match cp? with
         | some p => [.fileChanged p]
         | none => [])

/-- Whether a `WriteOutcome` is `trap`. -/
def WriteOutcome.isTrap : WriteOutcome → Bool
  | .trap => true
  | _ => false

variable {oom : State → State → Prop}

/-- Contract for `std::fs::write::inner(path_ptr = x0, path_len = x1, buf = x2, n = x3)` with ghost
    state `(path_ptr, bs, buf, data, lb, lk)`. Requires `data.length ≤ FS_SAFE_MAX_FILESIZE`,
    `buf.toNat + data.length ≤ USER_VA_LIMIT`, a non-trapping `fsWriteOutcome`, and allocator
    headroom for the temporary `CString` when `384 ≤ bs.length`. Updates `fs`, `trace`, and `x0`
    according to `fsWriteOutcome s0.fs bs`, or transitions to `oom` during the pre-`openat` path
    allocation. -/
def fsWriteSpec (A : RustStdAlloc oom) (addrs : RustStdIoAddrs) (stackBytes : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (path, bs, buf, data, lb, lk) s =>
    ⌜s.readReg64 .x0 = path ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x2 = buf ∧
      (s.readReg64 .x3).toNat = data.length ∧ data.length ≤ Arm64.FS_SAFE_MAX_FILESIZE ∧
      buf.toNat + data.length ≤ Arm64.USER_VA_LIMIT ∧
      (fsWriteOutcome s.fs bs).isTrap = false ∧
      ¬ NullAllowed (bs.length + 1) 1 ∧
      (384 ≤ bs.length → A.CanAlloc lb lk (bs.length + 1) 1)⌝ ∗
      A.pool lb lk s ∗ (path ↦ₛ bs) ∗ (buf ↦ₛ data) ∗ StdErrCells addrs s.tpidrEl0 ∗
      IoImageRoCells addrs ∗ stackFrameAt s.sp stackBytes
  post := fun (path, bs, buf, data, lb, lk) s0 sf =>
    ⌜IoCallFrame s0 sf ∧
      (match fsWriteOutcome s0.fs bs with
       | .nul =>
         sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.readReg64 .x0 = IoErr.nulInPath.repr addrs
       | .err e =>
         sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.readReg64 .x0 = (IoErr.os e).repr addrs
       | .trap => False
       | .ok segs fd ev =>
         sf.fs = s0.fs.setEntry segs (some (.file data)) ∧
           sf.trace = s0.trace ++ ev ++ TraceEvent.ofBytes (OutputStream.ofFd fd) data ∧
           sf.readReg64 .x0 = 0#64)⌝ ∗
      A.pool lb lk sf ∗ (path ↦ₛ bs) ∗ (buf ↦ₛ data) ∗ StdErrCells addrs s0.tpidrEl0 ∗
      IoImageRoCells addrs ∗ stackFrameAt s0.sp stackBytes
  onOom := fun _ s0 sf => ⌜∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

end VerifiedLibraries.RustStd
