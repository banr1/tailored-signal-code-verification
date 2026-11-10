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
# Specification of `std::fs::read`

Specifies `std::fs::read::inner(path: &Path) -> io::Result<Vec<u8>>` (`rustc 1.98.1`, `sret`
result `x8 = ret`, `x0 = path_ptr`, `x1 = path_len`):

1. Copies `path` into a NUL-terminated buffer (stack below 384 bytes, otherwise a temporary
   heap `CString` freed before `open` returns), returning `Err(NUL_ERR)` without syscalls if `path`
   contains a NUL byte, then calls `openat(AT_FDCWD, path, O_RDONLY | O_CLOEXEC | O_LARGEFILE)`.
2. Calls `fstat`, allocates `Vec::try_with_capacity(st_size)?`, reads the file contents via
   `default_read_to_end`, and closes the descriptor.

Directory paths are excluded by the precondition: musl `open` issues
`fcntl(fd, F_SETFD, FD_CLOEXEC)`, which `Arm64.execFcntl` models only on `.localFile` descriptors.
Out-of-memory stops satisfy `FsReadPrefix bs s0 sm`: either before `openat` (allocating the path
`CString` when `384 <= bs.length`) or immediately after `openat` (allocating the result `Vec`).
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-- Outcome of `std::fs::read` on path bytes `bs` (without trailing NUL) in file system `fs`:
    - `nul`: `bs` contains a NUL byte;
    - `err e`: `openat` fails with errno `e`;
    - `trap`: the `openat` model fails closed (leading `/` or `..` segment);
    - `dir`: `openat` opened a directory (excluded by `fsReadSpec`);
    - `ok fb`: the regular file at the path holds bytes `fb`. -/
inductive ReadOutcome where
  | nul
  | err (e : BitVec 64)
  | trap
  | dir
  | ok (fb : List (BitVec 8))
  deriving Inhabited

/-- Pure outcome model for `std::fs::read` on path bytes `bs` in `fs`. Checks for interior NUL
    bytes first, returns `ENAMETOOLONG` when `PATH_MAX <= bs.length`, and otherwise dispatches on
    `Arm64.openatPure fs AT_FDCWD_W32 (cPathOf bs) stdReadOpenFlags` and the resolved entry at
    `normalizePath (cPathOf bs)`. -/
def fsReadOutcome (fs : FsState) (bs : List (BitVec 8)) : ReadOutcome :=
  if 0#8 ∈ bs then .nul
  else if PATH_MAX ≤ bs.length then .err ENAMETOOLONG
  else
    match Arm64.openatPure fs AT_FDCWD_W32 (cPathOf bs) stdReadOpenFlags with
    | .trap _ => .trap
    | .errno e => .err e
    | .opened _ _ _ =>
      match fs.getEntry (normalizePath (cPathOf bs)) with
      | some (.file fb) => .ok fb
      | some .dir => .dir
      | none => .trap

/-- Whether `ReadOutcome` is `.trap`. -/
def ReadOutcome.isTrap : ReadOutcome → Bool
  | .trap => true
  | _ => false

/-- Intermediate state `sm` at which an allocation during `std::fs::read` on `bs` from `s0` runs
    out of memory: trace and signal dispositions match `s0`, and `sm.fs` is either `s0.fs` (before
    `openat`) or the post-`openat` state with the newly opened descriptor. -/
def FsReadPrefix (bs : List (BitVec 8)) (s0 sm : State) : Prop :=
  IoFrame s0 sm ∧
    (sm.fs = s0.fs ∨
      ∃ fd fs' cp?, bs.length < PATH_MAX ∧
        Arm64.openatPure s0.fs AT_FDCWD_W32 (cPathOf bs) stdReadOpenFlags = .opened fd fs' cp? ∧
        sm.fs = fs')

variable {oom : State → State → Prop}

/-- Contract for `std::fs::read::inner(ret = x8, path_ptr = x0, path_len = x1)` with ghost state
    `(ret, path_ptr, bs, lb, lk)`. Preserves `s0.fs` and `s0.trace` on normal return, writes the
    `io::Result<Vec<u8>>` representation into `ret` according to `fsReadOutcome s0.fs bs` (including
    `Err(OutOfMemory)` when `NullAllowed fb.length 1` holds and the allocator returns null), and
    forbids panic and exit. -/
def fsReadSpec (A : RustStdAlloc oom) (addrs : RustStdIoAddrs) (stackBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (ret, path, bs, lb, lk) s =>
    ⌜s.readReg64 .x8 = ret ∧ s.readReg64 .x0 = path ∧ (s.readReg64 .x1).toNat = bs.length ∧
      ret.toNat % 8 = 0 ∧ stackBytes ≤ s.sp.toNat ∧ s.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      (fsReadOutcome s.fs bs).isTrap = false ∧ fsReadOutcome s.fs bs ≠ .dir ∧
      ¬ NullAllowed (bs.length + 1) 1 ∧
      (384 ≤ bs.length → A.CanAlloc lb lk (bs.length + 1) 1) ∧
      (∀ fb, fsReadOutcome s.fs bs = .ok fb →
        fb.length < 2 ^ 63 ∧ (0 < fb.length → A.CanAlloc lb lk fb.length 1))⌝ ∗
      A.pool lb lk s ∗ (path ↦ₛ bs) ∗ memRegion ret 24 ∗ StdErrCells addrs s.tpidrEl0 ∗
      IoImageRoCells addrs ∗ (addrs.emptyCStr ↦₈ᵣ 0#8) ∗ stackFrameAt s.sp stackBytes
  post := fun (ret, path, bs, lb, lk) s0 sf =>
    ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗
      (path ↦ₛ bs) ∗ StdErrCells addrs s0.tpidrEl0 ∗ IoImageRoCells addrs ∗
      (addrs.emptyCStr ↦₈ᵣ 0#8) ∗ stackFrameAt s0.sp stackBytes ∗
      (match fsReadOutcome s0.fs bs with
       | .nul => A.pool lb lk sf ∗ ioResultVecErr addrs ret .nulInPath
       | .err e => A.pool lb lk sf ∗ ioResultVecErr addrs ret (.os e)
       | .trap => ⌜False⌝
       | .dir => ⌜False⌝
       | .ok fb =>
         if fb = [] then
           A.pool lb lk sf ∗ (∃∗ ptr : BitVec 64, ioResultVecOk A ret 0#64 ptr [])
         else
           ∃∗ nullRet : Bool,
             if nullRet then
               ⌜NullAllowed fb.length 1⌝ ∗ A.pool lb lk sf ∗
                 ioResultVecErr addrs ret .outOfMemory
             else
               A.pool (lb + A.cost fb.length 1) (lk + 1) sf ∗
                 (∃∗ ptr : BitVec 64, ioResultVecOk A ret (BitVec.ofNat 64 fb.length) ptr fb))
  onOom := fun (_, _, bs, _, _) s0 sf => ⌜∃ sm, FsReadPrefix bs s0 sm ∧ oom sm sf⌝

end VerifiedLibraries.RustStd
