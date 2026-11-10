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
# Specification of `<String as Clone>::clone`

Trusted specification (`stringCloneStack`, `rustStringCloneSpec`) for compiled
`<alloc::string::String as core::clone::Clone>::clone` (`x0 = &self`, `x8 = ret`). An empty
source writes `{cap = 0, ptr = 1, len = 0}` without calling the allocator; a non-empty source
allocates `len` bytes with alignment `1` via `__rust_alloc`, copies the slice with `memcpy`,
panics via `handle_error` only when `NullAllowed len 1` holds, and propagates out-of-memory
from `__rust_alloc`.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-- Stack bytes used below `sp` by `String::clone`: its `0x30`-byte frame plus the 4096-byte
    `hookStack` budget of the allocator shim and `__rust_alloc`. -/
abbrev stringCloneStack : Nat := 0x30 + 4096

variable {oom : State → State → Prop}

/-- Contract for `<String as Clone>::clone(ret = x8, self = x0)` with ghost tuple
    `(self, ret, cap, ptr, bs, lb, lk)`. Preserves the source string, file system, and trace;
    writes `{0, 1, 0}` when `bs = []` or allocates a fresh `bs.length`-byte buffer when
    `bs ≠ []`. -/
def rustStringCloneSpec (A : RustStdAlloc oom) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (self, ret, cap, ptr, bs, lb, lk) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret ∧ bs.length < 2 ^ 63 ∧
      (bs ≠ [] → A.CanAlloc lb lk bs.length 1)⌝ ∗
      vecHeader self cap ptr (BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗ memRegion ret 24 ∗
      A.pool lb lk s ∗ StdErrnoCell s.tpidrEl0 ∗ stackFrameAt s.sp stringCloneStack
  post := fun (self, ret, cap, ptr, bs, lb, lk) s0 sf =>
    ⌜IoCallFrame s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗
      vecHeader self cap ptr (BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      StdErrnoCell s0.tpidrEl0 ∗ stackFrameAt s0.sp stringCloneStack ∗
      (if bs = [] then
         A.pool lb lk sf ∗ vecHeader ret 0#64 1#64 0#64 ∗ ioVecBuf A 0#64 1#64 []
       else
         A.pool (lb + A.cost bs.length 1) (lk + 1) sf ∗
           (∃∗ q : BitVec 64, vecHeader ret (BitVec.ofNat 64 bs.length) q
              (BitVec.ofNat 64 bs.length) ∗ ioVecBuf A (BitVec.ofNat 64 bs.length) q bs))
  onPanic := fun (_, _, _, _, bs, _, _) s0 sf =>
    ⌜NullAllowed bs.length 1 ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace⌝
  onOom := fun _ s0 sf => ⌜∃ sm, IoFrame s0 sm ∧ sm.fs = s0.fs ∧ oom sm sf⌝

end VerifiedLibraries.RustStd
