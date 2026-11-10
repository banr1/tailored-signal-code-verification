/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.RustStd.Spec.IoCommon
public import VerifiedLibraries.RustStd.Generated.CorePlacedObj

/-!
# `core::slice::memchr::memrchr` Specification

Defines `lastIndexOf`, the pure mirror of `core::slice::memchr::memrchr`, and `coreMemrchrSpec`,
its Hoare specification over `coreMultiLib`.
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

/-- Demangled symbol name of `core::slice::memchr::memrchr` in `coreMultiLib`. -/
abbrev coreMemrchrSym : String :=
  "core::slice::memchr::memrchr"

/-- Returns the last index in `bs` equal to `c`, mirroring `core::slice::memchr::memrchr`
    (`core/src/slice/memchr.rs:109-111`). -/
def lastIndexOf (c : BitVec 8) (bs : List (BitVec 8)) : Option Nat :=
  ((List.range bs.length).filter fun i => bs[i]? == some c).getLast?

/-- Specification of `core::slice::memchr::memrchr(c, p, len) -> Option<usize>`: reads needle `c` in
    `w0[7:0]`, slice pointer `p` in `x1`, and length `bs.length < 2 ^ 64` in `x2`, returning the
    last matching index in `(x0, x1)` via `RustAbi.optionU64` (`none` leaves `x1` unconstrained
    because the implementation returns `x1 = 0` or `x1 = p` depending on whether the tail byte loop
    ran) with `onPanic = ⌜False⌝`. -/
rust_spec coreMemrchrSpec
    (c : u8) (p : slice8 bs) (ghost bs : List (BitVec 8)) (sp : sp) : RustAbi.optionU64
  requires_cond bs.length < 2 ^ 64
  preserves     (p ↦ₛ bs) ∗ stackFrameAt sp 16
  ensures_pure  sf.trace = s0.trace ∧ sf.fs = s0.fs
  returns       (lastIndexOf c bs).map (BitVec.ofNat 64)

end VerifiedLibraries.RustStd
