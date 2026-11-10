/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# In-Image `RawVec::grow_one` Contracts

**Checked by Lean.**

Intermediate `RustAlloc` specifications for `<alloc::raw_vec::RawVec<u8>>::grow_one` and
`<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one` linked into `libsignalSessionImage`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet

abbrev growOneU8Name : String :=
  "<alloc::raw_vec::RawVec<u8>>::grow_one"

abbrev growOneVecU8Name : String :=
  "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one"

/-- Ghost state `(v, cap, ptr, bs)` for `RawVec<T>::grow_one`. -/
structure GrowOneCall where
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- New capacity after `<alloc::raw_vec::RawVec<u8>>::grow_one`:
`max (2 * cap.toNat) 8` (`RawVec::<u8>::MIN_NON_ZERO_CAP = 8` for 1-byte elements). -/
def newCapU8 (cap : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (max (2 * cap.toNat) 8)

/-- `RustAlloc` contract for `<alloc::raw_vec::RawVec<u8>>::grow_one` (`x0 = v` points to the 16-byte `{cap, ptr}` header). -/
def growOneU8Spec (A : RustAlloc) : Spec GrowOneCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 8 < 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 1 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0⌝ ∗
        (x.v ↦₆₄ newCapU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 8) 1 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) (max (2 * x.cap.toNat) 8 - x.cap.toNat)) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- New capacity after `<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one`:
`max (2 * cap.toNat) 4` (`RawVec::<Vec<u8>>::MIN_NON_ZERO_CAP = 4` for 24-byte elements). -/
def newCapVecU8 (cap : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (max (2 * cap.toNat) 4)

/-- `RustAlloc` contract for `<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one` (`x0 = v` points to the 16-byte `{cap, ptr}` header). -/
def growOneVecU8Spec (A : RustAlloc) : Spec GrowOneCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.LibsignalSpqrV1
