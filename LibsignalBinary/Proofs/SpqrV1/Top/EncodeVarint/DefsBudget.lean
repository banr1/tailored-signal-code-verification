/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Defs

/-!
# Budget-Threaded Specification for `spqr::encode_varint` (`0x54040`, 164 insns)

Defines the deterministic allocator event trace `spqrEncodeVarintEvents` and budget-threaded
specification `spqrEncodeVarintSpecX` for `spqr::encode_varint` (`0x54040`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (growOneU8BudgetSpec growOneU8Events)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (MAX_VARINT_BYTES_LEN encodeVarintLoop encode_varint growOneU8Name newCapU8)
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (spqrEncodeVarintName spqrEncodeVarintStackX)

/-! ## 1. Deterministic `spqr::encode_varint` Allocator Events & Envelope -/

/-- Single-byte `RawVec<u8>::grow_one`-and-push transition `(cap, len) → (cap', len + 1)`
emitting `[]` when `len < cap.toNat` and `growOneU8Events cap` (`newCapU8 cap`) when
`len = cap.toNat`. -/
def growOneU8ByteStep (cap : BitVec 64) (len : Nat) : BitVec 64 × List AllocEvent :=
  if len < cap.toNat then
    (cap, [])
  else
    (newCapU8 cap, growOneU8Events cap)

/-- Deterministic `AllocEvent` list emitted while pushing `n` bytes one-by-one into a `Vec<u8>`
with initial `(cap, len)` via `<RawVec<u8>>::grow_one`. -/
def growOneU8BytesEvents : Nat → BitVec 64 → Nat → List AllocEvent
  | 0, _, _ => []
  | n + 1, cap, len =>
    let step := growOneU8ByteStep cap len
    step.2 ++ growOneU8BytesEvents n step.1 (len + 1)

/-- Deterministic `AllocEvent` list emitted by `spqr::encode_varint` on `x`. -/
def spqrEncodeVarintEvents (x : EncodeVarintGhost) : List AllocEvent :=
  growOneU8BytesEvents (encodeVarintLoop MAX_VARINT_BYTES_LEN x.val).length x.cap x.bs.length

/-- Callee-fixed allocator event envelope of `spqr::encode_varint`. -/
def SpqrEncodeVarintEnv (x : EncodeVarintGhost) (evs : List AllocEvent) : Prop :=
  evs = spqrEncodeVarintEvents x

theorem spqrEncodeVarintEnv_events (x : EncodeVarintGhost) :
    SpqrEncodeVarintEnv x (spqrEncodeVarintEvents x) := rfl

theorem growOneU8BytesEvents_of_spare :
    ∀ (n : Nat) (cap : BitVec 64) (len : Nat),
      len + n ≤ cap.toNat → growOneU8BytesEvents n cap len = []
  | 0, _, _, _ => rfl
  | n + 1, cap, len, h => by
    have hlt : len < cap.toNat := by omega
    simp only [growOneU8BytesEvents, growOneU8ByteStep, hlt, ↓reduceIte, List.nil_append]
    exact growOneU8BytesEvents_of_spare n cap (len + 1) (by omega)

theorem spqrEncodeVarintEvents_of_spare {x : EncodeVarintGhost}
    (h : x.bs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN x.val).length ≤ x.cap.toNat) :
    spqrEncodeVarintEvents x = [] :=
  growOneU8BytesEvents_of_spare
    (encodeVarintLoop MAX_VARINT_BYTES_LEN x.val).length x.cap x.bs.length h

/-! ## 2. Budget-Threaded Callee Hypothesis & `spqrEncodeVarintSpecX` -/

/-- `<alloc::raw_vec::RawVec<u8>>::grow_one` meets `growOneU8BudgetSpec M A lim` on
`tripleRatchetProgAtExt b ext`. -/
def GrowOneU8OkExt {M : AllocCostModel} (b : BitVec 64) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr growOneU8Name)
    (growOneU8BudgetSpec M A lim)

/-- Budget-threaded specification of `spqr::encode_varint` (`0x54040`, 164 instructions)
at `spqrEncodeVarintStackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv M lim st (SpqrEncodeVarintEnv x)`). -/
def spqrEncodeVarintSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (SpqrEncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp spqrEncodeVarintStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (encode_varint x.val x.bs)) ∗
      (∃∗ evs : List AllocEvent, ⌜SpqrEncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp spqrEncodeVarintStackX

/-- `spqr::encode_varint` meets `spqrEncodeVarintSpecX A lim` on `tripleRatchetProgAtExt b ext`. -/
def SpqrEncodeVarintOkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName)
    (spqrEncodeVarintSpecX A lim)

/-- `spqr::encode_varint` meets `(spqrEncodeVarintSpecX A lim).inImage img` on
`tripleRatchetProgAtExt img.base ext`. -/
def SpqrEncodeVarintOkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr spqrEncodeVarintName)
    ((spqrEncodeVarintSpecX A lim).inImage img)

abbrev EncodeVarintOkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  SpqrEncodeVarintOkX img A lim ext

end LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
