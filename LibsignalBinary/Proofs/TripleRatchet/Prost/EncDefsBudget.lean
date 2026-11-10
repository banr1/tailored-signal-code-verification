/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Budget-Threaded Prost Encoding Leaf Specifications

Deterministic `Vec::reserve` allocator event envelopes and `RustCliAllocBudget`-threaded
specifications for `encode_varint::<Vec<u8>>` and `<wire::SignalMessage as Message>::encoded_len`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv VmPreserved
   rustAllocEvents rustReallocEvents)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded blkPC_10 blkPl_10 blkPC_108 blkPl_108)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encode)
open CryptoVerification.LibsignalTripleRatchet
  (reserveCap tripleRatchetProgAtExt trTrapProgAt tripleRatchetProgAt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (encodeVarintName encodedLenName encodeVarintStack encodeVarintStackX encodedLenStack
   wireSignalMessageAt WireLengthsFit EncodeVarintGhost EncodedLenGhost)

/-! ## Deterministic `encode_varint` allocator events and envelope -/

/-- Single-byte reserve-and-push transition `(cap, len) → (cap', len + 1)` matching
`do_reserve_and_handle` (`additional := 1`) when `len = cap` and emitting `[]` when `len < cap`. -/
def pushByteStep (cap len : Nat) : Nat × List AllocEvent :=
  if len < cap then
    (cap, [])
  else
    let newCap := reserveCap cap len 1
    let evs := if cap = 0 then rustAllocEvents newCap 1 else rustReallocEvents cap newCap 1
    (newCap, evs)

/-- Deterministic `AllocEvent` list emitted while pushing `n` bytes one-by-one into a `Vec<u8>`
with initial `(cap, len)` via `do_reserve_and_handle` (`additional := 1`). -/
def pushBytesEvents : Nat → Nat → Nat → List AllocEvent
  | 0, _, _ => []
  | n + 1, cap, len =>
    let step := pushByteStep cap len
    step.2 ++ pushBytesEvents n step.1 (len + 1)

/-- Deterministic `AllocEvent` list emitted by `encode_varint::<Vec<u8>> [local#1]` on `x`. -/
def encodeVarintEvents (x : EncodeVarintGhost) : List AllocEvent :=
  pushBytesEvents (encodeVarint x.val).length x.cap.toNat x.bs.length

/-- Callee-fixed allocator event envelope of `encode_varint::<Vec<u8>> [local#1]`. -/
def EncodeVarintEnv (x : EncodeVarintGhost) (evs : List AllocEvent) : Prop :=
  evs = encodeVarintEvents x

theorem encodeVarintEnv_events (x : EncodeVarintGhost) :
    EncodeVarintEnv x (encodeVarintEvents x) := rfl

theorem pushBytesEvents_of_spare :
    ∀ (n cap len : Nat), len + n ≤ cap → pushBytesEvents n cap len = []
  | 0, _, _, _ => rfl
  | n + 1, cap, len, h => by
    have hlt : len < cap := by omega
    simp only [pushBytesEvents, pushByteStep, hlt, ↓reduceIte, List.nil_append]
    exact pushBytesEvents_of_spare n cap (len + 1) (by omega)

theorem encodeVarintEvents_of_spare {x : EncodeVarintGhost}
    (h : x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat) :
    encodeVarintEvents x = [] :=
  pushBytesEvents_of_spare (encodeVarint x.val).length x.cap.toNat x.bs.length h

/-! ## Budget-threaded `encodeVarintSpec` and `encodeVarintSpecX` -/

/-- Budget-threaded contract of `prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]`
(`encodeVarintStack`, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encodeVarintSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp encodeVarintStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp encodeVarintStack

/-- Budget-threaded contract of `encode_varint::<Vec<u8>> [local#1]` at `encodeVarintStackX`. -/
def encodeVarintSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp encodeVarintStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp encodeVarintStackX

/-! ## `VmPreserved`-augmented `encodedLenSpec` -/

/-- `VmPreserved`-augmented contract of
`<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len`
(`0` allocations; callers pass `A.repAlloc` and transport `A.pool lim st` via `VmPreserved`). -/
def encodedLenSpec (A : RustAlloc) : Spec EncodedLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ WireLengthsFit x.m⌝ ∗
      wireSignalMessageAt A x.g x.a x.m ∗ stackAt s.sp encodedLenStack
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧
      sf.readReg64 .x0 = BitVec.ofNat 64 (encode x.m).length ∧ sf.trace = s0.trace⌝ ∗
      wireSignalMessageAt A x.g x.a x.m ∗ stackAt s0.sp encodedLenStack

/-! ## Target `subroutine_ok` propositions -/

def EncodeVarintOkExt {M : AllocCostModel} (b : BitVec 64) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeVarintName)
    (encodeVarintSpec A lim)

def EncodeVarintOk_trap {M : AllocCostModel} (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr encodeVarintName)
    (encodeVarintSpec A lim)

def EncodeVarintOk {M : AllocCostModel} (b : BitVec 64) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName)
    (encodeVarintSpec A lim)

def EncodedLenOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodedLenName)
    (encodedLenSpec A)

def EncodedLenOk_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr encodedLenName)
    (encodedLenSpec A)

def EncodedLenOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr encodedLenName)
    (encodedLenSpec A)

abbrev EncodeVarintPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
    (blkPl_10).base
    (withLsCodeLoaded lsmpl (encodeVarintSpec A lim))

abbrev EncodeVarintPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
    (blkPl_10).base
    (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim))

abbrev EncodedLenPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_108).rebase (blkPl_108).base H)
    (blkPl_108).base
    (encodedLenSpec A)

end LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
