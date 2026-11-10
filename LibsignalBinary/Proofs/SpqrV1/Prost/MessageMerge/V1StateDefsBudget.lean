/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefs

/-!
# Budget-Threaded Specifications and Loop Invariants for `V1State::merge`

Defines the `Polynomial{Encoder,Decoder}` capacity upper bound `optInnerStatePolyCapBound`,
allocator event envelopes (`V1StateMergeEnv`, `V1StateMergePostEnv`), `RustCliAllocBudget`
contracts (`v1StateMergeSpec`, `v1StateMergePlacedSpec`), and loop/error frame bundles for
`V1State::merge` (Block `298`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeLoopEnv)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound V1StateMergeGhost chunkedInlStack codecWireTypeToProto
   optPolyDecoderPtsLen optPolyEncoderPolysLen optPolyEncoderPtsLen
   optProtoInnerStateCapAt v1StateJumpTablesAt v1StateJumpTablesPlacedAt
   v1StateMergeStack v1StateSavedRegsAt)

/-! ## 1. `Polynomial{Encoder,Decoder}` Capacity Bound for `Option V1State.InnerState` -/

/-- Maximum initial `Polynomial{Encoder,Decoder}` vector length inside `V1State.InnerState`. -/
def innerStatePolyCapMax : V1State.InnerState → Nat
  | .keysUnsampled _ => 0
  | .keysSampled s =>
      Nat.max (optPolyEncoderPtsLen s.sendingHdr) (optPolyEncoderPolysLen s.sendingHdr)
  | .headerSent s =>
      Nat.max
        (Nat.max (optPolyEncoderPtsLen s.sendingEk) (optPolyEncoderPolysLen s.sendingEk))
        (optPolyDecoderPtsLen s.receivingCt1)
  | .ct1Received s =>
      Nat.max (optPolyEncoderPtsLen s.sendingEk) (optPolyEncoderPolysLen s.sendingEk)
  | .ekSentCt1Received s =>
      optPolyDecoderPtsLen s.receivingCt2
  | .noHeaderReceived s =>
      optPolyDecoderPtsLen s.receivingHdr
  | .headerReceived s =>
      optPolyDecoderPtsLen s.receivingEk
  | .ct1Sampled s =>
      Nat.max
        (Nat.max (optPolyEncoderPtsLen s.sendingCt1) (optPolyEncoderPolysLen s.sendingCt1))
        (optPolyDecoderPtsLen s.receivingEk)
  | .ekReceivedCt1Sampled s =>
      Nat.max (optPolyEncoderPtsLen s.sendingCt1) (optPolyEncoderPolysLen s.sendingCt1)
  | .ct1Acknowledged s =>
      optPolyDecoderPtsLen s.receivingEk
  | .ct2Sampled s =>
      Nat.max (optPolyEncoderPtsLen s.sendingCt2) (optPolyEncoderPolysLen s.sendingCt2)

/-- Maximum initial `Polynomial{Encoder,Decoder}` vector length inside `Option V1State.InnerState`. -/
def optInnerStatePolyCapMax : Option V1State.InnerState → Nat
  | none => 0
  | some st => innerStatePolyCapMax st

/-- Uniform `growVecU8` capacity upper bound across `V1State::merge` starting from `(opt, bsLen)`. -/
def optInnerStatePolyCapBound (opt : Option V1State.InnerState) (bsLen : Nat) : Nat :=
  optInnerStatePolyCapMax opt + bsLen

theorem optInnerStatePolyCapBound_mono_len {opt : Option V1State.InnerState} {m n : Nat}
    (hle : m ≤ n) :
    optInnerStatePolyCapBound opt m ≤ optInnerStatePolyCapBound opt n := by
  unfold optInnerStatePolyCapBound
  omega

/-! ## 2. Allocator Event Envelopes for `V1State::merge` -/

/-- Precondition allocator event envelope for `V1State::merge`:
each outer byte consumed allows up to `8` `SpqrMergeIterEnv` steps (`1` optional `InnerState`
variant-switch deallocation + `6 * Δ` inner `Chunked.*` steps), plus `16` error-unwind steps. -/
def V1StateMergeEnv (x : V1StateMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (8 * x.bs.length + 16) x.bs.length
    (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs

/-- Postcondition allocator event envelope for `V1State::merge`. -/
def V1StateMergePostEnv (x : V1StateMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (8 * (x.bs.length - rest.length)) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs
  | none =>
    SpqrMergeLoopEnv (8 * x.bs.length + 16) x.bs.length
      (optInnerStatePolyCapBound x.msg.innerState x.bs.length) evs

theorem v1StateMergePostEnv_imp_pre {x : V1StateMergeGhost} {evs : List AllocEvent}
    (h : V1StateMergePostEnv x evs) :
    V1StateMergeEnv x evs := by
  dsimp only [V1StateMergePostEnv, V1StateMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-! ## 3. Base-Parameterized & Relocatable `[LibsignalPlacement]` Hoare Contracts -/

/-- Envelope-parameterized base-offset contract of `V1State::merge`. -/
def v1StateMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64)
    (PreEnv PostEnv : V1StateMergeGhost → List AllocEvent → Prop) :
    Spec (V1StateMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64 ∧
      OptInnerStatePolyBound x.bs.length x.msg.innerState ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      optProtoInnerStateCapAt A.repAlloc x.msgPtr x.bs.length x.msg.innerState ∗
      v1StateJumpTablesAt b ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp v1StateMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ v1StateJumpTablesAt b ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp v1StateMergeStack ∗
      match (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
          optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m'.innerState ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded base-offset contract of `V1State::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def v1StateMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (b : BitVec 64) : Spec (V1StateMergeGhost × M.σ) :=
  v1StateMergeSpecOfEnv A lim b V1StateMergeEnv V1StateMergePostEnv

def v1StateErrFrame {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (b : BitVec 64) (s0 sf : State)
    (msgPtr bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc msgPtr is') ∗
    v1StateJumpTablesAt b ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st sf ∗ v1StateSavedRegsAt s0.sp s0

def v1StateLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (b : BitVec 64) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State) (bs cur : List (BitVec 8)) : SepProp :=
  optProtoInnerStateCapAt A.repAlloc msgPtr cur.length m.innerState ∗
    v1StateJumpTablesAt b ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    A.pool lim st s ∗
    stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
    v1StateSavedRegsAt s0.sp s0

/-- Envelope-parameterized relocatable `[LibsignalPlacement]` contract of `V1State::merge`. -/
def v1StateMergePlacedSpecOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : V1StateMergeGhost → List AllocEvent → Prop) :
    Spec (V1StateMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      OptInnerStatePolyBound x.bs.length x.msg.innerState ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      optProtoInnerStateCapAt A.repAlloc x.msgPtr x.bs.length x.msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp v1StateMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp v1StateMergeStack ∗
      match (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
          optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m'.innerState ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded relocatable `[LibsignalPlacement]` contract of `V1State::merge`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def v1StateMergePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (V1StateMergeGhost × M.σ) :=
  v1StateMergePlacedSpecOfEnv A lim V1StateMergeEnv V1StateMergePostEnv

def v1StateErrFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 sf : State)
    (msgPtr bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A.repAlloc msgPtr is') ∗
    v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗ memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st sf ∗ v1StateSavedRegsAt s0.sp s0

def v1StateLoopPrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State) (bs cur : List (BitVec 8)) : SepProp :=
  optProtoInnerStateCapAt A.repAlloc msgPtr cur.length m.innerState ∗
    v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    A.pool lim st s ∗
    stackAt (s0.sp - 816#64) chunkedInlStack ∗ memRegion (s0.sp - 816#64) 720 ∗
    v1StateSavedRegsAt s0.sp s0

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
