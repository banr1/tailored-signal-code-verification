/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop

/-!
# Budget-Threaded SPQR V1 `Chunked.*` and `Unchunked.*` `prost::encoding::message::merge` Specifications

Defines callee-closed allocation event envelopes (`DecodeErrorPushMergeEnv`, `BytesMerge3EnvCore`,
`SpqrMergeSmallStep`, `SpqrMergeLoopEnv`), budget-threaded `RustCliAllocBudget` contracts for
`Unchunked.{Ct1Sent,EkSentCt1Received}::merge` and
`V1State.Chunked.{Ct1Received,Ct1Acknowledged,EkSentCt1Received,Ct1Sampled}::merge`, linear
`PhaseCreditSpec` bounds, and `FitsEnv fineCostModel` witnesses.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   fitsEvents_append rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (GrowOneVecU8Env RawVecGrowEnv rawVecNewCap)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen decodeErrorHookStack reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr
  (chunkedCt1SampledPBAt ct1SentPBAt ekSentCt1ReceivedPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost UnchunkedEkSentCt1ReceivedMergeGhost unchunkedMergeStack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1AcknowledgedMergeGhost ChunkedCt1ReceivedMergeGhost
   ChunkedCt1SampledMergeGhost ChunkedEkSentCt1ReceivedMergeGhost
   chunkedCt1AcknowledgedPBAt chunkedCt1AcknowledgedPBCapAt
   chunkedCt1ReceivedPBAt chunkedCt1ReceivedPBCapAt
   chunkedCt1SampledPBCapAt
   chunkedEkSentCt1ReceivedPBAt chunkedEkSentCt1ReceivedPBCapAt
   chunkedMergeStack codecWireTypeToProto
   optPolyDecoderPtsLen optPolyEncoderPolysLen optPolyEncoderPtsLen
   unchunkedCt1SentPBCapAt unchunkedEkSentCt1ReceivedPBCapAt)

/-! ## 1. Callee-Closed Allocator Event Envelopes for SPQR Protobuf `merge` -/

/-- Exact slice consumption of a successful `mergeBytes wt bs = some (v, rest)`:
at least `1` varint length byte plus `v.length` payload bytes are consumed. -/
theorem mergeBytes_len_bound {wt : WireType} {bs v rest : List (BitVec 8)}
    (hm : mergeBytes wt bs = some (v, rest)) :
    rest.length + v.length + 1 ≤ bs.length := by
  unfold mergeBytes at hm
  split at hm
  · simp at hm
  · cases hd : decodeVarint bs with
    | none => simp [hd] at hm
    | some p =>
      rcases p with ⟨len, r1⟩
      simp only [hd] at hm
      split at hm
      · simp at hm
      · rename_i hnotlt
        simp only [Option.some.injEq, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        obtain ⟨k1, hk1_pos, hk1_le, hr1⟩ :=
          CryptoVerification.LibsignalTripleRatchet.Wire.decodeVarint_suffix hd
        have hr1_len : r1.length = bs.length - k1 := by simp [hr1]
        have hv_len : (r1.take len.toNat).length = len.toNat :=
          List.length_take_of_le (by omega)
        have hdrop_len : (r1.drop len.toNat).length = r1.length - len.toNat :=
          List.length_drop
        omega

/-- Deterministic allocator event envelope of `<DecodeError>::push` on a stack of length `n`:
no-op when `n < cap`, initial `4 * 32 = 128` B allocation when `n = cap = 0`, or
doubling `realloc` from `n * 32` to `max (2 * n) 4 * 32` when `0 < n = cap`. -/
def DecodeErrorPushMergeEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ evs = rustAllocEvents (4 * 32) 8) ∨
  (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)

/-- Bounded-envelope counterpart of `SpecBudget.decodeErrorPushBudgetSpec` using
`DecodeErrorPushMergeEnv`, so `FitsEnv` is satisfiable at `n = 0`. -/
def decodeErrorPushMergeBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32 ∧
      FitsEnv M lim st
        (DecodeErrorPushMergeEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp decodeErrorHookStack
  post := fun (d, e, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushMergeEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeErrorHookStack

/-- Callee-fixed pointer-independent event envelope of
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>` (Block `7` / Block `290`), matching
`MergeDefsBudget.bytesMergeEventsCore` (including the temporary `Bytes` allocation/drop and
deterministic `doReserveClearEvents` via `reserveCap`). -/
def BytesMerge3EnvCore (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  evs = bytesMergeEventsCore wt valCap bs

/-- Single constant- or capacity-bounded step inside SPQR `Unchunked` / `Chunked` / `V1State` `merge`
subroutines with `Polynomial{Decoder,Encoder}` vector capacities bounded by `polyCapBound`. -/
inductive SpqrMergeSmallStep (polyCapBound : Nat) : List AllocEvent → Prop where
  | nil : SpqrMergeSmallStep polyCapBound []
  | deallocs {evs : List AllocEvent} :
      (∀ ev ∈ evs, ∃ al sz, ev = .free al sz) → SpqrMergeSmallStep polyCapBound evs
  | fromErr : SpqrMergeSmallStep polyCapBound (rustAllocEvents 72 8)
  | pushErr {n : Nat} {evs : List AllocEvent} :
      n ≤ 4 → DecodeErrorPushMergeEnv n evs → SpqrMergeSmallStep polyCapBound evs
  | bytesMergeErr (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
      {evs : List AllocEvent} :
      mergeBytes wt bs = none →
      BytesMerge3EnvCore wt valCap bs evs → SpqrMergeSmallStep polyCapBound evs
  | growVecU8 (g : GrowOneCall) {evs : List AllocEvent} :
      g.cap.toNat < polyCapBound → GrowOneVecU8Env g evs → SpqrMergeSmallStep polyCapBound evs

/-- Single non-payload step envelope (`SpqrMergeSmallStep polyCapBound`) indexed by `(maxLen, polyCapBound)`. -/
abbrev SpqrMergeIterEnv (_maxLen polyCapBound : Nat) : List AllocEvent → Prop :=
  SpqrMergeSmallStep polyCapBound

theorem SpqrMergeSmallStep.mono {poly₁ poly₂ : Nat} {evs : List AllocEvent}
    (hpoly : poly₁ ≤ poly₂) (h : SpqrMergeSmallStep poly₁ evs) :
    SpqrMergeSmallStep poly₂ evs := by
  cases h with
  | nil => exact .nil
  | deallocs hf => exact .deallocs hf
  | fromErr => exact .fromErr
  | pushErr hn hp => exact .pushErr hn hp
  | bytesMergeErr wt valCap bs hm hb => exact .bytesMergeErr wt valCap bs hm hb
  | growVecU8 g hc hg => exact .growVecU8 g (Nat.lt_of_lt_of_le hc hpoly) hg

theorem SpqrMergeIterEnv.mono {maxLen₁ maxLen₂ poly₁ poly₂ : Nat} {evs : List AllocEvent}
    (_hlen : maxLen₁ ≤ maxLen₂) (hpoly : poly₁ ≤ poly₂)
    (h : SpqrMergeIterEnv maxLen₁ poly₁ evs) :
    SpqrMergeIterEnv maxLen₂ poly₂ evs :=
  SpqrMergeSmallStep.mono hpoly h

/-- Linear-budget sequential allocation envelope of SPQR `Unchunked` / `Chunked` / `V1State`
`merge` subroutines on an input slice of length at most `maxLen` with `Polynomial{Decoder,Encoder}`
vector capacities bounded by `polyCapBound`:
* `step` charges `1` budget unit for a bounded `SpqrMergeSmallStep polyCapBound` event list;
* `bytesStep` charges `2 * v.length + 1` budget units for a successful `mergeBytes wt bs = some (v, rest)`
  on `bs.length ≤ maxLen`, bounding total allocation credit linearly in `fuel` (`O(fuel * (polyCapBound + 1))`). -/
inductive SpqrMergeLoopEnv : Nat → Nat → Nat → List AllocEvent → Prop where
  | nil {fuel maxLen polyCapBound : Nat} : SpqrMergeLoopEnv fuel maxLen polyCapBound []
  | step {fuel maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent} :
      SpqrMergeSmallStep polyCapBound evs₁ →
      SpqrMergeLoopEnv fuel maxLen polyCapBound evs₂ →
      SpqrMergeLoopEnv (fuel + 1) maxLen polyCapBound (evs₁ ++ evs₂)
  | bytesStep {fuel maxLen polyCapBound : Nat} (wt : WireType) (valCap : BitVec 64)
      (bs v rest : List (BitVec 8)) {evs₁ evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ maxLen →
      BytesMerge3EnvCore wt valCap bs evs₁ →
      SpqrMergeLoopEnv fuel maxLen polyCapBound evs₂ →
      SpqrMergeLoopEnv (fuel + 2 * v.length + 1) maxLen polyCapBound (evs₁ ++ evs₂)

theorem SpqrMergeLoopEnv.single {fuel maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : SpqrMergeIterEnv maxLen polyCapBound evs) :
    SpqrMergeLoopEnv (fuel + 1) maxLen polyCapBound evs := by
  simpa using SpqrMergeLoopEnv.step (fuel := fuel) (maxLen := maxLen) h .nil

theorem SpqrMergeLoopEnv.bytesSingle {fuel maxLen polyCapBound : Nat}
    {wt : WireType} {valCap : BitVec 64} {bs v rest : List (BitVec 8)} {evs : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest))
    (hbs : bs.length ≤ maxLen)
    (hb : BytesMerge3EnvCore wt valCap bs evs) :
    SpqrMergeLoopEnv (fuel + 2 * v.length + 1) maxLen polyCapBound evs := by
  simpa using
    SpqrMergeLoopEnv.bytesStep (fuel := fuel) (maxLen := maxLen) (polyCapBound := polyCapBound)
      wt valCap bs v rest hm hbs hb .nil

theorem SpqrMergeLoopEnv.mono_fuel {fuel₁ fuel₂ maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (hle : fuel₁ ≤ fuel₂) (h : SpqrMergeLoopEnv fuel₁ maxLen polyCapBound evs) :
    SpqrMergeLoopEnv fuel₂ maxLen polyCapBound evs := by
  induction h generalizing fuel₂ with
  | nil => exact .nil
  | @step fuel _ _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 1 := ⟨fuel₂ - 1, by omega⟩
    exact .step h1 (ih (by omega))
  | @bytesStep fuel _ _ wt valCap bs v rest evs₁ evs₂ hm hbs hb _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 2 * v.length + 1 :=
      ⟨fuel₂ - (2 * v.length + 1), by omega⟩
    exact .bytesStep wt valCap bs v rest hm hbs hb (ih (by omega))

theorem SpqrMergeLoopEnv.mono {f₁ f₂ maxLen₁ maxLen₂ poly₁ poly₂ : Nat} {evs : List AllocEvent}
    (hf : f₁ ≤ f₂) (hlen : maxLen₁ ≤ maxLen₂) (hpoly : poly₁ ≤ poly₂)
    (h : SpqrMergeLoopEnv f₁ maxLen₁ poly₁ evs) :
    SpqrMergeLoopEnv f₂ maxLen₂ poly₂ evs := by
  induction h generalizing f₂ with
  | nil => exact .nil
  | @step fuel _ _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
    exact .step (h1.mono hpoly) (ih (by omega) hlen hpoly)
  | @bytesStep fuel _ _ wt valCap bs v rest evs₁ evs₂ hm hbs hb _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, f₂ = k + 2 * v.length + 1 :=
      ⟨f₂ - (2 * v.length + 1), by omega⟩
    exact .bytesStep wt valCap bs v rest hm (Nat.le_trans hbs hlen) hb (ih (by omega) hlen hpoly)

theorem SpqrMergeLoopEnv.append {f₁ f₂ maxLen polyCapBound : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyCapBound evs₁)
    (h₂ : SpqrMergeLoopEnv f₂ maxLen polyCapBound evs₂) :
    SpqrMergeLoopEnv (f₁ + f₂) maxLen polyCapBound (evs₁ ++ evs₂) := by
  induction h₁ with
  | @nil fuel _ _ =>
    simpa using h₂.mono_fuel (Nat.le_add_left f₂ fuel)
  | @step fuel _ _ e₁ e₂ head _ ih =>
    rw [List.append_assoc, show fuel + 1 + f₂ = (fuel + f₂) + 1 by omega]
    exact .step head (ih h₂)
  | @bytesStep fuel _ _ wt valCap bs v rest e₁ e₂ hm hbs hb _ ih =>
    rw [List.append_assoc,
      show fuel + 2 * v.length + 1 + f₂ = (fuel + f₂) + 2 * v.length + 1 by omega]
    exact .bytesStep wt valCap bs v rest hm hbs hb (ih h₂)

theorem FitsEnv.spqrMergeLoop_head {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → SpqrMergeIterEnv maxLen polyCapBound evs)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv (fuel + 1) maxLen polyCapBound)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (SpqrMergeLoopEnv.single (hsub evs he))

theorem FitsEnv.spqrMergeLoop_tail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {evs₁ : List AllocEvent}
    (h1 : SpqrMergeIterEnv maxLen polyCapBound evs₁)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv (fuel + 1) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (SpqrMergeLoopEnv fuel maxLen polyCapBound) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (.step h1 h2))).2

theorem FitsEnv.spqrMergeLoop_bytesHead {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {wt : WireType} {valCap : BitVec 64} {bs : List (BitVec 8)}
    (hbs : bs.length ≤ maxLen)
    (hfuel : max 1 (2 * bs.length) ≤ fuel)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv fuel maxLen polyCapBound)) :
    FitsEnv M lim st (BytesMerge3EnvCore wt valCap bs) := by
  intro evs hb
  cases hm : mergeBytes wt bs with
  | none =>
    have h1 : SpqrMergeLoopEnv 1 maxLen polyCapBound evs :=
      SpqrMergeLoopEnv.single (fuel := 0) (maxLen := maxLen)
        (.bytesMergeErr wt valCap bs hm hb)
    exact hFit evs (h1.mono_fuel (by omega))
  | some p =>
    rcases p with ⟨v, rest⟩
    have hbound := mergeBytes_len_bound hm
    have h1 : SpqrMergeLoopEnv (0 + 2 * v.length + 1) maxLen polyCapBound evs :=
      SpqrMergeLoopEnv.bytesSingle (fuel := 0) (maxLen := maxLen) (polyCapBound := polyCapBound)
        hm hbs hb
    exact hFit evs (h1.mono_fuel (by omega))

theorem FitsEnv.spqrMergeLoop_bytesTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen polyCapBound : Nat} {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest))
    (hbs : bs.length ≤ maxLen)
    (hb : BytesMerge3EnvCore wt valCap bs evs₁)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv (fuel + 2 * v.length + 1) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (SpqrMergeLoopEnv fuel maxLen polyCapBound) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (hFit (evs₁ ++ evs₂) (.bytesStep wt valCap bs v rest hm hbs hb h2))).2

theorem FitsEnv.spqrMergeLoop_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ maxLen polyCapBound : Nat} {evs₁ : List AllocEvent}
    (h₁ : SpqrMergeLoopEnv f₁ maxLen polyCapBound evs₁)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv (f₁ + f₂) maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (SpqrMergeLoopEnv f₂ maxLen polyCapBound) :=
  fun evs₂ h₂ =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (h₁.append h₂))).2

theorem FitsEnv.spqrMergeLoop_mono {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₁ f₂ maxLen₁ maxLen₂ poly₁ poly₂ : Nat}
    (hf : f₁ ≤ f₂) (hlen : maxLen₁ ≤ maxLen₂) (hpoly : poly₁ ≤ poly₂)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f₂ maxLen₂ poly₂)) :
    FitsEnv M lim st (SpqrMergeLoopEnv f₁ maxLen₁ poly₁) :=
  hFit.mono fun _ h => h.mono hf hlen hpoly

/-! ## 2. Budget-Threaded `Unchunked.{Ct1Sent, EkSentCt1Received}` `merge` Specs -/

/-- Precondition allocation envelope of `Unchunked.Ct1Sent::merge` (depth `1`, `polyCapBound = 0`). -/
def UnchunkedCt1SentMergeEnv (x : UnchunkedCt1SentMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

/-- Postcondition allocation envelope of `Unchunked.Ct1Sent::merge`: proportional to consumed bytes
`x.bs.length - rest.length` on `Ok`, and bounded by `4 * x.bs.length + 8` on `Err`. -/
def UnchunkedCt1SentMergePostEnv (x : UnchunkedCt1SentMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some (_, rest) => SpqrMergeLoopEnv (4 * (x.bs.length - rest.length)) x.bs.length 0 evs
  | none => SpqrMergeLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

theorem unchunkedCt1SentMergePostEnv_imp_pre {x : UnchunkedCt1SentMergeGhost} {evs : List AllocEvent}
    (h : UnchunkedCt1SentMergePostEnv x evs) :
    UnchunkedCt1SentMergeEnv x evs := by
  dsimp only [UnchunkedCt1SentMergePostEnv, UnchunkedCt1SentMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `Unchunked.Ct1Sent::merge`. -/
def unchunkedCt1SentMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp unchunkedMergeStack ∗
      match (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.Ct1Sent, ct1SentPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `Unchunked.Ct1Sent::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def unchunkedCt1SentMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (UnchunkedCt1SentMergeGhost × M.σ) :=
  unchunkedCt1SentMergeSpecOfEnv A lim UnchunkedCt1SentMergeEnv UnchunkedCt1SentMergePostEnv

/-- Precondition allocation envelope of `Unchunked.EkSentCt1Received::merge`. -/
def UnchunkedEkSentCt1ReceivedMergeEnv (x : UnchunkedEkSentCt1ReceivedMergeGhost)
    (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

/-- Postcondition allocation envelope of `Unchunked.EkSentCt1Received::merge`. -/
def UnchunkedEkSentCt1ReceivedMergePostEnv (x : UnchunkedEkSentCt1ReceivedMergeGhost)
    (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
  | some (_, rest) => SpqrMergeLoopEnv (4 * (x.bs.length - rest.length)) x.bs.length 0 evs
  | none => SpqrMergeLoopEnv (4 * x.bs.length + 8) x.bs.length 0 evs

theorem unchunkedEkSentCt1ReceivedMergePostEnv_imp_pre {x : UnchunkedEkSentCt1ReceivedMergeGhost}
    {evs : List AllocEvent} (h : UnchunkedEkSentCt1ReceivedMergePostEnv x evs) :
    UnchunkedEkSentCt1ReceivedMergeEnv x evs := by
  dsimp only [UnchunkedEkSentCt1ReceivedMergePostEnv, UnchunkedEkSentCt1ReceivedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `Unchunked.EkSentCt1Received::merge`. -/
def unchunkedEkSentCt1ReceivedMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp unchunkedMergeStack ∗
      match (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.EkSentCt1Received, ekSentCt1ReceivedPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `Unchunked.EkSentCt1Received::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def unchunkedEkSentCt1ReceivedMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) :=
  unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
    UnchunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv

/-! ## 3. Budget-Threaded `V1State.Chunked.*` `merge` Specs -/

/-- `PolynomialEncoder` capacity upper bound for `Chunked.Ct1Received::merge`. -/
def ct1ReceivedPolyCapBound (x : ChunkedCt1ReceivedMergeGhost) : Nat :=
  Nat.max (optPolyEncoderPtsLen x.msg.sendingEk) (optPolyEncoderPolysLen x.msg.sendingEk) + x.bs.length

def ChunkedCt1ReceivedMergeEnv (x : ChunkedCt1ReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1ReceivedPolyCapBound x) evs

def ChunkedCt1ReceivedMergePostEnv (x : ChunkedCt1ReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (ct1ReceivedPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1ReceivedPolyCapBound x) evs

theorem chunkedCt1ReceivedMergePostEnv_imp_pre {x : ChunkedCt1ReceivedMergeGhost} {evs : List AllocEvent}
    (h : ChunkedCt1ReceivedMergePostEnv x evs) :
    ChunkedCt1ReceivedMergeEnv x evs := by
  dsimp only [ChunkedCt1ReceivedMergePostEnv, ChunkedCt1ReceivedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.Ct1Received::merge`. -/
def chunkedCt1ReceivedMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyEncoderPtsLen x.msg.sendingEk + x.bs.length < 2 ^ 56 ∧
      optPolyEncoderPolysLen x.msg.sendingEk + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (mergeMessage V1State.Chunked.Ct1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct1Received, chunkedCt1ReceivedPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.Ct1Received::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedCt1ReceivedMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedCt1ReceivedMergeGhost × M.σ) :=
  chunkedCt1ReceivedMergeSpecOfEnv A lim ChunkedCt1ReceivedMergeEnv ChunkedCt1ReceivedMergePostEnv

/-- `PolynomialDecoder` capacity upper bound for `Chunked.Ct1Acknowledged::merge`. -/
def ct1AcknowledgedPolyCapBound (x : ChunkedCt1AcknowledgedMergeGhost) : Nat :=
  optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length

def ChunkedCt1AcknowledgedMergeEnv (x : ChunkedCt1AcknowledgedMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1AcknowledgedPolyCapBound x) evs

def ChunkedCt1AcknowledgedMergePostEnv (x : ChunkedCt1AcknowledgedMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (ct1AcknowledgedPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1AcknowledgedPolyCapBound x) evs

theorem chunkedCt1AcknowledgedMergePostEnv_imp_pre {x : ChunkedCt1AcknowledgedMergeGhost}
    {evs : List AllocEvent} (h : ChunkedCt1AcknowledgedMergePostEnv x evs) :
    ChunkedCt1AcknowledgedMergeEnv x evs := by
  dsimp only [ChunkedCt1AcknowledgedMergePostEnv, ChunkedCt1AcknowledgedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.Ct1Acknowledged::merge`. -/
def chunkedCt1AcknowledgedMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedCt1AcknowledgedMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedCt1AcknowledgedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedCt1AcknowledgedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt1AcknowledgedPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct1Acknowledged, chunkedCt1AcknowledgedPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.Ct1Acknowledged::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedCt1AcknowledgedMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedCt1AcknowledgedMergeGhost × M.σ) :=
  chunkedCt1AcknowledgedMergeSpecOfEnv A lim
    ChunkedCt1AcknowledgedMergeEnv ChunkedCt1AcknowledgedMergePostEnv

/-- `PolynomialDecoder` capacity upper bound for `Chunked.EkSentCt1Received::merge`. -/
def ekSentCt1ReceivedPolyCapBound (x : ChunkedEkSentCt1ReceivedMergeGhost) : Nat :=
  optPolyDecoderPtsLen x.msg.receivingCt2 + x.bs.length

def ChunkedEkSentCt1ReceivedMergeEnv (x : ChunkedEkSentCt1ReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ekSentCt1ReceivedPolyCapBound x) evs

def ChunkedEkSentCt1ReceivedMergePostEnv (x : ChunkedEkSentCt1ReceivedMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (ekSentCt1ReceivedPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ekSentCt1ReceivedPolyCapBound x) evs

theorem chunkedEkSentCt1ReceivedMergePostEnv_imp_pre {x : ChunkedEkSentCt1ReceivedMergeGhost}
    {evs : List AllocEvent} (h : ChunkedEkSentCt1ReceivedMergePostEnv x evs) :
    ChunkedEkSentCt1ReceivedMergeEnv x evs := by
  dsimp only [ChunkedEkSentCt1ReceivedMergePostEnv, ChunkedEkSentCt1ReceivedMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.EkSentCt1Received::merge`. -/
def chunkedEkSentCt1ReceivedMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyDecoderPtsLen x.msg.receivingCt2 + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.EkSentCt1Received, chunkedEkSentCt1ReceivedPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.EkSentCt1Received::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedEkSentCt1ReceivedMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedEkSentCt1ReceivedMergeGhost × M.σ) :=
  chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
    ChunkedEkSentCt1ReceivedMergeEnv ChunkedEkSentCt1ReceivedMergePostEnv

/-- `Polynomial{Encoder,Decoder}` capacity upper bound for `Chunked.Ct1Sampled::merge`. -/
def ct1SampledPolyCapBound (x : ChunkedCt1SampledMergeGhost) : Nat :=
  Nat.max
    (Nat.max (optPolyEncoderPtsLen x.msg.sendingCt1) (optPolyEncoderPolysLen x.msg.sendingCt1))
    (optPolyDecoderPtsLen x.msg.receivingEk) + x.bs.length

def ChunkedCt1SampledMergeEnv (x : ChunkedCt1SampledMergeGhost) (evs : List AllocEvent) : Prop :=
  SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1SampledPolyCapBound x) evs

def ChunkedCt1SampledMergePostEnv (x : ChunkedCt1SampledMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
  | some (_, rest) =>
    SpqrMergeLoopEnv (6 * (x.bs.length - rest.length)) x.bs.length (ct1SampledPolyCapBound x) evs
  | none =>
    SpqrMergeLoopEnv (6 * x.bs.length + 12) x.bs.length (ct1SampledPolyCapBound x) evs

theorem chunkedCt1SampledMergePostEnv_imp_pre {x : ChunkedCt1SampledMergeGhost}
    {evs : List AllocEvent} (h : ChunkedCt1SampledMergePostEnv x evs) :
    ChunkedCt1SampledMergeEnv x evs := by
  dsimp only [ChunkedCt1SampledMergePostEnv, ChunkedCt1SampledMergeEnv] at h ⊢
  split at h
  · exact h.mono_fuel (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded contract of `V1State.Chunked.Ct1Sampled::merge`. -/
def chunkedCt1SampledMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : ChunkedCt1SampledMergeGhost → List AllocEvent → Prop) :
    Spec (ChunkedCt1SampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyEncoderPtsLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 ∧
      optPolyEncoderPolysLen x.msg.sendingCt1 + x.bs.length < 2 ^ 56 ∧
      optPolyDecoderPtsLen x.msg.receivingEk + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      chunkedCt1SampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp chunkedMergeStack ∗
      match (mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt1SampledPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct1Sampled, chunkedCt1SampledPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded contract of `V1State.Chunked.Ct1Sampled::merge` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chunkedCt1SampledMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChunkedCt1SampledMergeGhost × M.σ) :=
  chunkedCt1SampledMergeSpecOfEnv A lim
    ChunkedCt1SampledMergeEnv ChunkedCt1SampledMergePostEnv

/-! ## 4. Linear `PhaseCreditSpec` & `FitsEnv fineCostModel` Witnesses -/

/-- Per-unit `cumSmall` bound for `SpqrMergeLoopEnv` (`96 * polyCapBound + 19110`). -/
def spqrStepCum (polyCapBound : Nat) : Nat :=
  96 * polyCapBound + 19110

/-- Per-unit `liveLarge` / `peakLarge` bound for `SpqrMergeLoopEnv` (`48 * polyCapBound + 16406`). -/
def spqrStepLive (polyCapBound : Nat) : Nat :=
  48 * polyCapBound + 16406

private def nonFreeCount : List AllocEvent → Nat
  | [] => 0
  | .free _ _ :: tl => nonFreeCount tl
  | _ :: tl => nonFreeCount tl + 1

private theorem nonFreeCount_append :
    ∀ (xs ys : List AllocEvent), nonFreeCount (xs ++ ys) = nonFreeCount xs + nonFreeCount ys
  | [], _ => by simp [nonFreeCount]
  | .free _ _ :: xs, ys => by simp [nonFreeCount, nonFreeCount_append xs ys]
  | .alloc _ :: xs, ys => by simp [nonFreeCount, nonFreeCount_append xs ys]; omega
  | .aligned _ _ :: xs, ys => by simp [nonFreeCount, nonFreeCount_append xs ys]; omega
  | .realloc _ _ _ :: xs, ys => by simp [nonFreeCount, nonFreeCount_append xs ys]; omega

private theorem rustAllocEvents_bounds {req al maxReq : Nat}
    (hreq : req ≤ maxReq) (hal : al ≤ 16) :
    nonFreeCount (rustAllocEvents req al) ≤ 1 ∧
      ∀ ev ∈ rustAllocEvents req al, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split
  · refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hreq, by simp [eventStepAlign]⟩
  · refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hreq, by simp only [eventStepAlign]; omega⟩

private theorem rustDeallocEvents_bounds (req al maxReq : Nat) :
    nonFreeCount (rustDeallocEvents req al) = 0 ∧
      ∀ ev ∈ rustDeallocEvents req al, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustDeallocEvents
  refine ⟨by simp [nonFreeCount], ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.zero_le maxReq, by simp [eventStepAlign]⟩

private theorem rustReallocEvents_bounds {old new al maxReq : Nat}
    (hnew : new ≤ maxReq) (hal : al ≤ 16) :
    nonFreeCount (rustReallocEvents old new al) ≤ 1 ∧
      ∀ ev ∈ rustReallocEvents old new al, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  split
  · refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hnew, hal⟩
  · refine ⟨by simp [nonFreeCount], ?_⟩
    intro ev hev
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · exact ⟨hnew, by simp only [eventStepAlign]; omega⟩
    · exact ⟨Nat.zero_le maxReq, by simp [eventStepAlign]⟩

private theorem doReserveClearEvents_bounds {cap vLen maxReq : Nat}
    (hcap_bound : max 8 (2 * vLen) ≤ maxReq) :
    nonFreeCount (doReserveClearEvents cap vLen) ≤ 1 ∧
      ∀ ev ∈ doReserveClearEvents cap vLen, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold doReserveClearEvents
  split
  · exact ⟨by simp [nonFreeCount], (fun _ h => nomatch h)⟩
  · have hnew : reserveCap cap 0 vLen ≤ maxReq := by
      unfold reserveCap
      omega
    split
    · exact rustAllocEvents_bounds hnew (by decide)
    · exact rustReallocEvents_bounds hnew (by decide)

private theorem deallocs_bounds {maxReq : Nat} :
    ∀ {evs : List AllocEvent},
      (∀ ev ∈ evs, ∃ al sz, ev = .free al sz) →
      nonFreeCount evs = 0 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16
  | [], _ => ⟨rfl, (fun _ hm => nomatch hm)⟩
  | ev :: tl, hf => by
    obtain ⟨al, sz, rfl⟩ := hf ev List.mem_cons_self
    obtain ⟨hc, hb⟩ := deallocs_bounds (maxReq := maxReq)
      (fun e he => hf e (List.mem_cons_of_mem _ he))
    refine ⟨by simp [nonFreeCount, hc], fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | htl
    · exact ⟨Nat.zero_le maxReq, by simp [eventStepAlign]⟩
    · exact hb e htl

private theorem stepEvents_bounded_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxReq : Nat) :
    ∀ (evs : List AllocEvent) (maxAllocs : Nat) (st0 : M.σ),
      nonFreeCount evs ≤ maxAllocs →
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxAllocs * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 + maxAllocs * (maxReq + 8195) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + maxAllocs * (maxReq + 8195))
  | [], _, st0, _, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    omega
  | .free al sz :: tl, maxAllocs, st0, hcnt, hall => by
    simp only [AllocCostModel.stepEvents_cons]
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_bounded_le hM maxReq tl maxAllocs
      (M.step (.free al sz) st0) hcnt (fun e he => hall e (List.mem_cons_of_mem _ he))
    omega
  | .alloc req :: tl, maxAllocs, st0, hcnt, hall => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_mul : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      have hl_mul : (k + 1) * (maxReq + 8195) = k * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ := hall (.alloc req) List.mem_cons_self
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_bounded_le hM maxReq tl k
        (M.step (.alloc req) st0) (by omega) (fun e he => hall e (List.mem_cons_of_mem _ he))
      omega
  | .aligned al req :: tl, maxAllocs, st0, hcnt, hall => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_mul : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      have hl_mul : (k + 1) * (maxReq + 8195) = k * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ := hall (.aligned al req) List.mem_cons_self
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_bounded_le hM maxReq tl k
        (M.step (.aligned al req) st0) (by omega) (fun e he => hall e (List.mem_cons_of_mem _ he))
      omega
  | .realloc al o n :: tl, maxAllocs, st0, hcnt, hall => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_mul : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      have hl_mul : (k + 1) * (maxReq + 8195) = k * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ := hall (.realloc al o n) List.mem_cons_self
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_bounded_le hM maxReq tl k
        (M.step (.realloc al o n) st0) (by omega) (fun e he => hall e (List.mem_cons_of_mem _ he))
      omega

private theorem spqrMergeSmallStep_bounds {polyCapBound : Nat} {evs : List AllocEvent}
    (h : SpqrMergeSmallStep polyCapBound evs) :
    nonFreeCount evs ≤ 1 ∧
      ∀ ev ∈ evs, eventStepReq ev ≤ max 256 (48 * polyCapBound) ∧ eventStepAlign ev ≤ 16 := by
  cases h with
  | nil => exact ⟨by simp [nonFreeCount], (fun _ hm => nomatch hm)⟩
  | deallocs hf =>
    obtain ⟨hc, hb⟩ := deallocs_bounds (maxReq := max 256 (48 * polyCapBound)) hf
    exact ⟨by omega, hb⟩
  | fromErr =>
    exact rustAllocEvents_bounds (by omega) (by decide)
  | pushErr hn hp =>
    rcases hp with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨by simp [nonFreeCount], (fun _ hm => nomatch hm)⟩
    · exact rustAllocEvents_bounds (by omega) (by decide)
    · exact rustReallocEvents_bounds (by omega) (by decide)
  | bytesMergeErr wt valCap bs hm hb =>
    unfold BytesMerge3EnvCore bytesMergeEventsCore at hb
    rw [hm] at hb
    subst hb
    exact rustAllocEvents_bounds (by omega) (by decide)
  | growVecU8 g hcap hg =>
    unfold GrowOneVecU8Env RawVecGrowEnv at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact rustAllocEvents_bounds (by omega) (by decide)
    · have hnew : rawVecNewCap 4 g.cap.toNat * 24 ≤ max 256 (48 * polyCapBound) := by
        unfold rawVecNewCap
        omega
      exact rustReallocEvents_bounds hnew (by decide)

private theorem spqrMergeLoopEnv_linear_credit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {fuel maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : SpqrMergeLoopEnv fuel maxLen polyCapBound evs) :
    (∀ ev ∈ evs,
      eventStepReq ev ≤ max (max 256 (48 * polyCapBound)) (2 * maxLen + 8) ∧
        eventStepAlign ev ≤ 16) ∧
      ∀ st0 : M.σ,
        HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
          HasFineReallocCredit.cumSmall st0 + spqrStepCum polyCapBound * fuel ∧
        HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
          HasFineReallocCredit.liveLarge st0 + spqrStepLive polyCapBound * fuel ∧
        HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
          max (HasFineReallocCredit.peakLarge st0)
            (HasFineReallocCredit.liveLarge st0 + spqrStepLive polyCapBound * fuel) := by
  induction h with
  | nil =>
    refine ⟨(fun _ hm => nomatch hm), fun st0 => ?_⟩
    simp only [AllocCostModel.stepEvents_nil]
    omega
  | @step fuel maxLen polyCapBound evs₁ evs₂ h1 _ ih =>
    obtain ⟨hc₁, hb₁⟩ := spqrMergeSmallStep_bounds h1
    obtain ⟨hb₂, hst₂⟩ := ih
    refine ⟨fun ev hev => ?_, fun st0 => ?_⟩
    · rcases List.mem_append.mp hev with m1 | m2
      · obtain ⟨hr, ha⟩ := hb₁ ev m1
        exact ⟨by omega, ha⟩
      · exact hb₂ ev m2
    · rw [M.stepEvents_append]
      obtain ⟨cs₁, ll₁, pk₁⟩ :=
        stepEvents_bounded_le hM (max 256 (48 * polyCapBound)) evs₁ 1 st0 hc₁ hb₁
      obtain ⟨cs₂, ll₂, pk₂⟩ := hst₂ (M.stepEvents evs₁ st0)
      have hcs_step :
          1 * (2 * max 256 (48 * polyCapBound) + 9539) ≤ spqrStepCum polyCapBound := by
        unfold spqrStepCum; omega
      have hll_step :
          1 * (max 256 (48 * polyCapBound) + 8195) ≤ spqrStepLive polyCapBound := by
        unfold spqrStepLive; omega
      have hcs_rhs :
          spqrStepCum polyCapBound * (fuel + 1) =
            spqrStepCum polyCapBound * fuel + spqrStepCum polyCapBound :=
        Nat.mul_succ _ _
      have hll_rhs :
          spqrStepLive polyCapBound * (fuel + 1) =
            spqrStepLive polyCapBound * fuel + spqrStepLive polyCapBound :=
        Nat.mul_succ _ _
      omega
  | @bytesStep fuel maxLen polyCapBound wt valCap bs v rest evs₁ evs₂ hm hbs hb _ ih =>
    unfold BytesMerge3EnvCore at hb
    subst hb
    obtain ⟨hb₂, hst₂⟩ := ih
    have hv_le : v.length ≤ maxLen := by
      have hlen := mergeBytes_len_bound hm
      omega
    have hb₁ : nonFreeCount (bytesMergeEventsCore wt valCap bs) ≤ 2 ∧
        ∀ ev ∈ bytesMergeEventsCore wt valCap bs,
          eventStepReq ev ≤ 2 * v.length + 8 ∧ eventStepAlign ev ≤ 16 := by
      unfold bytesMergeEventsCore
      rw [hm]
      by_cases hv0 : v.length = 0
      · simp only [hv0, ↓reduceIte]
        exact ⟨by simp [nonFreeCount], (fun _ h => nomatch h)⟩
      · simp only [hv0, ↓reduceIte]
        obtain ⟨cA, bA⟩ := rustAllocEvents_bounds (req := v.length) (al := 1)
          (maxReq := 2 * v.length + 8) (by omega) (by decide)
        obtain ⟨cR, bR⟩ := doReserveClearEvents_bounds (cap := valCap.toNat) (vLen := v.length)
          (maxReq := 2 * v.length + 8) (by omega)
        obtain ⟨cD, bD⟩ := rustDeallocEvents_bounds v.length 1 (2 * v.length + 8)
        simp only [List.append_assoc, nonFreeCount_append]
        refine ⟨by omega, fun ev hev => ?_⟩
        rcases List.mem_append.mp hev with mA | mRest
        · exact bA ev mA
        · rcases List.mem_append.mp mRest with mR | mD
          · exact bR ev mR
          · exact bD ev mD
    refine ⟨fun ev hev => ?_, fun st0 => ?_⟩
    · rcases List.mem_append.mp hev with m1 | m2
      · obtain ⟨hr, ha⟩ := hb₁.2 ev m1
        exact ⟨by omega, ha⟩
      · exact hb₂ ev m2
    · rw [M.stepEvents_append]
      obtain ⟨cs₁, ll₁, pk₁⟩ := stepEvents_bounded_le hM (2 * v.length + 8)
        (bytesMergeEventsCore wt valCap bs) 2 st0 hb₁.1 hb₁.2
      obtain ⟨cs₂, ll₂, pk₂⟩ := hst₂ (M.stepEvents (bytesMergeEventsCore wt valCap bs) st0)
      have hcs_lhs : 2 * (2 * (2 * v.length + 8) + 9539) = 8 * v.length + 19110 := by
        rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
      have hcs_v : 8 * v.length ≤ spqrStepCum polyCapBound * (2 * v.length) := by
        have h1 : 8 * v.length ≤ 19110 * (2 * v.length) := by
          rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right v.length (by omega)
        have h2 : 19110 * (2 * v.length) ≤ spqrStepCum polyCapBound * (2 * v.length) :=
          Nat.mul_le_mul_right (2 * v.length) (by unfold spqrStepCum; omega)
        exact Nat.le_trans h1 h2
      have hcs_c0 : 19110 ≤ spqrStepCum polyCapBound := by unfold spqrStepCum; omega
      have hcs_rhs :
          spqrStepCum polyCapBound * (fuel + 2 * v.length + 1) =
            spqrStepCum polyCapBound * fuel +
              spqrStepCum polyCapBound * (2 * v.length) +
              spqrStepCum polyCapBound := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have hll_lhs : 2 * (2 * v.length + 8 + 8195) = 4 * v.length + 16406 := by
        rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
      have hll_v : 4 * v.length ≤ spqrStepLive polyCapBound * (2 * v.length) := by
        have h1 : 4 * v.length ≤ 16406 * (2 * v.length) := by
          rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right v.length (by omega)
        have h2 : 16406 * (2 * v.length) ≤ spqrStepLive polyCapBound * (2 * v.length) :=
          Nat.mul_le_mul_right (2 * v.length) (by unfold spqrStepLive; omega)
        exact Nat.le_trans h1 h2
      have hll_c0 : 16406 ≤ spqrStepLive polyCapBound := by unfold spqrStepLive; omega
      have hll_rhs :
          spqrStepLive polyCapBound * (fuel + 2 * v.length + 1) =
            spqrStepLive polyCapBound * fuel +
              spqrStepLive polyCapBound * (2 * v.length) +
              spqrStepLive polyCapBound := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega

/-- Linear `PhaseCreditSpec` (`O(fuel * (polyCapBound + 1))`) for
`SpqrMergeLoopEnv fuel maxLen polyCapBound`. -/
theorem spqrMergeLoopEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (fuel maxLen polyCapBound : Nat) :
    PhaseCreditSpec M (SpqrMergeLoopEnv fuel maxLen polyCapBound)
      (spqrStepCum polyCapBound * fuel)
      (spqrStepLive polyCapBound * fuel)
      (spqrStepLive polyCapBound * fuel)
      (max (max 256 (48 * polyCapBound)) (2 * maxLen + 8)) where
  req_align _ hE ev hev := (spqrMergeLoopEnv_linear_credit hM hE).1 ev hev
  credit_le st0 {_} hE := (spqrMergeLoopEnv_linear_credit hM hE).2 st0

/-- Explicit `1 GiB` (`2 ^ 30`) `BudgetLimits` literal for `FitsEnv fineCostModel` witnesses. -/
def spqrMergeWitnessLimits : BudgetLimits :=
  { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 2 ^ 30, enforced := true }

def spqrWitnessBytes : List (BitVec 8) := [3#8, 1#8, 2#8, 3#8]

theorem decodeErrorPushMergeEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ DecodeErrorPushMergeEnv 1 evs :=
  ⟨rustReallocEvents (1 * 32) (max (2 * 1) 4 * 32) 8, by decide, Or.inr (Or.inr ⟨by decide, rfl⟩)⟩

theorem bytesMerge3EnvCore_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ BytesMerge3EnvCore .lengthDelimited 0#64 spqrWitnessBytes evs :=
  ⟨bytesMergeEventsCore .lengthDelimited 0#64 spqrWitnessBytes, by decide, rfl⟩

theorem spqrMergeSmallStep_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ SpqrMergeSmallStep 1 evs :=
  ⟨rustAllocEvents 72 8, by decide, .fromErr⟩

theorem spqrMergeIterEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ SpqrMergeIterEnv 4 1 evs :=
  spqrMergeSmallStep_inhabited

theorem spqrMergeLoopEnv_inhabited {fuel polyCapBound : Nat} (hf : 7 ≤ fuel) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ SpqrMergeLoopEnv fuel 4 polyCapBound evs := by
  refine ⟨bytesMergeEventsCore .lengthDelimited 0#64 spqrWitnessBytes, by decide, ?_⟩
  have hm : mergeBytes .lengthDelimited spqrWitnessBytes = some ([1#8, 2#8, 3#8], []) := by
    decide
  have h1 : SpqrMergeLoopEnv (0 + 2 * [1#8, 2#8, 3#8].length + 1) 4 polyCapBound
      (bytesMergeEventsCore .lengthDelimited 0#64 spqrWitnessBytes) :=
    SpqrMergeLoopEnv.bytesSingle (fuel := 0) (maxLen := 4) (polyCapBound := polyCapBound)
      hm (by decide) rfl
  exact h1.mono_fuel (by simpa using hf)

theorem spqrMergeLoopEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init (SpqrMergeLoopEnv 36 4 4) :=
  fitsEnv_fineCostModel_of_phaseCredit
    (spqrMergeLoopEnv_phaseCreditSpec fineCostModel_modelHyps 36 4 4)
    (by decide) rfl (by decide) (by decide)

theorem spqrMergeSmallStep_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init (SpqrMergeSmallStep 1) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h =>
    (SpqrMergeLoopEnv.single (fuel := 0) (maxLen := 4) h).mono (by decide) (by decide) (by decide)

theorem spqrMergeIterEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init (SpqrMergeIterEnv 4 1) :=
  spqrMergeSmallStep_fitsEnv_witness

theorem decodeErrorPushMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (DecodeErrorPushMergeEnv 1) :=
  spqrMergeSmallStep_fitsEnv_witness.mono fun _ h => .pushErr (by decide) h

theorem bytesMerge3EnvCore_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (BytesMerge3EnvCore .lengthDelimited 0#64 spqrWitnessBytes) :=
  FitsEnv.spqrMergeLoop_bytesHead (by decide) (by decide) spqrMergeLoopEnv_fitsEnv_witness

def unchunkedCt1SentWitnessGhost : UnchunkedCt1SentMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

def unchunkedEkSentCt1ReceivedWitnessGhost : UnchunkedEkSentCt1ReceivedMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

def chunkedCt1ReceivedWitnessGhost : ChunkedCt1ReceivedMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

def chunkedCt1AcknowledgedWitnessGhost : ChunkedCt1AcknowledgedMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

def chunkedEkSentCt1ReceivedWitnessGhost : ChunkedEkSentCt1ReceivedMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

def chunkedCt1SampledWitnessGhost : ChunkedCt1SampledMergeGhost :=
  { wt := .varint, msgPtr := 0#64, msg := default, bufRef := 0#64, slot := 0#64,
    ptr := 0#64, bs := spqrWitnessBytes }

theorem unchunkedCt1SentMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ UnchunkedCt1SentMergePostEnv unchunkedCt1SentWitnessGhost evs :=
  spqrMergeLoopEnv_inhabited (by decide)

theorem unchunkedCt1SentMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (UnchunkedCt1SentMergeEnv unchunkedCt1SentWitnessGhost) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem unchunkedCt1SentMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (UnchunkedCt1SentMergePostEnv unchunkedCt1SentWitnessGhost) :=
  unchunkedCt1SentMergeEnv_fitsEnv_witness.mono fun _ => unchunkedCt1SentMergePostEnv_imp_pre

theorem unchunkedEkSentCt1ReceivedMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧
        UnchunkedEkSentCt1ReceivedMergePostEnv unchunkedEkSentCt1ReceivedWitnessGhost evs :=
  spqrMergeLoopEnv_inhabited (by decide)

theorem unchunkedEkSentCt1ReceivedMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (UnchunkedEkSentCt1ReceivedMergeEnv unchunkedEkSentCt1ReceivedWitnessGhost) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem unchunkedEkSentCt1ReceivedMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (UnchunkedEkSentCt1ReceivedMergePostEnv unchunkedEkSentCt1ReceivedWitnessGhost) :=
  unchunkedEkSentCt1ReceivedMergeEnv_fitsEnv_witness.mono fun _ =>
    unchunkedEkSentCt1ReceivedMergePostEnv_imp_pre

theorem chunkedCt1ReceivedMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ ChunkedCt1ReceivedMergePostEnv chunkedCt1ReceivedWitnessGhost evs :=
  spqrMergeLoopEnv_inhabited (by decide)

theorem chunkedCt1ReceivedMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedCt1ReceivedMergeEnv chunkedCt1ReceivedWitnessGhost) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem chunkedCt1ReceivedMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedCt1ReceivedMergePostEnv chunkedCt1ReceivedWitnessGhost) :=
  chunkedCt1ReceivedMergeEnv_fitsEnv_witness.mono fun _ => chunkedCt1ReceivedMergePostEnv_imp_pre

theorem chunkedCt1AcknowledgedMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ ChunkedCt1AcknowledgedMergePostEnv chunkedCt1AcknowledgedWitnessGhost evs :=
  spqrMergeLoopEnv_inhabited (by decide)

theorem chunkedCt1AcknowledgedMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedCt1AcknowledgedMergeEnv chunkedCt1AcknowledgedWitnessGhost) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem chunkedCt1AcknowledgedMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedCt1AcknowledgedMergePostEnv chunkedCt1AcknowledgedWitnessGhost) :=
  chunkedCt1AcknowledgedMergeEnv_fitsEnv_witness.mono fun _ =>
    chunkedCt1AcknowledgedMergePostEnv_imp_pre

theorem chunkedEkSentCt1ReceivedMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ ChunkedEkSentCt1ReceivedMergePostEnv chunkedEkSentCt1ReceivedWitnessGhost evs :=
  spqrMergeLoopEnv_inhabited (by decide)

theorem chunkedEkSentCt1ReceivedMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedEkSentCt1ReceivedMergeEnv chunkedEkSentCt1ReceivedWitnessGhost) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem chunkedEkSentCt1ReceivedMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedEkSentCt1ReceivedMergePostEnv chunkedEkSentCt1ReceivedWitnessGhost) :=
  chunkedEkSentCt1ReceivedMergeEnv_fitsEnv_witness.mono fun _ =>
    chunkedEkSentCt1ReceivedMergePostEnv_imp_pre

theorem chunkedCt1SampledMergePostEnv_inhabited :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ ChunkedCt1SampledMergePostEnv chunkedCt1SampledWitnessGhost evs :=
  spqrMergeLoopEnv_inhabited (by decide)

theorem chunkedCt1SampledMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedCt1SampledMergeEnv chunkedCt1SampledWitnessGhost) :=
  spqrMergeLoopEnv_fitsEnv_witness.mono fun _ h => h.mono (by decide) (by decide) (by decide)

theorem chunkedCt1SampledMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel spqrMergeWitnessLimits fineCostModel.init
      (ChunkedCt1SampledMergePostEnv chunkedCt1SampledWitnessGhost) :=
  chunkedCt1SampledMergeEnv_fitsEnv_witness.mono fun _ => chunkedCt1SampledMergePostEnv_imp_pre

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
