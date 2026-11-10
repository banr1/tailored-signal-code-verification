/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep

/-!
# Budget-Threaded Record Decoder Envelopes and Callee Contracts

`RustCliAllocBudget`-threaded allocation envelopes (`DecodeErrorPushBoundedEnv`,
`RecordCodecLoopEnv`, `PreKeyDeserializeEnv`, `IdentityKeyPairTryFromEnv`), linear
`PhaseCreditSpec` bounds, `FitsEnv fineCostModel` satisfiability witnesses, and relocatable
`[LibsignalPlacement]` dependency bundles (`CodecHooksPlaced`, `PortDepsPlaced`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.RecordCodecs.DepsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary
  (DecodeGhost preKeyResultAt identityKeyPairResultAt identityKeyResultAt
   ls_subroutine_ok_lscro_of_block ls_subroutine_ok_lscro_of_cl
   ls_subroutine_ok_lscro_of_plain sepWPp_of_sepWP_lscro)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   fitsEvents_append rustAllocEvents rustDeallocEvents rustReallocEvents
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved DecodeErrorFromEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustDeallocExternSpecWithStack rustDeallocExternWithStack_of_rustDealloc
   decodeErrorFromSpecWithStack decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DropDecodeErrorEnv dropDecodeErrorSpecX
   DecodeVarintSliceEnv decodeVarintSliceEvents decodeVarintSliceSpecX
   Int32MergeEnv int32MergeEvents int32MergeSpecX
   SkipFieldEnv skipFieldEventsCore skipFieldSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore bytesMergeRawSpecX doReserveClearEvents)

/-! ## 1. Callee-Fixed Loop & Cleanup Event Envelopes -/

/-- Deterministic `DecodeError::push` allocation envelope at stack length `n`:
no-op when `n < cap`, initial `4 * 32 = 128` B allocation when `n = cap = 0`, or
doubling `realloc` from `n * 32` to `max (2 * n) 4 * 32` when `0 < n = cap`. -/
def DecodeErrorPushBoundedEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ evs = rustAllocEvents (4 * 32) 8) ∨
  (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)

/-- Bounded-envelope counterpart of `decodeErrorPushExternBudgetSpecWithStack`,
using `DecodeErrorPushBoundedEnv n` so `FitsEnv` is satisfiable at `n = 0`. -/
def decodeErrorPushBoundedExternBudgetSpecWithStack (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ e ≠ 0#64 ∧ n < 2 ^ 32 ∧
      FitsEnv M lim st (DecodeErrorPushBoundedEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp hookStack
  post := fun (d, _, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ e' : BitVec 64, ⌜e' ≠ 0#64⌝ ∗ (d ↦₆₄ e') ∗
        decodeErrorAtStackLen A.repAlloc e' (n + 1)) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushBoundedEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp hookStack

abbrev decodeErrorPushBoundedExternSpecWithStack :=
  @decodeErrorPushBoundedExternBudgetSpecWithStack

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

/-- Bounded constant-size single-call step inside `PreKeyRecord::deserialize` or
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (`[]`, `72` B `DecodeError::from`,
or `≤ 128` B `DecodeError::push` at depth `0`). -/
inductive RecordCodecErrStep : List AllocEvent → Prop where
  | nil : RecordCodecErrStep []
  | fromErr : RecordCodecErrStep (rustAllocEvents 72 8)
  | push0 {evs : List AllocEvent} : DecodeErrorPushBoundedEnv 0 evs → RecordCodecErrStep evs

/-- Compatibility alias preserving `RecordCodecIterEnv maxLen` for non-`bytesMerge` steps. -/
abbrev RecordCodecIterEnv (_maxLen : Nat) : List AllocEvent → Prop :=
  RecordCodecErrStep

theorem RecordCodecIterEnv.mono_maxLen {m₁ m₂ : Nat} {evs : List AllocEvent}
    (_hle : m₁ ≤ m₂) (h : RecordCodecIterEnv m₁ evs) : RecordCodecIterEnv m₂ evs :=
  h

theorem RecordCodecIterEnv.of_decodeErrorFrom {maxLen : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) : RecordCodecIterEnv maxLen evs := by
  rw [h]; exact .fromErr

theorem RecordCodecIterEnv.of_decodeErrorPush0 {maxLen : Nat} {evs : List AllocEvent}
    (h : DecodeErrorPushBoundedEnv 0 evs) : RecordCodecIterEnv maxLen evs :=
  .push0 h

theorem RecordCodecIterEnv.of_decodeVarintSlice {maxLen : Nat} {bs : List (BitVec 8)}
    {evs : List AllocEvent} (h : DecodeVarintSliceEnv bs evs) :
    RecordCodecIterEnv maxLen evs := by
  rw [h]; unfold decodeVarintSliceEvents
  cases decodeVarint bs
  · exact .fromErr
  · exact .nil

theorem RecordCodecIterEnv.of_decodeVarintSlow {maxLen : Nat} {bs : List (BitVec 8)}
    {evs : List AllocEvent} (h : DecodeVarintSlowEnv bs evs) :
    RecordCodecIterEnv maxLen evs := by
  rw [h]; unfold decodeVarintSlowEvents
  cases varintSlow bs
  · exact .fromErr
  · exact .nil

theorem RecordCodecIterEnv.of_int32Merge {maxLen : Nat} {x : Prost.Int32MergeGhost}
    {evs : List AllocEvent} (h : Int32MergeEnv x evs) :
    RecordCodecIterEnv maxLen evs := by
  rw [h]; unfold int32MergeEvents
  cases mergeUint32 x.wt x.bs
  · exact .fromErr
  · exact .nil

theorem RecordCodecIterEnv.of_skipField {maxLen : Nat} {x : Prost.SkipFieldGhost}
    {evs : List AllocEvent} (h : SkipFieldEnv x evs) :
    RecordCodecIterEnv maxLen evs := by
  rw [h]; unfold skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs
  · exact .fromErr
  · exact .nil

theorem RecordCodecIterEnv.of_bytesMergeErr {maxLen : Nat} {x : Prost.BytesMergeGhost}
    {evs : List AllocEvent} (hm : mergeBytes x.wt x.bs = none) (h : BytesMergeEnv x evs) :
    RecordCodecIterEnv maxLen evs := by
  rw [h]
  unfold bytesMergeEventsCore
  rw [hm]
  exact .fromErr

/-- Linear-budget protobuf decode-loop envelope (`budget ≤ 2 * len + 3`, `maxLen = len`):
each constant-size `RecordCodecErrStep` (`≤ 128` B) consumes `1` unit of `budget`, while each
successful `bytes::merge` (`mergeBytes wt bs = some (v, rest)`) consumes `2 * v.length + 1`
units of `budget` for its deterministic `bytesMergeEventsCore wt valCap bs` events, keeping total
cumulative and peak memory strictly `O(budget)`. -/
inductive RecordCodecLoopEnv : Nat → Nat → List AllocEvent → Prop where
  | nil {budget maxLen : Nat} : RecordCodecLoopEnv budget maxLen []
  | step {budget maxLen : Nat} {evs₁ evs₂ : List AllocEvent} :
      RecordCodecErrStep evs₁ → RecordCodecLoopEnv budget maxLen evs₂ →
      RecordCodecLoopEnv (budget + 1) maxLen (evs₁ ++ evs₂)
  | bytesStep {budget maxLen : Nat}
      (wt : WireType) (valCap : BitVec 64) (bs v rest : List (BitVec 8))
      {evs₁ evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ maxLen →
      evs₁ = bytesMergeEventsCore wt valCap bs →
      RecordCodecLoopEnv budget maxLen evs₂ →
      RecordCodecLoopEnv (budget + 2 * v.length + 1) maxLen (evs₁ ++ evs₂)

theorem RecordCodecLoopEnv.single {fuel maxLen : Nat} {evs : List AllocEvent}
    (h : RecordCodecIterEnv maxLen evs) : RecordCodecLoopEnv (fuel + 1) maxLen evs := by
  simpa using RecordCodecLoopEnv.step (budget := fuel) h .nil

theorem RecordCodecLoopEnv.mono_fuel {fuel₁ fuel₂ maxLen : Nat} {evs : List AllocEvent}
    (hle : fuel₁ ≤ fuel₂) (h : RecordCodecLoopEnv fuel₁ maxLen evs) :
    RecordCodecLoopEnv fuel₂ maxLen evs := by
  induction h generalizing fuel₂ with
  | nil => exact .nil
  | @step budget _ evs₁ evs₂ h1 _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 1 := ⟨fuel₂ - 1, by omega⟩
    exact .step h1 (ih (by omega))
  | @bytesStep budget _ wt valCap bs v rest evs₁ evs₂ hm hbs heq _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel₂ = k + 2 * v.length + 1 :=
      ⟨fuel₂ - (2 * v.length + 1), by omega⟩
    exact .bytesStep wt valCap bs v rest hm hbs heq (ih (by omega))

theorem RecordCodecLoopEnv.mono_maxLen {fuel m₁ m₂ : Nat} {evs : List AllocEvent}
    (hle : m₁ ≤ m₂) (h : RecordCodecLoopEnv fuel m₁ evs) :
    RecordCodecLoopEnv fuel m₂ evs := by
  induction h with
  | nil => exact .nil
  | step h1 _ ih => exact .step h1 (ih hle)
  | bytesStep wt valCap bs v rest hm hbs heq _ ih =>
    exact .bytesStep wt valCap bs v rest hm (Nat.le_trans hbs hle) heq (ih hle)

theorem RecordCodecLoopEnv.of_bytesMerge {maxLen : Nat} {x : Prost.BytesMergeGhost}
    {evs : List AllocEvent} (hlen : x.bs.length ≤ maxLen) (h : BytesMergeEnv x evs) :
    RecordCodecLoopEnv (2 * x.bs.length + 1) maxLen evs := by
  cases hm : mergeBytes x.wt x.bs with
  | none =>
    have h1 : RecordCodecLoopEnv 1 maxLen evs :=
      RecordCodecLoopEnv.single (RecordCodecIterEnv.of_bytesMergeErr hm h)
    exact h1.mono_fuel (by omega)
  | some p =>
    rcases p with ⟨v, rest⟩
    have hbound := mergeBytes_len_bound hm
    have hstep : RecordCodecLoopEnv (0 + 2 * v.length + 1) maxLen (evs ++ []) :=
      RecordCodecLoopEnv.bytesStep x.wt x.valCap x.bs v rest hm hlen h .nil
    rw [List.append_nil] at hstep
    exact hstep.mono_fuel (by omega)

theorem fitsEnv_recordCodecLoop_head {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen : Nat} {E : List AllocEvent → Prop}
    (hsub : ∀ evs, E evs → RecordCodecIterEnv maxLen evs)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    FitsEnv M lim st E :=
  fun evs he => hFit evs (RecordCodecLoopEnv.single (hsub evs he))

theorem fitsEnv_recordCodecLoop_bytesHead {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {budget maxLen : Nat} {x : Prost.BytesMergeGhost}
    (hlen : x.bs.length ≤ maxLen) (hbud : 2 * x.bs.length + 1 ≤ budget)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv budget maxLen)) :
    FitsEnv M lim st (BytesMergeEnv x) :=
  fun evs he => hFit evs ((RecordCodecLoopEnv.of_bytesMerge hlen he).mono_fuel hbud)

theorem fitsEnv_recordCodecLoop_tail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel maxLen : Nat} {evs₁ : List AllocEvent}
    (h1 : RecordCodecIterEnv maxLen evs₁)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv fuel maxLen) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (.step h1 h2))).2

theorem fitsEnv_recordCodecLoop_bytesTail {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {budget maxLen : Nat} {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest)) (hlen : bs.length ≤ maxLen)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt valCap bs)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (budget + 2 * v.length + 1) maxLen)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (RecordCodecLoopEnv budget maxLen) :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (hFit (evs₁ ++ evs₂) (.bytesStep wt valCap bs v rest hm hlen hevs₁ h2))).2

theorem fitsEnv_recordCodecLoop_mono_fuel {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {fuel₁ fuel₂ maxLen : Nat} (hle : fuel₁ ≤ fuel₂)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv fuel₂ maxLen)) :
    FitsEnv M lim st (RecordCodecLoopEnv fuel₁ maxLen) :=
  hFit.mono fun _ h => h.mono_fuel hle

/-- Optional `Vec<u8>` buffer deallocation (`cap = 0` or `dealloc(ptr, cap, 1)`). -/
def OptByteFreeEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ∃ cap : Nat, 0 < cap ∧ cap < 2 ^ 63 ∧ evs = rustDeallocEvents cap 1

theorem OptByteFreeEnv.nil : OptByteFreeEnv [] := Or.inl rfl

theorem OptByteFreeEnv.dealloc {cap : Nat} (hpos : 0 < cap) (hlt : cap < 2 ^ 63) :
    OptByteFreeEnv (rustDeallocEvents cap 1) :=
  Or.inr ⟨cap, hpos, hlt, rfl⟩

/-- Up to two `Vec<u8>` buffer deallocations (`public_key`, `private_key`). -/
def TwoOptByteFreeEnv (evs : List AllocEvent) : Prop :=
  ∃ e1 e2 : List AllocEvent, OptByteFreeEnv e1 ∧ OptByteFreeEnv e2 ∧ evs = e1 ++ e2

theorem TwoOptByteFreeEnv.nil : TwoOptByteFreeEnv [] :=
  ⟨[], [], .nil, .nil, rfl⟩

theorem TwoOptByteFreeEnv.single {evs : List AllocEvent} (h : OptByteFreeEnv evs) :
    TwoOptByteFreeEnv evs :=
  ⟨[], evs, .nil, h, rfl⟩

theorem TwoOptByteFreeEnv.pair {e1 e2 : List AllocEvent}
    (h1 : OptByteFreeEnv e1) (h2 : OptByteFreeEnv e2) : TwoOptByteFreeEnv (e1 ++ e2) :=
  ⟨e1, e2, h1, h2, rfl⟩

/-- Protobuf decode-error cleanup: up to two `Vec<u8>` buffer deallocations (`pub`/`pk`, `priv`/`sk`)
followed by `drop_glue::<DecodeError>`. -/
def RecordCodecErrCleanupEnv (evs : List AllocEvent) : Prop :=
  ∃ evsF evsD : List AllocEvent,
    TwoOptByteFreeEnv evsF ∧ DropDecodeErrorEnv evsD ∧ evs = evsF ++ evsD

theorem RecordCodecErrCleanupEnv.of_two_drop {e1 e2 evsD : List AllocEvent}
    (h1 : OptByteFreeEnv e1) (h2 : OptByteFreeEnv e2) (hd : DropDecodeErrorEnv evsD) :
    RecordCodecErrCleanupEnv (e1 ++ (e2 ++ evsD)) :=
  ⟨e1 ++ e2, evsD, .pair h1 h2, hd, (List.append_assoc e1 e2 evsD).symm⟩

/-- Fuel-parameterized event envelope for `PreKeyRecord::deserialize` sub-proofs:
`PkSubEnv (2 * len + 3) len` equals `PreKeyDeserializeEnv len` definitionally (`rfl`). -/
def PkSubEnv (fuel maxLen : Nat) (evs : List AllocEvent) : Prop :=
  RecordCodecLoopEnv fuel maxLen evs ∨
  ∃ evsL evsC : List AllocEvent,
    RecordCodecLoopEnv fuel maxLen evsL ∧ RecordCodecErrCleanupEnv evsC ∧
    evs = evsL ++ evsC

theorem PkSubEnv.of_loop {fuel maxLen : Nat} {evs : List AllocEvent}
    (h : RecordCodecLoopEnv fuel maxLen evs) : PkSubEnv fuel maxLen evs :=
  Or.inl h

theorem PkSubEnv.of_errCleanup {fuel maxLen : Nat} {evsC : List AllocEvent}
    (hC : RecordCodecErrCleanupEnv evsC) : PkSubEnv fuel maxLen evsC :=
  Or.inr ⟨[], evsC, .nil, hC, rfl⟩

theorem PkSubEnv.prepend_iter {fuel maxLen : Nat} {evs₁ evs₂ : List AllocEvent}
    (h1 : RecordCodecIterEnv maxLen evs₁) (h2 : PkSubEnv fuel maxLen evs₂) :
    PkSubEnv (fuel + 1) maxLen (evs₁ ++ evs₂) := by
  rcases h2 with hL | ⟨evsL, evsC, hL, hC, rfl⟩
  · exact Or.inl (.step h1 hL)
  · exact Or.inr ⟨evs₁ ++ evsL, evsC, .step h1 hL, hC, (List.append_assoc _ _ _).symm⟩

theorem PkSubEnv.prepend_bytes {budget maxLen : Nat} {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)} {evs₁ evs₂ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest)) (hlen : bs.length ≤ maxLen)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt valCap bs) (h2 : PkSubEnv budget maxLen evs₂) :
    PkSubEnv (budget + 2 * v.length + 1) maxLen (evs₁ ++ evs₂) := by
  rcases h2 with hL | ⟨evsL, evsC, hL, hC, rfl⟩
  · exact Or.inl (.bytesStep wt valCap bs v rest hm hlen hevs₁ hL)
  · exact Or.inr ⟨evs₁ ++ evsL, evsC,
      .bytesStep wt valCap bs v rest hm hlen hevs₁ hL, hC, (List.append_assoc _ _ _).symm⟩

theorem PkSubEnv.mono_fuel {f₁ f₂ maxLen : Nat} {evs : List AllocEvent}
    (hle : f₁ ≤ f₂) (h : PkSubEnv f₁ maxLen evs) : PkSubEnv f₂ maxLen evs := by
  rcases h with hL | ⟨evsL, evsC, hL, hC, rfl⟩
  · exact Or.inl (hL.mono_fuel hle)
  · exact Or.inr ⟨evsL, evsC, hL.mono_fuel hle, hC, rfl⟩

/-- Callee-fixed event envelope of `PreKeyRecord::deserialize`:
bounded protobuf loop events, optionally followed by `RecordCodecErrCleanupEnv` on `Err`. -/
abbrev PreKeyDeserializeEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  PkSubEnv (2 * len + 3) len evs

theorem PreKeyDeserializeEnv.of_loop {len : Nat} {evs : List AllocEvent}
    (h : RecordCodecLoopEnv (2 * len + 3) len evs) : PreKeyDeserializeEnv len evs :=
  Or.inl h

theorem PreKeyDeserializeEnv.of_loop_errCleanup {len : Nat} {evsL evsC : List AllocEvent}
    (hL : RecordCodecLoopEnv (2 * len + 3) len evsL) (hC : RecordCodecErrCleanupEnv evsC) :
    PreKeyDeserializeEnv len (evsL ++ evsC) :=
  Or.inr ⟨evsL, evsC, hL, hC, rfl⟩

/-- Post-loop deallocation envelope of `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`:
frees up to two temporary `Vec<u8>` buffers (`Ok` or key-validation `Err`), or drops
`DecodeError` and frees up to two `Vec<u8>` buffers (protobuf `Err`). -/
def IkpPostCleanupEnv (evs : List AllocEvent) : Prop :=
  TwoOptByteFreeEnv evs ∨ RecordCodecErrCleanupEnv evs

theorem IkpPostCleanupEnv.nil : IkpPostCleanupEnv [] :=
  Or.inl .nil

theorem IkpPostCleanupEnv.of_twoOpt {evs : List AllocEvent} (h : TwoOptByteFreeEnv evs) :
    IkpPostCleanupEnv evs :=
  Or.inl h

theorem IkpPostCleanupEnv.of_errCleanup {evs : List AllocEvent} (h : RecordCodecErrCleanupEnv evs) :
    IkpPostCleanupEnv evs :=
  Or.inr h

/-- Fuel-parameterized event envelope for `IdentityKeyPair::try_from` sub-proofs:
`IkpSubEnv (2 * len + 3) len` equals `IdentityKeyPairTryFromEnv len` definitionally (`rfl`). -/
def IkpSubEnv (fuel maxLen : Nat) (evs : List AllocEvent) : Prop :=
  ∃ evsL evsC : List AllocEvent,
    RecordCodecLoopEnv fuel maxLen evsL ∧ IkpPostCleanupEnv evsC ∧
    evs = evsL ++ evsC

theorem IkpSubEnv.of_cleanup {fuel maxLen : Nat} {evsC : List AllocEvent}
    (hC : IkpPostCleanupEnv evsC) : IkpSubEnv fuel maxLen evsC :=
  ⟨[], evsC, .nil, hC, rfl⟩

theorem IkpSubEnv.prepend_iter {fuel maxLen : Nat} {evs₁ evs₂ : List AllocEvent}
    (h1 : RecordCodecIterEnv maxLen evs₁) (h2 : IkpSubEnv fuel maxLen evs₂) :
    IkpSubEnv (fuel + 1) maxLen (evs₁ ++ evs₂) := by
  rcases h2 with ⟨evsL, evsC, hL, hC, rfl⟩
  exact ⟨evs₁ ++ evsL, evsC, .step h1 hL, hC, (List.append_assoc _ _ _).symm⟩

theorem IkpSubEnv.prepend_bytes {budget maxLen : Nat} {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)} {evs₁ evs₂ : List AllocEvent}
    (hm : mergeBytes wt bs = some (v, rest)) (hlen : bs.length ≤ maxLen)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt valCap bs) (h2 : IkpSubEnv budget maxLen evs₂) :
    IkpSubEnv (budget + 2 * v.length + 1) maxLen (evs₁ ++ evs₂) := by
  rcases h2 with ⟨evsL, evsC, hL, hC, rfl⟩
  exact ⟨evs₁ ++ evsL, evsC,
    .bytesStep wt valCap bs v rest hm hlen hevs₁ hL, hC, (List.append_assoc _ _ _).symm⟩

theorem IkpSubEnv.mono_fuel {f₁ f₂ maxLen : Nat} {evs : List AllocEvent}
    (hle : f₁ ≤ f₂) (h : IkpSubEnv f₁ maxLen evs) : IkpSubEnv f₂ maxLen evs := by
  rcases h with ⟨evsL, evsC, hL, hC, rfl⟩
  exact ⟨evsL, evsC, hL.mono_fuel hle, hC, rfl⟩

/-- Callee-fixed event envelope of `<IdentityKeyPair as TryFrom<&[u8]>>::try_from`. -/
abbrev IdentityKeyPairTryFromEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  IkpSubEnv (2 * len + 3) len evs

theorem IdentityKeyPairTryFromEnv.of_cleanup {len : Nat} {evsC : List AllocEvent}
    (hC : IkpPostCleanupEnv evsC) : IdentityKeyPairTryFromEnv len evsC :=
  ⟨[], evsC, .nil, hC, rfl⟩

theorem IdentityKeyPairTryFromEnv.of_loop_cleanup {len : Nat} {evsL evsC : List AllocEvent}
    (hL : RecordCodecLoopEnv (2 * len + 3) len evsL) (hC : IkpPostCleanupEnv evsC) :
    IdentityKeyPairTryFromEnv len (evsL ++ evsC) :=
  ⟨evsL, evsC, hL, hC, rfl⟩

/-! ## 2. Relocatable `[LibsignalPlacement]` Contracts & Callee Dependencies -/

/-- Budget-threaded external hook contracts (`__rust_alloc`, `__rust_realloc`, `__rust_dealloc`,
`__rust_no_alloc_shim_is_unstable_v2`, `memcpy`, and OOM panic stubs) sufficient to discharge all
`RecordCodecs` callees on a relocatable `[LibsignalPlacement]`. -/
structure CodecHooksPlaced [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat H lsMemcpySym (withVmPreserved framelessMemcpySpec)
  panic_alloc : H Prost.lsHandleAllocErrorSym = some Rust.panicked
  panic_raw : H lsHandleErrorSym = some Rust.panicked

/-- Relocatable `[LibsignalPlacement]` budget-threaded callee contracts for
`PreKeyRecord::deserialize` (Block `65`), `IdentityKey::decode` (Block `18`), and
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`). -/
structure PortDepsPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  varintSlice :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H) (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim))
  int32Merge :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpecX A lim))
  skipField :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H) (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecX A lim))
  dropDecodeError :
    subroutine_ok ((blkPC_4).rebase (blkPl_4).base H) (blkPl_4).base
      (dropDecodeErrorSpecX A lim)
  bytesMerge :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A lim))
  pkTryFrom :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base
      pkTryFromPlacedSpec
  varintSlow :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack)))
  decodeErrorFrom :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))
  decodeErrorPush :
    subroutine_ok (lsProg_257 H) (blkPl_257).base
      (withLsCodeLoaded lsmpl (decodeErrorPushBoundedExternSpecWithStack M A lim (2 * extHookStack)))
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)

/-- Image-free inner budget-threaded specification of `PreKeyRecord::deserialize`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv`). -/
def preKeyDeserializeRawSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st (RecordCodecLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s.sp smallRootStack ∗
      A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜PreKeyDeserializeEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      preKeyResultAt A.repAlloc x.ret (PreKeyRecord.deserialize x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp smallRootStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded specification of `PreKeyRecord::deserialize`
(Block `65`). -/
abbrev preKeyDeserializePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (preKeyDeserializeRawSpec A lim)

/-- Image-free inner budget-threaded specification of
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from` using `lsLogOff`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv`). -/
def identityKeyPairTryFromRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
      FitsEnv M lim st (RecordCodecLoopEnv (2 * x.bytes.length + 3) x.bytes.length)⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 72 ∗ lsLogOff ∗
      stackAt s.sp smallRootStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ evs : List AllocEvent, ⌜IdentityKeyPairTryFromEnv x.bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp smallRootStack

/-- Relocatable `[LibsignalPlacement]` budget-threaded specification of
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`). -/
abbrev identityKeyPairTryFromPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (DecodeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (identityKeyPairTryFromRawSpec A lim)

/-- Image-free inner specification of `IdentityKey::decode` over `A : RustCliAllocBudget M`
using `lsLogOff` (`IdentityKey::decode` performs zero heap allocations). -/
def identityKeyDecodeRawSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) : Spec DecodeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bytesA ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
      s.readReg64 .x8 = x.ret⌝ ∗
      (x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 48 ∗ lsLogOff ∗ stackAt s.sp 0x60
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ identityKeyResultAt A.repAlloc x.ret (decodeIdentityKey x.bytes) ∗
      (x.bytesA ↦ₛ x.bytes) ∗ lsLogOff ∗ stackAt s0.sp 0x60

/-- Relocatable `[LibsignalPlacement]` specification of `IdentityKey::decode` (Block `18`)
over `A : RustCliAllocBudget M`. -/
abbrev identityKeyDecodePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) : Spec DecodeGhost :=
  withLsCodeLoaded lsmpl (identityKeyDecodeRawSpec A)

/-! ## 3. Deallocation Transfer & `noPanicQp` `Wire.SepWPp` Combinators -/

theorem ls_dealloc_lscro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) (hi_unmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (rustDeallocExternWithStack_of_rustDealloc (by decide) (by decide)
      (ls_hook_ok_of_mem (sym := lsRustDeallocSym) hdealloc (by decide) hi hi_unmut))

/-- Panic postcondition ruling out all panics under `FitsEnv`. -/
def noPanicQp (_s0 : State) : State → SepProp → Prop :=
  fun _ _ => False

theorem sepWPp_frame_noPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Q' : State → SepProp → Prop}
    (h : Wire.SepWPp prog ret s P Q' (noPanicQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    Wire.SepWPp prog ret s (P ∗ F) Q (noPanicQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm, hv⟩⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ Qp : State → SepProp → Prop}
    (h : Wire.SepWPp prog ret s P Q₁ Qp)
    (hq : ∀ sf Pf, Q₁ sf Pf → Q₂ sf Pf) :
    Wire.SepWPp prog ret s P Q₂ Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq1, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hq1, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem sepWPp_of_sepWP_end_noPanic_lscro {prog : Program} {pl : Obj.MultiPlacement}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      Wire.VRegsAt s sf ∧
      (LibsignalCodeRoLoaded pl sf.mem → Q sf Pf))) :
    Wire.SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hcrl.of_keepsFrozen hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_call_noPanic_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : State} {P T F : SepProp} {φ : Prop}
    {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (_htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (noPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcrl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hpan_eq sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hoom
    rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 4. Linear `PhaseCreditSpec` Bounds and `FitsEnv fineCostModel` Witnesses -/

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
  · exact ⟨by simp [nonFreeCount], fun _ h => nomatch h⟩
  · have hnew : reserveCap cap 0 vLen ≤ maxReq := by
      unfold reserveCap
      omega
    split
    · exact rustAllocEvents_bounds hnew (by decide)
    · exact rustReallocEvents_bounds hnew (by decide)

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

private theorem recordCodecErrStep_bounds {evs : List AllocEvent}
    (h : RecordCodecErrStep evs) :
    nonFreeCount evs ≤ 1 ∧
      ∀ ev ∈ evs, eventStepReq ev ≤ 128 ∧ eventStepAlign ev ≤ 16 := by
  cases h with
  | nil => exact ⟨by simp [nonFreeCount], fun _ hm => nomatch hm⟩
  | fromErr => exact rustAllocEvents_bounds (by decide) (by decide)
  | push0 hp =>
    rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
    · exact ⟨by simp [nonFreeCount], fun _ hm => nomatch hm⟩
    · exact rustAllocEvents_bounds (by decide) (by decide)
    · omega

private theorem freeOnly_cleanup_events :
    ∀ {evs : List AllocEvent},
      (OptByteFreeEnv evs ∨ TwoOptByteFreeEnv evs ∨
        RecordCodecErrCleanupEnv evs ∨ IkpPostCleanupEnv evs) →
      nonFreeCount evs = 0 ∧ ∀ ev ∈ evs, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
  have hOpt : ∀ {e}, OptByteFreeEnv e →
      nonFreeCount e = 0 ∧ ∀ ev ∈ e, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
    rintro e (rfl | ⟨cap, _, _, rfl⟩)
    · exact ⟨rfl, fun _ hm => nomatch hm⟩
    · exact rustDeallocEvents_bounds cap 1 0
  have hDrop : ∀ {e}, DropDecodeErrorEnv e →
      nonFreeCount e = 0 ∧ ∀ ev ∈ e, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
    rintro e (rfl | ⟨c, _, _, rfl⟩)
    · exact rustDeallocEvents_bounds 72 8 0
    · obtain ⟨c1, b1⟩ := rustDeallocEvents_bounds (c * 32) 8 0
      obtain ⟨c2, b2⟩ := rustDeallocEvents_bounds 72 8 0
      rw [nonFreeCount_append, c1, c2]
      refine ⟨rfl, fun ev hev => ?_⟩
      rcases List.mem_append.mp hev with m1 | m2
      · exact b1 ev m1
      · exact b2 ev m2
  have hTwo : ∀ {e}, TwoOptByteFreeEnv e →
      nonFreeCount e = 0 ∧ ∀ ev ∈ e, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
    rintro _ ⟨e1, e2, h1, h2, rfl⟩
    obtain ⟨c1, b1⟩ := hOpt h1
    obtain ⟨c2, b2⟩ := hOpt h2
    rw [nonFreeCount_append, c1, c2]
    refine ⟨rfl, fun ev hev => ?_⟩
    rcases List.mem_append.mp hev with m1 | m2
    · exact b1 ev m1
    · exact b2 ev m2
  have hErr : ∀ {e}, RecordCodecErrCleanupEnv e →
      nonFreeCount e = 0 ∧ ∀ ev ∈ e, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
    rintro _ ⟨eF, eD, hF, hD, rfl⟩
    obtain ⟨c1, b1⟩ := hTwo hF
    obtain ⟨c2, b2⟩ := hDrop hD
    rw [nonFreeCount_append, c1, c2]
    refine ⟨rfl, fun ev hev => ?_⟩
    rcases List.mem_append.mp hev with m1 | m2
    · exact b1 ev m1
    · exact b2 ev m2
  rintro evs (h1 | h2 | h3 | (h4a | h4b))
  · exact hOpt h1
  · exact hTwo h2
  · exact hErr h3
  · exact hTwo h4a
  · exact hErr h4b

private theorem recordCodecLoopEnv_linear_credit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {budget maxLen : Nat} {evs : List AllocEvent}
    (h : RecordCodecLoopEnv budget maxLen evs) :
    (∀ ev ∈ evs, eventStepReq ev ≤ max 128 (2 * maxLen + 8) ∧ eventStepAlign ev ≤ 16) ∧
      ∀ st0 : M.σ,
        HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
          HasFineReallocCredit.cumSmall st0 + 19110 * budget ∧
        HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
          HasFineReallocCredit.liveLarge st0 + 16406 * budget ∧
        HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
          max (HasFineReallocCredit.peakLarge st0)
            (HasFineReallocCredit.liveLarge st0 + 16406 * budget) := by
  induction h with
  | nil =>
    refine ⟨(fun _ hm => nomatch hm), fun st0 => ?_⟩
    simp only [AllocCostModel.stepEvents_nil]
    omega
  | @step budget maxLen evs₁ evs₂ h1 _ ih =>
    obtain ⟨hc₁, hb₁⟩ := recordCodecErrStep_bounds h1
    obtain ⟨hb₂, hst₂⟩ := ih
    refine ⟨fun ev hev => ?_, fun st0 => ?_⟩
    · rcases List.mem_append.mp hev with m1 | m2
      · obtain ⟨hr, ha⟩ := hb₁ ev m1
        exact ⟨by omega, ha⟩
      · exact hb₂ ev m2
    · rw [M.stepEvents_append]
      obtain ⟨cs₁, ll₁, pk₁⟩ := stepEvents_bounded_le hM 128 evs₁ 1 st0 hc₁ hb₁
      obtain ⟨cs₂, ll₂, pk₂⟩ := hst₂ (M.stepEvents evs₁ st0)
      omega
  | @bytesStep budget maxLen wt valCap bs v rest evs₁ evs₂ hm hbs heq _ ih =>
    subst heq
    obtain ⟨hb₂, hst₂⟩ := ih
    have hv_le : v.length ≤ maxLen := by
      have hb := mergeBytes_len_bound hm
      omega
    have hb₁ : nonFreeCount (bytesMergeEventsCore wt valCap bs) ≤ 2 ∧
        ∀ ev ∈ bytesMergeEventsCore wt valCap bs,
          eventStepReq ev ≤ 2 * v.length + 8 ∧ eventStepAlign ev ≤ 16 := by
      unfold bytesMergeEventsCore
      rw [hm]
      by_cases hv0 : v.length = 0
      · simp only [hv0, ↓reduceIte]
        exact ⟨by simp [nonFreeCount], fun _ h => nomatch h⟩
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
      have hcs_v : 8 * v.length ≤ 19110 * (2 * v.length) := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right v.length (by omega)
      have hcs_rhs :
          19110 * (budget + 2 * v.length + 1) =
            19110 * budget + 19110 * (2 * v.length) + 19110 := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have hll_lhs : 2 * (2 * v.length + 8 + 8195) = 4 * v.length + 16406 := by
        rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
      have hll_v : 4 * v.length ≤ 16406 * (2 * v.length) := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right v.length (by omega)
      have hll_rhs :
          16406 * (budget + 2 * v.length + 1) =
            16406 * budget + 16406 * (2 * v.length) + 16406 := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega

/-- Linear `PhaseCreditSpec` (`O(budget)`) for `RecordCodecLoopEnv budget maxLen`. -/
theorem recordCodecLoopEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (budget maxLen : Nat) :
    PhaseCreditSpec M (RecordCodecLoopEnv budget maxLen)
      (19110 * budget) (16406 * budget) (16406 * budget) (max 128 (2 * maxLen + 8)) where
  req_align _ hE ev hev := (recordCodecLoopEnv_linear_credit hM hE).1 ev hev
  credit_le st0 {_} hE := (recordCodecLoopEnv_linear_credit hM hE).2 st0

/-- Linear `PhaseCreditSpec` for `PkSubEnv budget maxLen` (including `PreKeyDeserializeEnv len`). -/
theorem pkSubEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (budget maxLen : Nat) :
    PhaseCreditSpec M (PkSubEnv budget maxLen)
      (19110 * budget) (16406 * budget) (16406 * budget) (max 128 (2 * maxLen + 8)) where
  req_align _ hE ev hev := by
    rcases hE with hL | ⟨evsL, evsC, hL, hC, rfl⟩
    · exact (recordCodecLoopEnv_linear_credit hM hL).1 ev hev
    · rcases List.mem_append.mp hev with mL | mC
      · exact (recordCodecLoopEnv_linear_credit hM hL).1 ev mL
      · obtain ⟨hr, ha⟩ := (freeOnly_cleanup_events (Or.inr (Or.inr (Or.inl hC)))).2 ev mC
        exact ⟨by omega, ha⟩
  credit_le st0 {_} hE := by
    rcases hE with hL | ⟨evsL, evsC, hL, hC, rfl⟩
    · exact (recordCodecLoopEnv_linear_credit hM hL).2 st0
    · rw [M.stepEvents_append]
      obtain ⟨cs₁, ll₁, pk₁⟩ := (recordCodecLoopEnv_linear_credit hM hL).2 st0
      obtain ⟨cFree, bFree⟩ := freeOnly_cleanup_events (Or.inr (Or.inr (Or.inl hC)))
      obtain ⟨cs₂, ll₂, pk₂⟩ := stepEvents_bounded_le hM 0 evsC 0
        (M.stepEvents evsL st0) (by omega) bFree
      omega

/-- Linear `PhaseCreditSpec` for `IkpSubEnv budget maxLen` (including `IdentityKeyPairTryFromEnv len`). -/
theorem ikpSubEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (budget maxLen : Nat) :
    PhaseCreditSpec M (IkpSubEnv budget maxLen)
      (19110 * budget) (16406 * budget) (16406 * budget) (max 128 (2 * maxLen + 8)) where
  req_align _ hE ev hev := by
    rcases hE with ⟨evsL, evsC, hL, hC, rfl⟩
    rcases List.mem_append.mp hev with mL | mC
    · exact (recordCodecLoopEnv_linear_credit hM hL).1 ev mL
    · obtain ⟨hr, ha⟩ := (freeOnly_cleanup_events (Or.inr (Or.inr (Or.inr hC)))).2 ev mC
      exact ⟨by omega, ha⟩
  credit_le st0 {_} hE := by
    rcases hE with ⟨evsL, evsC, hL, hC, rfl⟩
    rw [M.stepEvents_append]
    obtain ⟨cs₁, ll₁, pk₁⟩ := (recordCodecLoopEnv_linear_credit hM hL).2 st0
    obtain ⟨cFree, bFree⟩ := freeOnly_cleanup_events (Or.inr (Or.inr (Or.inr hC)))
    obtain ⟨cs₂, ll₂, pk₂⟩ := stepEvents_bounded_le hM 0 evsC 0
      (M.stepEvents evsL st0) (by omega) bFree
    omega

/-- Explicit `1 GiB` (`2 ^ 30`) `BudgetLimits` literal for `FitsEnv fineCostModel` satisfiability witnesses. -/
def recordCodecWitnessLimits : BudgetLimits :=
  { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 2 ^ 30, enforced := true }

theorem decodeErrorPushBoundedEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ DecodeErrorPushBoundedEnv 1 evs :=
  ⟨rustReallocEvents 32 128 8, by decide, Or.inr (Or.inr ⟨by decide, rfl⟩)⟩

theorem recordCodecErrStep_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ RecordCodecErrStep evs :=
  ⟨rustAllocEvents 72 8, by decide, .fromErr⟩

theorem recordCodecLoopEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ RecordCodecLoopEnv 11 4 evs := by
  refine ⟨bytesMergeEventsCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] ++ [], by decide, ?_⟩
  have hm : mergeBytes .lengthDelimited [3#8, 1#8, 2#8, 3#8] = some ([1#8, 2#8, 3#8], []) := by
    decide
  have h1 : RecordCodecLoopEnv (0 + 2 * [1#8, 2#8, 3#8].length + 1) 4
      (bytesMergeEventsCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] ++ []) :=
    RecordCodecLoopEnv.bytesStep .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] [1#8, 2#8, 3#8] []
      hm (by decide) rfl .nil
  exact h1.mono_fuel (by decide)

theorem preKeyDeserializeEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ PreKeyDeserializeEnv 4 evs := by
  obtain ⟨evs, hne, hL⟩ := recordCodecLoopEnv_inhabited
  exact ⟨evs, hne, PreKeyDeserializeEnv.of_loop hL⟩

theorem identityKeyPairTryFromEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ IdentityKeyPairTryFromEnv 4 evs := by
  obtain ⟨evs, hne, hL⟩ := recordCodecLoopEnv_inhabited
  refine ⟨evs ++ [], by simpa using hne, ?_⟩
  exact IdentityKeyPairTryFromEnv.of_loop_cleanup hL .nil

/-- Satisfiability witness for `RecordCodecLoopEnv 11 4` (allocating `bytesStep` reachable). -/
theorem recordCodecLoopEnv_fitsEnv_witness :
    FitsEnv fineCostModel recordCodecWitnessLimits fineCostModel.init (RecordCodecLoopEnv 11 4) :=
  fitsEnv_fineCostModel_of_phaseCredit
    (recordCodecLoopEnv_phaseCreditSpec fineCostModel_modelHyps 11 4)
    (by decide) rfl (by decide) (by decide)

/-- Satisfiability witness for `RecordCodecErrStep` / `RecordCodecIterEnv 4` (allocating `fromErr`/`push0` reachable). -/
theorem recordCodecErrStep_fitsEnv_witness :
    FitsEnv fineCostModel recordCodecWitnessLimits fineCostModel.init RecordCodecErrStep :=
  recordCodecLoopEnv_fitsEnv_witness.mono fun _ h =>
    (RecordCodecLoopEnv.single (fuel := 0) (maxLen := 4) h).mono_fuel (by decide)

theorem recordCodecIterEnv_fitsEnv_witness :
    FitsEnv fineCostModel recordCodecWitnessLimits fineCostModel.init (RecordCodecIterEnv 4) :=
  recordCodecErrStep_fitsEnv_witness

/-- Satisfiability witness for `DecodeErrorPushBoundedEnv 1` (reallocating disjunct reachable). -/
theorem decodeErrorPushBoundedEnv_fitsEnv_witness :
    FitsEnv fineCostModel recordCodecWitnessLimits fineCostModel.init
      (DecodeErrorPushBoundedEnv 1) := by
  have hSpec : PhaseCreditSpec fineCostModel (DecodeErrorPushBoundedEnv 1) 9795 8323 8323 128 := by
    refine ⟨fun _ hE ev hev => ?_, fun st0 {evs} hE => ?_⟩
    · rcases hE with rfl | ⟨h0, _⟩ | ⟨_, rfl⟩
      · nomatch hev
      · omega
      · exact (rustReallocEvents_bounds (maxReq := 128) (by decide) (by decide)).2 ev hev
    · rcases hE with rfl | ⟨h0, _⟩ | ⟨_, rfl⟩
      · simp only [AllocCostModel.stepEvents_nil]; omega
      · omega
      · obtain ⟨hc, hb⟩ := rustReallocEvents_bounds (old := 1 * 32)
          (new := max (2 * 1) 4 * 32) (al := 8) (maxReq := 128) (by decide) (by decide)
        obtain ⟨cs, ll, pk⟩ := stepEvents_bounded_le fineCostModel_modelHyps 128
          (rustReallocEvents (1 * 32) (max (2 * 1) 4 * 32) 8) 1 st0 hc hb
        omega
  exact fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl (by decide) (by decide)

/-- Satisfiability witness for `PreKeyDeserializeEnv 4` (`PkSubEnv 11 4`, allocating trace reachable). -/
theorem preKeyDeserializeEnv_fitsEnv_witness :
    FitsEnv fineCostModel recordCodecWitnessLimits fineCostModel.init
      (PreKeyDeserializeEnv 4) :=
  fitsEnv_fineCostModel_of_phaseCredit
    (pkSubEnv_phaseCreditSpec fineCostModel_modelHyps 11 4)
    (by decide) rfl (by decide) (by decide)

/-- Satisfiability witness for `IdentityKeyPairTryFromEnv 4` (`IkpSubEnv 11 4`, allocating trace reachable). -/
theorem identityKeyPairTryFromEnv_fitsEnv_witness :
    FitsEnv fineCostModel recordCodecWitnessLimits fineCostModel.init
      (IdentityKeyPairTryFromEnv 4) :=
  fitsEnv_fineCostModel_of_phaseCredit
    (ikpSubEnv_phaseCreditSpec fineCostModel_modelHyps 11 4)
    (by decide) rfl (by decide) (by decide)

end LibsignalBinary.Proofs.RecordCodecs.DepsBudget
