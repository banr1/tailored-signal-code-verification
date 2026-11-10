/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBase

/-!
# Budget-Threaded Base Specification for `Authenticator::merge`

Defines the slice-shrinking allocator event envelope `AuthMergeLoopEnv` (bounding
`DecodeError::push` and `bytes::merge` events), the budget-threaded `authMergeSpec`,
`PhaseCreditSpec` bounds, and `FitsEnv fineCostModel` non-vacuity witnesses.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   fitsEvents_append rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineDynIvsOfCum fineMaxGroupsOfCum
   fineMaxMetaAreasOfCum fineStepReserveOfCum)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (codecWireTypeToProto)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost authMergeStack authenticatorPBCapAt)

/-! ## Allocator Event Envelope -/

/-- Bounded allocator event envelope of `DecodeError::push` on stack length `n`: `[]`,
initial 128-byte alloc (`n = 0`), or doubling realloc from `n * 32` to `max (2 * n) 4 * 32`. -/
def DecodeErrorPushBoundedEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ evs = rustAllocEvents 128 8) ∨
  (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)

/-- Deterministic event envelope of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`. -/
def AuthBytesMerge3EnvCore (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  evs = bytesMergeEventsCore wt valCap bs

/-- Sequential event envelope for `Authenticator::merge` with `errRem` remaining error-path
allocations and `byteRem` remaining unconsumed payload bytes. -/
inductive AuthMergeLoopEnv : Nat → Nat → List AllocEvent → Prop where
  | nil {errRem byteRem : Nat} : AuthMergeLoopEnv errRem byteRem []
  | errFrom {errRem byteRem : Nat} {evs₂ : List AllocEvent} :
      AuthMergeLoopEnv errRem byteRem evs₂ →
      AuthMergeLoopEnv (errRem + 1) byteRem (rustAllocEvents 72 8 ++ evs₂)
  | errPush {errRem byteRem n : Nat} {evs₁ evs₂ : List AllocEvent} :
      n ≤ 1 → DecodeErrorPushBoundedEnv n evs₁ →
      AuthMergeLoopEnv errRem byteRem evs₂ →
      AuthMergeLoopEnv (errRem + 1) byteRem (evs₁ ++ evs₂)
  | bytesStep {errRem byteRem byteRem' : Nat}
      (wt : WireType) (valCap : BitVec 64) (bs v rest : List (BitVec 8))
      {evs₁ evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ byteRem →
      byteRem' + v.length + 1 ≤ byteRem →
      AuthBytesMerge3EnvCore wt valCap bs evs₁ →
      AuthMergeLoopEnv errRem byteRem' evs₂ →
      AuthMergeLoopEnv errRem byteRem (evs₁ ++ evs₂)

theorem AuthMergeLoopEnv.mono {e₁ e₂ b₁ b₂ : Nat} {evs : List AllocEvent}
    (he : e₁ ≤ e₂) (hb : b₁ ≤ b₂)
    (h : AuthMergeLoopEnv e₁ b₁ evs) :
    AuthMergeLoopEnv e₂ b₂ evs := by
  induction h generalizing e₂ b₂ with
  | nil => exact .nil
  | errFrom _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, e₂ = k + 1 := ⟨e₂ - 1, by omega⟩
    exact .errFrom (ih (by omega) hb)
  | errPush hn hp _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, e₂ = k + 1 := ⟨e₂ - 1, by omega⟩
    exact .errPush hn hp (ih (by omega) hb)
  | bytesStep wt valCap bs v rest hm hbs hshr hcore _ ih =>
    exact .bytesStep wt valCap bs v rest hm
      (Nat.le_trans hbs hb) (Nat.le_trans hshr hb) hcore
      (ih he (Nat.le_refl _))

theorem AuthMergeLoopEnv.mono_fuel {e₁ e₂ byteRem : Nat} {evs : List AllocEvent}
    (hle : e₁ ≤ e₂) (h : AuthMergeLoopEnv e₁ byteRem evs) :
    AuthMergeLoopEnv e₂ byteRem evs :=
  h.mono hle (Nat.le_refl byteRem)

theorem AuthMergeLoopEnv.append {e₁ e₂ b₁ b₂ : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : AuthMergeLoopEnv e₁ b₁ evs₁)
    (h₂ : AuthMergeLoopEnv e₂ b₂ evs₂) :
    AuthMergeLoopEnv (e₁ + e₂) (b₁ + b₂) (evs₁ ++ evs₂) := by
  induction h₁ with
  | @nil errRem byteRem =>
    simpa using h₂.mono (Nat.le_add_left e₂ errRem) (Nat.le_add_left b₂ byteRem)
  | @errFrom errRem _ _ _ ih =>
    rw [List.append_assoc, show errRem + 1 + e₂ = (errRem + e₂) + 1 by omega]
    exact .errFrom ih
  | @errPush errRem _ n eA _ hn hp _ ih =>
    rw [List.append_assoc, show errRem + 1 + e₂ = (errRem + e₂) + 1 by omega]
    exact .errPush hn hp ih
  | @bytesStep errRem byteRem byteRem' wt valCap bs v rest eA _ hm hbs hshr hcore _ ih =>
    rw [List.append_assoc]
    exact AuthMergeLoopEnv.bytesStep (byteRem' := byteRem' + b₂) wt valCap bs v rest hm
      (by omega) (by omega) hcore ih

theorem FitsEnv.authMergeLoop_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {e₁ e₂ b₁ b₂ : Nat} {evs₁ : List AllocEvent}
    (h₁ : AuthMergeLoopEnv e₁ b₁ evs₁)
    (hFit : FitsEnv M lim st (AuthMergeLoopEnv (e₁ + e₂) (b₁ + b₂))) :
    FitsEnv M lim (M.stepEvents evs₁ st) (AuthMergeLoopEnv e₂ b₂) :=
  fun evs₂ h₂ =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) (h₁.append h₂))).2

theorem FitsEnv.authMergeLoop_mono {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {e₁ e₂ b₁ b₂ : Nat}
    (he : e₁ ≤ e₂) (hb : b₁ ≤ b₂)
    (hFit : FitsEnv M lim st (AuthMergeLoopEnv e₂ b₂)) :
    FitsEnv M lim st (AuthMergeLoopEnv e₁ b₁) :=
  hFit.mono fun _ h => h.mono he hb

/-! ## Budget-Threaded `Authenticator::merge` Specification -/

/-- Precondition allocation envelope (`errRem = 4`, `byteRem = x.bs.length`). -/
def AuthMergeEnv (x : AuthMergeGhost) (evs : List AllocEvent) : Prop :=
  AuthMergeLoopEnv 4 x.bs.length evs

/-- Postcondition allocation envelope (`errRem = 0` and `x.bs.length - rest.length` bytes on `Ok`). -/
def AuthMergePostEnv (x : AuthMergeGhost) (evs : List AllocEvent) : Prop :=
  match (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption with
  | some (_, rest) => AuthMergeLoopEnv 0 (x.bs.length - rest.length) evs
  | none => AuthMergeLoopEnv 4 x.bs.length evs

theorem authMergePostEnv_imp_pre {x : AuthMergeGhost} {evs : List AllocEvent}
    (h : AuthMergePostEnv x evs) :
    AuthMergeEnv x evs := by
  dsimp only [AuthMergePostEnv, AuthMergeEnv] at h ⊢
  split at h
  · exact h.mono (by omega) (by omega)
  · exact h

/-- Envelope-parameterized budget-threaded specification of `Authenticator::merge`. -/
def authMergeSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop) :
    Spec (AuthMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      authenticatorPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp authMergeStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp authMergeStack ∗
      match (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ authenticatorPBCapAt A.repAlloc x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
          (∃∗ m' : ProtoAuthenticator, authenticatorPBAt A.repAlloc x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

/-- Budget-threaded specification of `Authenticator::merge`. -/
def authMergeSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (AuthMergeGhost × M.σ) :=
  authMergeSpecOfEnv A lim AuthMergeEnv AuthMergePostEnv

/-! ## `PhaseCreditSpec` and `FitsEnv` Witnesses -/

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
  · rename_i hgt
    have hnew : reserveCap cap 0 vLen ≤ maxReq := by
      unfold reserveCap
      omega
    split
    · exact rustAllocEvents_bounds hnew (by decide)
    · exact rustReallocEvents_bounds hnew (by decide)

private theorem authMergeLoopEnv_bounds {errRem byteRem : Nat} {evs : List AllocEvent}
    (h : AuthMergeLoopEnv errRem byteRem evs) :
    nonFreeCount evs ≤ errRem + 2 * byteRem ∧
      ∀ ev ∈ evs, eventStepReq ev ≤ max 128 (2 * byteRem + 8) ∧ eventStepAlign ev ≤ 16 := by
  induction h with
  | nil =>
    exact ⟨by simp [nonFreeCount], fun _ hm => nomatch hm⟩
  | @errFrom errRem byteRem evs₂ _ ih =>
    obtain ⟨hc₂, hb₂⟩ := ih
    obtain ⟨hc₁, hb₁⟩ := rustAllocEvents_bounds (req := 72) (al := 8)
      (maxReq := max 128 (2 * byteRem + 8)) (by omega) (by decide)
    rw [nonFreeCount_append]
    refine ⟨by omega, fun ev hev => ?_⟩
    rcases List.mem_append.mp hev with h1 | h2
    · exact hb₁ ev h1
    · exact hb₂ ev h2
  | @errPush errRem byteRem n evs₁ evs₂ hn hp _ ih =>
    obtain ⟨hc₂, hb₂⟩ := ih
    have hb₁ : nonFreeCount evs₁ ≤ 1 ∧
        ∀ ev ∈ evs₁, eventStepReq ev ≤ max 128 (2 * byteRem + 8) ∧ eventStepAlign ev ≤ 16 := by
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨by simp [nonFreeCount], fun _ hm => nomatch hm⟩
      · exact rustAllocEvents_bounds (by omega) (by decide)
      · exact rustReallocEvents_bounds (by omega) (by decide)
    rw [nonFreeCount_append]
    refine ⟨by omega, fun ev hev => ?_⟩
    rcases List.mem_append.mp hev with h1 | h2
    · exact hb₁.2 ev h1
    · exact hb₂ ev h2
  | @bytesStep errRem byteRem byteRem' wt valCap bs v rest evs₁ evs₂ hm _ hshr hcore _ ih =>
    obtain ⟨hc₂, hb₂⟩ := ih
    rw [AuthBytesMerge3EnvCore] at hcore
    subst hcore
    unfold bytesMergeEventsCore
    rw [hm]
    by_cases hv0 : v.length = 0
    · simp only [hv0, ↓reduceIte, List.nil_append]
      refine ⟨by omega, fun ev hev => ?_⟩
      obtain ⟨hr, ha⟩ := hb₂ ev hev
      exact ⟨by omega, ha⟩
    · simp only [hv0, ↓reduceIte]
      obtain ⟨hcA, hbA⟩ := rustAllocEvents_bounds (req := v.length) (al := 1)
        (maxReq := max 128 (2 * byteRem + 8)) (by omega) (by decide)
      obtain ⟨hcR, hbR⟩ := doReserveClearEvents_bounds (cap := valCap.toNat) (vLen := v.length)
        (maxReq := max 128 (2 * byteRem + 8)) (by omega)
      obtain ⟨hcD, hbD⟩ := rustDeallocEvents_bounds v.length 1 (max 128 (2 * byteRem + 8))
      simp only [List.append_assoc, nonFreeCount_append]
      refine ⟨by omega, fun ev hev => ?_⟩
      rcases List.mem_append.mp hev with hA | hRest
      · exact hbA ev hA
      · rcases List.mem_append.mp hRest with hR | hRest2
        · exact hbR ev hR
        · rcases List.mem_append.mp hRest2 with hD | h2
          · exact hbD ev hD
          · obtain ⟨hr, ha⟩ := hb₂ ev h2
            exact ⟨by omega, ha⟩

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

/-- `PhaseCreditSpec` bound for `AuthMergeLoopEnv errRem byteRem` under `ModelHyps M`. -/
theorem authMergeLoopEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (errRem byteRem : Nat) :
    let K := errRem + 2 * byteRem
    let R := max 128 (2 * byteRem + 8)
    PhaseCreditSpec M (AuthMergeLoopEnv errRem byteRem)
      (K * (2 * R + 9539)) (K * (R + 8195)) (K * (R + 8195)) R where
  req_align _ hE ev hev := (authMergeLoopEnv_bounds hE).2 ev hev
  credit_le st0 {evs} hE :=
    let ⟨hc, hb⟩ := authMergeLoopEnv_bounds hE
    stepEvents_bounded_le hM (max 128 (2 * byteRem + 8)) evs (errRem + 2 * byteRem) st0 hc hb

/-- 1 GiB (`2 ^ 30`) `BudgetLimits` witness configuration. -/
def authMergeWitnessLimits : BudgetLimits :=
  { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 2 ^ 30, enforced := true }

/-- Concrete 5-byte length-delimited `Authenticator` witness input exercising a non-empty allocation trace. -/
def authMergeWitnessGhost : AuthMergeGhost where
  wt := .lengthDelimited
  msgPtr := 0#64
  msg := { rootKey := [], macKey := [] }
  bufRef := 0#64
  slot := 0#64
  ptr := 0#64
  bs := [5#8, 10#8, 3#8, 1#8, 2#8, 3#8]

/-- Non-empty trace witness for `DecodeErrorPushBoundedEnv 1`. -/
theorem decodeErrorPushBoundedEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ DecodeErrorPushBoundedEnv 1 evs :=
  ⟨rustReallocEvents 32 128 8, by decide, Or.inr (Or.inr ⟨by decide, rfl⟩)⟩

/-- Non-empty trace witness for `AuthBytesMerge3EnvCore`. -/
theorem authBytesMerge3EnvCore_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧
      AuthBytesMerge3EnvCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] evs :=
  ⟨bytesMergeEventsCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8], by decide, rfl⟩

/-- Non-empty trace witness for `AuthMergePostEnv authMergeWitnessGhost`. -/
theorem authMergePostEnv_inhabited :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ AuthMergePostEnv authMergeWitnessGhost evs := by
  refine ⟨bytesMergeEventsCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] ++ [], by decide, ?_⟩
  have hm : mergeBytes .lengthDelimited [3#8, 1#8, 2#8, 3#8] = some ([1#8, 2#8, 3#8], []) := by
    decide
  have hstep : AuthMergeLoopEnv 0 6
      (bytesMergeEventsCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] ++ []) :=
    AuthMergeLoopEnv.bytesStep (byteRem' := 0)
      .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] [1#8, 2#8, 3#8] []
      hm (by decide) (by decide) rfl .nil
  have hparse :
      (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto authMergeWitnessGhost.wt)
        authMergeWitnessGhost.msg authMergeWitnessGhost.bs 97).toOption =
      some ({ rootKey := [1#8, 2#8, 3#8], macKey := [] }, []) := by
    decide
  dsimp only [AuthMergePostEnv]
  rw [hparse]
  exact hstep

/-- `FitsEnv fineCostModel` witness for `AuthMergeLoopEnv 4 6`. -/
theorem authMergeLoopEnv_fitsEnv_witness :
    FitsEnv fineCostModel authMergeWitnessLimits fineCostModel.init (AuthMergeLoopEnv 4 6) :=
  fitsEnv_fineCostModel_of_phaseCredit
    (authMergeLoopEnv_phaseCreditSpec fineCostModel_modelHyps 4 6)
    (by decide) rfl (by decide) (by decide)

theorem decodeErrorPushBoundedEnv_fitsEnv_witness :
    FitsEnv fineCostModel authMergeWitnessLimits fineCostModel.init
      (DecodeErrorPushBoundedEnv 1) := by
  refine authMergeLoopEnv_fitsEnv_witness.mono fun evs h => ?_
  have h1 : AuthMergeLoopEnv 1 0 (evs ++ []) :=
    AuthMergeLoopEnv.errPush (Nat.le_refl 1) h .nil
  rw [List.append_nil] at h1
  exact h1.mono (by decide) (by decide)

theorem authBytesMerge3EnvCore_fitsEnv_witness :
    FitsEnv fineCostModel authMergeWitnessLimits fineCostModel.init
      (AuthBytesMerge3EnvCore .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8]) := by
  have hm : mergeBytes .lengthDelimited [3#8, 1#8, 2#8, 3#8] = some ([1#8, 2#8, 3#8], []) := by
    decide
  refine authMergeLoopEnv_fitsEnv_witness.mono fun evs h => ?_
  have h1 : AuthMergeLoopEnv 0 4 (evs ++ []) :=
    AuthMergeLoopEnv.bytesStep (byteRem' := 0)
      .lengthDelimited 0#64 [3#8, 1#8, 2#8, 3#8] [1#8, 2#8, 3#8] []
      hm (by decide) (by decide) h .nil
  rw [List.append_nil] at h1
  exact h1.mono (by decide) (by decide)

theorem authMergeEnv_fitsEnv_witness :
    FitsEnv fineCostModel authMergeWitnessLimits fineCostModel.init
      (AuthMergeEnv authMergeWitnessGhost) :=
  authMergeLoopEnv_fitsEnv_witness

/-- `FitsEnv fineCostModel` witness for `AuthMergePostEnv authMergeWitnessGhost`. -/
theorem authMergePostEnv_fitsEnv_witness :
    FitsEnv fineCostModel authMergeWitnessLimits fineCostModel.init
      (AuthMergePostEnv authMergeWitnessGhost) :=
  authMergeEnv_fitsEnv_witness.mono fun _ h => authMergePostEnv_imp_pre h

end LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
