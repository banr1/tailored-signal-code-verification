/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers

/-!
# Multi-Step 4-Field Protobuf Loop & Error-Tail Fine-Credit Bounds

Nominal-type-agnostic `PhaseCreditSpec` and `PhaseGroupSpec` combinators for
`PreKeySignalMessage::try_from` over `WirePksmTryFromHelpers`:
1. All-quadrant affine bounds for `rustReallocEvents` and `<DecodeError>::push`
   (`phaseCreditSpec_rustRealloc_aff`, `phaseCreditSpec_decodeErrorPush_aff`).
2. Affine and small-regime `PhaseCreditSpec`s for 1-push and 2-push protobuf decode error tails.
3. Inductive 4-field loop invariants (`ProtoLoop4StateInv`, `ProtoLoop4StateInvS`,
   `ProtoLoop4GroupInv`) and loop specs (`ProtoLoop4BoundedEnv`) cancelling temporary varint/slice
   buffers and overwritten `sc = 63` `Vec<u8>` field buffers.
4. Post-loop `into_boxed_slice` and `try_clone_from_ref` length-bounded combinators.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit

open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ModelHyps PhaseCreditSpec stepEvents_freeOnly_le)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (ProtoCaps4 ProtoField4
   phaseCreditSpec_intoBoxedCap_S phaseCreditSpec_intoBoxedCap_aff
   phaseCreditSpec_intoBoxedCap_small_S
   phaseCreditSpec_tryCloneBytes_S phaseCreditSpec_tryCloneBytes_aff
   req_align_bytesMergeEventsCore stepEvents_bytesMergeCore_caps4_aff
   vecLargeCredit_eq_bytesLargeLive)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers (bytesLargeLive)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (WireGroupHyps WireLowInterceptHyps bytesMergeEventsCore_groups_step
   bytesMergeEventsCore_step_tight phaseGroupSpec_rustAlloc_cap
   phaseGroupSpec_rustAlloc_le108 phaseGroupSpec_rustRealloc_cap
   phaseGroupSpec_tryCloneBytes wireRemGrows)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (intoBoxedSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

/-! ## All-Quadrant `rustReallocEvents` & `<DecodeError>::push` Affine Bounds -/

/-- Hypothesis-free affine `PhaseCreditSpec` for `rustReallocEvents old new al` (`al ≤ 16`,
`al ≤ new`) under `ModelHyps M`, covering all four `(small/large × small/large)` quadrants. -/
theorem phaseCreditSpec_rustRealloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (2 * new + 9539) (new + 8195) (new + 8195) new where
  req_align := by
    rintro evs rfl ev hMem
    unfold rustReallocEvents at hMem
    simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hMem
    subst hMem
    exact ⟨Nat.le_refl new, hal⟩
  credit_le := by
    rintro st0 evs rfl
    have hEq : rustReallocEvents old new al = [.realloc al old new] := by
      unfold rustReallocEvents
      simp only [hal, hal_new, and_self, ↓reduceIte]
    rw [hEq]
    simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    by_cases hOld : old ≤ HasFineReallocCredit.smallMaxReq M
    · by_cases hNew : new ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hC, hL, hP⟩ := hM.step_realloc_small_small_any st0 hal hOld hNew
        have hSm := hM.smallRealloc_le hNew
        exact ⟨by omega, by omega, by omega⟩
      · have hNewGt : HasFineReallocCredit.smallMaxReq M < new := by omega
        obtain ⟨hC, hL, hP⟩ := hM.step_realloc_small_large_any st0 hal hOld hNewGt
        have hm := hM.meta_le
        have hl := hM.largeCost_le hNewGt
        exact ⟨by omega, by omega, by omega⟩
    · have hOldGt : HasFineReallocCredit.smallMaxReq M < old := by omega
      by_cases hNew : new ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hC, hL, hP⟩ := hM.step_realloc_large_small_any st0 hal hOldGt hNew
        have hSm := hM.smallRealloc_le hNew
        exact ⟨by omega, by omega, by omega⟩
      · have hNewGt : HasFineReallocCredit.smallMaxReq M < new := by omega
        obtain ⟨hC, hL, hP⟩ := HasFineReallocCredit.step_realloc_large_large st0 hal hOldGt hNewGt
        have hm := hM.meta_le
        have hl := hM.largeCost_le hNewGt
        exact ⟨by omega, by omega, by omega⟩

/-- Parametric affine `PhaseCreditSpec` for any `<DecodeError>::push` envelope of index `n`
(`[]`, `n = 0` initial `128` B alloc, or `0 < n` `max (2 * n) 4 * 32` B realloc). -/
theorem phaseCreditSpec_decodeErrorPush_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (n : Nat) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      (n = 0 ∧ evs = rustAllocEvents 128 8) ∨
      (0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)) :
    let capBytes := max (2 * n) 4 * 32
    PhaseCreditSpec M Env
      (2 * capBytes + 9539) (capBytes + 8195) (capBytes + 8195) capBytes := by
  dsimp only
  have hNil : PhaseCreditSpec M (· = [])
      (2 * (max (2 * n) 4 * 32) + 9539) (max (2 * n) 4 * 32 + 8195)
      (max (2 * n) 4 * 32 + 8195) (max (2 * n) 4 * 32) :=
    (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  have hAlloc128 : PhaseCreditSpec M (fun evs => n = 0 ∧ evs = rustAllocEvents 128 8)
      (2 * (max (2 * n) 4 * 32) + 9539) (max (2 * n) 4 * 32 + 8195)
      (max (2 * n) 4 * 32 + 8195) (max (2 * n) 4 * 32) := by
    have hGe128 : 128 ≤ max (2 * n) 4 * 32 := by omega
    exact ((PhaseCreditSpec.rustAlloc_aff hM (req := 128) (al := 8) (by decide)).of_imp
      (fun _ h => h.2)).mono (by omega) (by omega) (by omega) hGe128
  have hRealloc : PhaseCreditSpec M
      (fun evs => 0 < n ∧ evs = rustReallocEvents (n * 32) (max (2 * n) 4 * 32) 8)
      (2 * (max (2 * n) 4 * 32) + 9539) (max (2 * n) 4 * 32 + 8195)
      (max (2 * n) 4 * 32 + 8195) (max (2 * n) 4 * 32) := by
    have hAlNew : 8 ≤ max (2 * n) 4 * 32 := by omega
    exact (phaseCreditSpec_rustRealloc_aff hM (old := n * 32)
      (new := max (2 * n) 4 * 32) (al := 8) (by decide) hAlNew).of_imp (fun _ h => h.2)
  exact ((hNil.or (hAlloc128.or hRealloc)).of_imp hEnv).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Specialization of `phaseCreditSpec_decodeErrorPush_aff` at `n = 0` (`maxReq = 128`). -/
theorem phaseCreditSpec_decodeErrorPush0_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs → evs = [] ∨ evs = rustAllocEvents 128 8) :
    PhaseCreditSpec M Env 9795 8323 8323 128 := by
  have hBase := phaseCreditSpec_decodeErrorPush_aff hM 0 Env (fun evs h => by
    rcases hEnv evs h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩))
  exact hBase.mono (by decide) (by decide) (by decide) (by decide)

/-- Specialization of `phaseCreditSpec_decodeErrorPush_aff` at `n = 1` (`maxReq = 128`). -/
theorem phaseCreditSpec_decodeErrorPush1_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs → evs = [] ∨ evs = rustReallocEvents 32 128 8) :
    PhaseCreditSpec M Env 9795 8323 8323 128 := by
  have hBase := phaseCreditSpec_decodeErrorPush_aff hM 1 Env (fun evs h => by
    rcases hEnv evs h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨by decide, rfl⟩))
  exact hBase.mono (by decide) (by decide) (by decide) (by decide)

/-! ## Protobuf Decode Error-Tail `PhaseCreditSpec`s -/

/-- Affine `PhaseCreditSpec` for 1-push protobuf decode error tails (`[]`, `rustAllocEvents 72 8`,
or `rustAllocEvents 72 8 ++ push0`, optionally followed by `FreeOnlyEvs`). -/
theorem phaseCreditSpec_errTail1_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      ∃ evs_core evs_free,
        evs = evs_core ++ evs_free ∧
        FreeOnlyEvs evs_free ∧
        (evs_core = [] ∨
         evs_core = rustAllocEvents 72 8 ∨
         ∃ evs_p, evs_core = rustAllocEvents 72 8 ++ evs_p ∧
           (evs_p = [] ∨ evs_p = rustAllocEvents 128 8))) :
    PhaseCreditSpec M Env 19478 16590 16590 128 := by
  have hOpt72 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 72 8)
      9683 8267 8267 72 :=
    ((PhaseCreditSpec.nil M).or
      (PhaseCreditSpec.rustAlloc_aff hM (req := 72) (al := 8) (by decide))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPush0 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 128 8)
      9795 8323 8323 128 :=
    phaseCreditSpec_decodeErrorPush0_aff hM _ (fun _ h => h)
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  refine (((hOpt72.seq hPush0).seq hFree).of_imp (fun evs hE => ?_)).mono
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨evs_core, evs_free, rfl, hFr, hCore⟩ := hEnv evs hE
  refine Or.inr ⟨evs_core, evs_free, rfl, ?_, hFr⟩
  rcases hCore with rfl | rfl | ⟨evs_p, rfl, hp⟩
  · exact Or.inr ⟨[], [], rfl, Or.inl rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rustAllocEvents 72 8, [], by simp, Or.inr rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rustAllocEvents 72 8, evs_p, rfl, Or.inr rfl, hp⟩

/-- Affine `PhaseCreditSpec` for 2-push protobuf decode error tails (allowing up to `push0` +
`push1` and trailing `FreeOnlyEvs`). -/
theorem phaseCreditSpec_errTail2_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      ∃ evs_72 evs_p0 evs_p1 evs_free,
        evs = evs_72 ++ evs_p0 ++ evs_p1 ++ evs_free ∧
        (evs_72 = [] ∨ evs_72 = rustAllocEvents 72 8) ∧
        (evs_p0 = [] ∨ evs_p0 = rustAllocEvents 128 8) ∧
        (evs_p1 = [] ∨ evs_p1 = rustReallocEvents 32 128 8) ∧
        FreeOnlyEvs evs_free) :
    PhaseCreditSpec M Env 29273 24913 24913 128 := by
  have hOpt72 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 72 8)
      9683 8267 8267 72 :=
    ((PhaseCreditSpec.nil M).or
      (PhaseCreditSpec.rustAlloc_aff hM (req := 72) (al := 8) (by decide))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPush0 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 128 8)
      9795 8323 8323 128 :=
    phaseCreditSpec_decodeErrorPush0_aff hM _ (fun _ h => h)
  have hPush1 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustReallocEvents 32 128 8)
      9795 8323 8323 128 :=
    phaseCreditSpec_decodeErrorPush1_aff hM _ (fun _ h => h)
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps hM
  refine ((((hOpt72.seq hPush0).seq hPush1).seq hFree).of_imp (fun evs hE => ?_)).mono
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨e72, ep0, ep1, ef, rfl, h72, hp0, hp1, hf⟩ := hEnv evs hE
  exact Or.inr ⟨e72 ++ ep0 ++ ep1, ef, rfl,
    Or.inr ⟨e72 ++ ep0, ep1, rfl, Or.inr ⟨e72, ep0, rfl, h72, hp0⟩, hp1⟩, hf⟩

/-! ## Modular 4-Field Protobuf Loop Invariant (`ProtoLoop4StateInv`) & Loop `PhaseCreditSpec` -/

/-- Nominal-type-agnostic inductive invariant for a 4-field `Vec<u8>` protobuf decode loop
terminated by a tail phase `(tc, tl, tp, tr)` with remaining byte budget `rem`. -/
def ProtoLoop4StateInv (M : AllocCostModel) [HasFineReallocCredit M]
    (tc tl tp tr rem : Nat) (caps : ProtoCaps4) (evs : List AllocEvent) : Prop :=
  (∀ ev ∈ evs, eventStepReq ev ≤ max tr (max 128 (2 * rem)) ∧ eventStepAlign ev ≤ 16) ∧
  ∀ (st : M.σ) (L0 used N : Nat),
    HasFineReallocCredit.liveLarge st ≤ L0 + caps.largeCredit M →
    caps.sum ≤ 4 * used →
    used + rem ≤ N →
    let sf := M.stepEvents evs st
    HasFineReallocCredit.cumSmall sf ≤ HasFineReallocCredit.cumSmall st + 9548 * rem + tc ∧
    HasFineReallocCredit.liveLarge sf ≤ L0 + (4 * N + 32780 + tl) ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st) (L0 + (5 * N + 49170 + tp))

/-- Base case (`done` / loop exit): lifts any `TailEnv` event trace satisfying
`PhaseCreditSpec M TailEnv tc tl tp tr` into `ProtoLoop4StateInv`. -/
theorem ProtoLoop4StateInv.of_tail {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {TailEnv : List AllocEvent → Prop}
    {tc tl tp tr rem : Nat} {caps : ProtoCaps4} {evs : List AllocEvent}
    (hTail : PhaseCreditSpec M TailEnv tc tl tp tr) (hE : TailEnv evs) :
    ProtoLoop4StateInv M tc tl tp tr rem caps evs := by
  refine ⟨fun ev hMem => ?_, fun st L0 used N hLive hSum hBound => ?_⟩
  · obtain ⟨hReq, hAl⟩ := hTail.req_align evs hE ev hMem
    exact ⟨Nat.le_trans hReq (Nat.le_max_left _ _), hAl⟩
  · obtain ⟨hC, hL, hP⟩ := hTail.credit_le st hE
    have hCapsLg : caps.largeCredit M ≤ caps.sum + 32780 :=
      ProtoCaps4.largeCredit_le_sum_add hM caps
    exact ⟨by omega, by omega, by omega⟩

/-- 0-event scalar/varint/skip step (`rem' ≤ rem`, unchanged `caps`). -/
theorem ProtoLoop4StateInv.of_skip {M : AllocCostModel} [HasFineReallocCredit M]
    {tc tl tp tr rem rem' : Nat} {caps : ProtoCaps4} {evs : List AllocEvent}
    (hRem : rem' ≤ rem)
    (ih : ProtoLoop4StateInv M tc tl tp tr rem' caps evs) :
    ProtoLoop4StateInv M tc tl tp tr rem caps evs := by
  refine ⟨fun ev hMem => ?_, fun st L0 used N hLive hSum hBound => ?_⟩
  · obtain ⟨hReq, hAl⟩ := ih.1 ev hMem
    exact ⟨by omega, hAl⟩
  · obtain ⟨hC, hL, hP⟩ := ih.2 st L0 (used + (rem - rem')) N hLive (by omega) (by omega)
    exact ⟨by omega, hL, hP⟩

/-- Prepends a `FreeOnlyEvs` prefix (`rem' ≤ rem`, unchanged `caps`). -/
theorem ProtoLoop4StateInv.of_free_prepend {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {tc tl tp tr rem rem' : Nat} {caps : ProtoCaps4}
    {evs₁ evs₂ : List AllocEvent}
    (hRem : rem' ≤ rem) (hFree : FreeOnlyEvs evs₁)
    (ih : ProtoLoop4StateInv M tc tl tp tr rem' caps evs₂) :
    ProtoLoop4StateInv M tc tl tp tr rem caps (evs₁ ++ evs₂) := by
  refine ⟨fun ev hMem => ?_, fun st L0 used N hLive hSum hBound => ?_⟩
  · rcases List.mem_append.mp hMem with hMem1 | hMem2
    · obtain ⟨al, sz, rfl⟩ := hFree ev hMem1
      exact ⟨Nat.zero_le _, Nat.le_refl 16⟩
    · obtain ⟨hReq, hAl⟩ := ih.1 ev hMem2
      exact ⟨by omega, hAl⟩
  · rw [AllocCostModel.stepEvents_append]
    obtain ⟨hC1, hL1, hP1⟩ := stepEvents_freeOnly_le hM.freeNonInc hFree st
    obtain ⟨hC2, hL2, hP2⟩ :=
      ih.2 (M.stepEvents evs₁ st) L0 (used + (rem - rem')) N
        (Nat.le_trans hL1 hLive) (by omega) (by omega)
    exact ⟨by omega, hL2, by omega⟩

/-- Inductive `bytesMergeEventsCore` step on field `f : ProtoField4` (cancelling temporary
decode buffers and overwritten `sc = 63` `Vec<u8>` field capacities, including Kyber overwrites). -/
theorem ProtoLoop4StateInv.of_bytesStep {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (f : ProtoField4)
    {tc tl tp tr rem rem' : Nat} {caps : ProtoCaps4}
    {wt : WireType} {bs v rest : List (BitVec 8)} {evs₂ : List AllocEvent}
    (hMerge : mergeBytes wt bs = some (v, rest))
    (hBs : bs.length ≤ rem)
    (hRem : rem' + v.length + 1 ≤ rem)
    (hCapFit : caps.get f < 2 ^ 64)
    (ih : ProtoLoop4StateInv M tc tl tp tr rem'
      (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
      evs₂) :
    ProtoLoop4StateInv M tc tl tp tr rem caps
      (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂) := by
  refine ⟨fun ev hMem => ?_, fun st L0 used N hLive hSum hBound => ?_⟩
  · rcases List.mem_append.mp hMem with hMem1 | hMem2
    · obtain ⟨hReq, hAl⟩ := req_align_bytesMergeEventsCore hMem1
      exact ⟨by omega, hAl⟩
    · obtain ⟨hReq, hAl⟩ := ih.1 ev hMem2
      exact ⟨by omega, hAl⟩
  · rw [AllocCostModel.stepEvents_append]
    obtain ⟨hC1, hL1, hP1, hSum'⟩ :=
      stepEvents_bytesMergeCore_caps4_aff hM st f caps wt bs v rest
        hMerge hRem hCapFit hLive hSum (N := N) (by omega)
    obtain ⟨hC2, hL2, hP2⟩ :=
      ih.2 (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs) st)
        L0 (used + (rem - rem')) N hL1 hSum' (by omega)
    exact ⟨by omega, hL2, by omega⟩

/-- Eliminates `ProtoLoop4StateInv` from `(N, ProtoCaps4.zero)` into a full `PhaseCreditSpec`. -/
theorem ProtoLoop4StateInv.to_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {tc tl tp tr N : Nat}
    (hInv : ∀ evs, Env evs → ProtoLoop4StateInv M tc tl tp tr N ProtoCaps4.zero evs) :
    PhaseCreditSpec M Env
      (9548 * N + tc) (4 * N + 32780 + tl) (5 * N + 49170 + tp) (max tr (max 128 (2 * N))) where
  req_align evs hE ev hMem := (hInv evs hE).1 ev hMem
  credit_le st0 {evs} hE := by
    have hLive0 :
        HasFineReallocCredit.liveLarge st0 ≤
          HasFineReallocCredit.liveLarge st0 + ProtoCaps4.zero.largeCredit M := by
      rw [ProtoCaps4.largeCredit_zero]
      omega
    have hSum0 : ProtoCaps4.zero.sum ≤ 4 * 0 := by
      rw [ProtoCaps4.sum_zero]
    obtain ⟨hC, hL, hP⟩ :=
      (hInv evs hE).2 st0 (HasFineReallocCredit.liveLarge st0) 0 N hLive0 hSum0 (by omega)
    exact ⟨by omega, hL, hP⟩

/-- Canonical 4-field slice-budgeted protobuf decode loop envelope over `ProtoCaps4`. -/
inductive ProtoLoop4BoundedEnv (TailEnv : List AllocEvent → Prop) :
    Nat → ProtoCaps4 → List AllocEvent → Prop where
  | done {rem : Nat} {caps : ProtoCaps4} {evs : List AllocEvent} :
      TailEnv evs →
      ProtoLoop4BoundedEnv TailEnv rem caps evs
  | skipStep {rem rem' : Nat} {caps : ProtoCaps4} {evs : List AllocEvent} :
      rem' ≤ rem →
      ProtoLoop4BoundedEnv TailEnv rem' caps evs →
      ProtoLoop4BoundedEnv TailEnv rem caps evs
  | freeStep {rem rem' : Nat} {caps : ProtoCaps4} {evs₁ evs₂ : List AllocEvent} :
      rem' ≤ rem →
      FreeOnlyEvs evs₁ →
      ProtoLoop4BoundedEnv TailEnv rem' caps evs₂ →
      ProtoLoop4BoundedEnv TailEnv rem caps (evs₁ ++ evs₂)
  | bytesStep (f : ProtoField4) {rem rem' : Nat} {caps : ProtoCaps4}
      (wt : WireType) (bs v rest : List (BitVec 8)) {evs₂ : List AllocEvent} :
      mergeBytes wt bs = some (v, rest) →
      bs.length ≤ rem →
      rem' + v.length + 1 ≤ rem →
      caps.get f < 2 ^ 64 →
      ProtoLoop4BoundedEnv TailEnv rem'
        (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
        evs₂ →
      ProtoLoop4BoundedEnv TailEnv rem caps
        (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂)

/-- Full affine `PhaseCreditSpec` for `ProtoLoop4BoundedEnv TailEnv N ProtoCaps4.zero`. -/
theorem phaseCreditSpec_protoLoop4_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {TailEnv : List AllocEvent → Prop} {tc tl tp tr : Nat} (N : Nat)
    (hTail : PhaseCreditSpec M TailEnv tc tl tp tr) :
    PhaseCreditSpec M (ProtoLoop4BoundedEnv TailEnv N ProtoCaps4.zero)
      (9548 * N + tc) (4 * N + 32780 + tl) (5 * N + 49170 + tp) (max tr (max 128 (2 * N))) := by
  have hInv : ∀ {rem caps evs}, ProtoLoop4BoundedEnv TailEnv rem caps evs →
      ProtoLoop4StateInv M tc tl tp tr rem caps evs := by
    intro rem caps evs h
    induction h with
    | done hE => exact ProtoLoop4StateInv.of_tail hM hTail hE
    | skipStep hLe _ ih => exact ProtoLoop4StateInv.of_skip hLe ih
    | freeStep hLe hFr _ ih => exact ProtoLoop4StateInv.of_free_prepend hM hLe hFr ih
    | bytesStep f wt bs v rest hMb hBs hRem hCap _ ih =>
        exact ProtoLoop4StateInv.of_bytesStep hM f hMb hBs hRem hCap ih
  exact ProtoLoop4StateInv.to_phaseCreditSpec (fun _ h => hInv h)

/-! ## Post-Loop Length-Bounded `into_boxed_slice` & `try_clone_from_ref` Combinators -/

/-- Affine `PhaseCreditSpec` for an optional/bounded `into_boxed_slice` phase with `bs.length ≤ N`
(covers both mandatory `Vec<u8>::into_boxed_slice` and `Option` Kyber payload `into_boxed_slice`). -/
theorem phaseCreditSpec_intoBoxedBounded_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (N : Nat) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ (bs : List (BitVec 8)) (cap : BitVec 64),
        bs.length ≤ N ∧ evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseCreditSpec M Env (2 * N + 9539) (N + 8195) (N + 8195) N where
  req_align evs hE ev hMem := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, hLen, rfl⟩
    · nomatch hMem
    · have hSpec :=
        phaseCreditSpec_intoBoxedCap_aff hM bs
          (· = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) (fun _ h => ⟨cap, h⟩)
      obtain ⟨hReq, hAl⟩ := hSpec.req_align _ rfl ev hMem
      exact ⟨Nat.le_trans hReq hLen, hAl⟩
  credit_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, hLen, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    · have hSpec :=
        phaseCreditSpec_intoBoxedCap_aff hM bs
          (· = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) (fun _ h => ⟨cap, h⟩)
      obtain ⟨hC, hL, hP⟩ := hSpec.credit_le st0 (evs := intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) rfl
      have hC' : (if bs.length = 0 then 0 else 2 * bs.length + 9539) ≤ 2 * N + 9539 := by
        split <;> omega
      have hL' :
          (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195) ≤
            N + 8195 := by
        split <;> omega
      exact ⟨by omega, by omega, by omega⟩

/-- Affine `PhaseCreditSpec` for an optional/bounded `try_clone_from_ref` phase with
`bs.length ≤ N`. -/
theorem phaseCreditSpec_tryCloneBounded_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (N : Nat) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ bs : List (BitVec 8),
        bs.length ≤ N ∧ evs = (if bs = [] then [] else rustAllocEvents bs.length 1)) :
    PhaseCreditSpec M Env (2 * N + 9539) (N + 8195) (N + 8195) N where
  req_align evs hE ev hMem := by
    rcases hEnv evs hE with rfl | ⟨bs, hLen, rfl⟩
    · nomatch hMem
    · obtain ⟨hReq, hAl⟩ := (phaseCreditSpec_tryCloneBytes_aff hM bs).req_align _ rfl ev hMem
      exact ⟨Nat.le_trans hReq hLen, hAl⟩
  credit_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, hLen, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨hC, hL, hP⟩ :=
        (phaseCreditSpec_tryCloneBytes_aff hM bs).credit_le st0
          (evs := if bs = [] then [] else rustAllocEvents bs.length 1) rfl
      have hC' : (if bs.length = 0 then 0 else 2 * bs.length + 9539) ≤ 2 * N + 9539 := by
        split <;> omega
      have hL' :
          (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195) ≤
            N + 8195 := by
        split <;> omega
      exact ⟨by omega, by omega, by omega⟩

/-! ## Tight `WireLowInterceptHyps` Loop, Error-Tail, & Post-Loop Combinators -/

/-- Small-regime (`128 ≤ S`) 1-push protobuf decode error tail: zero `liveLarge` and `peakLarge`
delta (`(19478, 0, 0, 128)`). -/
theorem phaseCreditSpec_errTail1_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S)
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      ∃ evs_core evs_free,
        evs = evs_core ++ evs_free ∧
        FreeOnlyEvs evs_free ∧
        (evs_core = [] ∨
         evs_core = rustAllocEvents 72 8 ∨
         ∃ evs_p, evs_core = rustAllocEvents 72 8 ++ evs_p ∧
           (evs_p = [] ∨ evs_p = rustAllocEvents 128 8))) :
    PhaseCreditSpec M Env 19478 0 0 128 := by
  have h72Sm : 72 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have h128Sm : 128 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hOpt72 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 72 8) 9683 0 0 72 :=
    ((PhaseCreditSpec.nil M).or
      ((PhaseCreditSpec.rustAlloc_small M (req := 72) (al := 8) (by decide) (by decide) h72Sm).mono
        (hM.smallAlloc_le h72Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPush0 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 128 8) 9795 0 0 128 :=
    ((PhaseCreditSpec.nil M).or
      ((PhaseCreditSpec.rustAlloc_small M (req := 128) (al := 8) (by decide) (by decide) h128Sm).mono
        (hM.smallAlloc_le h128Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  refine (((hOpt72.seq hPush0).seq hFree).of_imp (fun evs hE => ?_)).mono
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨evs_core, evs_free, rfl, hFr, hCore⟩ := hEnv evs hE
  refine Or.inr ⟨evs_core, evs_free, rfl, ?_, hFr⟩
  rcases hCore with rfl | rfl | ⟨evs_p, rfl, hp⟩
  · exact Or.inr ⟨[], [], rfl, Or.inl rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rustAllocEvents 72 8, [], by simp, Or.inr rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rustAllocEvents 72 8, evs_p, rfl, Or.inr rfl, hp⟩

/-- Small-regime (`128 ≤ S`) 2-push protobuf decode error tail: zero `liveLarge` and `peakLarge`
delta (`(29273, 0, 0, 128)`). -/
theorem phaseCreditSpec_errTail2_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S)
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      ∃ evs_72 evs_p0 evs_p1 evs_free,
        evs = evs_72 ++ evs_p0 ++ evs_p1 ++ evs_free ∧
        (evs_72 = [] ∨ evs_72 = rustAllocEvents 72 8) ∧
        (evs_p0 = [] ∨ evs_p0 = rustAllocEvents 128 8) ∧
        (evs_p1 = [] ∨ evs_p1 = rustReallocEvents 32 128 8) ∧
        FreeOnlyEvs evs_free) :
    PhaseCreditSpec M Env 29273 0 0 128 := by
  have h32Sm : 32 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have h72Sm : 72 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have h128Sm : 128 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  have hOpt72 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 72 8) 9683 0 0 72 :=
    ((PhaseCreditSpec.nil M).or
      ((PhaseCreditSpec.rustAlloc_small M (req := 72) (al := 8) (by decide) (by decide) h72Sm).mono
        (hM.smallAlloc_le h72Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPush0 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustAllocEvents 128 8) 9795 0 0 128 :=
    ((PhaseCreditSpec.nil M).or
      ((PhaseCreditSpec.rustAlloc_small M (req := 128) (al := 8) (by decide) (by decide) h128Sm).mono
        (hM.smallAlloc_le h128Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPush1 : PhaseCreditSpec M (fun e => e = [] ∨ e = rustReallocEvents 32 128 8) 9795 0 0 128 :=
    ((PhaseCreditSpec.nil M).or
      ((PhaseCreditSpec.rustRealloc_small_small M (old := 32) (new := 128) (al := 8)
          (by decide) (by decide) (by decide) h32Sm (by decide) h128Sm).mono
        (hM.smallRealloc_le h128Sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  refine ((((hOpt72.seq hPush0).seq hPush1).seq hFree).of_imp (fun evs hE => ?_)).mono
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨e72, ep0, ep1, ef, rfl, h72, hp0, hp1, hf⟩ := hEnv evs hE
  exact Or.inr ⟨e72 ++ ep0 ++ ep1, ef, rfl,
    Or.inr ⟨e72 ++ ep0, ep1, rfl, Or.inr ⟨e72, ep0, rfl, h72, hp0⟩, hp1⟩, hf⟩

/-- Tight `S`-parameterized inductive invariant for a 4-field `Vec<u8>` protobuf decode loop
tracking amortized capacity growth (`minSum` + `remGrows`) and `g`-sum `sc = 63` bounds. -/
def ProtoLoop4StateInvS (M : AllocCostModel) [HasFineReallocCredit M]
    (S tc tl tp tr rem : Nat) (caps : ProtoCaps4) (evs : List AllocEvent) : Prop :=
  (∀ ev ∈ evs, eventStepReq ev ≤ max tr (max 128 (2 * rem)) ∧ eventStepAlign ev ≤ 16) ∧
  ∀ (st : M.σ) (g : ProtoCaps4) (L0 N : Nat),
    rem ≤ N →
    caps.bounded N →
    caps.boundedG g →
    g.sum + rem ≤ N →
    HasFineReallocCredit.liveLarge st ≤ L0 + caps.largeCredit M →
    let sf := M.stepEvents evs st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + 94 * rem +
        4 * (4 * min (max 8 (2 * N)) S - caps.minSum S) +
        9539 * caps.remGrows N + tc ∧
    HasFineReallocCredit.liveLarge sf ≤ L0 + (2 * N + 32780 + tl) ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (L0 + max (3 * N + 49170) (2 * N + 32780 + tp))

abbrev ProtoLoop4StateInvTight (M : AllocCostModel) [HasFineReallocCredit M] :=
  ProtoLoop4StateInvS M 135167

theorem ProtoLoop4StateInvS.of_tail {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {TailEnv : List AllocEvent → Prop}
    {tc tl tp tr rem : Nat} {caps : ProtoCaps4} {evs : List AllocEvent}
    (hTail : PhaseCreditSpec M TailEnv tc tl tp tr) (hE : TailEnv evs) :
    ProtoLoop4StateInvS M S tc tl tp tr rem caps evs := by
  refine ⟨fun ev hMem => ?_, fun st g L0 N _ _ hcg hg_rem hLive => ?_⟩
  · obtain ⟨hReq, hAl⟩ := hTail.req_align evs hE ev hMem
    exact ⟨Nat.le_trans hReq (Nat.le_max_left _ _), hAl⟩
  · obtain ⟨hC, hL, hP⟩ := hTail.credit_le st hE
    have hCapsLg := ProtoCaps4.largeCredit_le_g hM hSm hS8 hcg
    set Mmax := 4 * min (max 8 (2 * N)) S
    set MS := caps.minSum S
    set GW := caps.remGrows N
    exact ⟨by omega, by omega, by omega⟩

theorem ProtoLoop4StateInvS.of_skip {M : AllocCostModel} [HasFineReallocCredit M]
    {S tc tl tp tr rem rem' : Nat} {caps : ProtoCaps4} {evs : List AllocEvent}
    (hRem : rem' ≤ rem)
    (ih : ProtoLoop4StateInvS M S tc tl tp tr rem' caps evs) :
    ProtoLoop4StateInvS M S tc tl tp tr rem caps evs := by
  refine ⟨fun ev hMem => ?_, fun st g L0 N hRemN hcaps hcg hg_rem hLive => ?_⟩
  · obtain ⟨hReq, hAl⟩ := ih.1 ev hMem
    exact ⟨by omega, hAl⟩
  · obtain ⟨hC, hL, hP⟩ := ih.2 st g L0 N (by omega) hcaps hcg (by omega) hLive
    set Mmax := 4 * min (max 8 (2 * N)) S
    set MS := caps.minSum S
    set GW := caps.remGrows N
    have hmono : 94 * rem' ≤ 94 * rem := Nat.mul_le_mul_left 94 hRem
    exact ⟨Nat.le_trans hC (by omega), hL, hP⟩

theorem ProtoLoop4StateInvS.of_free_prepend {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S tc tl tp tr rem rem' : Nat} {caps : ProtoCaps4}
    {evs₁ evs₂ : List AllocEvent}
    (hRem : rem' ≤ rem) (hFree : FreeOnlyEvs evs₁)
    (ih : ProtoLoop4StateInvS M S tc tl tp tr rem' caps evs₂) :
    ProtoLoop4StateInvS M S tc tl tp tr rem caps (evs₁ ++ evs₂) := by
  refine ⟨fun ev hMem => ?_, fun st g L0 N hRemN hcaps hcg hg_rem hLive => ?_⟩
  · rcases List.mem_append.mp hMem with hMem1 | hMem2
    · obtain ⟨al, sz, rfl⟩ := hFree ev hMem1
      exact ⟨Nat.zero_le _, Nat.le_refl 16⟩
    · obtain ⟨hReq, hAl⟩ := ih.1 ev hMem2
      exact ⟨by omega, hAl⟩
  · rw [AllocCostModel.stepEvents_append]
    obtain ⟨hC1, hL1, hP1⟩ := stepEvents_freeOnly_le hM.freeNonInc hFree st
    obtain ⟨hC2, hL2, hP2⟩ :=
      ih.2 (M.stepEvents evs₁ st) g L0 N (by omega) hcaps hcg (by omega) (Nat.le_trans hL1 hLive)
    set Mmax := 4 * min (max 8 (2 * N)) S
    set MS := caps.minSum S
    set GW := caps.remGrows N
    have hmono : 94 * rem' ≤ 94 * rem := Nat.mul_le_mul_left 94 hRem
    exact ⟨by omega, hL2, by omega⟩

theorem ProtoLoop4StateInvS.of_bytesStep {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    (f : ProtoField4)
    {tc tl tp tr rem rem' : Nat} {caps : ProtoCaps4}
    {wt : WireType} {bs v rest : List (BitVec 8)} {evs₂ : List AllocEvent}
    (hMerge : mergeBytes wt bs = some (v, rest))
    (_hBs : bs.length ≤ rem)
    (hRem : rem' + v.length + 1 ≤ rem)
    (hCapFit : caps.get f < 2 ^ 64)
    (ih : ProtoLoop4StateInvS M S tc tl tp tr rem'
      (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
      evs₂) :
    ProtoLoop4StateInvS M S tc tl tp tr rem caps
      (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂) := by
  refine ⟨fun ev hMem => ?_, fun st g L0 N hRemN hcaps hcg hg_rem hLive => ?_⟩
  · rcases List.mem_append.mp hMem with hMem1 | hMem2
    · obtain ⟨hReq, hAl⟩ := req_align_bytesMergeEventsCore hMem1
      exact ⟨by omega, hAl⟩
    · obtain ⟨hReq, hAl⟩ := ih.1 ev hMem2
      exact ⟨by omega, hAl⟩
  · have hcap_max : caps.get f ≤ max 8 (2 * N) := by
      obtain ⟨h0, h1, h2, h3⟩ := hcaps
      cases f <;> simp only [ProtoCaps4.get] <;> omega
    set cap := caps.get f
    set cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    set g_f := g.get f
    set g_f' := if v.length ≤ cap then g_f else v.length
    obtain ⟨hg_sum_pre, _, hcap_g_pre, _⟩ :=
      ProtoCaps4.g_props hcg f (v_cap := cap) (v_g := g_f)
        (by obtain ⟨h0, h1, h2, h3⟩ := hcg; dsimp only [cap, g_f]; cases f <;> dsimp only [ProtoCaps4.get] <;> omega)
    change g.sum = g.otherSum f + g_f at hg_sum_pre
    change cap ≤ max (2 * g_f) 8 at hcap_g_pre
    have hdec_pre := ProtoCaps4.largeCredit_eq_other_add M caps f
    have hdec_post := ProtoCaps4.largeCredit_set M caps f cap'
    rw [vecLargeCredit_eq_bytesLargeLive] at hdec_pre hdec_post
    change caps.largeCredit M = caps.otherLargeCredit M f + bytesLargeLive M cap at hdec_pre
    have hlive' : HasFineReallocCredit.liveLarge st ≤
        L0 + caps.otherLargeCredit M f + bytesLargeLive M cap := by omega
    obtain ⟨_, hmin_le, _, hcap'_max, hcap'_g, hg_rem', hcum1, hlive1, hpeak1⟩ :=
      bytesMergeEventsCore_step_tight hM hLow hSm hS8 hMerge hRem hRemN hCapFit hcap_max
        hcap_g_pre (ProtoCaps4.otherLargeCredit_le_g hM hSm hS8 hcg f) (by omega) st hlive'
    change min cap S ≤ min cap' S at hmin_le
    change cap' ≤ max 8 (2 * N) at hcap'_max
    change cap' ≤ max (2 * g_f') 8 at hcap'_g
    change g.otherSum f + g_f' + rem' ≤ N at hg_rem'
    obtain ⟨_, hcaps', _, hms'_le, hms_eq⟩ := ProtoCaps4.minSum_props hcaps f hmin_le hcap'_max
    obtain ⟨_, hg_sum_post, _, hcg'⟩ := ProtoCaps4.g_props hcg f hcap'_g
    obtain ⟨hgw_pre, hgw_post⟩ := ProtoCaps4.remGrows_decomp N caps f cap'
    rw [AllocCostModel.stepEvents_append]
    set evs₁ := bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs
    set st₁ := M.stepEvents evs₁ st
    change HasFineReallocCredit.liveLarge st₁ ≤
      L0 + caps.otherLargeCredit M f + bytesLargeLive M cap' at hlive1
    change (caps.set f cap').largeCredit M =
      caps.otherLargeCredit M f + bytesLargeLive M cap' at hdec_post
    have hlive1' : HasFineReallocCredit.liveLarge st₁ ≤
        L0 + (caps.set f cap').largeCredit M := by omega
    obtain ⟨hcum2, hlv2, hpk2⟩ :=
      ih.2 st₁ (g.set f g_f') L0 N (by omega) hcaps' hcg' (by omega) hlive1'
    set st₂ := M.stepEvents evs₂ st₁
    set Mmax := 4 * min (max 8 (2 * N)) S
    set W := wireRemGrows N cap
    set W' := wireRemGrows N cap'
    set GW_other := caps.otherRemGrows N f
    set MS := caps.minSum S
    set MS' := (caps.set f cap').minSum S
    set MC := min cap S
    set MC' := min cap' S
    change HasFineReallocCredit.cumSmall st₁ + 9539 * W' ≤
      HasFineReallocCredit.cumSmall st + 94 * (rem - rem') + 4 * (MC' - MC) + 9539 * W at hcum1
    change caps.remGrows N = GW_other + W at hgw_pre
    change (caps.set f cap').remGrows N = GW_other + W' at hgw_post
    change MS' ≤ Mmax at hms'_le
    change MS' + MC = MS + MC' at hms_eq
    have hcum_comb : HasFineReallocCredit.cumSmall st₂ ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (Mmax - MS) + 9539 * caps.remGrows N + tc := by
      have hrem_mul : 94 * (rem - rem') + 94 * rem' = 94 * rem := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      set R1 := 94 * (rem - rem')
      set R2 := 94 * rem'
      set R := 94 * rem
      rw [hgw_post] at hcum2
      rw [hgw_pre]
      omega
    have hpk_comb : HasFineReallocCredit.peakLarge st₂ ≤
        max (HasFineReallocCredit.peakLarge st)
          (L0 + max (3 * N + 49170) (2 * N + 32780 + tp)) := by
      have hpk1' : HasFineReallocCredit.peakLarge st₁ ≤
          max (HasFineReallocCredit.peakLarge st)
            (L0 + max (3 * N + 49170) (2 * N + 32780 + tp)) :=
        Nat.le_trans hpeak1 (max_le_max (Nat.le_refl _) (Nat.add_le_add_left (Nat.le_max_left _ _) _))
      exact Nat.le_trans hpk2 (Nat.max_le.mpr ⟨hpk1', Nat.le_max_right _ _⟩)
    exact ⟨hcum_comb, hlv2, hpk_comb⟩

theorem ProtoLoop4StateInvS.to_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {S tc tl tp tr N : Nat}
    (hInv : ∀ evs, Env evs → ProtoLoop4StateInvS M S tc tl tp tr N ProtoCaps4.zero evs) :
    PhaseCreditSpec M Env
      (94 * N + 16 * min (max 8 (2 * N)) S + 38156 * wireRemGrows N 0 + tc)
      (2 * N + 32780 + tl)
      (max (3 * N + 49170) (2 * N + 32780 + tp))
      (max tr (max 128 (2 * N))) where
  req_align evs hE ev hMem := (hInv evs hE).1 ev hMem
  credit_le st0 {evs} hE := by
    have hzero_bd : ProtoCaps4.zero.bounded N := by simp [ProtoCaps4.bounded, ProtoCaps4.zero]
    have hzero_g : ProtoCaps4.zero.boundedG ProtoCaps4.zero := by
      simp [ProtoCaps4.boundedG, ProtoCaps4.zero]
    have hzero_lg : ProtoCaps4.zero.largeCredit M = 0 := ProtoCaps4.largeCredit_zero M
    have hzero_sum : ProtoCaps4.zero.sum = 0 := rfl
    have hzero_ms : ProtoCaps4.zero.minSum S = 0 := by simp [ProtoCaps4.minSum, ProtoCaps4.zero]
    have hzero_gw : ProtoCaps4.zero.remGrows N = 4 * wireRemGrows N 0 := by
      simp only [ProtoCaps4.remGrows, ProtoCaps4.zero]
      omega
    obtain ⟨hC, hL, hP⟩ :=
      (hInv evs hE).2 st0 ProtoCaps4.zero (HasFineReallocCredit.liveLarge st0) N
        (Nat.le_refl N) hzero_bd hzero_g (by omega) (by omega)
    rw [hzero_ms, Nat.sub_zero, hzero_gw] at hC
    set A := min (max 8 (2 * N)) S
    set K := wireRemGrows N 0
    exact ⟨Nat.le_trans hC (by omega), hL, hP⟩

/-- Tight `S`-parameterized `PhaseCreditSpec` for `ProtoLoop4BoundedEnv TailEnv N ProtoCaps4.zero`. -/
theorem phaseCreditSpec_protoLoop4_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {TailEnv : List AllocEvent → Prop} {tc tl tp tr : Nat} (N : Nat)
    (hTail : PhaseCreditSpec M TailEnv tc tl tp tr) :
    PhaseCreditSpec M (ProtoLoop4BoundedEnv TailEnv N ProtoCaps4.zero)
      (94 * N + 16 * min (max 8 (2 * N)) S + 38156 * wireRemGrows N 0 + tc)
      (2 * N + 32780 + tl)
      (max (3 * N + 49170) (2 * N + 32780 + tp))
      (max tr (max 128 (2 * N))) := by
  have hInv : ∀ {rem caps evs}, ProtoLoop4BoundedEnv TailEnv rem caps evs →
      ProtoLoop4StateInvS M S tc tl tp tr rem caps evs := by
    intro rem caps evs h
    induction h with
    | done hE => exact ProtoLoop4StateInvS.of_tail hM hSm hS8 hTail hE
    | skipStep hLe _ ih => exact ProtoLoop4StateInvS.of_skip hLe ih
    | freeStep hLe hFr _ ih => exact ProtoLoop4StateInvS.of_free_prepend hM hLe hFr ih
    | bytesStep f wt bs v rest hMb hBs hRem hCap _ ih =>
        exact ProtoLoop4StateInvS.of_bytesStep hM hLow hSm hS8 f hMb hBs hRem hCap ih
  exact ProtoLoop4StateInvS.to_phaseCreditSpec (fun _ h => hInv h)

/-- Tight `S`-capped `PhaseCreditSpec` for an optional/bounded `into_boxed_slice` phase with
`bs.length ≤ N`. -/
theorem phaseCreditSpec_intoBoxedBounded_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (N : Nat) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ (bs : List (BitVec 8)) (cap : BitVec 64),
        bs.length ≤ N ∧ evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseCreditSpec M Env (2 * min N S + 9539) (N + 8195) (N + 8195) N where
  req_align evs hE ev hMem := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, hLen, rfl⟩
    · nomatch hMem
    · have hSpec :=
        phaseCreditSpec_intoBoxedCap_S hM hSm bs
          (· = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) (fun _ h => ⟨cap, h⟩)
      obtain ⟨hReq, hAl⟩ := hSpec.req_align _ rfl ev hMem
      exact ⟨Nat.le_trans hReq hLen, hAl⟩
  credit_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, hLen, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_max_left _ _⟩
    · have hMinLe : min bs.length S ≤ min N S :=
        Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hLen, Nat.min_le_right _ _⟩
      have hSpec :=
        (phaseCreditSpec_intoBoxedCap_S hM hSm bs
          (· = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) (fun _ h => ⟨cap, h⟩)).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hMinLe) 9539)
          (Nat.add_le_add_right hLen 8195)
          (Nat.add_le_add_right hLen 8195)
          hLen
      exact hSpec.credit_le st0 rfl

/-- Small-slice (`N ≤ S`) `into_boxed_slice` combinator: zero `liveLarge` and `peakLarge` delta. -/
theorem phaseCreditSpec_intoBoxedSmall_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (N : Nat) (hNS : N ≤ S) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ (bs : List (BitVec 8)) (cap : BitVec 64),
        bs.length ≤ N ∧ evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseCreditSpec M Env (2 * N + 9539) 0 0 N where
  req_align evs hE ev hMem := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, hLen, rfl⟩
    · nomatch hMem
    · have hSpec :=
        phaseCreditSpec_intoBoxedCap_small_S hM hSm bs (Nat.le_trans hLen hNS)
          (· = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) (fun _ h => ⟨cap, h⟩)
      obtain ⟨hReq, hAl⟩ := hSpec.req_align _ rfl ev hMem
      exact ⟨Nat.le_trans hReq hLen, hAl⟩
  credit_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, hLen, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_max_left _ _⟩
    · have hSpec :=
        (phaseCreditSpec_intoBoxedCap_small_S hM hSm bs (Nat.le_trans hLen hNS)
          (· = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) (fun _ h => ⟨cap, h⟩)).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hLen) 9539)
          (Nat.le_refl 0)
          (Nat.le_refl 0)
          hLen
      exact hSpec.credit_le st0 rfl

/-- Tight `S`-capped `PhaseCreditSpec` for an optional/bounded `try_clone_from_ref` phase with
`bs.length ≤ N`. -/
theorem phaseCreditSpec_tryCloneBounded_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (N : Nat) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ bs : List (BitVec 8),
        bs.length ≤ N ∧ evs = (if bs = [] then [] else rustAllocEvents bs.length 1)) :
    PhaseCreditSpec M Env (2 * min N S + 9539) (N + 8195) (N + 8195) N where
  req_align evs hE ev hMem := by
    rcases hEnv evs hE with rfl | ⟨bs, hLen, rfl⟩
    · nomatch hMem
    · obtain ⟨hReq, hAl⟩ := (phaseCreditSpec_tryCloneBytes_S hM hSm bs).req_align _ rfl ev hMem
      exact ⟨Nat.le_trans hReq hLen, hAl⟩
  credit_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, hLen, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_max_left _ _⟩
    · have hMinLe : min bs.length S ≤ min N S :=
        Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) hLen, Nat.min_le_right _ _⟩
      have hSpec :=
        ((phaseCreditSpec_tryCloneBytes_S hM hSm bs).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hMinLe) 9539)
          (Nat.add_le_add_right hLen 8195)
          (Nat.add_le_add_right hLen 8195)
          hLen)
      exact hSpec.credit_le st0 rfl

/-! ## 4-Field Loop, Error-Tail, & Post-Loop `PhaseGroupSpec` Combinators -/

/-- `PhaseGroupSpec` for 1-push protobuf decode error tails (`43464 + 140011 = 183475`). -/
theorem phaseGroupSpec_errTail1 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      ∃ evs_core evs_free,
        evs = evs_core ++ evs_free ∧
        FreeOnlyEvs evs_free ∧
        (evs_core = [] ∨
         evs_core = rustAllocEvents 72 8 ∨
         ∃ evs_p, evs_core = rustAllocEvents 72 8 ++ evs_p ∧
           (evs_p = [] ∨ evs_p = rustAllocEvents 128 8))) :
    PhaseGroupSpec M Env 183475 := by
  have hOpt72 : PhaseGroupSpec M (fun e => e = [] ∨ e = rustAllocEvents 72 8) 43464 :=
    ((PhaseGroupSpec.nil M).or
      (phaseGroupSpec_rustAlloc_le108 hGrp (by decide : 72 ≤ 108) (by decide : 8 ≤ 16))).mono
      (by decide : max 0 43464 ≤ 43464)
  have hPush0 : PhaseGroupSpec M (fun e => e = [] ∨ e = rustAllocEvents 128 8) 140011 :=
    ((PhaseGroupSpec.nil M).or
      (phaseGroupSpec_rustAlloc_cap hGrp 128 (by decide : 8 ≤ 16))).mono
      (by decide : max 0 140011 ≤ 140011)
  have hFree := PhaseGroupSpec.freeOnly M
  refine (((hOpt72.seq hPush0).seq hFree).of_imp (fun evs hE => ?_)).mono
    (by decide : 43464 + 140011 + 0 ≤ 183475)
  obtain ⟨evs_core, evs_free, rfl, hFr, hCore⟩ := hEnv evs hE
  refine Or.inr ⟨evs_core, evs_free, rfl, ?_, hFr⟩
  rcases hCore with rfl | rfl | ⟨evs_p, rfl, hp⟩
  · exact Or.inr ⟨[], [], rfl, Or.inl rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rustAllocEvents 72 8, [], by simp, Or.inr rfl, Or.inl rfl⟩
  · exact Or.inr ⟨rustAllocEvents 72 8, evs_p, rfl, Or.inr rfl, hp⟩

/-- `PhaseGroupSpec` for 2-push protobuf decode error tails (`43464 + 140011 + 140011 = 323486`). -/
theorem phaseGroupSpec_errTail2 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      ∃ evs_72 evs_p0 evs_p1 evs_free,
        evs = evs_72 ++ evs_p0 ++ evs_p1 ++ evs_free ∧
        (evs_72 = [] ∨ evs_72 = rustAllocEvents 72 8) ∧
        (evs_p0 = [] ∨ evs_p0 = rustAllocEvents 128 8) ∧
        (evs_p1 = [] ∨ evs_p1 = rustReallocEvents 32 128 8) ∧
        FreeOnlyEvs evs_free) :
    PhaseGroupSpec M Env 323486 := by
  have hOpt72 : PhaseGroupSpec M (fun e => e = [] ∨ e = rustAllocEvents 72 8) 43464 :=
    ((PhaseGroupSpec.nil M).or
      (phaseGroupSpec_rustAlloc_le108 hGrp (by decide : 72 ≤ 108) (by decide : 8 ≤ 16))).mono
      (by decide : max 0 43464 ≤ 43464)
  have hPush0 : PhaseGroupSpec M (fun e => e = [] ∨ e = rustAllocEvents 128 8) 140011 :=
    ((PhaseGroupSpec.nil M).or
      (phaseGroupSpec_rustAlloc_cap hGrp 128 (by decide : 8 ≤ 16))).mono
      (by decide : max 0 140011 ≤ 140011)
  have hPush1 : PhaseGroupSpec M (fun e => e = [] ∨ e = rustReallocEvents 32 128 8) 140011 :=
    ((PhaseGroupSpec.nil M).or
      (phaseGroupSpec_rustRealloc_cap hGrp 32 128 (by decide : 8 ≤ 16))).mono
      (by decide : max 0 140011 ≤ 140011)
  have hFree := PhaseGroupSpec.freeOnly M
  refine ((((hOpt72.seq hPush0).seq hPush1).seq hFree).of_imp (fun evs hE => ?_)).mono
    (by decide : 43464 + 140011 + 140011 + 0 ≤ 323486)
  obtain ⟨e72, ep0, ep1, ef, rfl, h72, hp0, hp1, hf⟩ := hEnv evs hE
  exact Or.inr ⟨e72 ++ ep0 ++ ep1, ef, rfl,
    Or.inr ⟨e72 ++ ep0, ep1, rfl, Or.inr ⟨e72, ep0, rfl, h72, hp0⟩, hp1⟩, hf⟩

/-- Modular inductive invariant for 4-field `Vec<u8>` protobuf decode loop group accounting. -/
def ProtoLoop4GroupInv (M : AllocCostModel) [HasFineGroupCredit M]
    (tg rem : Nat) (caps : ProtoCaps4) (evs : List AllocEvent) : Prop :=
  ∀ (st : M.σ) (N : Nat),
    rem ≤ N →
    HasFineGroupCredit.groupsScaled (M.stepEvents evs st) ≤
      HasFineGroupCredit.groupsScaled st + 2369 * rem +
        140011 * caps.remGrows N + tg

private theorem proto_grp_tail {g0 gf R W T : Nat} (h : gf ≤ g0 + T) :
    gf ≤ g0 + R + W + T := by
  omega

private theorem proto_grp_skip {g0 gf R' R W T : Nat}
    (h : gf ≤ g0 + R' + W + T) (hr : R' ≤ R) :
    gf ≤ g0 + R + W + T := by
  omega

private theorem proto_grp_free {g0 g1 gf R' R W T : Nat}
    (h1 : g1 ≤ g0 + 0) (h2 : gf ≤ g1 + R' + W + T) (hr : R' ≤ R) :
    gf ≤ g0 + R + W + T := by
  omega

private theorem proto_grp_comb {g0 g1 g2 r1 r2 r kw kw' kother t : Nat}
    (hstep : g1 + kw' ≤ g0 + r1 + kw)
    (hih : g2 ≤ g1 + r2 + (kother + kw') + t)
    (hr : r1 + r2 = r) :
    g2 ≤ g0 + r + (kother + kw) + t := by
  omega

theorem ProtoLoop4GroupInv.of_tail {M : AllocCostModel} [HasFineGroupCredit M]
    {TailEnv : List AllocEvent → Prop} {tg rem : Nat} {caps : ProtoCaps4}
    {evs : List AllocEvent}
    (hTail : PhaseGroupSpec M TailEnv tg) (hE : TailEnv evs) :
    ProtoLoop4GroupInv M tg rem caps evs :=
  fun st _ _ => proto_grp_tail (hTail.groups_le st hE)

theorem ProtoLoop4GroupInv.of_skip {M : AllocCostModel} [HasFineGroupCredit M]
    {tg rem rem' : Nat} {caps : ProtoCaps4} {evs : List AllocEvent}
    (hRem : rem' ≤ rem)
    (ih : ProtoLoop4GroupInv M tg rem' caps evs) :
    ProtoLoop4GroupInv M tg rem caps evs :=
  fun st N hRemN =>
    proto_grp_skip (ih st N (Nat.le_trans hRem hRemN)) (Nat.mul_le_mul_left 2369 hRem)

theorem ProtoLoop4GroupInv.of_free_prepend {M : AllocCostModel} [HasFineGroupCredit M]
    {tg rem rem' : Nat} {caps : ProtoCaps4} {evs₁ evs₂ : List AllocEvent}
    (hRem : rem' ≤ rem) (hFree : FreeOnlyEvs evs₁)
    (ih : ProtoLoop4GroupInv M tg rem' caps evs₂) :
    ProtoLoop4GroupInv M tg rem caps (evs₁ ++ evs₂) := by
  intro st N hRemN
  rw [AllocCostModel.stepEvents_append]
  have h1 := (PhaseGroupSpec.freeOnly M).groups_le st hFree
  have h2 := ih (M.stepEvents evs₁ st) N (Nat.le_trans hRem hRemN)
  exact proto_grp_free h1 h2 (Nat.mul_le_mul_left 2369 hRem)

theorem ProtoLoop4GroupInv.of_bytesStep {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (f : ProtoField4)
    {tg rem rem' : Nat} {caps : ProtoCaps4}
    {wt : WireType} {bs v rest : List (BitVec 8)} {evs₂ : List AllocEvent}
    (hMerge : mergeBytes wt bs = some (v, rest))
    (_hBs : bs.length ≤ rem)
    (hRem : rem' + v.length + 1 ≤ rem)
    (hCapFit : caps.get f < 2 ^ 64)
    (ih : ProtoLoop4GroupInv M tg rem'
      (caps.set f (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length))
      evs₂) :
    ProtoLoop4GroupInv M tg rem caps
      (bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs ++ evs₂) := by
  intro st N hRemN
  set cap := caps.get f
  set cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
  have hstep := bytesMergeEventsCore_groups_step hGrp hMerge hRem hRemN hCapFit st
  change HasFineGroupCredit.groupsScaled
      (M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st) +
      140011 * wireRemGrows N cap' ≤
    HasFineGroupCredit.groupsScaled st + 2369 * (rem - rem') +
      140011 * wireRemGrows N cap at hstep
  rw [AllocCostModel.stepEvents_append]
  set st₁ := M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st
  have hih := ih st₁ N (by omega)
  obtain ⟨hgw_pre, hgw_post⟩ := ProtoCaps4.remGrows_decomp N caps f cap'
  rw [hgw_post, Nat.mul_add] at hih
  rw [hgw_pre, Nat.mul_add]
  have hrem_mul : 2369 * (rem - rem') + 2369 * rem' = 2369 * rem := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
  exact proto_grp_comb hstep hih hrem_mul

private theorem proto_grp_assoc {gf g0 a b c : Nat} (h : gf ≤ g0 + a + b + c) :
    gf ≤ g0 + (a + b + c) := by
  omega

theorem ProtoLoop4GroupInv.to_phaseGroupSpec {M : AllocCostModel} [HasFineGroupCredit M]
    {Env : List AllocEvent → Prop} {tg N : Nat}
    (hInv : ∀ evs, Env evs → ProtoLoop4GroupInv M tg N ProtoCaps4.zero evs) :
    PhaseGroupSpec M Env (2369 * N + 560044 * wireRemGrows N 0 + tg) where
  groups_le st0 {evs} hE := by
    have h := hInv evs hE st0 N (Nat.le_refl N)
    have hzero_gw : ProtoCaps4.zero.remGrows N = 4 * wireRemGrows N 0 := by
      simp only [ProtoCaps4.remGrows, ProtoCaps4.zero]
      omega
    have hmul4 : 140011 * (4 * wireRemGrows N 0) = 560044 * wireRemGrows N 0 := by
      rw [← Nat.mul_assoc]
    rw [hzero_gw, hmul4] at h
    exact proto_grp_assoc h

/-- `PhaseGroupSpec` for `ProtoLoop4BoundedEnv TailEnv N ProtoCaps4.zero`. -/
theorem phaseGroupSpec_protoLoop4 {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {TailEnv : List AllocEvent → Prop} {tg : Nat} (N : Nat)
    (hTail : PhaseGroupSpec M TailEnv tg) :
    PhaseGroupSpec M (ProtoLoop4BoundedEnv TailEnv N ProtoCaps4.zero)
      (2369 * N + 560044 * wireRemGrows N 0 + tg) := by
  have hInv : ∀ {rem caps evs}, ProtoLoop4BoundedEnv TailEnv rem caps evs →
      ProtoLoop4GroupInv M tg rem caps evs := by
    intro rem caps evs h
    induction h with
    | done hE => exact ProtoLoop4GroupInv.of_tail hTail hE
    | skipStep hLe _ ih => exact ProtoLoop4GroupInv.of_skip hLe ih
    | freeStep hLe hFr _ ih => exact ProtoLoop4GroupInv.of_free_prepend hLe hFr ih
    | bytesStep f wt bs v rest hMb hBs hRem hCap _ ih =>
        exact ProtoLoop4GroupInv.of_bytesStep hGrp f hMb hBs hRem hCap ih
  exact ProtoLoop4GroupInv.to_phaseGroupSpec (fun _ h => hInv h)

theorem phaseGroupSpec_intoBoxedBounded {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ (bs : List (BitVec 8)) (cap : BitVec 64),
        evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseGroupSpec M Env 140011 where
  groups_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, cap, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact Nat.le_add_right _ 140011
    · unfold intoBoxedSliceEvents
      dsimp only
      split
      · simp only [AllocCostModel.stepEvents_nil]
        exact Nat.le_add_right _ 140011
      · split
        · exact ((PhaseGroupSpec.rustDealloc M cap.toNat 1).mono (Nat.zero_le 140011)).groups_le
            st0 rfl
        · exact (phaseGroupSpec_rustRealloc_cap hGrp cap.toNat bs.length (by decide : 1 ≤ 16)).groups_le
            st0 rfl

theorem phaseGroupSpec_tryCloneBounded {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs →
      evs = [] ∨
      ∃ bs : List (BitVec 8),
        evs = (if bs = [] then [] else rustAllocEvents bs.length 1)) :
    PhaseGroupSpec M Env 140011 where
  groups_le st0 {evs} hE := by
    rcases hEnv evs hE with rfl | ⟨bs, rfl⟩
    · simp only [AllocCostModel.stepEvents_nil]
      exact Nat.le_add_right _ 140011
    · exact (phaseGroupSpec_tryCloneBytes hGrp bs).groups_le st0 rfl

end LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit
