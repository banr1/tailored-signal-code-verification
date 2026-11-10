/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame

/-!
# Budget-Threaded Relocatable `OTR::from_session_state` Decomposition

Provides the `[LibsignalPlacement]` `RustCliAllocBudget` specifications (`otrFromRawPlacedSpec`,
`otrFromPlacedSpec`) and four-case decomposition (`subroutine_ok_of_cases4_placed`) for
`<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FreeOnlyEvs)
open CryptoGames.LibsignalSession (OutgoingTripleRatchet SessionState SignalProtocolError)
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded LibsignalRoLoaded lsmpl lsLogFilterAddr
   withLsCodeLoaded extract_withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt otrResultAt)
open CryptoVerification.LibsignalTripleRatchet (OtrFromGhost smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (withLsRoLoaded)

/-- Budget-threaded relocatable specification of `OTR::from_session_state` (`FreeOnlyEvs`,
    `0` `FitsEnv` needed). -/
def otrFromRawPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (OtrFromGhost × M.σ) where
  pre := fun (x, st) s =>
    (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrFromRawPlacedSpec
      (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜FreeOnlyEvs evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrFromRawPlacedSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

abbrev otrFromPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (OtrFromGhost × M.σ) :=
  withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (otrFromRawPlacedSpec M A lim))

def otrFromCasePlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (P : OtrFromGhost → Prop) :
    Spec (OtrFromGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜P x ∧ LibsignalCodeLoaded lsmpl s.mem ∧ LibsignalRoLoaded lsmpl s.mem ∧
      s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗
      memRegion x.ret 200 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt s.sp smallRootStack ∗ A.pool lim st s
  post := (otrFromRawPlacedSpec M A lim).post
  onPanic := (otrFromRawPlacedSpec M A lim).onPanic

theorem otrFromCasePlacedSpec_pre_of_pre [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : OtrFromGhost → Prop} {x : OtrFromGhost} {st : M.σ} {s0 : State} {R : SepProp}
    (hx : P x)
    (hpre : s0.mem ⊨ (otrFromPlacedSpec M A lim).pre (x, st) s0 ∗ R) :
    s0.mem ⊨ (otrFromCasePlacedSpec M A lim P).pre (x, st) s0 ∗ R := by
  dsimp only [otrFromPlacedSpec, withLsRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hro, hpre⟩ := hpre
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [otrFromRawPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrFromRawPlacedSpec,
    otrFromCasePlacedSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨⟨hx, hcl, hro, hpre.1.1, hpre.1.2⟩, hpre.2⟩

theorem subroutine_ok_of_cases4_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P₁ P₂ P₃ P₄ : OtrFromGhost → Prop}
    (hcov : ∀ x, P₁ x ∨ P₂ x ∨ P₃ x ∨ P₄ x)
    (h1 : subroutine_ok prog entry (otrFromCasePlacedSpec M A lim P₁))
    (h2 : subroutine_ok prog entry (otrFromCasePlacedSpec M A lim P₂))
    (h3 : subroutine_ok prog entry (otrFromCasePlacedSpec M A lim P₃))
    (h4 : subroutine_ok prog entry (otrFromCasePlacedSpec M A lim P₄)) :
    subroutine_ok prog entry (otrFromPlacedSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  rcases hcov x with hx | hx | hx | hx
  · exact h1.mono_outcome (x, st) R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp
      fun _ hout => hout
  · exact h2.mono_outcome (x, st) R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp
      fun _ hout => hout
  · exact h3.mono_outcome (x, st) R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp
      fun _ hout => hout
  · exact h4.mono_outcome (x, st) R s0 hpc hrun (otrFromCasePlacedSpec_pre_of_pre hx hpre) hsp
      fun _ hout => hout

theorem SepWP.instantiate_otrFrom_placed_post [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {target_pc : BitVec 64} {s s0 : State} {P R : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : OtrFromGhost) (st : M.σ) (G' : SessionGhost) (evs : List AllocEvent)
    (hfree : FreeOnlyEvs evs)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜x.model.1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A.repAlloc x.ss G' x.model.2) ∗
          otrResultAt A.repAlloc x.ret x.G.pq x.model.1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗
          A.pool lim (M.stepEvents evs st) sf) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (otrFromRawPlacedSpec M A lim).post (x, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.mono h fun sf P_f _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  have hm1 : sf.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrFromRawPlacedSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf ∗ R :=
    Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro G'))))
      (h1 hm)
  have hm2 : sf.mem ⊨
      (⌜FreeOnlyEvs evs⌝ ∗
        (CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.otrFromRawPlacedSpec
          (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf) ∗ R :=
    Satisfies.mono
      (sepConj_mono_left (Entails.pure_right hfree (Entails.refl _)))
      hm1
  exact Satisfies.mono
    (sepConj_mono_left (Entails.sepExists_intro evs))
    hm2

namespace FromSessionStateFacts

theorem finish_otrFrom_placed [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {target_pc : BitVec 64} {s s0 : State} {P R : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : OtrFromGhost) (st : M.σ) (G' : SessionGhost) (evs : List AllocEvent)
    (hfree : FreeOnlyEvs evs)
    (res' : Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8))))
    (st' : SessionState (List (BitVec 8)))
    (hmod1 : x.model.1 = res')
    (hmod2 : x.model.2 = st')
    (_hnopanic : res' ≠ .error .panic)
    (_hagree : x.G.AgreeExceptPq G')
    (hdone : SepWP prog target_pc s
      (sessionStateAt A.repAlloc x.ss G' st' ∗
        otrResultAt A.repAlloc x.ret x.G.pq res' ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim (M.stepEvents evs st) s)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜res' ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (⌜x.G.AgreeExceptPq G'⌝ ∗ sessionStateAt A.repAlloc x.ss G' st') ∗
            otrResultAt A.repAlloc x.ret x.G.pq res' ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp smallRootStack ∗
            A.pool lim (M.stepEvents evs st) sf) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))
    (hent : P ⊢
      sessionStateAt A.repAlloc x.ss G' st' ∗
        otrResultAt A.repAlloc x.ret x.G.pq res' ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim (M.stepEvents evs st) s) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (otrFromRawPlacedSpec M A lim).post (x, st) s0 sf ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  apply SepWP.instantiate_otrFrom_placed_post x st G' evs hfree
  rw [hmod1, hmod2]
  exact SepWP.weaken_pre hent hdone

end FromSessionStateFacts

end LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget
