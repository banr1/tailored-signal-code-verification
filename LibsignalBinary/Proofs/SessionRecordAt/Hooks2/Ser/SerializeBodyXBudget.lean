/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyX
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded `SessionRecord::serialize` `None` / `Some` Case Split (Block `52`)

Combines `serialize_none_placed_okX` and `serialize_some_placed_okX` to establish
`withLsCodeLoaded lsmpl (serializeSpecX M A lim)` on Block `52` (`SessionRecord::serialize`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyXBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl extract_withLsCodeLoaded
)
open CryptoVerification.RustHeap (vecAt)
open CryptoVerification.LibsignalPublicApiRepr (sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52)
open CryptoVerification.E2E.Record.Serialization (
  encCurMem encSessionMem encRecordMem
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  prevVecFrameX vecAt_empty_splitX
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (SerializeEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  SerializeEnvX fitsEnv_serializeEnv_of_serializeEnvX
  serializeSpecX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX SessionClonePlacedOkX EncodeRawPlacedOkX
  DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget (
  serializeNoneSpecX serialize_none_placed_okX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeXBudget (
  SerializeSomeAllocEnv serializeSomeSpecX serialize_some_placed_okX
)

section Placed

private theorem pack_withLsCodeLoaded_sbx {pl : MultiPlacement} {α : Type} {S : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hp : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl S).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm _ ⌜LibsignalCodeLoaded pl s0.mem⌝, satisfies_pure_sepConj]
  exact ⟨hcl, hp⟩

/-- Relocatable `[LibsignalPlacement]` budget-threaded `SessionRecord::serialize` on `lsProg_52 H`. -/
theorem serialize_placed_ok_of_leaves_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPlacedOkX M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSpecX M A lim)) := by
  have hnone := serialize_none_placed_okX (M := M) (A := A) (lim := lim) hC
  have hsome := serialize_some_placed_okX hC hClone hEV hRaw hDrop
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre0 hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrameX A.repAlloc x.self x.g ∗ memRegion (x.self + 32#64) 336
    have hpre' : s0.mem ⊨
        (withLsCodeLoaded lsmpl (serializeNoneSpecX M A lim)).pre
          ((x.self, x.out, x.g.prevPtr), st) s0 ∗ (F ∗ R) := by
      refine pack_withLsCodeLoaded_sbx hcl0 ?_
      simp only [serializeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨⟨hpre.1.1, hpre.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre.2
    refine hnone.mono_outcome ((x.self, x.out, x.g.prevPtr), st) (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨h1, h2, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost ⊢
      simp only [serializeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepExists_sepConj_left,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨[], ⟨hpost.1, SerializeEnvX.nil x.g x.r⟩, ?_⟩
      simp only [AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
    · exact False.elim (not_satisfies_false_sepConj hoom)
  ·
    simp only [serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A.repAlloc 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    simp only [serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A.repAlloc 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    have henv_eq : SerializeEnv x.g x.r = SerializeSomeAllocEnv G sess := by
      funext evs
      dsimp only [SerializeEnv, SerializeSomeAllocEnv]
      rw [henc]
    let F := prevVecFrameX A.repAlloc x.self x.g
    have hpre' : s0.mem ⊨
        (withLsCodeLoaded lsmpl (serializeSomeSpecX M A lim)).pre
          (⟨x.self, x.out, x.g.prevPtr, G, sess⟩, st) s0 ∗ (F ∗ R) := by
      refine pack_withLsCodeLoaded_sbx hcl0 ?_
      simp only [serializeSpecX, serializeSomeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      have hFit_some : FitsEnv M lim st (SerializeSomeAllocEnv G sess) := by
        rw [← henv_eq]
        exact fitsEnv_serializeEnv_of_serializeEnvX hpre.1.2.2.2
      refine ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hFit_some⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre.2
    refine hsome.mono_outcome (⟨x.self, x.out, x.g.prevPtr, G, sess⟩, st) (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
    · refine Or.inl ⟨h1, h2, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost ⊢
      simp only [serializeSpecX, serializeSomeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepExists_sepConj_left,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨evs, ⟨htr, henv⟩, hmem⟩
      refine ⟨evs, ⟨htr, ?_⟩, ?_⟩
      · dsimp only [SerializeEnvX]
        rwa [henv_eq]
      · exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
    · exact False.elim (not_satisfies_false_sepConj hoom)

theorem serialize_placed_cl_of_leaves_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H)
    (hClone : SessionClonePlacedOkX M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hRaw : EncodeRawPlacedOkX M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (serialize_placed_ok_of_leaves_ext hC hClone hEV hRaw hDrop)

end Placed

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyXBudget
