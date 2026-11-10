/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize` (`0x1857c`): `None` / `Some` Case Split

Combines `serialize_none_okX` and `serialize_some_okX` to verify `SessionRecord::serialize`
(`0x1857c`, Block `52`) against `serializeSpecX A` on `SP2Ext` and under relocatable
`[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

theorem L1_SerializeBodyX : True := trivial

/-- Empty previous-sessions `Vec` layout without its `ptr` and `len` header words. -/
def prevVecFrameX (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) : SepProp :=
  (r ↦₆₄ g.prevCap) ∗ vecBuf A 24 8 (fun (_ : Unit) _ => emp) g.prevCap g.prevPtr []

theorem vecAt_empty_splitX (A : RustAlloc) (r : BitVec 64) (g : RecordGhost) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr [] =
      ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗ prevVecFrameX A r g := by
  unfold vecAt vecHeader prevVecFrameX
  simp only [List.length_nil]
  ac_rfl

/-- `SessionRecord::serialize` (`0x1857c`) satisfies `(serializeSpecX A).inImage img` on
`SP2Ext img.base ext` given its callee and stub contracts. -/
theorem serialize_ok_of_leaves_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hClone : SessionCloneOkX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (hRaw : EncodeRawOkX img A ext)
    (hDrop : DropSessionStructureLocal1OkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName)
      ((serializeSpecX A).inImage img) := by
  have hnone := serialize_none_okX (img := img) (A := A) (ext := ext) hC
  have hsome := serialize_some_okX hC hClone hEV hRaw hDrop
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrameX A x.self x.g ∗ memRegion (x.self + 32#64) 336 ∗ A.pool
    have hpre' : s0.mem ⊨ ((serializeNoneSpecX A).inImage img).pre (x.self, x.out, x.g.prevPtr) s0 ∗
        (F ∗ R) := by
      simp only [Spec.inImage, serializeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2.2
    refine hnone.mono_outcome (x.self, x.out, x.g.prevPtr) (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩)
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [Spec.inImage, serializeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
  ·
    simp only [Spec.inImage, serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.2.1
  ·
    simp only [Spec.inImage, serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrameX A x.self x.g
    have hpre' : s0.mem ⊨ ((serializeSomeSpecX A).inImage img).pre
        ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ s0 ∗ (F ∗ R) := by
      simp only [Spec.inImage, serializeSpecX, serializeSomeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨hpre.1, hpre.2.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2.2
    refine hsome.mono_outcome ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩)
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      simp only [Spec.inImage, serializeSpecX, serializeSomeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      simp only [Spec.inImage, serializeSpecX, serializeSomeSpecX] at hpan ⊢
      rw [← sepConj_assoc] at hpan
      exact allowPanic_frame id hpan
    · exact False.elim (not_satisfies_false_sepConj hex)

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `52`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_SerializeBodyX_Placed : True := trivial

private theorem pack_withLsCodeLoaded_sbx {pl : MultiPlacement} {α : Type} {S : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hp : s0.mem ⊨ S.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl S).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm _ ⌜LibsignalCodeLoaded pl s0.mem⌝, satisfies_pure_sepConj]
  exact ⟨hcl, hp⟩

/-- Relocatable `SessionRecord::serialize` (Block `52`) satisfies `withLsCodeLoaded lsmpl (serializeSpecX A)`. -/
theorem serialize_placed_ok_of_leaves_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hClone : SessionClonePlacedOkX A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    subroutine_ok (lsProg_52 H) (blkPl_52).base
      (withLsCodeLoaded lsmpl (serializeSpecX A)) := by
  have hnone := serialize_none_placed_okX hC
  have hsome := serialize_some_placed_okX hC hClone hEV hRaw hDrop
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre0 hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre0
  rcases hcur_g : x.g.cur with _ | G <;> rcases hcur_r : x.r.currentSession with _ | sess
  ·
    have henc : encRecordMem x.g x.r = [] := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrameX A x.self x.g ∗ memRegion (x.self + 32#64) 336 ∗ A.pool
    have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (serializeNoneSpecX A)).pre (x.self, x.out, x.g.prevPtr) s0 ∗
        (F ∗ R) := by
      refine pack_withLsCodeLoaded_sbx hcl0 ?_
      simp only [serializeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨⟨hpre.1.1, hpre.1.2.1⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine hnone.mono_outcome (x.self, x.out, x.g.prevPtr) (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩)
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost ⊢
      simp only [serializeSpecX, serializeNoneSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · exact False.elim (not_satisfies_false_sepConj hpan)
    · exact False.elim (not_satisfies_false_sepConj hex)
  ·
    simp only [serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    simp only [serializeSpecX, sessionRecordAt, hcur_g, hcur_r,
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_comm (vecAt A 24 8 (fun _ _ => emp) x.self x.g.prevCap x.g.prevPtr []),
      sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.2.1
  ·
    have henc : encRecordMem x.g x.r = lenField 1 (encSessionMem G sess) := by
      simp [encRecordMem, encCurMem, hcur_g, hcur_r]
    let F := prevVecFrameX A x.self x.g
    have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (serializeSomeSpecX A)).pre
        ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ s0 ∗ (F ∗ R) := by
      refine pack_withLsCodeLoaded_sbx hcl0 ?_
      simp only [serializeSpecX, serializeSomeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      refine ⟨hpre.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre.2
    refine hsome.mono_outcome ⟨x.self, x.out, x.g.prevPtr, G, sess⟩ (F ∗ R) s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨h1, h2, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨_, _, hex⟩ | ⟨_hoom_st, _hoom_post⟩)
    rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
    · refine Or.inl ⟨h1, h2, ?_⟩
      dsimp only [withLsCodeLoaded] at hpost ⊢
      simp only [serializeSpecX, serializeSomeSpecX, sessionRecordAt, hcur_g,
        hcur_r, henc, vecAt_empty_splitX, F, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost.2
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      dsimp only [withLsCodeLoaded, serializeSpecX, serializeSomeSpecX] at hpan ⊢
      rw [← sepConj_assoc] at hpan
      exact allowPanic_frame id hpan
    · exact False.elim (not_satisfies_false_sepConj hex)

theorem serialize_placed_cl_of_leaves_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H)
    (hClone : SessionClonePlacedOkX A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hRaw : EncodeRawPlacedOkX A H)
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 52)
      (withLsCl lsmpl (serializeSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (serialize_placed_ok_of_leaves_ext hC hClone hEV hRaw hDrop)

end Placed

end CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
