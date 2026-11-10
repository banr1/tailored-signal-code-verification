/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.Cost.Tight2Sound
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
import VerifiedLibraries.Mallocng.Proofs.Top

/-!
# Placed Entry Contracts for the Usage-Indexed Tight Cost Model

Derives the model-indexed placed entry contracts
`mallocngModel*Spec mallocngTight2CostModel mallocngTight2Iface` from the block-token-generic
contracts `mallocng*TokSpec MallocngTightBlock`, and assembles `mallocngTight2Sound` and
`VerifiedLibraries.Mallocng.mallocngTight2Cost_ok`.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng
  VerifiedLibraries.Mallocng.Proofs

/-! ## Reserve and OOM bridges -/

theorem tight2_stepReserve_alloc (r : Nat) (b : mallocngTight2CostModel.σ) :
    mallocngTight2CostModel.stepReserve (.alloc r) b =
      MallocngTightStepBound r (MallocngBudget.peakCount b) :=
  mallocngTight2Reserve_eq _ _

theorem tight2_stepReserve_aligned (a r : Nat) (b : mallocngTight2CostModel.σ) :
    mallocngTight2CostModel.stepReserve (.aligned a r) b =
      MallocngTightStepBound (mallocngAlignedEffSize a r) (MallocngBudget.peakCount b) :=
  mallocngTight2Reserve_eq _ _

/-- `stepB` of the model specs for an `ok`-guarded event equals the tight bound at the guarded
    request. -/
theorem tight2_stepB_ite (ok : Bool) (ev : AllocEvent) (r : Nat)
    (b : mallocngTight2CostModel.σ)
    (hev : mallocngTight2CostModel.stepReserve ev b =
      MallocngTightStepBound r (MallocngBudget.peakCount b)) :
    (if ok then mallocngTight2CostModel.stepReserve ev b
      else mallocngTight2CostModel.stepReserve (.alloc 0) b) =
      MallocngTightStepBound (if ok then r else 0) (MallocngBudget.peakCount b) := by
  cases ok
  · exact tight2_stepReserve_alloc 0 b
  · exact hev

theorem MallocngTightOomCond.to_stepOomCond {svc : State → State} {r pc : Nat} {s0 sf : State}
    (h : MallocngTightOomCond svc r pc s0 sf) :
    MallocngStepOomCond svc (MallocngTightStepBound r pc) s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hlen, hsum, hcov, hgap⟩ := h
  refine ⟨hfs, htr, hsig, ivs, hlen, hsum, hcov, fun hs => ?_⟩
  obtain ⟨sz, h1, h2, _, h4, h5⟩ := hgap hs
  refine ⟨sz, h1, h2, ?_, h5⟩
  rw [MallocngTightTotalBound_eq] at h4
  rw [MallocngTightStepBound_eq]
  exact h4

theorem tight2_step_alloc_ite (ok : Bool) (r : Nat)
    (b : mallocngTight2CostModel.σ) :
    (if ok then mallocngTight2CostModel.step (.alloc r) b else b) =
      mallocngAllocBudget ok r b := by
  cases ok <;> rfl

theorem tight2_step_aligned_ite (ok : Bool) (a r : Nat)
    (b : mallocngTight2CostModel.σ) :
    (if ok then mallocngTight2CostModel.step (.aligned a r) b else b) =
      mallocngAlignedBudget ok a r b := by
  cases ok <;> rfl

/-! ## `__libc_malloc_impl` contracts at `MallocngTightBlock` -/

private theorem tight2_libcMallocImpl_tok_ok (hK : LibcMallocImplPlacedTightKStmt) :
    LibcMallocImplPlacedTokStmt MallocngTightBlock := by
  intro _ γ tp brkStart b ivs0 req
  refine subroutine_ok_mono (hK γ tp brkStart b ivs0 req)
    (fun _ _ _ hp => hp) (fun _ R s0 sf hq => ?_)
  dsimp only [libcMallocImplPlacedTightKSpec, libcMallocImplPlacedTokSpec, withCL] at hq ⊢
  refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_right ?_)))) hq
  by_cases hReq : req ≤ MallocngMaxAllocSize
  · simp only [hReq, ↓reduceIte]
    refine Entails.sepExists_mono fun p => Entails.sepExists_mono fun bs =>
      Entails.sepExists_mono fun st' => ?_
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right ?_))))
    exact mallocngBlockTokenK_to_tight γ p req 0 16 (Nat.zero_le _)
  · simp only [hReq, ↓reduceIte]
    exact Entails.refl _

private theorem tight2_libcMallocImpl24_ok : LibcMallocImplPlaced24Stmt := by
  intro _ γ tp brkStart b ivs0 req
  have hB2 :=
    placed_libcMallocImpl24B2_uncond_ok
      placed_allocMeta_full_ok
      (placed_allocSlot_full_ok placed_allocMeta_full_ok)
      γ tp brkStart b ivs0 req
  refine subroutine_ok_mono hB2 (fun _ _ _ hp => hp) (fun _ _ s0 sf hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)
  · dsimp only [libcMallocImplPlacedSpec24B2, libcMallocImplPlacedSpec24, withCL] at hq ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hq
    refine sepConj_mono_left ?_
    by_cases hReq : req ≤ MallocngMaxAllocSize
    · simp only [hReq, ↓reduceIte]
      unfold mallocImplSuccessPost24 mallocImplSuccessBody24
      refine sepConj_mono (Entails.refl _) (sepConj_mono_right ?_)
      apply Entails.sepExists_elim; intro p
      apply Entails.sepExists_elim; intro bs
      apply Entails.sepExists_elim; intro st'
      refine Entails.trans ?_ (Entails.sepExists_intro p)
      refine Entails.trans ?_ (Entails.sepExists_intro bs)
      refine Entails.trans ?_ (Entails.sepExists_intro st')
      apply Entails.pure_left
      rintro ⟨h1, h2, h3, h4, h5, h6, h7, g', hg', idx, hIdx, hSl, hOff, hMm, hSc24_26, _hSc24, hSc63⟩
      exact Entails.pure_right
        ⟨h1, h2, h3, h4, h5, h6, h7, g', hg', idx, hIdx, hSl, hOff, hMm, hSc24_26, hSc63⟩
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (mallocngBlockTokenK_to_token γ p req 0)))))
    · simp only [hReq, ↓reduceIte]
      exact Entails.refl _
  · dsimp only [libcMallocImplPlacedSpec24B2, libcMallocImplPlacedSpec24, withCL] at ho ⊢
    exact ho

/-! ## Entry contracts -/

theorem tight2_malloc_ok (hK : LibcMallocImplPlacedTightKStmt) (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngModelMallocSpec mallocngTight2CostModel mallocngTight2Iface svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := mallocPlaced_entry_tok_ok
    (placed_defaultMalloc_tok_of_impl (tight2_libcMallocImpl_tok_ok hK)) mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp)
    (fun x _ _ _ hq => ?_) (hoom := fun x _ _ _ ho => ?_)⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngMallocTokSpec,
      mallocngModelMallocSpec, ToBaseSpec.toSpec] at hq ⊢
    generalize decide (x.1.toNat ≤ MallocngMaxAllocSize) = ok at hq ⊢
    rw [tight2_stepB_ite ok (.alloc x.1.toNat) x.1.toNat x.2.2.2.2.1
        (tight2_stepReserve_alloc _ _),
      tight2_step_alloc_ite]
    exact hq
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngMallocTokSpec,
      mallocngModelMallocSpec, ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    generalize decide (x.1.toNat ≤ MallocngMaxAllocSize) = ok at ho ⊢
    rw [tight2_stepB_ite ok (.alloc x.1.toNat) x.1.toNat x.2.2.2.2.1
        (tight2_stepReserve_alloc _ _)]
    exact ⟨MallocngTightOomCond.to_stepOomCond ho.1, ho.2⟩

theorem tight2_calloc_ok (hK : LibcMallocImplPlacedTightKStmt) (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngModelCallocSpec mallocngTight2CostModel mallocngTight2Iface svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := callocPlaced_entry_tok_ok
    (placed_defaultMalloc_tok_of_impl (tight2_libcMallocImpl_tok_ok hK)) mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp)
    (fun x _ _ _ hq => ?_) (hoom := fun x _ _ _ ho => ?_)⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngCallocTokSpec,
      mallocngModelCallocSpec, ToBaseSpec.toSpec] at hq ⊢
    generalize decide (x.1.toNat * x.2.1.toNat ≤ MallocngMaxAllocSize) = ok at hq ⊢
    rw [tight2_stepB_ite ok _ _ _ (tight2_stepReserve_alloc _ _),
      tight2_step_alloc_ite]
    exact hq
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngCallocTokSpec,
      mallocngModelCallocSpec, ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    generalize decide (x.1.toNat * x.2.1.toNat ≤ MallocngMaxAllocSize) = ok at ho ⊢
    rw [tight2_stepB_ite ok _ _ _ (tight2_stepReserve_alloc _ _)]
    exact ⟨MallocngTightOomCond.to_stepOomCond ho.1, ho.2⟩

theorem tight2_alignedAlloc_ok (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngModelAlignedAllocSpec mallocngTight2CostModel mallocngTight2Iface
        svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := alignedAllocPlaced_entry_tok_ok (B := MallocngTightBlock)
    (fun _ _ _ _ => Entails.refl _) tight2_libcMallocImpl24_ok mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp)
    (fun x _ _ _ hq => ?_) (hoom := fun x _ _ _ ho => ?_)⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngAlignedAllocTokSpec,
      mallocngModelAlignedAllocSpec,
      ToBaseSpec.toSpec] at hq ⊢
    generalize mallocngAlignedAllocOk x.1 x.2.1 = ok at hq ⊢
    rw [tight2_stepB_ite ok _ _ _ (tight2_stepReserve_aligned _ _ _),
      tight2_step_aligned_ite]
    exact hq
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngAlignedAllocTokSpec,
      mallocngModelAlignedAllocSpec,
      ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    generalize mallocngAlignedAllocOk x.1 x.2.1 = ok at ho ⊢
    rw [tight2_stepB_ite ok _ _ _ (tight2_stepReserve_aligned _ _ _)]
    exact ⟨MallocngTightOomCond.to_stepOomCond ho.1, ho.2⟩

theorem tight2_posixMemalign_ok (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngModelPosixMemalignSpec mallocngTight2CostModel mallocngTight2Iface
        svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := posixMemalignPlaced_entry_tok_ok (B := MallocngTightBlock)
    (fun _ _ _ _ => Entails.refl _) tight2_libcMallocImpl24_ok mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp)
    (fun x _ _ _ hq => ?_) (hoom := fun x _ _ _ ho => ?_)⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngPosixMemalignTokSpec,
      mallocngModelPosixMemalignSpec,
      ToBaseSpec.toSpec] at hq ⊢
    generalize mallocngPosixMemalignOk x.2.1 x.2.2.1 = ok at hq ⊢
    rw [tight2_stepB_ite ok _ _ _ (tight2_stepReserve_aligned _ _ _),
      tight2_step_aligned_ite]
    exact hq
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngPosixMemalignTokSpec,
      mallocngModelPosixMemalignSpec,
      ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    generalize mallocngPosixMemalignOk x.2.1 x.2.2.1 = ok at ho ⊢
    rw [tight2_stepB_ite ok _ _ _ (tight2_stepReserve_aligned _ _ _)]
    exact ⟨MallocngTightOomCond.to_stepOomCond ho.1, ho.2⟩

theorem tight2_step_free_ite (p : BitVec 64) (align n : Nat)
    (b : mallocngTight2CostModel.σ) :
    (if (p == 0#64) = true then b else mallocngTight2CostModel.step (.free align n) b) =
      mallocngFreeBudget (p == 0#64) n b := by
  cases (p == 0#64) <;> rfl

theorem tight2_free_ok (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "free"
      (mallocngModelFreeSpec mallocngTight2CostModel mallocngTight2Iface γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := mallocngPlacedFreeTight_ok mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_map hsub (fun y R s0 hp => ?_)⟩
  refine ⟨(y.1, y.2.1, y.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1, y.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2), R,
    ?_, fun sf hq => ?_⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngFreeSpec, mallocngModelFreeSpec,
      ToBaseSpec.toSpec] at hp ⊢
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
      (sepConj_mono_left ?_)))) hp
    by_cases h0 : y.1 = 0#64
    · rw [ite_eq_left h0, ite_eq_left h0]
      all_goals exact Entails.refl _
    · rw [ite_eq_right h0, ite_eq_right h0]
      exact sepConj_mono_left (mallocngTightBlock_to_token _ _ _ _)
  · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngFreeSpec, mallocngModelFreeSpec,
      ToBaseSpec.toSpec] at hq ⊢
    rw [tight2_step_free_ite]
    exact hq

/-! ## `realloc` -/

theorem tight2_stepReserve_realloc (al old n : Nat) (b : mallocngTight2CostModel.σ) :
    mallocngTight2CostModel.stepReserve (.realloc al old n) b =
      MallocngTightStepBound (mallocngAlignedEffSize al n) (MallocngBudget.peakCount b) :=
  mallocngTight2Reserve_eq _ _

private theorem tight2_reallocRes_le {a al : Nat} (n : Nat) (ha : a ≤ max al 16) :
    mallocngReallocRes a n ≤ mallocngAlignedEffSize al n := by
  unfold mallocngReallocRes mallocngAlignedEffSize
  have := Nat.le_max_left al 16
  have := Nat.le_max_right al 16
  split
  · have : max al 16 = 16 := Nat.max_eq_right (by omega)
    omega
  · have : max al 16 = al := Nat.max_eq_left (by omega)
    omega

private theorem tight2_realloc_acc (ok : Bool) (a al n : Nat) (b : mallocngTight2CostModel.σ)
    {s0 sf : State} (ha : a ≤ max al 16) {ev : AllocEvent}
    (hev : mallocngTight2CostModel.stepReserve ev b =
      MallocngTightStepBound (mallocngAlignedEffSize al n) (MallocngBudget.peakCount b))
    (h : MallocngCallAccounting 16
      (MallocngTightStepBound (if ok then mallocngReallocRes a n else 0)
        (MallocngBudget.peakCount b)) s0 sf) :
    MallocngCallAccounting 16
      (if ok then mallocngTight2CostModel.stepReserve ev b
        else mallocngTight2CostModel.stepReserve (.alloc 0) b) s0 sf := by
  refine ⟨h.1, MallocngMappedDelta.mono (Nat.le_refl _) ?_ h.2⟩
  cases ok
  · exact Nat.le_of_eq (tight2_stepReserve_alloc 0 b).symm
  · exact Nat.le_trans (MallocngTightStepBound_mono (tight2_reallocRes_le n ha)) (Nat.le_of_eq hev.symm)

private theorem tight2_realloc_oom (ok : Bool) (al n : Nat) (b : mallocngTight2CostModel.σ)
    {svc : State → State} {s0 sf : State} {ev : AllocEvent}
    (hev : mallocngTight2CostModel.stepReserve ev b =
      MallocngTightStepBound (mallocngAlignedEffSize al n) (MallocngBudget.peakCount b))
    (h : MallocngTightOomCond svc (if ok then n else 0) (MallocngBudget.peakCount b) s0 sf)
    (hn : n ≤ mallocngAlignedEffSize al n) :
    MallocngStepOomCond svc
      (if ok then mallocngTight2CostModel.stepReserve ev b
        else mallocngTight2CostModel.stepReserve (.alloc 0) b) s0 sf := by
  have hle : MallocngTightStepBound (if ok then n else 0) (MallocngBudget.peakCount b) ≤
      (if ok then mallocngTight2CostModel.stepReserve ev b
        else mallocngTight2CostModel.stepReserve (.alloc 0) b) := by
    cases ok
    · exact Nat.le_of_eq (tight2_stepReserve_alloc 0 b).symm
    · exact Nat.le_trans (MallocngTightStepBound_mono hn) (Nat.le_of_eq hev.symm)
  obtain ⟨hfs, htr, hsig, ivs, hlen, hsum, hcov, hgap⟩ := MallocngTightOomCond.to_stepOomCond h
  refine ⟨hfs, htr, hsig, ivs, hlen, Nat.le_trans hsum hle, hcov, fun hs => ?_⟩
  obtain ⟨sz, h1, h2, h3, h4⟩ := hgap hs
  exact ⟨sz, h1, h2, Nat.le_trans h3 hle, h4⟩

private theorem tight2_initBlock_some (γ : GhostName) (p : BitVec 64) (sz al : Nat)
    (bs : List (BitVec 8)) :
    MallocngTightBlock γ p sz (max al 16) ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length) ⊢
      mallocngTight2Iface.BlockM γ p sz (max (max al 16) 16) ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length) := by
  rw [Nat.max_eq_left (Nat.le_max_right al 16)]
  exact Entails.refl _

/-- Placed `realloc` entry contract at `MallocngTightBlock` (`mallocngReallocTightBlockSpec`). -/
def MallocngReallocTightBlockStmt : Prop :=
  ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
    VerifiedLibraries.mallocngLib.Placeable mpl → MallocngSvcValid svc → ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocTightBlockSpec svc γ (mallocngAddrsOfPlacement mpl))

theorem tight2_realloc_ok (hRe : MallocngReallocTightBlockStmt) (mpl : Obj.MultiPlacement)
    (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngModelReallocSpec mallocngTight2CostModel mallocngTight2Iface svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := hRe mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_map_oom' hsub (fun y R s0 hp => ?_)⟩
  obtain ⟨p, n, sp, oldBlk, tp, brkStart, st, ivs0⟩ := y
  cases oldBlk with
  | none =>
    refine ⟨(p, n, sp, 16, none, tp, brkStart, st, ivs0), R, ?_, fun sf hq => ?_, fun sf ho => ?_⟩
    · exact hp
    · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngReallocTightBlockSpec,
        mallocngModelReallocSpec, ToBaseSpec.toSpec] at hq ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hq
      generalize decide (n.toNat ≤ MallocngMaxAllocSize) = ok
      cases ok
      · exact sepConj_mono (Entails.pure_mono fun ⟨h1, h2, h3⟩ =>
          ⟨h1, h2, tight2_realloc_acc false _ _ _ _ (Nat.le_max_left 16 16)
            (tight2_stepReserve_realloc _ _ _ _) h3⟩) (Entails.refl _)
      · exact sepConj_mono (Entails.pure_mono fun ⟨h1, h2, h3⟩ =>
          ⟨h1, h2, tight2_realloc_acc true _ _ _ _ (Nat.le_max_left 16 16)
            (tight2_stepReserve_realloc _ _ _ _) h3⟩) (Entails.refl _)
    · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngReallocTightBlockSpec,
        mallocngModelReallocSpec, ToBaseSpec.toSpec] at ho ⊢
      rw [satisfies_pure_sepConj] at ho ⊢
      exact ⟨tight2_realloc_oom _ _ _ _ (tight2_stepReserve_realloc _ _ _ _)
        ho.1 (by unfold mallocngAlignedEffSize; split <;> omega), ho.2⟩
  | some blk =>
    obtain ⟨sz, al, bs⟩ := blk
    refine ⟨(p, n, sp, max al 16, some (sz, bs), tp, brkStart, st, ivs0), R, ?_,
      fun sf hq => ?_, fun sf ho => ?_⟩
    · exact hp
    · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngReallocTightBlockSpec,
        mallocngModelReallocSpec, ToBaseSpec.toSpec] at hq ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hq
      generalize decide (n.toNat ≤ MallocngMaxAllocSize) = ok
      cases ok
      · exact sepConj_mono (Entails.pure_mono fun ⟨h1, h2, h3⟩ =>
          ⟨h1, h2, tight2_realloc_acc false _ _ _ _ (Nat.le_refl _)
            (tight2_stepReserve_realloc _ _ _ _) h3⟩)
          (Entails.refl _)
      · exact sepConj_mono (Entails.pure_mono fun ⟨h1, h2, h3⟩ =>
          ⟨h1, h2, tight2_realloc_acc true _ _ _ _ (Nat.le_refl _)
            (tight2_stepReserve_realloc _ _ _ _) h3⟩)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (by
              simp only [OptOwn, ↓reduceIte, Option.map_some, Option.getD_some]
              exact tight2_initBlock_some γ _ _ al _) (Entails.refl _)))
    · dsimp only [MultiPlacedLib.withCodeLoaded, mallocngReallocTightBlockSpec,
        mallocngModelReallocSpec, ToBaseSpec.toSpec] at ho ⊢
      rw [satisfies_pure_sepConj] at ho ⊢
      exact ⟨tight2_realloc_oom _ _ _ _ (tight2_stepReserve_realloc _ _ _ _)
        ho.1 (by unfold mallocngAlignedEffSize; split <;> omega), ho.2⟩

theorem mallocngTight2Sound_of_realloc (hK : LibcMallocImplPlacedTightKStmt)
    (hRealloc : ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl → MallocngSvcValid svc → ∀ γ : GhostName,
      mallocngMultiEntryOk mpl svc "realloc"
        (mallocngModelReallocSpec mallocngTight2CostModel mallocngTight2Iface svc γ
          (mallocngAddrsOfPlacement mpl))) :
    MallocngTight2SoundStmt :=
  mallocngTight2Sound_of_entries (mallocngTight2CoreFacts_ok) fun mpl svc hPl hSvc =>
    { malloc_ok := tight2_malloc_ok hK mpl svc hPl hSvc
      free_ok := tight2_free_ok mpl svc hPl hSvc
      calloc_ok := tight2_calloc_ok hK mpl svc hPl hSvc
      realloc_ok := hRealloc mpl svc hPl hSvc
      alignedAlloc_ok := tight2_alignedAlloc_ok mpl svc hPl hSvc
      posixMemalign_ok := tight2_posixMemalign_ok mpl svc hPl hSvc }

theorem mallocngTight2Sound_of_tightK (hK : LibcMallocImplPlacedTightKStmt)
    (hRe : MallocngReallocTightBlockStmt) : MallocngTight2SoundStmt :=
  mallocngTight2Sound_of_realloc hK (tight2_realloc_ok hRe)

/-- Soundness of the usage-indexed tight cost model `mallocngTight2CostModel` with block token
    `MallocngTightBlock` for `mallocngLib`. -/
theorem mallocngTight2Sound : MallocngTight2SoundStmt :=
  mallocngTight2Sound_of_tightK
    (placed_libcMallocImpl_tightK_uncond_ok placed_allocMeta_full_ok
      (placed_allocSlot_full_ok placed_allocMeta_full_ok))
    mallocngPlacedReallocTightBlock_ok

end VerifiedLibraries.Mallocng.Proofs.Cost

namespace VerifiedLibraries.Mallocng

/-- The trusted usage-indexed tight cost statement `MallocngTight2CostStmt` (`Spec/Cost.lean`). -/
theorem mallocngTight2Cost_ok : MallocngTight2CostStmt :=
  Proofs.Cost.mallocngTight2CostStmt_of_sound Proofs.Cost.mallocngTight2Sound

end VerifiedLibraries.Mallocng
