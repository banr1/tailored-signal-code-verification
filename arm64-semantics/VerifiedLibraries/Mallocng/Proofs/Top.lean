/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Spec
import VerifiedLibraries.Mallocng.Proofs.Accounting
import VerifiedLibraries.Mallocng.Proofs.Internal
import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplProof
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
import VerifiedLibraries.Mallocng.Proofs.PlacedNontrivialFreeProof
import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeProof
import VerifiedLibraries.Mallocng.Proofs.PlacedFreeEntryProof
import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof

/-!
# Top-Level `mallocng` Correctness

Assembles `mallocngIfaceWf_ok : MallocngIfaceWfStmt` and `mallocngTop_ok : MallocngTopStmt` over the
concrete `mallocngIface` witness, together with tracked `auxv` startup/teardown lemmas and tight
resource-bound entry contracts.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng.Proofs

/-- Verified `MallocngIfaceFacts` bundle for the concrete `mallocngIface`. -/
theorem mallocngIfaceFacts_ok : MallocngIfaceFacts mallocngIface where
  init                 := mallocngPlacedInit_ok
  init_resources       := mallocngInitResources_ok
  heap_split_runtime   := mallocngHeap_split_runtime
  heap_roSplit         := mallocngHeap_roSplit
  block_noRO           := mallocngBlock_noRO
  block_nonnull        := mallocngBlock_nonnull
  block_exclusive      := mallocngBlock_exclusive
  heap_footprint_bound := mallocngHeap_footprint_bound

/-- Top-level verified `MallocngIfaceWfStmt` witness over the concrete `mallocngIface`. -/
theorem mallocngIfaceWf_ok : MallocngIfaceWfStmt :=
  ⟨mallocngIface, mallocngIfaceFacts_ok⟩

/-- Non-vacuity / reachability witness for internal `MallocngMetaCountInv` (`inv-audit`). -/
theorem mallocngMetaCountInv_reachable : MallocngMetaCountInv :=
  mallocngMetaCountInv_holds

private theorem placed_libcMallocImpl24_ok : LibcMallocImplPlaced24Stmt := by
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

private theorem alignedAllocPlaced_entry_ok (hMalloc : LibcMallocImplPlaced24Stmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngAlignedAllocSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := alignedAllocPlaced_entry_tight_ok hMalloc mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngAlignedAllocTightSpec,
      mallocngAlignedAllocSpec, ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, MallocngCallAccounting.tight_to_step hq.1.2⟩, hq.2⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngAlignedAllocTightSpec,
      mallocngAlignedAllocSpec, ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

private theorem posixMemalignPlaced_entry_ok (hMalloc : LibcMallocImplPlaced24Stmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngPosixMemalignSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := posixMemalignPlaced_entry_tight_ok hMalloc mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngPosixMemalignTightSpec,
      mallocngPosixMemalignSpec, ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.1, MallocngCallAccounting.tight_to_step hq.1.2.2⟩, hq.2⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngPosixMemalignTightSpec,
      mallocngPosixMemalignSpec, ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

private theorem callocPlaced_entry_ok (hDefMalloc : DefaultMallocPlacedTightStmt)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngCallocSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) := by
  obtain ⟨hexp, i, off, hlk, hsub⟩ := callocPlaced_entry_tight_ok hDefMalloc mpl svc hPl hSvc γ
  refine ⟨hexp, i, off, hlk, subroutine_ok_mono hsub (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    (hoom := fun _ _ _ _ ho => ?_)⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngCallocTightSpec, mallocngCallocSpec,
      ToBaseSpec.toSpec] at hq ⊢
    simp only [sepConj_assoc] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1.1, MallocngCallAccounting.tight_to_step hq.1.2⟩, hq.2⟩
  · dsimp only [Obj.MultiPlacedLib.withCodeLoaded, mallocngCallocTightSpec, mallocngCallocSpec,
      ToBaseSpec.toSpec] at ho ⊢
    rw [satisfies_pure_sepConj] at ho ⊢
    exact ⟨ho.1.to_oomCond (Nat.le_refl _), ho.2⟩

/-- Hookless multi-block placed contracts (`MallocngPlacedEntryContracts`) for all 6 C exports of
    `VerifiedLibraries.mallocngLib` (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`,
    `posix_memalign`). -/
theorem mallocngPlacedEntries_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) :
    MallocngPlacedEntryContracts mallocngIface mpl svc :=
  let hSlot : AllocSlotPlacedFullStmt := placed_allocSlot_full_ok placed_allocMeta_full_ok
  let hImpl : LibcMallocImplPlacedTightStmt := placed_libcMallocImpl_tight_uncond_ok placed_allocMeta_full_ok hSlot
  let hImplK : LibcMallocImplPlacedTightKStmt :=
    placed_libcMallocImpl_tightK_uncond_ok placed_allocMeta_full_ok hSlot
  let hDefMalloc : DefaultMallocPlacedTightStmt := placed_defaultMalloc_tight_of_impl hImpl
  let hFree : LibcFreePlacedStmt := placed_libcFree_ok placed_nontrivialFree_ok
  { malloc_ok :=
      mallocPlaced_entry_uncond_ok placed_allocMeta_full_ok hSlot mpl svc hPl hSvc
    free_ok :=
      freePlaced_entry_ok placed_nontrivialFree_ok mpl svc hPl hSvc
    calloc_ok :=
      callocPlaced_entry_ok hDefMalloc mpl svc hPl hSvc
    realloc_ok :=
      reallocPlaced_entry_ok hImplK hFree mpl svc hPl hSvc
    alignedAlloc_ok :=
      alignedAllocPlaced_entry_ok placed_libcMallocImpl24_ok mpl svc hPl hSvc
    posixMemalign_ok :=
      posixMemalignPlaced_entry_ok placed_libcMallocImpl24_ok mpl svc hPl hSvc }

/-- Complete verified `MallocngTopFacts` bundle for the concrete `mallocngIface`. -/
theorem mallocngTopFacts_ok : MallocngTopFacts mallocngIface :=
  { mallocngIfaceFacts_ok with
    entries_ok := mallocngPlacedEntries_ok }

/-- Top-level verified `MallocngTopStmt` witness over the concrete `mallocngIface`. -/
theorem mallocngTop_ok : MallocngTopStmt :=
  ⟨mallocngIface, mallocngTopFacts_ok⟩

end VerifiedLibraries.Mallocng

namespace VerifiedLibraries.Mallocng

open Arm64 ProofLib ProofLib.SepLogic

/-- Concrete `MallocngIface` witness re-exported at `VerifiedLibraries.Mallocng.mallocngIface`. -/
abbrev mallocngIface : MallocngIface :=
  Proofs.mallocngIface

/-- Concrete startup `auxv` + `AT_RANDOM` secret snapshot
    `(preEntries, randPtr, sufEntries, nullVal, sec)`. -/
abbrev MallocngAuxvSnap : Type :=
  Proofs.MallocngAuxvSnap

/-- Exclusive caller ticket witnessing that `mallocngIface.MallocngCore γ` owns the exact
    concrete startup `auxv` table `(auxvPtr, snap)`. -/
abbrev MallocngAuxvTicket
    (γ : GhostName) (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) : SepProp :=
  Proofs.MallocngAuxvTicket γ auxvPtr snap

/-- Tracked startup initialization for `mallocngIface.MallocngCore`: preserves the concrete
    startup `auxv` table `(auxvPtr, preEntries, randPtr, sufEntries, nullVal, sec)` via an
    agreement ticket `MallocngAuxvTicket γ auxvPtr (...)` recoverable at teardown. -/
theorem mallocngInitCore_tracked
    (A : MallocngAddrs) (brkStart auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hPreTags : ∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hSufTags : ∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hLen64 : preEntries.length + sufEntries.length ≤ 64)
    (hAuxvFit : auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48)
    (hRandFit : randPtr.toNat + 16 ≤ 2 ^ 48) :
    MallocngRoTablesAt A ∗ (A.ctx ↦ₛ List.replicate 928 0#8) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    (auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v])) ∗ ((randPtr + 8#64) ↦₆₄ sec) ⊢
      |==> (∃∗ γ : GhostName,
        mallocngIface.MallocngCore γ A brkStart brkStart mallocngZeroBudget [] ∗
        MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec)) :=
  Proofs.mallocngInitCore_tracked A brkStart auxvPtr preEntries randPtr sufEntries nullVal sec
    hBrkWf hPreTags hSufTags hLen64 hAuxvFit hRandFit

/-- Teardown of `mallocngIface.MallocngCore` paired with `MallocngAuxvTicket`: recovers the exact
    startup `__libc.auxv` pointer, `auxv` table words, and `AT_RANDOM` secret word. -/
theorem mallocngCore_teardown_auxv
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64) :
    mallocngIface.MallocngCore γ A brkStart brk b ivs ∗
    MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec) ⊢
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      (auxvPtr ↦₆₄*
        ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
          fun (t, v) => [t, v])) ∗
      ((randPtr + 8#64) ↦₆₄ sec) ∗
      ∃∗ R_dead : SepProp, R_dead :=
  Proofs.mallocngCore_teardown_auxv γ A brkStart brk b ivs auxvPtr preEntries randPtr sufEntries
    nullVal sec

abbrev MallocngTightStepBound (reqBytes peakCount : Nat) : Nat :=
  Proofs.MallocngTightStepBound reqBytes peakCount

abbrev MallocngTightTotalBound (reqBytes peakCount : Nat) : Nat :=
  Proofs.MallocngTightTotalBound reqBytes peakCount

abbrev MallocngTightOomCond
    (svc : State → State) (reqBytes peakCount : Nat) (s0 sf : State) : Prop :=
  Proofs.MallocngTightOomCond svc reqBytes peakCount s0 sf

abbrev mallocngMallocTightSpec := Proofs.mallocngMallocTightSpec

abbrev mallocngReallocTightSpec := Proofs.mallocngReallocTightSpec

abbrev mallocngReallocTightBlockSpec := Proofs.mallocngReallocTightBlockSpec

/-- Tight dynamic heap VA interval sum bound on `mallocngIface.MallocngHeap`. -/
theorem mallocngHeap_ivs_tight_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs ⊢
      ⌜(b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
        ivs.length ≤ 48 + 2 * b.peakCount ∧
        (ivs.map Prod.snd).sum ≤
          14917632 + 24576 * ((88 + 8 * b.peakCount) / 101) + 1048576 * b.liveCount + b.liveCost⌝ ∗
      mallocngIface.MallocngHeap γ A tp brkStart brk b ivs :=
  Entails.extract_heap_fact (Proofs.mallocngHeap_ivs_tight_bound γ A tp brkStart brk b ivs)

/-- Tight placed `malloc` entry contract for `mallocngIface`. -/
theorem mallocngPlacedMallocTight_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngMallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.mallocPlaced_entry_tight_uncond_ok
    Proofs.placed_allocMeta_full_ok
    (Proofs.placed_allocSlot_full_ok Proofs.placed_allocMeta_full_ok)
    mpl svc hPl hSvc γ

/-- Tight placed `realloc` entry contract for `mallocngIface`. -/
theorem mallocngPlacedReallocTight_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.reallocPlaced_entry_tight_ok
    (Proofs.placed_libcMallocImpl_tightK_uncond_ok
      Proofs.placed_allocMeta_full_ok
      (Proofs.placed_allocSlot_full_ok Proofs.placed_allocMeta_full_ok))
    (Proofs.placed_libcFree_ok Proofs.placed_nontrivialFree_ok)
    mpl svc hPl hSvc γ

/-- Alignment-indexed tight placed `realloc` entry contract for `mallocngIface`: the old and new
    blocks carry ghost overhead `≤ a - 16` (`MallocngTightBlock`) and success charges
    `MallocngTightStepBound (mallocngReallocRes a newSize)`. -/
theorem mallocngPlacedReallocTightBlock_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocTightBlockSpec svc γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.reallocPlaced_entry_tightBlock_ok
    (Proofs.placed_libcMallocImpl_tightK_uncond_ok
      Proofs.placed_allocMeta_full_ok
      (Proofs.placed_allocSlot_full_ok Proofs.placed_allocMeta_full_ok))
    (Proofs.placed_libcFree_ok Proofs.placed_nontrivialFree_ok)
    mpl svc hPl hSvc γ

abbrev mallocngCallocTightSpec := Proofs.mallocngCallocTightSpec

/-- Tight placed `calloc` entry contract for `mallocngIface`: success delta
    `≤ MallocngTightStepBound total` and `MallocngTightOomCond` at `total = nmemb * size`. -/
theorem mallocngPlacedCallocTight_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngCallocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.callocPlaced_entry_tight_ok
    (Proofs.placed_defaultMalloc_tight_of_impl
      (Proofs.placed_libcMallocImpl_tight_uncond_ok
        Proofs.placed_allocMeta_full_ok
        (Proofs.placed_allocSlot_full_ok Proofs.placed_allocMeta_full_ok)))
    mpl svc hPl hSvc γ

/-- Placed `free` entry contract for `mallocngIface`: the trusted `mallocngFreeSpec` already
    carries zero reserve (`MallocngCallAccounting 0 0`, no `.OutOfMemory`). -/
theorem mallocngPlacedFreeTight_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "free"
      (mallocngFreeSpec mallocngIface γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.freePlaced_entry_ok Proofs.placed_nontrivialFree_ok mpl svc hPl hSvc γ

abbrev mallocngAlignedAllocTightSpec := Proofs.mallocngAlignedAllocTightSpec

abbrev mallocngPosixMemalignTightSpec := Proofs.mallocngPosixMemalignTightSpec

/-- Tight placed `aligned_alloc` entry contract for `mallocngIface`: success delta
    `≤ MallocngTightStepBound eff` and `MallocngTightOomCond` at `eff = mallocngAlignedEffSize`. -/
theorem mallocngPlacedAlignedAllocTight_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngAlignedAllocTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.alignedAllocPlaced_entry_tight_ok placed_libcMallocImpl24_ok mpl svc hPl hSvc γ

/-- Tight placed `posix_memalign` entry contract for `mallocngIface`: success delta
    `≤ MallocngTightStepBound eff` and `MallocngTightOomCond` at `eff = mallocngAlignedEffSize`. -/
theorem mallocngPlacedPosixMemalignTight_ok
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hSvc : MallocngSvcValid svc) (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngPosixMemalignTightSpec mallocngIface svc γ (mallocngAddrsOfPlacement mpl)) :=
  Proofs.posixMemalignPlaced_entry_tight_ok placed_libcMallocImpl24_ok mpl svc hPl hSvc γ

end VerifiedLibraries.Mallocng
