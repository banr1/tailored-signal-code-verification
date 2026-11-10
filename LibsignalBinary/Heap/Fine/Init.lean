/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.Inv

/-!
# `FineBlock` Ghost-Token and Startup Initialization Laws

Establishes structural and frame-preserving update laws for `FineBlock` together with runtime
splitting and startup initialization (`fineHeap_split_runtime`, `fineHeap_init_resources`,
`fineHeap_init`) for `MallocngCostModelIface` and `MallocngCostModelSound`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## `FineBlock` Ghost-Token Laws -/

@[scoped simp]
theorem noRO_fineBlock (γ : GhostName) (p : BitVec 64) (n effAlign : Nat) :
    SepProp.NoRO (FineBlock γ p n effAlign) :=
  SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
    (SepProp.NoRO.sepConj (noRO_mallocngBlockToken (fineBaseGam γ) p n)
      (SepProp.NoRO.ghostMapElem (fineAlignGam γ) p effAlign))

/-- Discharges `MallocngCostModelIface.block_noWrap`. -/
theorem fineBlock_noWrap (γ : GhostName) (p : BitVec 64) (n effAlign : Nat) :
    FineBlock γ p n effAlign ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ FineBlock γ p n effAlign := by
  unfold FineBlock
  refine Entails.pure_left fun hal => ?_
  have h1 :
      MallocngBlockToken (fineBaseGam γ) p n ∗ ghostMapElem (fineAlignGam γ) p effAlign ⊢
        (⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ MallocngBlockToken (fineBaseGam γ) p n) ∗
          ghostMapElem (fineAlignGam γ) p effAlign :=
    sepConj_mono_left (mallocngBlock_noWrap (fineBaseGam γ) p n)
  refine Entails.trans h1 ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hnw => ?_
  exact Entails.pure_right hnw (Entails.pure_right hal (Entails.refl _))

/-- Discharges `MallocngCostModelSound.block_nonnull`. -/
theorem fineBlock_nonnull (γ : GhostName) (p : BitVec 64) (n effAlign : Nat) :
    FineBlock γ p n effAlign ⊢
      ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗
        FineBlock γ p n effAlign := by
  unfold FineBlock
  refine Entails.pure_left fun hal => ?_
  have h1 :
      MallocngBlockToken (fineBaseGam γ) p n ∗ ghostMapElem (fineAlignGam γ) p effAlign ⊢
        (⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗
          MallocngBlockToken (fineBaseGam γ) p n) ∗
          ghostMapElem (fineAlignGam γ) p effAlign :=
    sepConj_mono_left (mallocngBlock_nonnull (fineBaseGam γ) p n)
  refine Entails.trans h1 ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hwf => ?_
  exact Entails.pure_right hwf (Entails.pure_right hal (Entails.refl _))

/-- Discharges `MallocngCostModelSound.block_exclusive`. -/
theorem fineBlock_exclusive (γ : GhostName)
    (p₁ : BitVec 64) (n₁ al₁ : Nat) (p₂ : BitVec 64) (n₂ al₂ : Nat) :
    FineBlock γ p₁ n₁ al₁ ∗ FineBlock γ p₂ n₂ al₂ ⊢
      ⌜p₁ ≠ p₂⌝ ∗ FineBlock γ p₁ n₁ al₁ ∗ FineBlock γ p₂ n₂ al₂ := by
  by_cases hne : p₁ = p₂
  · subst hne
    unfold FineBlock
    rw [sepConj_assoc]
    refine Entails.pure_left fun _ => ?_
    have hPerm :
        (MallocngBlockToken (fineBaseGam γ) p₁ n₁ ∗ ghostMapElem (fineAlignGam γ) p₁ al₁) ∗
          ⌜16 ≤ al₂⌝ ∗ MallocngBlockToken (fineBaseGam γ) p₁ n₂ ∗
            ghostMapElem (fineAlignGam γ) p₁ al₂ =
        ⌜16 ≤ al₂⌝ ∗
          ((MallocngBlockToken (fineBaseGam γ) p₁ n₁ ∗
              MallocngBlockToken (fineBaseGam γ) p₁ n₂) ∗
            (ghostMapElem (fineAlignGam γ) p₁ al₁ ∗
              ghostMapElem (fineAlignGam γ) p₁ al₂)) := by ac_rfl
    rw [hPerm]
    refine Entails.pure_left fun _ => ?_
    refine Entails.trans (sepConj_mono_left (mallocngBlock_exclusive (fineBaseGam γ) p₁ n₁ p₁ n₂)) ?_
    rw [sepConj_assoc]
    exact Entails.pure_left fun hFalse => False.elim (hFalse rfl)
  · exact Entails.pure_right hne (Entails.refl _)

/-- Authoritative lookup of both `(p ↦ n)` and `(p ↦ effAlign)` from `FineBlock γ p n effAlign`. -/
theorem fineBlock_lookup (γ : GhostName)
    (L : MallocngLiveMap) (alignMap : BitVec 64 → Option Nat) (p : BitVec 64) (n effAlign : Nat) :
    ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
      FineBlock γ p n effAlign ⊢
      ⌜16 ≤ effAlign ∧ MallocngBlockWf p n ∧ L p = some n ∧ alignMap p = some effAlign⌝ ∗
        ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
        FineBlock γ p n effAlign := by
  unfold FineBlock
  have hPerm1 :
      ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
        ⌜16 ≤ effAlign⌝ ∗ MallocngBlockToken (fineBaseGam γ) p n ∗
          ghostMapElem (fineAlignGam γ) p effAlign =
      ⌜16 ≤ effAlign⌝ ∗
        (MallocngLiveAuth (fineBaseGam γ) L ∗ MallocngBlockToken (fineBaseGam γ) p n) ∗
        (ghostMapAuth (fineAlignGam γ) alignMap ∗ ghostMapElem (fineAlignGam γ) p effAlign) := by
    ac_rfl
  rw [hPerm1]
  refine Entails.pure_left fun hal => ?_
  have hLk1 := mallocngBlock_lookup (fineBaseGam γ) L p n
  have hLk2 := ghostMap_lookup (fineAlignGam γ) alignMap p effAlign
  refine Entails.trans (sepConj_mono hLk1 hLk2) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hwf, hLp⟩ => ?_
  have hPerm2 :
      (MallocngLiveAuth (fineBaseGam γ) L ∗ MallocngBlockToken (fineBaseGam γ) p n) ∗
        ⌜alignMap p = some effAlign⌝ ∗
          ghostMapAuth (fineAlignGam γ) alignMap ∗ ghostMapElem (fineAlignGam γ) p effAlign =
      ⌜alignMap p = some effAlign⌝ ∗
        (ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
          (MallocngBlockToken (fineBaseGam γ) p n ∗
            ghostMapElem (fineAlignGam γ) p effAlign)) := by ac_rfl
  rw [hPerm2]
  refine Entails.pure_left fun hAp => ?_
  refine Entails.pure_right ⟨hal, hwf, hLp, hAp⟩ ?_
  have hPerm3 :
      ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
        (MallocngBlockToken (fineBaseGam γ) p n ∗ ghostMapElem (fineAlignGam γ) p effAlign) =
      (ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L) ∗
        (MallocngBlockToken (fineBaseGam γ) p n ∗ ghostMapElem (fineAlignGam γ) p effAlign) := by
    ac_rfl
  rw [hPerm3]
  refine Entails.trans
    (sepConj_mono_right (Entails.pure_right hal (Entails.refl _))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Frame-preserving allocation of `FineBlock γ p n effAlign` when `L p = none` and `alignMap p = none`. -/
theorem fineBlock_alloc_bupd (γ : GhostName)
    (L : MallocngLiveMap) (alignMap : BitVec 64 → Option Nat) (p : BitVec 64) (n effAlign : Nat)
    (hal : 16 ≤ effAlign) (hwf : MallocngBlockWf p n)
    (hLnone : L p = none) (hAnone : alignMap p = none) :
    ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ⊢
      |==> (ghostMapAuth (fineAlignGam γ) (fun k => if k = p then some effAlign else alignMap k) ∗
        MallocngLiveAuth (fineBaseGam γ) (L.insert p n (effAlign - 16)) ∗
        FineBlock γ p n effAlign) := by
  have h1 := ghostMap_alloc (fineAlignGam γ) alignMap p effAlign hAnone
  have h2 := mallocngBlock_alloc_bupd (fineBaseGam γ) L p n (effAlign - 16) hwf hLnone
  refine Entails.trans (bupd_sep h1 h2) (bupd_mono ?_)
  unfold FineBlock
  rw [pure_sepConj_of_true hal]
  exact Entails.of_eq (by ac_rfl)

/-- Frame-preserving deletion of `FineBlock γ p n effAlign`. -/
theorem fineBlock_delete_bupd (γ : GhostName)
    (L : MallocngLiveMap) (alignMap : BitVec 64 → Option Nat) (p : BitVec 64) (n effAlign : Nat) :
    ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
      FineBlock γ p n effAlign ⊢
      |==> (ghostMapAuth (fineAlignGam γ) (fun k => if k = p then none else alignMap k) ∗
        MallocngLiveAuth (fineBaseGam γ) (L.erase p)) := by
  unfold FineBlock
  have hPerm :
      ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
        ⌜16 ≤ effAlign⌝ ∗ MallocngBlockToken (fineBaseGam γ) p n ∗
          ghostMapElem (fineAlignGam γ) p effAlign =
      ⌜16 ≤ effAlign⌝ ∗
        (ghostMapAuth (fineAlignGam γ) alignMap ∗ ghostMapElem (fineAlignGam γ) p effAlign) ∗
        (MallocngLiveAuth (fineBaseGam γ) L ∗ MallocngBlockToken (fineBaseGam γ) p n) := by
    ac_rfl
  rw [hPerm]
  refine Entails.pure_left fun _ => ?_
  exact bupd_sep
    (ghostMap_delete (fineAlignGam γ) alignMap p effAlign)
    (mallocngBlock_delete_bupd (fineBaseGam γ) L p n)

/-- Frame-preserving update of `(p ↦ oldN, oldAl)` to `(p ↦ newN, newAl)` (for in-place `realloc`). -/
theorem fineBlock_update_bupd (γ : GhostName)
    (L : MallocngLiveMap) (alignMap : BitVec 64 → Option Nat) (p : BitVec 64)
    (oldN oldAl newN newAl : Nat)
    (hal : 16 ≤ newAl) (hwf : MallocngBlockWf p newN) :
    ghostMapAuth (fineAlignGam γ) alignMap ∗ MallocngLiveAuth (fineBaseGam γ) L ∗
      FineBlock γ p oldN oldAl ⊢
      |==> (ghostMapAuth (fineAlignGam γ) (fun k => if k = p then some newAl else alignMap k) ∗
        MallocngLiveAuth (fineBaseGam γ) ((L.erase p).insert p newN (newAl - 16)) ∗
        FineBlock γ p newN newAl) := by
  let alignDel : BitVec 64 → Option Nat := fun k => if k = p then none else alignMap k
  let liveDel : MallocngLiveMap := L.erase p
  have hDel := fineBlock_delete_bupd γ L alignMap p oldN oldAl
  have hLnone : liveDel p = none := by
    show (L.erase p).req p = none
    simp
  have hIns := fineBlock_alloc_bupd γ liveDel alignDel p newN newAl hal hwf
    hLnone (by simp [alignDel])
  have hEqA : (fun k => if k = p then some newAl else alignDel k) =
      (fun k => if k = p then some newAl else alignMap k) := by
    funext k; by_cases hk : k = p <;> simp [alignDel, hk]
  rw [hEqA] at hIns
  exact Entails.trans (Entails.trans hDel (bupd_mono hIns)) (bupd_trans _)

/-! ## Runtime Split and Startup Initialization -/

/-- Discharges `MallocngCostModelSound.heap_split_runtime`. -/
theorem fineHeap_split_runtime
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) :
    FineHeapImpl γ A tp brkStart brk b ivs =
      (FineCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp) :=
  FineHeapImpl_eq γ A tp brkStart brk b ivs

private theorem ghostTriple_init_untracked :
    emp ⊢ |==> (∃∗ γ : GhostName,
      ghostMapAuth (fineAlignGam γ) (fun _ => none) ∗
      MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty ∗
      ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none)) := by
  have h1 : emp ⊢ |==> (∃∗ gA : GhostName, ghostMapAuth gA (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2 : emp ⊢ |==> (∃∗ gL : GhostName, ghostMapAuth gL (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h3 : emp ⊢ |==> (∃∗ gX : GhostName, ghostMapAuth gX (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h23 : emp ⊢ |==> ((∃∗ gL : GhostName, ghostMapAuth gL (fun _ => none)) ∗
      (∃∗ gX : GhostName, ghostMapAuth gX (fun _ => none))) := by
    conv => lhs; rw [← emp_sepConj emp]
    exact bupd_sep h2 h3
  have h123 : emp ⊢ |==> ((∃∗ gA : GhostName, ghostMapAuth gA (fun _ => none)) ∗
      ((∃∗ gL : GhostName, ghostMapAuth gL (fun _ => none)) ∗
        (∃∗ gX : GhostName, ghostMapAuth gX (fun _ => none)))) := by
    conv => lhs; rw [← emp_sepConj emp]
    exact bupd_sep h1 h23
  refine Entails.trans h123 (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun gA => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun gL => ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun gX => ?_
  let γ := natPair (natPair gL gX) gA
  have hAlign : fineAlignGam γ = gA := by simp [γ, fineAlignGam, natUnpair_natPair]
  have hLive : liveGhost (fineBaseGam γ) = gL := by
    simp [γ, fineBaseGam, liveGhost, natUnpair_natPair]
  have hAuxv : auxvGhost (fineBaseGam γ) = gX := by
    simp [γ, fineBaseGam, auxvGhost, natUnpair_natPair]
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun g =>
        ghostMapAuth (fineAlignGam g) (fun _ => none) ∗
        MallocngLiveAuth (fineBaseGam g) MallocngLiveMap.empty ∗
        ghostMapAuth (auxvGhost (fineBaseGam g)) (fun _ => none))
      γ)
  have hEncEmpty : MallocngLiveMap.empty.enc = (fun _ => none) := rfl
  unfold MallocngLiveAuth
  rw [hAlign, hLive, hAuxv, hEncEmpty]
  exact Entails.of_eq (by ac_rfl)

/-- Packs `MallocngStartupResources` + fresh triple ghost state into `FineHeapImpl` at
    `FineBudget.init` and `ivs = []`. -/
theorem fineStartup_packA (γ : GhostName) (A : MallocngAddrs) (tp brkStart auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    (ghostMapAuth (fineAlignGam γ) (fun _ => none) ∗
     MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty ∗
     ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none)) ∗
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr ⊢
      FineHeapImpl γ A tp brkStart brkStart FineBudget.init [] := by
  rw [FineHeapImpl_eq, FineCoreImpl_eq]
  let st0 := emptyMallocngSt auxvPtr
  have hWf : MallocngWF A.base brkStart brkStart 0 0 st0 :=
    emptyMallocngSt_wf auxvPtr hBrkWf
  have hFine0 : MallocngFineInv 0 FineBudget.init [] (fun _ => none) st0 :=
    emptyMallocngStOpt_fineInv auxvPtr none
  have hStep1 :
      (ghostMapAuth (fineAlignGam γ) (fun _ => none) ∗
       MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty ∗
       ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none)) ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
      MallocngAuxvAt st0.auxvPtr ⊢
      (MallocngRoTablesA A ∗
        FineCoreStInflightA 0 γ A brkStart brkStart FineBudget.init [] (fun _ => none) 0 0 st0) ∗
        MallocngRuntime A tp := by
    unfold FineCoreStInflightA MallocngCoreStInflightA MallocngAuxvState ByteMap ProtNoneByteMap
      MappedSet SetSep
    rw [pure_sepConj_of_true hFine0, pure_sepConj_of_true hWf]
    have hDom : st0.masterDom = [] := rfl
    have hMap : st0.liveMap = MallocngLiveMap.empty := rfl
    have hSnap : st0.auxvSnap = none := rfl
    rw [hDom, hMap, hSnap]
    dsimp only [MallocngAuxvAuthMap]
    simp only [BigSep_nil, sepConj_emp]
    generalize (ghostMapAuth (fineAlignGam γ) (fun _ => none)) = P0
    generalize (MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty) = P1
    generalize (ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none)) = P1b
    generalize (MallocngRoTablesA A) = P2
    generalize (A.ctx ↦ₛ st0.ctx.toBytes) = P3
    generalize (A.lock ↦₃₂ 0#32) = P4
    generalize (A.replaced ↦₃₂ 0#32) = P5
    generalize (A.aaReplaced ↦₃₂ 0#32) = P6
    generalize (MallocngRuntime A tp) = P7
    generalize ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) = P8
    generalize (MallocngAuxvAt st0.auxvPtr) = P9
    exact Entails.of_eq (by ac_rfl)
  have hEqLhs :
      (ghostMapAuth (fineAlignGam γ) (fun _ => none) ∗
       MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty ∗
       ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none)) ∗
      MallocngRoTablesAt A ∗
      (A.ctx ↦ₛ List.replicate 928 0#8) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr =
      (ghostMapAuth (fineAlignGam γ) (fun _ => none) ∗
       MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty ∗
       ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none)) ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
      MallocngAuxvAt st0.auxvPtr := by
    simp only [MallocngRoTablesA, st0, emptyMallocngSt, emptyCtxFields_toBytes]
  rw [hEqLhs]
  refine Entails.trans hStep1 ?_
  refine sepConj_mono_left (sepConj_mono_right ?_)
  refine Entails.trans
    (Entails.sepExists_intro
      (P := fun peakCost =>
        FineCoreStInflightA 0 γ A brkStart brkStart FineBudget.init [] (fun _ => none) 0 peakCost st0)
      0) ?_
  refine Entails.trans
    (Entails.sepExists_intro
      (P := fun liveCost =>
        ∃∗ peakCost : Nat,
          FineCoreStInflightA 0 γ A brkStart brkStart FineBudget.init [] (fun _ => none) liveCost peakCost st0)
      0) ?_
  refine Entails.trans
    (Entails.sepExists_intro
      (P := fun alignMap =>
        ∃∗ liveCost : Nat,
        ∃∗ peakCost : Nat,
          FineCoreStInflightA 0 γ A brkStart brkStart FineBudget.init [] alignMap liveCost peakCost st0)
      (fun _ => none)) ?_
  exact Entails.sepExists_intro
    (P := fun st =>
      ∃∗ alignMap : BitVec 64 → Option Nat,
      ∃∗ liveCost : Nat,
      ∃∗ peakCost : Nat,
        FineCoreStInflightA 0 γ A brkStart brkStart FineBudget.init [] alignMap liveCost peakCost st)
    st0

/-- Discharges `MallocngCostModelSound.init_resources`. -/
theorem fineHeap_init_resources
    (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (_hTpGe : 0xa4 ≤ tp.toNat)
    (_hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngStartupResources A tp ⊢
      |==> (∃∗ γ : GhostName,
        FineHeapImpl γ A tp brkStart brkStart FineBudget.init []) := by
  unfold MallocngStartupResources
  refine Entails.sepExists_elim fun auxvPtr => ?_
  let body :=
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr
  have h1 : body ⊢
      (|==> (∃∗ γ : GhostName,
        ghostMapAuth (fineAlignGam γ) (fun _ => none) ∗
        MallocngLiveAuth (fineBaseGam γ) MallocngLiveMap.empty ∗
        ghostMapAuth (auxvGhost (fineBaseGam γ)) (fun _ => none))) ∗ body := by
    conv => lhs; rw [← emp_sepConj body]
    exact sepConj_mono_left ghostTriple_init_untracked
  refine Entails.trans (Entails.trans h1 (bupd_frame_r _ _)) (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun γ => ?_
  exact fineStartup_packA γ A tp brkStart auxvPtr hBrkWf

/-- Discharges `MallocngCostModelSound.init`. -/
theorem fineHeap_init
    (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory) :
    let A := mallocngAddrsOfPlacement mpl
    0xa4 ≤ tp.toNat →
    tp.toNat ≤ 2 ^ 48 →
    MallocngBrkStartWf brkStart →
    (m ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) →
    ∃ γ : GhostName,
      m ⊨ |==> (FineHeapImpl γ A tp brkStart brkStart FineBudget.init [] ∗ R) := by
  intro A hTpGe hTpLe hBrkWf hSat
  have hStartup :
      (VerifiedLibraries.mallocngLib.dataInit mpl ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R := by
    rw [mallocngLib_dataInit_eq mpl]
    change
      ((MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32)) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R
    have hAssoc :
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32)) ∗
         MallocngRuntime A tp ∗
         ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
         MallocngAuxvAt auxvPtr ∗ R) =
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32) ∗
          MallocngRuntime A tp ∗
          ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
          MallocngAuxvAt auxvPtr) ∗ R) := by ac_rfl
    rw [hAssoc]
    refine sepConj_mono_left ?_
    unfold MallocngStartupResources
    exact Entails.sepExists_intro
      (P := fun av =>
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngRuntime A tp ∗
        ((A.libc + 8#64) ↦₆₄ av) ∗
        MallocngAuxvAt av)
      auxvPtr
  have hSatStartup := Satisfies.of_entails hSat hStartup
  have hInit :=
    Satisfies.of_bupd_frame_left
      (fineHeap_init_resources A tp brkStart hTpGe hTpLe hBrkWf)
      hSatStartup
  rw [sepExists_sepConj_left, satisfies_sepExists] at hInit
  obtain ⟨γ, hγ⟩ := hInit
  refine ⟨γ, ?_⟩
  rw [satisfies_bupd]
  exact hγ

end LibsignalBinary.Heap.Fine
