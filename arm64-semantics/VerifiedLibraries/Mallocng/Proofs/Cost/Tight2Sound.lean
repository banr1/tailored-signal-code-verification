/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.Top
import VerifiedLibraries.Mallocng.Proofs.Cost.Tight2
import VerifiedLibraries.Mallocng.Proofs.Cost.IvsTight2

/-!
# Soundness of the Usage-Indexed Tight Cost Model

Instantiates `MallocngCostModelIface` for `mallocngTight2CostModel` with alignment-indexed
`MallocngTightBlock` tokens, proves the non-entry `MallocngTight2CoreFacts` fields, and reduces
`MallocngTight2CostStmt` to the six placed entry contracts.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

private theorem tightBlock_wf (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    MallocngTightBlock γ p n a ⊢ ⌜MallocngBlockWf p n⌝ ∗ MallocngTightBlock γ p n a := by
  unfold MallocngTightBlock
  refine Entails.sepExists_elim fun k => Entails.pure_left fun hk => ?_
  unfold MallocngBlockTokenK
  refine Entails.pure_left fun hwf => Entails.pure_right hwf ?_
  exact Entails.sepExists_right (Q := fun k => ⌜k ≤ a - 16⌝ ∗ ⌜MallocngBlockWf p n⌝ ∗
    ghostMapElem (liveGhost γ) p (natPair k n)) k
    (Entails.pure_right hk (Entails.pure_right hwf (Entails.refl _)))

private theorem tightBlock_noWrap (γ : GhostName) (p : BitVec 64) (n a : Nat) :
    MallocngTightBlock γ p n a ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ MallocngTightBlock γ p n a :=
  Entails.trans (tightBlock_wf γ p n a) (Entails.pure_left fun hwf =>
    Entails.pure_right (Nat.le_trans hwf.2.2.1 (by decide)) (Entails.refl _))

private theorem tightBlock_exclusive (γ : GhostName)
    (p₁ : BitVec 64) (n₁ a₁ : Nat) (p₂ : BitVec 64) (n₂ a₂ : Nat) :
    MallocngTightBlock γ p₁ n₁ a₁ ∗ MallocngTightBlock γ p₂ n₂ a₂ ⊢
      ⌜p₁ ≠ p₂⌝ ∗ MallocngTightBlock γ p₁ n₁ a₁ ∗ MallocngTightBlock γ p₂ n₂ a₂ := by
  by_cases hne : p₁ = p₂
  · subst hne
    refine Entails.trans (sepConj_mono (mallocngTightBlock_to_token γ p₁ n₁ a₁)
      (mallocngTightBlock_to_token γ p₁ n₂ a₂)) ?_
    refine Entails.trans (mallocngBlock_exclusive γ p₁ n₁ p₁ n₂) ?_
    exact Entails.pure_left fun h => absurd rfl h
  · exact Entails.pure_right hne (Entails.refl _)

/-- `MallocngCostModelIface` view of `mallocngIface` for `mallocngTight2CostModel`, with the
    alignment-indexed block token. -/
def mallocngTight2Iface : MallocngCostModelIface mallocngTight2CostModel where
  HeapM := mallocngIface.MallocngHeap
  CoreM := mallocngIface.MallocngCore
  BlockM γ p n a := MallocngTightBlock γ p n a
  block_noWrap γ p n a := tightBlock_noWrap γ p n a

/-- Target soundness statement for the trusted usage-indexed tight model. -/
def MallocngTight2SoundStmt : Prop :=
  MallocngCostModelSound mallocngTight2CostModel mallocngTight2Iface

/-- The non-entry fields of `MallocngCostModelSound` (everything except `entries_ok`). -/
structure MallocngTight2CoreFacts : Prop where
  init :
    ∀ (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory),
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
        m ⊨ |==> (mallocngTight2Iface.HeapM γ A tp brkStart brkStart
          mallocngTight2CostModel.init [] ∗ R)
  init_resources :
    ∀ (A : MallocngAddrs) (tp brkStart : BitVec 64),
      0xa4 ≤ tp.toNat →
      tp.toNat ≤ 2 ^ 48 →
      MallocngBrkStartWf brkStart →
      MallocngStartupResources A tp ⊢
        |==> (∃∗ γ : GhostName, mallocngTight2Iface.HeapM γ A tp brkStart brkStart
          mallocngTight2CostModel.init [])
  heap_footprint_bound :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (st : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap),
      SepProp.Holds (mallocngTight2Iface.HeapM γ A tp brkStart brk st ivs) h →
      ivs.length ≤ mallocngTight2CostModel.maxDynIvs st ∧
      (ivs.map Prod.snd).sum ≤ mallocngTight2CostModel.footprint st ∧
      ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48

theorem mallocngTight2_heap_footprint_bound
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (st : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (mallocngIface.MallocngHeap γ A tp brkStart brk st ivs) h) :
    ivs.length ≤ mallocngTight2CostModel.maxDynIvs st ∧
    (ivs.map Prod.snd).sum ≤ mallocngTight2CostModel.footprint st ∧
    ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48 := by
  obtain ⟨hLen, hSum⟩ :=
    mallocngHeap_ivs_tight2Footprint (Nat.le_refl 6) γ A tp brkStart brk st ivs h hHolds
  have hWrap := (mallocngHeap_footprint_bound γ A tp brkStart brk st ivs h hHolds).2.1.2.2
  exact ⟨hLen, (tight2_footprint_eq st).symm ▸ hSum, hWrap⟩

theorem mallocngTight2CoreFacts_ok : MallocngTight2CoreFacts where
  init := mallocngPlacedInit_ok
  init_resources := mallocngInitResources_ok
  heap_footprint_bound := mallocngTight2_heap_footprint_bound

theorem mallocngTight2Sound_of_entries (hCore : MallocngTight2CoreFacts)
    (hEntries : ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      MallocngModelPlacedEntryContracts mallocngTight2CostModel
        mallocngTight2Iface mpl svc) :
    MallocngTight2SoundStmt where
  init := hCore.init
  init_resources := hCore.init_resources
  heap_split_runtime := mallocngHeap_split_runtime
  block_nonnull γ p n a := tightBlock_wf γ p n a
  block_exclusive γ p₁ n₁ a₁ p₂ n₂ a₂ := tightBlock_exclusive γ p₁ n₁ a₁ p₂ n₂ a₂
  heap_footprint_bound := hCore.heap_footprint_bound
  entries_ok := hEntries

theorem mallocngTight2CostStmt_of_sound (h : MallocngTight2SoundStmt) : MallocngTight2CostStmt :=
  ⟨mallocngTight2Iface, h⟩

end VerifiedLibraries.Mallocng.Proofs.Cost
