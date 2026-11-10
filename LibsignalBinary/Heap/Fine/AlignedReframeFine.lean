/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.MallocEntryFine
public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocStage3
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Fine-Grained `aligned_alloc` Exit Reframe

Combines the `aligned_alloc` (`blk12`, `+0x1b4 → ret`) exit reframe (`delta = 0` and `delta > 0`)
with a single-step `MallocngFineInv` commit (`st0 → st2`) via `ghostMap_alloc` and
`commit_claimed_slab_slot_aligned` / `commit_mmap63_group_aligned`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.AlignedH1

/-! ## Effective Request and `fineStepReserve` Identity -/

private theorem eff_eq_add_pad (align len : Nat) :
    mallocngAlignedEffSize align len = len + (max align 16 - 16) := by
  unfold mallocngAlignedEffSize; split <;> omega

private theorem effCost_le_aligned (a l c : Nat) :
    max (mallocngAlignedEffSize a l) c ≤ max l c + (max a 16 - 16) := by
  unfold mallocngAlignedEffSize; split <;> omega

namespace AlignedReframeHelpers

theorem fineStepReserve_aligned_eq (align len : Nat) (b : FineBudget) :
    fineStepReserve (.alloc (mallocngAlignedEffSize align len)) b = fineStepReserve (.aligned align len) b := by
  have hArg : mallocngAlignedEffSize align len + (max 16 16 - 16) + 8192 = len + (max align 16 - 16) + 8192 := by
    rw [eff_eq_add_pad]; omega
  dsimp only [fineStepReserve]; unfold FineStepBound; rw [hArg]
end AlignedReframeHelpers

/-! ## Reframed Group and Spatial Update -/
private def mkAlignedReframedGroup (g : GroupDesc) (idx : Nat) (new_p : BitVec 64) (align len : Nat) : GroupDesc :=
  { g with slots := g.slots.set idx (.liveUser new_p len (max len MallocngMinBlockCost + (max align 16 - 16))), freshZero := false }

private def mkAlignedReframedSt (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (p new_p : BitVec 64) (align len : Nat) (bv : BitVec 64 → BitVec 8) : MallocngSt :=
  let g2 := mkAlignedReframedGroup g idx new_p align len
  { st with groups := replaceGroupByMeta st.groups g.metaPtr g2, byteVal := bv,
            liveMap := (st.liveMap.erase p).insert new_p len (max align 16 - 16) }

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_spatial_fine {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} (γ : GhostName)
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p : BitVec 64} {eff effCost align len : Nat} (hSlot : g.slots[idx]'hIdx = .liveUser p eff effCost)
    (hpLeNew : p.toNat ≤ new_p.toNat) (hNewFitEff : new_p.toNat + len ≤ p.toNat + eff) (hBlkNew : MallocngBlockWf new_p len)
    {bv : BitVec 64 → BitVec 8}
    (hOutBand : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a) :
    let st2 := mkAlignedReframedSt st g idx p new_p align len bv
    (if new_p = p then none else st.liveMap new_p) = none ∧
    (∀ a : BitVec 64, OwnedRwByte st2 a ↔ (alignedSlotKeep st p eff a ∧ ¬ InRegion new_p len a)) ∧
    (∀ a : BitVec 64, OwnedRwByte st2 a → a ∈ st.masterDom) ∧
    ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st2.masterDom (OwnedMappedByte st2) = MappedSet st.masterDom (OwnedMappedByte st) ∧
    (∀ q r, st2.liveMap q = some r ↔
      ∃ h' ∈ st2.groups, ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat, h'.slots[j]'hj = .liveUser q r c) ∧
    (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p eff ∗
      ByteMap st.masterDom (alignedSlotKeep st p eff) bv ⊢
      |==> (MallocngLiveAuth γ st2.liveMap ∗ MallocngBlockToken γ new_p len ∗
        memRegion new_p len ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal)) := by
  dsimp only []; have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let g2 := mkAlignedReframedGroup g idx new_p align len; let st2 := mkAlignedReframedSt st g idx p new_p align len bv
  have hGWf := hwf.groups_wf g hg; have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have ⟨_, _, hStNat, hSub4Nat, hEnNat, _, hEn48, _, hEnMod12⟩ := group_slot_bounds hGWf hIdx
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSub3Nat := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hBlkP : MallocngBlockWf p eff := hSWf.2.2.2.2.1; have hPLo := hSWf.2.2.2.2.2.1; have hPHi := hSWf.2.2.2.2.2.2.1
  have hNoRes : st.reservedMetas = [] := by
    have h := hwf.inflight_wf; cases hR : st.reservedMetas with | nil => rfl | cons _ _ => simp [hR] at h
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g2)
  obtain ⟨rg, hrg, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rg.mem.toNat + rg.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
  have hSlotInRg : ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a → InRegion rg.mem (rg.maplen * 4096) a :=
    fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hPInSlot : ∀ a : BitVec 64, InRegion p eff a → InRegion (g.slotStart idx - 4#64) g.stride a :=
    fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hNewInP : ∀ a : BitVec 64, InRegion new_p len a → InRegion p eff a :=
    fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hOtherSlotDisj : ∀ {h0 : GroupDesc} (hh0 : h0 ∈ st.groups) {j : Nat} (hj0 : j < h0.slots.length)
      {u : BitVec 64} {r c : Nat}, (h0 ≠ g ∨ j ≠ idx) → h0.slots[j]'hj0 = .liveUser u r c →
      ∀ a : BitVec 64, InRegion (g.slotStart idx - 4#64) g.stride a → ¬ InRegion u r a := by
    intro h0 hh0 j hj0 u r c hDiff hSlot0 a haG hInU
    have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0; rw [hSlot0] at hSWf0
    have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, _⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
    have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hULo := hSWf0.2.2.2.2.2.1; have hUHi := hSWf0.2.2.2.2.2.2.1
    have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp hInU
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0])
      (hDiff.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)) haG ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  have hRootEq : ∀ a : BitVec 64,
      (∃ h ∈ st2.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
      (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) := fun a =>
    ⟨fun ⟨h, hh, hMp, hIn⟩ => (hRep.2.2.2.2.2.1 h hh).elim (fun hE => by subst hE; exact ⟨g, hg, hMp, hIn⟩) fun ⟨hh0, _⟩ => ⟨h, hh0, hMp, hIn⟩,
     fun ⟨h, hh, hMp, hIn⟩ => if hEq : h.metaPtr = g.metaPtr then
       by rw [mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq] at hMp hIn; exact ⟨g2, hRep.2.2.2.2.1, hMp, hIn⟩
     else ⟨h, hRep.2.2.2.2.2.2.1 h hh hEq, hMp, hIn⟩⟩
  have hOwnIff : ∀ a : BitVec 64, OwnedRwByte st2 a ↔ (alignedSlotKeep st p eff a ∧ ¬ InRegion new_p len a) := by
    intro a
    have hCM2 : ¬ CarvedMetaByte st2 a := by simp [CarvedMetaByte, st2, mkAlignedReframedSt, hNoRes]
    have hCM0 : ¬ CarvedMetaByte st a := by simp [CarvedMetaByte, hNoRes]
    constructor
    · rintro ⟨hSrc2, hNC2, _⟩
      have hSrc0 := hSrc2.imp id (hRootEq a).mp
      have hNotNew : ¬ InRegion new_p len a := fun hInN => by
        have hIdx2 : idx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hIdx]
        have hGet2 : g2.slots[idx]'hIdx2 =
            .liveUser new_p len (max len MallocngMinBlockCost + (max align 16 - 16)) := by
          simp [g2, mkAlignedReframedGroup]
        exact hNC2 ⟨g2, hRep.2.2.2.2.1, _, hGet2 ▸ List.getElem_mem hIdx2, hInN⟩
      refine ⟨?_, hNotNew⟩
      by_cases hInP : InRegion p eff a
      · exact Or.inr hInP
      · refine Or.inl ⟨hSrc0, fun ⟨h0, hh0, s, hs, hSub⟩ => ?_, hCM0⟩
        obtain ⟨j, hj0, hEqS⟩ := List.getElem_of_mem hs
        by_cases hSame : h0.metaPtr = g.metaPtr ∧ j = idx
        · rcases hSame with ⟨hM, rfl⟩
          have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hM; subst hE
          rw [← hEqS, hSlot] at hSub; exact hInP hSub
        · apply hNC2; by_cases hM : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hM; subst hE
            have hjNe : j ≠ idx := fun hJ => hSame ⟨rfl, hJ⟩
            have hj2 : j < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hj0]
            have hGet2 : g2.slots[j]'hj2 = s := by
              simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hEqS]
            exact ⟨g2, hRep.2.2.2.2.1, s, hGet2 ▸ List.getElem_mem hj2, hSub⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hM, s, hs, hSub⟩
    · rintro ⟨hKeep, hNotNew⟩
      have hSrc0 : (∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
          (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) :=
        hKeep.elim (fun hOwn => hOwn.1) (fun hInP => Or.inr ⟨rg, hrg, hRgMp, hSlotInRg a (hPInSlot a hInP)⟩)
      refine ⟨hSrc0.imp id (hRootEq a).mpr, fun ⟨h', hh', s, hs, hSub⟩ => ?_, hCM2⟩
      obtain ⟨j, hj', hEqS⟩ := List.getElem_of_mem hs
      rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
      · have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
        by_cases hjEq : j = idx
        · subst hjEq; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self] at hEqS
          rw [← hEqS] at hSub; exact hNotNew hSub
        · simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hEqS
          rcases hKeep with hOwn | hInP
          · exact hOwn.2.1 ⟨g, hg, s, hEqS ▸ List.getElem_mem hj0, hSub⟩
          · cases hS : s with
            | liveUser u r c => rw [hS] at hEqS hSub; exact hOtherSlotDisj hg hj0 (Or.inr hjEq) hEqS a (hPInSlot a hInP) hSub
            | _ => simp [hS] at hSub
      · rcases hKeep with hOwn | hInP
        · exact hOwn.2.1 ⟨h', hh0, s, hs, hSub⟩
        · cases hS : s with
          | liveUser u r c =>
            rw [hS] at hEqS hSub
            exact hOtherSlotDisj hh0 hj' (Or.inl fun hE => hNeM (congrArg GroupDesc.metaPtr hE)) hEqS a (hPInSlot a hInP) hSub
          | _ => simp [hS] at hSub
  have hDom2 : ∀ a : BitVec 64, OwnedRwByte st2 a → a ∈ st.masterDom := fun a hOwn2 =>
    ((hOwnIff a).mp hOwn2).1.elim (fun hOwn => hwf.masterDom_wf.2.1 a (Or.inl hOwn)) fun hInP =>
      hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rg, hrg, hRgMp, hSlotInRg a (hPInSlot a hInP)⟩)))))
  have hProtEq : ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun _ _ => Iff.rfl) fun a _ hProt => congrArg (a ↦₈ₙ ·) (hOutBand a fun hBand => ?_)
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hBand
    have hInRg := hSlotInRg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    have ⟨_, _, hCross⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
    rcases hProt with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
    · exact not_both_inRegion_of_disjointRegions
        (hCross (gp, 4096) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp)))
          (rg.mem, rg.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hRgMp⟩))) haGp hInRg
    · exact not_both_inRegion_of_disjointRegions
        (hCross (ap, 4096) (List.mem_append_right _ (List.mem_map_of_mem hap))
          (rg.mem, rg.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hRgMp⟩))) haAp hInRg
  have hMapSetEq : MappedSet st2.masterDom (OwnedMappedByte st2) = MappedSet st.masterDom (OwnedMappedByte st) := by
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl); unfold OwnedMappedByte
    change (_ ∨ _ ∨ _ ∨ (∃ h ∈ st2.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ↔ _
    rw [hRootEq a]; exact Iff.rfl
  have hNoOtherPtr : ∀ {h0 : GroupDesc} (hh0 : h0 ∈ st.groups) {j : Nat} (hj0 : j < h0.slots.length)
      {q : BitVec 64} {r c : Nat}, (h0 ≠ g ∨ j ≠ idx) → (q = p ∨ q = new_p) →
      h0.slots[j]'hj0 ≠ .liveUser q r c := by
    intro h0 hh0 j hj0 q r c hDiff hQ hSlot0
    have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0; rw [hSlot0] at hSWf0
    have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, hMod12_0⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
    have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hQMod0 : q.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hSWf0.2.2.2.2.1.2.1
    have hNewMod : new_p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hBlkNew.2.1
    have hPMod : p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hBlkP.2.1
    have := hSWf0.2.2.2.2.2.1; have := hSWf0.2.2.2.2.2.2.1
    have : q.toNat < (g.slotEnd idx).toNat := by rcases hQ with rfl | rfl <;> omega
    have : (g.slotStart idx).toNat ≤ q.toNat := by rcases hQ with rfl | rfl <;> omega
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0])
      (hDiff.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm))
      ((inRegion_iff_toNat (by omega) q).mpr ⟨by omega, by omega⟩)
      ((inRegion_iff_toNat (by omega) q).mpr ⟨by omega, by omega⟩)
  have hLiveMap2 : ∀ q r, st2.liveMap q = some r ↔
      ∃ h' ∈ st2.groups, ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat,
        h'.slots[j]'hj = .liveUser q r c := by
    intro q r
    change ((st.liveMap.erase p).insert new_p len (max align 16 - 16)).req q = some r ↔ _
    have hIdx2 : idx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hIdx]
    by_cases hqNew : q = new_p
    · cases hqNew; simp only [MallocngLiveMap.insert_req, ↓reduceIte, Option.some.injEq]
      refine ⟨fun hr => hr ▸ ⟨g2, hRep.2.2.2.2.1, idx, hIdx2, max len MallocngMinBlockCost + (max align 16 - 16),
        by simp [g2, mkAlignedReframedGroup]⟩, fun ⟨h', hh', j, hj', c, hSlot'⟩ => ?_⟩
      rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
      · by_cases hjEq : j = idx
        · subst hjEq; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self, SlotState.liveUser.injEq] at hSlot'
          exact hSlot'.2.1
        · have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
          simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
          exact False.elim (hNoOtherPtr hg hj0 (Or.inr hjEq) (Or.inr rfl) hSlot')
      · exact False.elim (hNoOtherPtr hh0 hj' (Or.inl fun hE => hNeM (congrArg GroupDesc.metaPtr hE)) (Or.inr rfl) hSlot')
    · by_cases hqp : q = p
      · cases hqp; simp only [MallocngLiveMap.insert_req, MallocngLiveMap.erase_req, hqNew, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨h', hh', j, hj', c, hSlot'⟩
        rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
        · by_cases hjEq : j = idx
          · subst hjEq; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self, SlotState.liveUser.injEq] at hSlot'
            exact hqNew hSlot'.1.symm
          · have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
            simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
            exact hNoOtherPtr hg hj0 (Or.inr hjEq) (Or.inl rfl) hSlot'
        · exact hNoOtherPtr hh0 hj' (Or.inl fun hE => hNeM (congrArg GroupDesc.metaPtr hE)) (Or.inl rfl) hSlot'
      · simp only [MallocngLiveMap.insert_req, MallocngLiveMap.erase_req, hqNew, hqp, ↓reduceIte]
        rw [show st.liveMap.req q = st.liveMap q from rfl, hwf.liveMap_wf q r]; constructor
        · rintro ⟨h0, hh0, j, hj0, c, hSlot0⟩
          by_cases hM : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hM; subst hE
            have hjNe : j ≠ idx := fun hJ => by subst hJ; rw [hSlot] at hSlot0; injection hSlot0 with hE; exact hqp hE.symm
            have hj2 : j < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hj0]
            exact ⟨g2, hRep.2.2.2.2.1, j, hj2, c, by simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hSlot0]⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hM, j, hj0, c, hSlot0⟩
        · rintro ⟨h', hh', j, hj', c, hSlot'⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · have hjNe : j ≠ idx := fun hJ => by
              subst hJ; simp only [g2, mkAlignedReframedGroup, List.getElem_set_self, SlotState.liveUser.injEq] at hSlot'
              exact hqNew hSlot'.1.symm
            have hj0 : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj'
            simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte] at hSlot'
            exact ⟨g, hg, j, hj0, c, hSlot'⟩
          · exact ⟨h', hh0, j, hj', c, hSlot'⟩
  let L1 : MallocngLiveMap := st.liveMap.erase p
  have hL1None : L1 new_p = none := by
    change (st.liveMap.erase p).req new_p = none
    rw [MallocngLiveMap.erase_req]
    by_cases hEq : new_p = p
    · simp [hEq]
    · simp only [hEq, ↓reduceIte]
      change st.liveMap new_p = none
      cases hLk : st.liveMap new_p with
      | none => rfl
      | some r =>
        obtain ⟨h0, hh0, j, hj0, c, hSlot0⟩ := (hwf.liveMap_wf new_p r).mp hLk
        have hDiff : h0 ≠ g ∨ j ≠ idx :=
          if hG : h0 = g then Or.inr fun hJ => by subst hG hJ; rw [hSlot] at hSlot0; injection hSlot0 with hE; exact hEq hE.symm
          else Or.inl hG
        exact False.elim (hNoOtherPtr hh0 hj0 hDiff (Or.inr rfl) hSlot0)
  have hL1If : (if new_p = p then none else st.liveMap new_p) = none := by
    have hE : L1 new_p = (if new_p = p then none else st.liveMap new_p) := by
      change (st.liveMap.erase p).req new_p = _
      rw [MallocngLiveMap.erase_req]
    rwa [← hE]
  refine ⟨hL1If, hOwnIff, hDom2, hProtEq, hMapSetEq, hLiveMap2, ?_⟩
  have hNewDom : ∀ a : BitVec 64, InRegion new_p len a → a ∈ st.masterDom := fun a ha =>
    hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rg, hrg, hRgMp, hSlotInRg a (hPInSlot a (hNewInP a ha))⟩)))))
  have hRemEq : ByteMap st.masterDom (fun a => alignedSlotKeep st p eff a ∧ ¬ InRegion new_p len a) bv =
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal :=
    SetSep_congr (fun a _ => (hOwnIff a).symm) (fun _ _ _ => rfl)
  have hExtEq : ByteMap st.masterDom (alignedSlotKeep st p eff) bv =
      ((new_p ↦ₛ readBytesFromMap bv new_p len) ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal) := by
    have hLen64 : len ≤ 2 ^ 64 := by have := hBlkNew.2.2.1; omega
    rw [ByteMap_extract_slice (keep := alignedSlotKeep st p eff) hwf.masterDom_wf.1 bv new_p
      hLen64 hNewDom (fun a ha => Or.inr (hNewInP a ha)), hRemEq]
  have hMemReg : (new_p ↦ₛ readBytesFromMap bv new_p len) ⊢ memRegion new_p len := by
    have h := pointsToBytes_entails_memRegion new_p (readBytesFromMap bv new_p len)
    rwa [readBytesFromMap_length] at h
  have hGhost : MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p eff ⊢
      |==> (MallocngLiveAuth γ st2.liveMap ∗ MallocngBlockToken γ new_p len) :=
    Entails.trans (mallocngBlock_delete_bupd γ st.liveMap p eff)
      (Entails.trans (bupd_mono (mallocngBlock_alloc_bupd γ L1 new_p len (max align 16 - 16) hBlkNew hL1None)) (bupd_trans _))
  rw [hExtEq, ← sepConj_assoc]
  refine Entails.trans (sepConj_mono hGhost (sepConj_mono_left hMemReg))
    (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  dsimp only [st2]; exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_wf_fine {base brkStart brk : BitVec 64}
    {liveCost peakCost liveCost' peakCost' eff effCost align len : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length) {p new_p : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p eff effCost) (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hpLeNew : p.toNat ≤ new_p.toNat) (hNewSubP : new_p.toNat - p.toNat ≤ max align 16 - 16)
    (hNewFitEff : new_p.toNat + len ≤ p.toNat + eff) (hBlkNew : MallocngBlockWf new_p len)
    (hResLt31 : (g.slotEnd idx).toNat - (new_p.toNat + len) < 2 ^ 31)
    (hLargeProps : ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff → g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27)
    (hTotSc48 : g.sc < 48 → (new_p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc)
    (hOldLeNewEff : effCost ≤ max len MallocngMinBlockCost + (max align 16 - 16))
    (hPeakLe : peakCost ≤ peakCost') (hLiveLePeak' : liveCost' ≤ peakCost')
    (hLiveStep : liveCost + (max len MallocngMinBlockCost + (max align 16 - 16)) = liveCost' + effCost)
    (hAlignMax : align ≤ MaxAlignedAllocAlign) {bv : BitVec 64 → BitVec 8}
    (hOutBand : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a)
    (hHdr3 : bv (new_p - 3#64) = BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len)) 5 <<< 5) ||| idx))
    (hHdrOff : let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧ readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    (hTrl1 : 1 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len) → bv (new_p + BitVec.ofNat 64 len) = 0#8)
    (hTrl5 : 5 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len) → bv (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap bv (g.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (new_p.toNat + len))))
    (hDom2 : ∀ a : BitVec 64, OwnedRwByte (mkAlignedReframedSt st g idx p new_p align len bv) a → a ∈ st.masterDom)
    (hLiveMap2 : ∀ q r, (mkAlignedReframedSt st g idx p new_p align len bv).liveMap q = some r ↔
      ∃ h' ∈ (mkAlignedReframedSt st g idx p new_p align len bv).groups, ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat, h'.slots[j]'hj = .liveUser q r c) :
    let st2 := mkAlignedReframedSt st g idx p new_p align len bv
    MallocngWF base brkStart brk liveCost' peakCost' st2 ∧
    totalLiveCount st2 = totalLiveCount st ∧ dynamicRootRegions st2 = dynamicRootRegions st := by
  dsimp only []; have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
  let effCost' := max len MallocngMinBlockCost + (max align 16 - 16)
  let g2 := mkAlignedReframedGroup g idx new_p align len; let st2 := mkAlignedReframedSt st g idx p new_p align len bv
  have hGWf := hwf.groups_wf g hg; have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have ⟨_, hStorNat, hStNat, hSub4Nat, hEnNat, hEnLeTot, hEn48, _, _⟩ := group_slot_bounds hGWf hIdx
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSub3Nat := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
  have hBvOut : ∀ a : BitVec 64, ¬ SlotWriteMod g idx a → bv a = st.byteVal a := fun a hNotMod =>
    hOutBand a fun hBand => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hBand
      exact hNotMod (Or.inr ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩, fun hEq => by have := congrArg BitVec.toNat hEq; omega⟩)
  obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf
    ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
  obtain ⟨rgG, hrgG, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
  have hMetaBytes : readBytesFromMap bv g2.metaPtr 40 = g2.metaBytes := by
    refine (readBytesFromMap_eq_of_inRegion (v₁ := bv) (v₂ := st.byteVal) (b := g.metaPtr) (n := 40) (by omega) fun a ha => hOutBand a fun hBand => ?_).trans hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hBand
    exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrgG hRgMp) (hInMaG a ha) ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hPLo := hSWf.2.2.2.2.2.1; have hPHi := hSWf.2.2.2.2.2.2.1
  have hNoNew : ∀ h0 ∈ st.groups, ∀ j (hj0 : j < h0.slots.length) r c, (h0 ≠ g ∨ j ≠ idx) →
      h0.slots[j]'hj0 ≠ .liveUser new_p r c := by
    intro h0 hh0 j hj0 r c hDiff hSlot0
    have ⟨_, _, _, _, _, _, _, _, hEnMod12⟩ := group_slot_bounds hGWf hIdx
    have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0; rw [hSlot0] at hSWf0
    have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, hMod12_0⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
    have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hQMod0 : new_p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hSWf0.2.2.2.2.1.2.1
    have hNewMod : new_p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hBlkNew.2.1
    have := hSWf0.2.2.2.2.2.1; have := hSWf0.2.2.2.2.2.2.1
    exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0])
      (hDiff.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm))
      ((inRegion_iff_toNat (by omega) new_p).mpr ⟨by omega, by omega⟩)
      ((inRegion_iff_toNat (by omega) new_p).mpr ⟨by omega, by omega⟩)
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g2)
  have hSlot2Wf : SlotWf st2 g2 idx (.liveUser new_p len effCost') := by
    dsimp only [SlotWf]
    rw [show g2.slotStart idx = g.slotStart idx from rfl, show g2.slotEnd idx = g.slotEnd idx from rfl,
      show g2.storage = g.storage from rfl, show g2.sc = g.sc from rfl,
      show g2.availMask = g.availMask from rfl, show g2.freedMask = g.freedMask from rfl,
      show g2.activeIdx = g.activeIdx from rfl, show st2.byteVal = bv from rfl]
    refine ⟨(hOutBand (g.slotStart idx - 4#64) fun hB => by
        have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) (g.slotStart idx - 4#64)).mp hB; omega).trans hSWf.1,
      by simp [hSWf.2.1], by simp [hSWf.2.2.1],
      fun hLt => False.elim (by have := hSWf.2.2.2.1 hLt; cases this),
      hBlkNew, by omega, by omega, by dsimp only [effCost']; omega,
      ⟨by dsimp only [effCost']; omega, by dsimp only [effCost']; omega,
       by simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_ov, ↓reduceIte]; dsimp only [effCost']; omega⟩, hResLt31,
      ⟨fun h2_48 => Nat.lt_of_lt_of_le (hSWf.2.2.2.2.2.2.2.2.2.2.1.1 h2_48) hOldLeNewEff, hTotSc48⟩,
      fun h63 => Nat.le_trans (hSWf.2.2.2.2.2.2.2.2.2.2.2.1 h63) (Nat.add_le_add_right hOldLeNewEff 8195),
      hHdr3, ?_, hTrl1, hTrl5⟩
    by_cases hTotLe : (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff
    · simpa [hTotLe] using hHdrOff
    · have ⟨h63, hI0, hLt27⟩ := hLargeProps hTotLe
      have hH : bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
          readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 ((new_p.toNat - g.storage.toNat) / 16)) := by
        simpa [hTotLe] using hHdrOff
      simp [hTotLe, h63, hI0, hLt27, hH.1, hH.2.1, hH.2.2]
  have hClaimEq : totalClaimedSlots st2 = totalClaimedSlots st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := g2)
    have hS := list_set_filter_len g.slots hIdx (.liveUser new_p len effCost') SlotState.isClaimed
    rw [hSlot] at hS; unfold totalClaimedSlots
    simp only [st2, mkAlignedReframedSt, g2, mkAlignedReframedGroup, effCost', SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hG hS ⊢; omega
  have hEffSum : totalLiveEffCost st2 + effCost = totalLiveEffCost st + effCost' := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (fun h => (h.slots.map slotEffCost).sum) (g1 := g2)
    have hS := list_set_map_sum g.slots hIdx (.liveUser new_p len effCost') slotEffCost
    rw [hSlot] at hS; unfold totalLiveEffCost
    simp only [st2, mkAlignedReframedSt, g2, mkAlignedReframedGroup, effCost', slotEffCost] at hG hS ⊢; omega
  have hCountEq : totalLiveCount st2 = totalLiveCount st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (fun h => (h.slots.map slotLiveCount).sum) (g1 := g2)
    have hS := list_set_map_sum g.slots hIdx (.liveUser new_p len effCost') slotLiveCount
    rw [hSlot] at hS; unfold totalLiveCount
    simp only [st2, mkAlignedReframedSt, g2, mkAlignedReframedGroup, effCost', slotLiveCount] at hG hS ⊢; omega
  have hDynEq : dynamicRootRegions st2 = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st2, mkAlignedReframedSt, g2] at hRep ⊢; rw [hRep.2.2.1]
  let hwf0 := hwf.mono_peakCost hPeakLe
  have hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by simp [hSlot]
  have hDisj := slotWriteMod_disjoint hwf0 hg hIdx hNotNested
  have hNestedMap : ∀ cg ∈ st.groups, cg.maplen = 0 →
      ∃ cg' ∈ st2.groups, cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
        cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap := fun cg hcg _ => by
    by_cases hEq : cg.metaPtr = g.metaPtr
    · rw [mem_groups_eq_of_metaPtr hwf0.groups_nodup.1 hcg hg hEq]; exact ⟨g2, hRep.2.2.2.2.1, rfl, rfl, rfl, rfl⟩
    · exact ⟨cg, hRep.2.2.2.2.2.2.1 cg hcg hEq, rfl, rfl, rfl, rfl⟩
  have hParentLift : ∀ h0 ∈ st.groups, h0.maplen = 0 →
      1 ≤ h0.lastIdx ∧ ∃ pg' ∈ st2.groups, ∃ pIdx : Nat, ∃ hp' : pIdx < pg'.slots.length,
        h0.parentMeta = some pg'.metaPtr ∧ pg'.sc < 48 ∧ h0.sc < pg'.sc ∧ pg'.sc ≤ 24 ∧
        pg'.slots[pIdx]'hp' = .liveNested h0.metaPtr ∧ (pg'.slotStart pIdx).toNat ≤ h0.mem.toNat ∧
        h0.mem.toNat + h0.nestedCap ≤ (pg'.slotEnd pIdx).toNat ∧ h0.nestedCap = slotStride pg'.sc - 4 :=
    fun h0 hh0 hM0 => by
      obtain ⟨hL1, pg, hpg, pIdx, hp, hPM, hPSc, hLtSc, hLe24, hPSlot, hPLo0, hPHi0, hPCap⟩ :=
        (hwf0.groups_wf h0 hh0).2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
      refine ⟨hL1, ?_⟩; by_cases hEq : pg.metaPtr = g.metaPtr
      · have hPgEq := mem_groups_eq_of_metaPtr hwf0.groups_nodup.1 hpg hg hEq; subst hPgEq
        have hpNe : pIdx ≠ idx := fun hJ => by subst hJ; exact hNotNested h0.metaPtr hPSlot
        have hp2 : pIdx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hp]
        exact ⟨g2, hRep.2.2.2.2.1, pIdx, hp2, hPM, hPSc, hLtSc, hLe24,
          by simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hpNe, ↓reduceIte, hPSlot],
          hPLo0, hPHi0, hPCap⟩
      · exact ⟨pg, hRep.2.2.2.2.2.2.1 pg hpg hEq, pIdx, hp, hPM, hPSc, hLtSc, hLe24, hPSlot, hPLo0, hPHi0, hPCap⟩
  have hwf2 : MallocngWF base brkStart brk liveCost' peakCost' st2 :=
    { base_wf := trivial, brk_bounds := hwf0.brk_bounds, ctx_lens := hwf0.ctx_lens, initDone_wf := hwf0.initDone_wf
      initZero_wf := fun h0 => by have hE := (hwf0.initZero_wf h0).2.2.2.2.2.2.2.2.2.1; rw [hE] at hg; cases hg
      bounces_wf := hwf0.bounces_wf
      usage_wf := fun sc hsc => (hwf0.usage_wf sc hsc).trans (hRep.2.2.2.1 sc).symm
      brk_mode_wf := hwf0.brk_mode_wf
      metaAreas_wf := ⟨hwf0.metaAreas_wf.1, fun ma hma =>
        let hMa := hwf0.metaAreas_wf.2.1 ma hma
        ⟨hMa.1, hMa.2.1, hMa.2.2.1, (readBytesFromMap_eq_of_inRegion (by decide)
          fun a ha => hBvOut a (hDisj.1 ma hma a ha)).trans hMa.2.2.2⟩, hwf0.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf0.guard_avail_wf.1, hwf0.guard_avail_wf.2.1, hwf0.guard_avail_wf.2.2.1, fun ap hap => by
        have hAp := hwf0.guard_avail_wf.2.2.2 ap hap
        have ⟨hABC, _, hCrossCD⟩ := pairwiseDisjoint_append hwf0.regions_disjoint.1
        have ⟨_, _, hCrossABC⟩ := pairwiseDisjoint_append hABC
        have hDisjMaAp := hCrossABC (maG.base, 4096) (List.mem_append_left _ (List.mem_map_of_mem hmaG))
          (ap, 4096) (List.mem_map_of_mem hap)
        have hDisjApRg := hCrossCD (ap, 4096) (List.mem_append_right _ (List.mem_map_of_mem hap))
          (rgG.mem, rgG.maplen * 4096) (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgG, decide_eq_true hRgMp⟩))
        refine ⟨hAp.1, hAp.2.1, hAp.2.2.1, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a fun hMod => ?_).trans hAp.2.2.2⟩
        rcases hMod with hM | ⟨hS, _⟩
        · exact not_both_inRegion_of_disjointRegions hDisjMaAp (hInMaG a hM) ha
        · have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hS
          have hInRg : InRegion rgG.mem (rgG.maplen * 4096) a := (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
          exact not_both_inRegion_of_disjointRegions hDisjApRg ha hInRg⟩
      inflight_wf := by have := hwf0.inflight_wf; dsimp only [st2, mkAlignedReframedSt, g2] at hClaimEq ⊢; omega
      free_bump_metas_wf := by
        have ⟨hDll, hFmB, hBump, hBmB, hUfNd, hUfIff⟩ := hwf0.free_bump_metas_wf
        have ⟨hNd123, _, _⟩ := List.nodup_append.mp hUfNd
        have ⟨hNd12, _, hDisjBm⟩ := List.nodup_append.mp hNd123
        have ⟨_, _, hDisjFm⟩ := List.nodup_append.mp hNd12
        refine ⟨hDll, fun fm hfm => ?_, hBump, fun bm hbm => ?_,
          by change ((replaceGroupByMeta st.groups g.metaPtr g2).map (·.metaPtr) ++ _ ++ _ ++ _).Nodup; rw [hRep.1]; exact hUfNd,
          fun m => by change m ∈ (replaceGroupByMeta st.groups g.metaPtr g2).map (·.metaPtr) ++ _ ++ _ ++ _ ↔ m ∈ allMetaSlots st; rw [hRep.1]; exact hUfIff m⟩
        · have hNe : fm.ptr ≠ g.metaPtr := fun hE => hDisjFm g.metaPtr (List.mem_map_of_mem hg) fm.ptr (List.mem_map_of_mem hfm) hE.symm
          have hAll := (hUfIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
          exact (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 fm.ptr hAll hNe a ha)).trans (hFmB fm hfm)
        · have hNe : bm ≠ g.metaPtr := fun hE => hDisjBm g.metaPtr (List.mem_append_left _ (List.mem_map_of_mem hg)) bm hbm hE.symm
          have hAll := (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
          exact (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 bm hAll hNe a ha)).trans (hBmB bm hbm)
      groups_nodup := ⟨hRep.1 ▸ hwf0.groups_nodup.1, hRep.2.1 ▸ hwf0.groups_nodup.2⟩
      groups_wf := fun h' hh' => by
        rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
        · have hHdrDisj := hDisj.2.2.1 g hg
          have hGMem48 : g.mem.toNat + 9 ≤ 2 ^ 64 := by have := hGWf.2.2.2.2.2.2.1; have := hGWf.2.2.2.2.2.2.2.1; omega
          refine ⟨hGWf.1, hGWf.2.1, by simp [g2, mkAlignedReframedGroup, hGWf.2.2.1], hGWf.2.2.2.1,
            hGWf.2.2.2.2.1, hGWf.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.2.1,
            (hBvOut _ hHdrDisj.2).trans hGWf.2.2.2.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.2.2.2.1,
            hGWf.2.2.2.2.2.2.2.2.2.2.2.1, hParentLift g hg, hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hMetaBytes,
            (readBytesFromMap_eq_of_inRegion (b := g.mem) (n := 8) (by decide) fun a ha => hBvOut a (hHdrDisj.1 a
              ((inRegion_iff_toNat (by omega) a).mpr (by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; omega)))).trans
              hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (hBvOut (g.mem + 8#64) (hHdrDisj.1 (g.mem + 8#64) ((inRegion_iff_toNat (by omega) (g.mem + 8#64)).mpr
              ⟨by rw [bv64_add_toNat (by omega)]; omega, by rw [bv64_add_toNat (by omega)]; omega⟩))).trans
              hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun j hj2 => ?_⟩
          have hj : j < g.slots.length := by simpa [g2, mkAlignedReframedGroup] using hj2
          by_cases hjEq : j = idx
          · subst hjEq; simpa [g2, mkAlignedReframedGroup] using hSlot2Wf
          · have hGet2 : g2.slots[j]'hj2 = g.slots[j]'hj := by simp only [g2, mkAlignedReframedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte]
            rw [hGet2]
            exact slotWf_other_of_slotSet hwf0 hg hIdx hNotNested hBvOut hNestedMap hg hj (Or.inr hjEq) rfl rfl rfl rfl rfl rfl rfl rfl rfl
              (hOv := fun u r0 e0 hS => by
                have hNe : u ≠ new_p := fun hE => hNoNew g hg j hj r0 e0 (Or.inr hjEq) (by rw [← hE]; exact hS)
                simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov, hNe, ↓reduceIte])
        · have hHWf := hwf0.groups_wf h' hh0
          have hHdrDisj := hDisj.2.2.1 h' hh0
          have hHMem48 : h'.mem.toNat + 9 ≤ 2 ^ 64 := by have := hHWf.2.2.2.2.2.2.1; have := hHWf.2.2.2.2.2.2.2.1; omega
          have hAllH := (hwf0.free_bump_metas_wf.2.2.2.2.2 h'.metaPtr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hh0))))
          refine ⟨hHWf.1, hHWf.2.1, hHWf.2.2.1, hHWf.2.2.2.1, hHWf.2.2.2.2.1, hHWf.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.1,
            (hBvOut _ hHdrDisj.2).trans hHWf.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.2.1, hParentLift h' hh0, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 h'.metaPtr hAllH hNeM a ha)).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hHdrDisj.1 a
              ((inRegion_iff_toNat (by omega) a).mpr (by have ⟨_, _⟩ := (inRegion_iff_toNat (by omega) a).mp ha; omega)))).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (hBvOut (h'.mem + 8#64) (hHdrDisj.1 (h'.mem + 8#64) ((inRegion_iff_toNat (by omega) (h'.mem + 8#64)).mpr
              ⟨by rw [bv64_add_toNat (by omega)]; omega, by rw [bv64_add_toNat (by omega)]; omega⟩))).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun j hj => slotWf_other_of_slotSet hwf0 hg hIdx hNotNested hBvOut hNestedMap hh0 hj (Or.inl hNeM) rfl rfl rfl rfl rfl rfl rfl rfl rfl
              (hOv := fun u r0 e0 hS => by
                have hNe : u ≠ new_p := fun hE => hNoNew h' hh0 j hj r0 e0
                  (Or.inl fun hG => hNeM (congrArg GroupDesc.metaPtr hG)) (by rw [← hE]; exact hS)
                simp only [st2, mkAlignedReframedSt, MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov, hNe, ↓reduceIte])⟩
      regions_disjoint := ⟨hDynEq ▸ hwf0.regions_disjoint.1, trivial⟩
      active_wf := fun sc h1 h2 => by
        have hAct := hwf0.active_wf sc h1 h2
        obtain ⟨pre, _, hGsSplit, hPreNe, _, _⟩ := split_groups_at_mem hwf0.groups_nodup.1 hg
        have hPreNone : pre.find? (·.metaPtr == g.metaPtr) = none :=
          List.find?_eq_none.mpr fun h hh hE => hPreNe h hh (beq_iff_eq.mp hE)
        have hFindG : st.groups.find? (·.metaPtr == g.metaPtr) = some g := by
          rw [hGsSplit, List.find?_append, List.find?_cons, hPreNone]; simp
        have hFMapEq : ((st.activeLists[sc]'h2).filterMap fun m => (findGroupByMeta st2 m).map fun h => (h.metaPtr, h.prev, h.next)) =
            ((st.activeLists[sc]'h2).filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
          congr 1; funext m; unfold findGroupByMeta
          change ((replaceGroupByMeta st.groups g.metaPtr g2).find? (·.metaPtr == m)).map _ = _
          rw [hRep.2.2.2.2.2.2.2 m]; by_cases hm : m == g.metaPtr
          · have hmEq := beq_iff_eq.mp hm; subst hmEq; simp [hFindG]; exact ⟨rfl, rfl, rfl⟩
          · simp [hm]
        refine ⟨fun m hm => ?_, hFMapEq ▸ hAct.2.1, hFMapEq ▸ hAct.2.2.1,
          fun h' hh' hSc' => (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact hAct.2.2.2.1 g hg hSc') (fun ⟨hh0, _⟩ => hAct.2.2.2.1 h' hh0 hSc'),
          fun i hi hPos h' hh' hEqM => (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact hAct.2.2.2.2.1 i hi hPos g hg hEqM) (fun ⟨hh0, _⟩ => hAct.2.2.2.2.1 i hi hPos h' hh0 hEqM),
          fun h₁ hh₁ h₂ hh₂ hSc₁ hSc₂ hLt₁ hLt₂ => ?_,
          fun h' hh' hSc' hLt => (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact hAct.2.2.2.2.2.2 g hg hSc' hLt) (fun ⟨hh0, _⟩ => hAct.2.2.2.2.2.2 h' hh0 hSc' hLt)⟩
        · obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct.1 m hm; by_cases hEq : h0.metaPtr = g.metaPtr
          · rw [mem_groups_eq_of_metaPtr hwf0.groups_nodup.1 hh0 hg hEq] at hM0 hSc0; exact ⟨g2, hRep.2.2.2.2.1, hM0, hSc0⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, hM0, hSc0⟩
        · have ⟨h₁0, hh₁0, hM₁, hSc₁0, hLt₁0⟩ : ∃ h₁0 ∈ st.groups, h₁.metaPtr = h₁0.metaPtr ∧ h₁0.sc = sc ∧ h₁0.activeIdx < h₁0.lastIdx :=
            (hRep.2.2.2.2.2.1 h₁ hh₁).elim (fun hE => by subst hE; exact ⟨g, hg, rfl, hSc₁, hLt₁⟩) fun ⟨hh0, _⟩ => ⟨h₁, hh0, rfl, hSc₁, hLt₁⟩
          have ⟨h₂0, hh₂0, hM₂, hSc₂0, hLt₂0⟩ : ∃ h₂0 ∈ st.groups, h₂.metaPtr = h₂0.metaPtr ∧ h₂0.sc = sc ∧ h₂0.activeIdx < h₂0.lastIdx :=
            (hRep.2.2.2.2.2.1 h₂ hh₂).elim (fun hE => by subst hE; exact ⟨g, hg, rfl, hSc₂, hLt₂⟩) fun ⟨hh0, _⟩ => ⟨h₂, hh0, rfl, hSc₂, hLt₂⟩
          exact hM₁.trans ((hAct.2.2.2.2.2.1 h₁0 hh₁0 h₂0 hh₂0 hSc₁0 hSc₂0 hLt₁0 hLt₂0).trans hM₂.symm)
      liveMap_wf := hLiveMap2, live_le_peak := hLiveLePeak'
      effCost_le_live := by have := hwf0.effCost_le_live; dsimp only [st2, mkAlignedReframedSt, g2, effCost'] at hEffSum ⊢; omega
      meta_pages_bound := hwf0.meta_pages_bound
      empty_groups_bound := by
        have hNE : ¬ g2.isEmpty = true := fun hE => by
          have hI : idx < g2.slots.length := by simp [g2, mkAlignedReframedGroup, hIdx]
          have hF := List.all_eq_true.mp hE _ (List.getElem_mem hI); simp [g2, mkAlignedReframedGroup, SlotState.isFree] at hF
        intro h' hh' hEmp; rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
        · exact False.elim (hNE hEmp)
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf0.empty_groups_bound h' hh0 hEmp
          exact ⟨e1, e2, e3, e4, e5, fun y hy hEy hSc => (hRep.2.2.2.2.2.1 y hy).elim
            (fun r => False.elim (hNE (r ▸ hEy))) (fun ⟨hy0, _⟩ => e6 y hy0 hEy hSc), e7⟩
      masterDom_wf := ⟨hwf0.masterDom_wf.1, fun a hAny => hAny.elim (hDom2 a) fun hRest =>
        hRest.elim (fun hP => hwf0.masterDom_wf.2.1 a (Or.inr (Or.inl hP))) fun hMap => by
          refine hwf0.masterDom_wf.2.1 a (Or.inr (Or.inr ?_)); unfold OwnedMappedByte at hMap ⊢
          exact hMap.imp id (Or.imp id (Or.imp id fun ⟨h', hh', hMp', hIn'⟩ =>
            (hRep.2.2.2.2.2.1 h' hh').elim (fun hE => by subst hE; exact ⟨g, hg, hMp', hIn'⟩) fun ⟨hh0, _⟩ => ⟨h', hh0, hMp', hIn'⟩)),
        fun a ha => hDynEq.symm ▸ hwf0.masterDom_wf.2.2 a ha⟩ }
  exact ⟨hwf2, hCountEq, hDynEq⟩

private theorem alignedAlloc_reframe_pure_props {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st : MallocngSt} (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length) {p new_p align len : BitVec 64}
    (hSlot : g.slots[idx]'hIdx = .liveUser p (mallocngAlignedEffSize align.toNat len.toNat)
      (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost))
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < mallocngAlignedEffSize align.toNat len.toNat)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ mallocngAlignedEffSize align.toNat len.toNat + 4115)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    (hNewEq : new_p = p + ((0#64 - p) &&&
      ((if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64) - 1#64))) :
    p.toNat ≤ new_p.toNat ∧ new_p.toNat - p.toNat ≤ max align.toNat 16 - 16 ∧
    new_p.toNat + len.toNat ≤ p.toNat + mallocngAlignedEffSize align.toNat len.toNat ∧ MallocngBlockWf new_p len.toNat ∧
    (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31 ∧
    (¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff →
      g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27) ∧
    (g.sc < 48 → (new_p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc) := by
  subst hNewEq
  have hBlkP : MallocngBlockWf p (mallocngAlignedEffSize align.toNat len.toNat) := by
    have h := (hwf.groups_wf g hg).slot_wf idx hIdx; rw [hSlot] at h; exact h.2.2.2.2.1
  obtain ⟨_, _, hDeltaLe, hNewNat, hNewFit, _, hBlkNew, _⟩ := alignedAlloc_snap_props hAlignOk hAlignMax hNoOvf hBlkP
  have hBnd := alignedAlloc_reframe_bounds hwf hg hIdx hSlot hOff255 hSc63 hAlignOk hAlignMax hNoOvf
  exact ⟨by omega, by omega, hNewFit, hBlkNew, hBnd.1, hBnd.2,
    fun h48 => alignedAlloc_totalOff_lt_sizeClass hwf hg hIdx hSlot hOff255 hSc24_26 hAlignOk hAlignMax hNoOvf h48⟩

/-! ## Single-Step Fine-Invariant and Ghost-Map Commit -/
private theorem replaceGroupByMeta_map_eq (gs : List GroupDesc) (g1 g' g2 : GroupDesc)
    (hm : g'.metaPtr = g1.metaPtr) :
    replaceGroupByMeta (gs.map fun g => if g.metaPtr == g1.metaPtr then g' else g) g'.metaPtr g2 =
      gs.map fun g => if g.metaPtr == g1.metaPtr then g2 else g := by
  unfold replaceGroupByMeta; rw [List.map_map]; refine List.map_congr_left fun g _ => ?_
  dsimp only [Function.comp]; by_cases h : g.metaPtr == g1.metaPtr <;> simp [h, hm]

private theorem replaceGroupByMeta_cons_eq (gs : List GroupDesc) (g' g2 : GroupDesc)
    (hNd : ((g' :: gs).map GroupDesc.metaPtr).Nodup) :
    replaceGroupByMeta (g' :: gs) g'.metaPtr g2 = g2 :: gs := by
  simp only [List.map_cons, List.nodup_cons] at hNd; unfold replaceGroupByMeta
  simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, List.cons.injEq, true_and]
  have hId : gs.map (fun h => if h.metaPtr == g'.metaPtr then g2 else h) = gs.map id :=
    List.map_congr_left fun h hh => by
      have hNe : (h.metaPtr == g'.metaPtr) = false := beq_eq_false_iff_ne.mpr fun hE => hNd.1 (hE ▸ List.mem_map_of_mem hh)
      simp [hNe]
  rw [hId, List.map_id]

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_fine_finish {A : MallocngAddrs} {brkStart brk : BitVec 64}
    {bCoarse : MallocngBudget} {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap0 : BitVec 64 → Option Nat} {st0 st' : MallocngSt} (γ : GhostName)
    (hwf' : MallocngWF A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st')
    {g' : GroupDesc} {idx : Nat} {p new_p align len : BitVec 64}
    (hRaw : MallocImplFineRawRel A.base brkStart b ivs0 alignMap0 st0 st' g' idx (mallocngAlignedEffSize align.toNat len.toNat) p)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    (hNewEq : new_p = p + ((0#64 - p) &&& ((if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64) - 1#64)))
    {bv : BitVec 64 → BitVec 8}
    (hOutBand : ∀ a : BitVec 64, ¬ InRegion (g'.slotStart idx - 3#64) (g'.stride - 1) a → bv a = st'.byteVal a)
    (hHdr3 : bv (new_p - 3#64) = BitVec.ofNat 8 ((min ((g'.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx))
    (hHdrOff : let tot' := (new_p.toNat - g'.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧ readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    (hTrl1 : 1 ≤ (g'.slotEnd idx).toNat - (new_p.toNat + len.toNat) → bv (new_p + len) = 0#8)
    (hTrl5 : 5 ≤ (g'.slotEnd idx).toNat - (new_p.toNat + len.toNat) → bv (g'.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap bv (g'.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32 ((g'.slotEnd idx).toNat - (new_p.toNat + len.toNat)))) :
    let eff := mallocngAlignedEffSize align.toNat len.toNat; let bf := FineBudget.stepAligned align.toNat len.toNat b
    (ghostMapAuth (fineAlignGam γ) alignMap0 ∗ MallocngRoTablesA A ∗ MallocngLiveAuth (fineBaseGam γ) st'.liveMap ∗
      MallocngBlockToken (fineBaseGam γ) p eff ∗ ByteMap st'.masterDom (alignedSlotKeep st' p eff) bv ∗
      (A.ctx ↦ₛ st'.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗ (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗
      ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState (fineBaseGam γ) st'.auxvPtr st'.auxvSnap ∗
      ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st')) ⊢
    |==> (FineCoreImpl γ A brkStart brk bf (dynamicRootRegions st') ∗
      FineBlock γ new_p len.toNat (max align.toNat 16) ∗ memRegion new_p len.toNat) := by
  intro eff bf
  obtain ⟨hInv0, hFreshP0, hLiveSt', hMetaSt', hg', ⟨hIdx', hSlot'⟩, hOff255, hSc24_26, hSc63, hBranch⟩ := hRaw
  let effCost' := max len.toNat MallocngMinBlockCost + (max align.toNat 16 - 16)
  let g2 := mkAlignedReframedGroup g' idx new_p align.toNat len.toNat
  let st2 := mkAlignedReframedSt st' g' idx p new_p align.toNat len.toNat bv
  let live2 := bCoarse.liveCost + effCost' - max eff MallocngMinBlockCost; let peak2 := max bCoarse.peakCost live2
  have hCostLe := effCost_le_aligned align.toNat len.toNat MallocngMinBlockCost
  obtain ⟨hpLeNew, hNewSubP, hNewFit, hBlkNew, hRes31, hLarge, hTotSc48⟩ :=
    alignedAlloc_reframe_pure_props hwf' hg' hIdx' hSlot' hOff255 hSc24_26 hSc63 hAlignOk hAlignMax hNoOvf hNewEq
  have ⟨hL1None, _, hDom2, hProtEq, hMapSetEq, hLiveMap2, hBupdBase⟩ :=
    alignedAlloc_reframe_spatial_fine (fineBaseGam γ) hwf' hg' hIdx' (align := align.toNat) (len := len.toNat) hSlot' hpLeNew hNewFit hBlkNew hOutBand
  have ⟨hwf2, _, hDynEq⟩ :=
    alignedAlloc_reframe_wf_fine (liveCost' := live2) (peakCost' := peak2) hwf' hg' hIdx' (align := align.toNat) (len := len.toNat)
      hSlot' hOff255 hpLeNew hNewSubP hNewFit hBlkNew hRes31 hLarge hTotSc48 hCostLe (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      (by dsimp only [live2, effCost', eff] at hCostLe ⊢; omega) hAlignMax hOutBand hHdr3 hHdrOff (by rwa [BitVec.ofNat_toNat]) hTrl5 hDom2 hLiveMap2
  have hL1Eq : ∀ k, (if k = p then none else st'.liveMap k) = st0.liveMap k := fun k => by
    by_cases hk : k = p
    · subst hk; simp [hFreshP0]
    · simp only [hk, ↓reduceIte]; change st'.liveMap.req k = st0.liveMap k
      rw [hLiveSt', MallocngLiveMap.insert_req]; simp [hk]
  have hFreshNew0 : st0.liveMap new_p = none := by rw [← hL1Eq new_p]; exact hL1None
  have hLiveSt2 : ∀ q, st2.liveMap q = if q = new_p then some len.toNat else st0.liveMap q := fun q => by
    change ((st'.liveMap.erase p).insert new_p len.toNat (max align.toNat 16 - 16)).req q = _
    simp only [MallocngLiveMap.insert_req, MallocngLiveMap.erase_req]
    by_cases hq : q = new_p
    · simp [hq]
    · simp only [hq, ↓reduceIte]; exact hL1Eq q
  have hAlignNone : alignMap0 new_p = none := by
    cases hAl : alignMap0 new_p with
    | none => rfl
    | some al => obtain ⟨_, n, hn⟩ := hInv0.alignMap_wf.1 new_p al hAl; rw [hFreshNew0] at hn; cases hn
  have hMetaLe2 : st2.metaAreas.length ≤ fineMaxMetaAreas bf :=
    Nat.le_trans hMetaSt' (fineMaxMetaAreas_mono (.aligned align.toNat len.toNat) b)
  let alignMap' : BitVec 64 → Option Nat := fun q => if q = new_p then some (max align.toNat 16) else alignMap0 q
  have hEffPad := eff_eq_add_pad align.toNat len.toNat
  have hFineInv2 : MallocngFineInv 0 bf (dynamicRootRegions st2) alignMap' st2 := by
    by_cases hSmall : eff ≤ MmapThresholdReq
    · simp only [eff, hSmall, ↓reduceDIte] at hBranch
      obtain ⟨sc, pk, pkSC, pkSB, st1, g1, brk1, live1, peak1, hsc, hAlt, hPk, hPres, hwf1, hg1Mem, hg1Sc, ⟨hIdx1, hClaimed⟩, hg'Same, hg'Slots, hGroupsSt'⟩ := hBranch
      have hEffSmall : len.toNat + (max align.toNat 16 - 16) ≤ MmapThresholdReq := by rwa [← hEffPad]
      have hAlt' : sc = sizeToClassUnits ((len.toNat + (max align.toNat 16 - 16) + 3) / 16) ∨
          sc = coarseAlt (sizeToClassUnits ((len.toNat + (max align.toNat 16 - 16) + 3) / 16)) := by rwa [← hEffPad]
      have hg2Same : FineGroupSameGeom g2 g1 := FineGroupSameGeom.trans ⟨rfl, rfl, rfl, rfl, rfl⟩ hg'Same
      have hg2Slots : g2.slots = g1.slots.set idx (.liveUser new_p len.toNat effCost') := by simp [g2, mkAlignedReframedGroup, hg'Slots, List.set_set, effCost']
      have hGroups2 : st2.groups = st1.groups.map (fun g => if g.metaPtr == g1.metaPtr then g2 else g) := by
        change replaceGroupByMeta st'.groups g'.metaPtr g2 = _; rw [hGroupsSt']; exact replaceGroupByMeta_map_eq st1.groups g1 g' g2 hg'Same.1
      exact commit_claimed_slab_slot_aligned hsc hEffSmall hAlt' hFreshNew0 hInv0 hPk hPres
        hwf1 hwf2 hg1Mem hg1Sc hIdx1 hClaimed hg2Same hg2Slots hGroups2 hLiveSt2 hMetaLe2
    · simp only [eff, hSmall, ↓reduceDIte] at hBranch
      obtain ⟨st1, hIdx0, hSame1, hGroupsSt', hg'Sc, hg'Slots, hg'Maplen⟩ := hBranch
      have hEffLarge : ¬ (len.toNat + (max align.toNat 16 - 16) ≤ MmapThresholdReq) := by rwa [← hEffPad]
      have hNdSt' : ((g' :: st1.groups).map GroupDesc.metaPtr).Nodup := by have hNd := hwf'.groups_nodup.1; rwa [hGroupsSt'] at hNd
      have hGroups2 : st2.groups = g2 :: st1.groups := by
        change replaceGroupByMeta st'.groups g'.metaPtr g2 = _; rw [hGroupsSt']; exact replaceGroupByMeta_cons_eq st1.groups g' g2 hNdSt'
      have hCgSlots : g2.slots = [.liveUser new_p len.toNat effCost'] := by subst hIdx0; simp [g2, mkAlignedReframedGroup, hg'Slots, effCost']
      have hCgEff : effCost' - max len.toNat MallocngMinBlockCost ≤ max align.toNat 16 - 16 := by dsimp only [effCost']; omega
      have hCgMap : g2.maplen * 4096 ≤ declCost63 len.toNat (max align.toNat 16) := by
        have hM : g'.maplen * 4096 ≤ len.toNat + (max align.toNat 16 - 16) + 4115 := by rwa [eff_eq_add_pad] at hg'Maplen
        change g'.maplen * 4096 ≤ len.toNat + (max align.toNat 16 - 16) + 8195; omega
      exact commit_mmap63_group_aligned hEffLarge hFreshNew0 hInv0 hSame1 hGroups2 hg'Sc hCgSlots hCgEff hCgMap hLiveSt2 hMetaLe2
  have hCombBupd := bupd_sep (ghostMap_alloc (fineAlignGam γ) alignMap0 new_p (max align.toNat 16) hAlignNone) hBupdBase
  have hRearrPre : ∀ (GA RO LA BT BM R0 : SepProp), (GA ∗ RO ∗ LA ∗ BT ∗ BM ∗ R0) = ((GA ∗ (LA ∗ BT ∗ BM)) ∗ (RO ∗ R0)) := fun _ _ _ _ _ _ => by ac_rfl
  rw [hRearrPre (ghostMapAuth (fineAlignGam γ) alignMap0) (MallocngRoTablesA A)
    (MallocngLiveAuth (fineBaseGam γ) st'.liveMap) (MallocngBlockToken (fineBaseGam γ) p eff) (ByteMap st'.masterDom (alignedSlotKeep st' p eff) bv)]
  refine Entails.trans (sepConj_mono_left hCombBupd) (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  rw [← hDynEq, FineCoreImpl_eq]
  have hEx : FineCoreStInflightA 0 γ A brkStart brk bf (dynamicRootRegions st2) alignMap' live2 peak2 st2 ⊢
      ∃∗ st : MallocngSt, ∃∗ am : BitVec 64 → Option Nat, ∃∗ lc : Nat, ∃∗ pc : Nat,
        FineCoreStInflightA 0 γ A brkStart brk bf (dynamicRootRegions st2) am lc pc st :=
    Entails.sepExists_right st2 (Entails.sepExists_right alignMap' (Entails.sepExists_right live2 (Entails.sepExists_right peak2 (Entails.refl _))))
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_right hEx))
  unfold FineCoreStInflightA MallocngCoreStInflightA FineBlock
  rw [pure_sepConj_of_true hFineInv2, pure_sepConj_of_true hwf2, pure_sepConj_of_true (Nat.le_max_right align.toNat 16), hProtEq, hMapSetEq,
      show st2.ctx = st'.ctx from rfl, show st2.auxvPtr = st'.auxvPtr from rfl, show st2.auxvSnap = st'.auxvSnap from rfl]
  generalize ghostMapAuth (fineAlignGam γ) alignMap' = P1, ghostMapElem (fineAlignGam γ) new_p (max align.toNat 16) = P2,
    MallocngRoTablesA A = P3, MallocngLiveAuth (fineBaseGam γ) st2.liveMap = P4, MallocngBlockToken (fineBaseGam γ) new_p len.toNat = P5,
    memRegion new_p len.toNat = P6, ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal = P7, (A.ctx ↦ₛ st'.ctx.toBytes) = P8,
    (A.lock ↦₃₂ 0#32) = P9, (A.replaced ↦₃₂ 0#32) = P10, (A.aaReplaced ↦₃₂ 0#32) = P11, ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) = P12,
    MallocngAuxvState (fineBaseGam γ) st'.auxvPtr st'.auxvSnap = P13,
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = P14, MappedSet st'.masterDom (OwnedMappedByte st') = P15
  exact Entails.of_eq (by ac_rfl)

/-! ## Unified `+0x1b4 → ret` Fine Reframe Stage -/

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_fwd_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p len : BitVec 64} {eff : Nat}
    (hStPlus16 : (g.slotStart idx).toNat + 16 ≤ new_p.toNat) (hNewFitEnd : new_p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    {bv : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a)
    (hHdrOff : let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
        readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    (hTrl1 : 1 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) → bv (new_p + len) = 0#8)
    (hTrl5 : 5 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) → bv (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap bv (g.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat))))
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x234#64) (hrun : s.status = .Running) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk) (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = new_p) (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 g.stride)
    (hx5 : (s.readReg64 .x5).truncate 8 = BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx))
    (hx6 : s.readReg64 .x6 = g.mem + 16#64) (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
  have hprog : blkPC_b12.rebase b (fun _ => none) = mallocngBlockProg mmpl 12 msvc := by rw [mallocngBlockProg_eq_b12, hb]
  have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1; have hGWf := hwf.groups_wf g hg
  have ⟨hEn48, hIdx31, hBand48, _hBandLo, _hBandHi, _hSub3Hi, _hSub2Lo, _hSub2Hi,
        _hM8Lo, _hM8Hi, _hM4Lo, _hM4Hi, _hM3Lo, _hM3Hi, _hM2Lo, _hM2Hi⟩ :
      (g.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 ∧ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ (g.slotStart idx).toNat ∧ (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (g.slotStart idx).toNat ≤ (g.slotStart idx - 3#64).toNat + 3 ∧
      (g.slotStart idx - 2#64).toNat + 2 ≤ (g.slotStart idx).toNat ∧ (g.slotStart idx).toNat ≤ (g.slotStart idx - 2#64).toNat + 2 ∧
      (new_p - 8#64).toNat + 8 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 8#64).toNat + 8 ∧
      (new_p - 4#64).toNat + 4 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 4#64).toNat + 4 ∧
      (new_p - 3#64).toNat + 3 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 3#64).toNat + 3 ∧
      (new_p - 2#64).toNat + 2 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 2#64).toNat + 2 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf; have ⟨_hIdxCnt, _, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hLast31 : g.lastIdx ≤ 31 := hGWf.2.1; have _hCntEq : g.cnt = g.lastIdx + 1 := rfl; have _hMul1 := Nat.add_one_mul idx g.stride
    have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega); have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 2) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 8) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 4) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 3) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 2) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hNewM3Band := subRegion_of_bounds hBand48 (ea := new_p - 3#64) (subLen := 1) (by omega) (by omega)
  have hStM3Band := subRegion_of_bounds hBand48 (ea := g.slotStart idx - 3#64) (subLen := 1) (by omega) (by omega)
  have hStM2Band := subRegion_of_bounds hBand48 (ea := g.slotStart idx - 2#64) (subLen := 2) (by omega) (by omega)
  have hMaddSt := bv_madd_slotStart (g := g) hIdx31; have _ := hStPlus16; have _ := hNewFitEnd; have _ := hEn48
  wp_step
  refine step_bm8 (pc := b + 0x238#64) (next_pc := b + 0x23c#64) (ea := new_p - 3#64)
    (val := BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx)) hNodup
    (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [evalAddrMode, arm64_norm, hx0]) (by simpa [arm64_norm] using hx5)
    (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1) ?_
  intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1; wp_step; wp_step; wp_step; wp_step
  refine step_bm8 (pc := b + 0x24c#64) (next_pc := b + 0x250#64) (ea := g.slotStart idx - 3#64) (val := 0xe0#8) hNodup
    (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [evalAddrMode, arm64_norm]) (by simp [arm64_norm])
    (fun a ha => (hInBand a (hStM3Band a ha)).2) (fun a ha => (hInBand a (hStM3Band a ha)).1) ?_
  intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
  let fwdW16 : BitVec 16 := (((new_p - g.slotStart idx) >>> 4).truncate 16)
  refine step_bm16 (pc := b + 0x250#64) (next_pc := b + 0x254#64) (ea := g.slotStart idx - 2#64) (val := fwdW16) hNodup
    (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [evalAddrMode, arm64_norm]) (by simp [arm64_norm, fwdW16])
    (fun a ha => (hInBand a (hStM2Band a ha)).2) (fun a ha => (hInBand a (hStM2Band a ha)).1) ?_
  intro m3 hm3 hkf3; have hcl3 := hcl2.of_keepsFrozen hkf3
  refine ldp19_20_to_epilogue (offLdp := 0x254) hb hprog (by wp_close_fetch_cl) (by wp_close_fetch_cl)
    (by bv_arith) rfl (by simp [arm64_norm, hrun]) hcl3 (hm3.trans (hm2.trans (hm1.trans hperm))) (by simp [arm64_norm, hbrk])
    (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0])
    ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
     by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
     by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩ ?_
  have hGeM8 : ∀ a : BitVec 64, (new_p - 8#64).toNat ≤ a.toNat → a ≠ new_p - 3#64 →
      writeBytesToMap (writeBytesToMap (writeBytesToMap bv (new_p - 3#64) [BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx)])
        (g.slotStart idx - 3#64) [0xe0#8]) (g.slotStart idx - 2#64) (unpack16 fwdW16) a = bv a := fun a _haLo haNe => by
    rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp hIn; omega),
        writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
        writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) haNe)]
  have hNe3 : ∀ a : BitVec 64, a.toNat ≠ (new_p - 3#64).toNat → a ≠ new_p - 3#64 := fun _ hn he => hn (congrArg BitVec.toNat he)
  refine ⟨outBand_write hStM2Band (outBand_write hStM3Band (outBand_write hNewM3Band hOut)), ?_, ?_, ?_, ?_⟩
  · rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) _).mp hIn; omega),
        writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
    exact writeBytesToMap_self_one _ _ _
  · dsimp only [] at hHdrOff ⊢; by_cases hTotLe : (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff <;> simp only [hTotLe, ↓reduceIte] at hHdrOff ⊢
    · exact ⟨(hGeM8 _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha; exact hGeM8 a (by omega) (hNe3 a (by omega))).trans hHdrOff.2⟩
    · exact ⟨(hGeM8 _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha; exact hGeM8 a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha; exact hGeM8 a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.2⟩
  · intro h1; have _hNewLenNat : (new_p + len).toNat = new_p.toNat + len.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact (hGeM8 _ (by omega) (hNe3 _ (by omega))).trans (hTrl1 h1)
  · intro h5; have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega); have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
    exact ⟨(hGeM8 _ (by omega) (hNe3 _ (by omega))).trans (hTrl5 h5).1,
      (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha; exact hGeM8 a (by omega) (hNe3 a (by omega))).trans (hTrl5 h5).2⟩

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_deltaPos_tail_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p len : BitVec 64} {eff : Nat}
    (hStPlus16 : (g.slotStart idx).toNat + 16 ≤ new_p.toNat) (hNewFitEnd : new_p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    (hRes31 : (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31)
    {bvHdr : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bvHdr a = st.byteVal a)
    (hHdrOff : let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bvHdr (new_p - 4#64) = 0#8 ∧ readBytesFromMap bvHdr (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bvHdr (new_p - 4#64) = 1#8 ∧ readBytesFromMap bvHdr (new_p - 2#64) 2 = [0#8, 0#8] ∧
        readBytesFromMap bvHdr (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1f8#64) (hrun : s.status = .Running) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk) (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = new_p) (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx3 : s.readReg64 .x3 = g.slotEnd idx) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 g.stride)
    (hx6 : s.readReg64 .x6 = g.mem + 16#64) (hx20 : s.readReg64 .x20 = len) (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bvHdr ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
  have _ := hb; have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1; have hGWf := hwf.groups_wf g hg
  have ⟨hEn48, hIdx31, hBand48, _hBandLo, _hBandHi, _hNewM8Lo, _hNewM8Hi, _hNewM4Lo, _hNewM4Hi,
        _hNewM3Lo, _hNewM3Hi, _hNewM2Lo, _hNewM2Hi⟩ :
      (g.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 ∧ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ (g.slotStart idx).toNat ∧
      (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (new_p - 8#64).toNat + 8 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 8#64).toNat + 8 ∧
      (new_p - 4#64).toNat + 4 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 4#64).toNat + 4 ∧
      (new_p - 3#64).toNat + 3 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 3#64).toNat + 3 ∧
      (new_p - 2#64).toNat + 2 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 2#64).toNat + 2 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf
    have ⟨_hIdxCnt, _, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hLast31 : g.lastIdx ≤ 31 := hGWf.2.1; have _hCntEq : g.cnt = g.lastIdx + 1 := rfl
    have _hMul1 : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.add_one_mul idx g.stride
    have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 8) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 4) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 3) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 2) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hNewM3Band := subRegion_of_bounds hBand48 (ea := new_p - 3#64) (subLen := 1) (by omega) (by omega)
  have hHdrOffLift : ∀ bv : BitVec 64 → BitVec 8, (∀ a : BitVec 64, a.toNat < new_p.toNat → a ≠ new_p - 3#64 → bv a = bvHdr a) →
      let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧ readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot') := fun bv hAg => by
    have hNe3 : ∀ a : BitVec 64, a.toNat ≠ (new_p - 3#64).toNat → a ≠ new_p - 3#64 := fun _ hn he => hn (congrArg BitVec.toNat he)
    dsimp only [] at hHdrOff ⊢; by_cases hTotLe : (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff <;> simp only [hTotLe, ↓reduceIte] at hHdrOff ⊢
    · exact ⟨(hAg _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha; exact hAg a (by omega) (hNe3 a (by omega))).trans hHdrOff.2⟩
    · exact ⟨(hAg _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha; exact hAg a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by have ⟨_, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha; exact hAg a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.2⟩
  let res' := (g.slotEnd idx).toNat - (new_p.toNat + len.toNat)
  have hSubs : (g.slotEnd idx - new_p).truncate 32 - len.truncate 32 = BitVec.ofNat 32 res' := res_subs32_eq hNewFitEnd hEn48
  have hIdxTr8 : ((BitVec.ofNat 32 idx).zeroExtend 64).truncate 8 = BitVec.ofNat 8 idx := by bv_omega
  refine step_bm8 (pc := b + 0x1f8#64) (next_pc := b + 0x1fc#64) (ea := new_p - 3#64) (val := BitVec.ofNat 8 idx) hNodup
    hpc (by bv_arith) hrun (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [evalAddrMode, arm64_norm, hx0]) (by simp only [arm64_norm, hx2]; exact hIdxTr8)
    (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1) ?_
  intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1
  let bv1 := writeBytesToMap bvHdr (new_p - 3#64) [BitVec.ofNat 8 idx]
  have hLowIdx : (BitVec.ofNat 8 idx).zeroExtend 32 &&& 0x1f#32 = BitVec.ofNat 32 idx := by
    simpa using (hdrByte_extract 0 idx (by omega) hIdx31).1
  wp_step; wp_step; wp_step; wp_step
  wp_if hResEq0
  · have hRes0 : res' = 0 := by
      have hEq : (g.slotEnd idx - new_p).truncate 32 - len.truncate 32 = 0#32 := by rw [hResEq0, BitVec.sub_self]
      rw [hSubs] at hEq; have ht := congrArg BitVec.toNat hEq; simp only [BitVec.toNat_ofNat] at ht; omega
    dsimp only [res'] at hRes0
    refine alignedAlloc_reframe_fwd_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hInBand (outBand_write hNewM3Band hOut)
      (hHdrOffLift _ (fun a _ hNe => writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)))
      (fun _ => by omega) (fun _ => by omega)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl1 (hm1.trans hperm) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx4])
      (by simp only [arm64_norm]; rw [hRes0, show (min 0 5 <<< 5) ||| idx = idx by simp]; bv_omega)
      (by simp [arm64_norm, hx6])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
       by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
  · have hResPos : 1 ≤ res' := by
      refine Classical.byContradiction fun hNot => hResEq0 ?_
      have h0 : res' = 0 := by omega
      exact eq_of_sub32_eq_zero (by rw [hSubs, h0])
    have ⟨_hNewLenLo, _hNewLenHi⟩ : (new_p + len).toNat ≤ new_p.toNat + len.toNat ∧ new_p.toNat + len.toNat ≤ (new_p + len).toNat := by
      have h := BitVec.toNat_add new_p len; rw [Nat.mod_eq_of_lt (by omega)] at h; exact ⟨by omega, by omega⟩
    have hNewLenBand := subRegion_of_bounds hBand48 (ea := new_p + len) (subLen := 1) (by omega) (by omega)
    have hEaEnd : g.slotEnd idx + (0#32 - BitVec.ofNat 32 res').signExtend 64 = new_p + len :=
      slotEnd_add_sxtw_neg_res hNewFitEnd hEn48 hResPos hRes31
    wp_step; wp_step
    refine step_bm8 (pc := b + 0x214#64) (next_pc := b + 0x218#64) (ea := new_p + len) (val := 0#8) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm]) (by simp only [evalAddrMode, arm64_norm, hx3, Prod.mk.injEq, and_true]; exact hEaEnd)
      (by simp [arm64_norm]) (fun a ha => (hInBand a (hNewLenBand a ha)).2) (fun a ha => (hInBand a (hNewLenBand a ha)).1) ?_
    intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
    let bv2 := writeBytesToMap bv1 (new_p + len) [0#8]
    wp_step
    wp_if hLe4
    · have hResLe4 : res' ≤ 4 := by rwa [bv32_sle4_iff hRes31, decide_eq_true_eq] at hLe4
      conv => arg 4; rw [byteMap_focus8 hNodup bv2 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; rw [← byteMap_focus8 hNodup bv2 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      have hBv2M3 : bv2 (new_p - 3#64) = BitVec.ofNat 8 idx := by
        dsimp only [bv2, bv1]
        rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
        exact writeBytesToMap_self_one _ _ _
      have hPack := hdr3_pack_le4 (hBv2M3.symm ▸ hLowIdx) hIdx31 hResPos hResLe4
      refine alignedAlloc_reframe_fwd_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hInBand
        (outBand_write hNewLenBand (outBand_write hNewM3Band hOut))
        (hHdrOffLift _ (fun a _haLt hNe => by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)]))
        (fun _ => writeBytesToMap_self_one _ _ _) (fun _ => by omega)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl2 (hm2.trans (hm1.trans hperm)) (by simp [arm64_norm, hbrk])
        (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx4])
        (by simp only [arm64_norm]; exact hPack) (by simp [arm64_norm, hx6])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
         by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
    · have hResGe5 : 5 ≤ res' := by rw [bv32_sle4_iff hRes31, decide_eq_true_eq] at hLe4; omega
      have ⟨_hEnM5Lo, _hEnM5Hi, _hEnM4Lo, _hEnM4Hi⟩ :
          (g.slotEnd idx - 5#64).toNat + 5 ≤ (g.slotEnd idx).toNat ∧ (g.slotEnd idx).toNat ≤ (g.slotEnd idx - 5#64).toNat + 5 ∧
          (g.slotEnd idx - 4#64).toNat + 4 ≤ (g.slotEnd idx).toNat ∧ (g.slotEnd idx).toNat ≤ (g.slotEnd idx - 4#64).toNat + 4 := by
        have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega)
        have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
        exact ⟨by omega, by omega, by omega, by omega⟩
      have hEnM5Band := subRegion_of_bounds hBand48 (ea := g.slotEnd idx - 5#64) (subLen := 1) (by omega) (by omega)
      have hEnM4Band := subRegion_of_bounds hBand48 (ea := g.slotEnd idx - 4#64) (subLen := 4) (by omega) (by omega)
      refine step_bm8 (pc := b + 0x21c#64) (next_pc := b + 0x220#64) (ea := g.slotEnd idx - 5#64) (val := 0#8) hNodup
        (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm]) (by simp only [evalAddrMode, arm64_norm, hx3]) (by simp [arm64_norm])
        (fun a ha => (hInBand a (hEnM5Band a ha)).2) (fun a ha => (hInBand a (hEnM5Band a ha)).1) ?_
      intro m3 hm3 hkf3; have hcl3 := hcl2.of_keepsFrozen hkf3
      refine step_bm32 (pc := b + 0x220#64) (next_pc := b + 0x224#64) (ea := g.slotEnd idx - 4#64) (val := BitVec.ofNat 32 res') hNodup
        (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm]) (by simp only [evalAddrMode, arm64_norm, hx3]) (by simp [arm64_norm])
        (fun a ha => (hInBand a (hEnM4Band a ha)).2) (fun a ha => (hInBand a (hEnM4Band a ha)).1) ?_
      intro m4 hm4 hkf4; have hcl4 := hcl3.of_keepsFrozen hkf4
      let bv4 := writeBytesToMap (writeBytesToMap bv2 (g.slotEnd idx - 5#64) [0#8]) (g.slotEnd idx - 4#64) (unpack32 (BitVec.ofNat 32 res'))
      conv => arg 4; rw [byteMap_focus8 hNodup bv4 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      wp_step; wp_step; wp_step; wp_step
      conv => arg 4; rw [← byteMap_focus8 hNodup bv4 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      have hBv4M3 : bv4 (new_p - 3#64) = BitVec.ofNat 8 idx := by
        dsimp only [bv4, bv2, bv1]
        rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
        exact writeBytesToMap_self_one _ _ _
      have hPack5 := hdr3_pack_ge5 (hBv4M3.symm ▸ hLowIdx) hIdx31 hResGe5
      refine alignedAlloc_reframe_fwd_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hInBand
        (outBand_write hEnM4Band (outBand_write hEnM5Band (outBand_write hNewLenBand (outBand_write hNewM3Band hOut))))
        (hHdrOffLift _ (fun a _haLt hNe => by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)]))
        (fun _ => by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega)]
          by_cases hEq5 : new_p + len = g.slotEnd idx - 5#64
          · rw [hEq5]; exact writeBytesToMap_self_one _ _ _
          · rw [writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hEq5)]; exact writeBytesToMap_self_one _ _ _)
        (fun _ => ⟨by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega)]
          exact writeBytesToMap_self_one _ _ _,
          readBytesFromMap_writeBytesToMap _ _ (unpack32 (BitVec.ofNat 32 res')) (by simp)⟩)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl4
        (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))) (by simp [arm64_norm, hbrk])
        (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx4])
        (by simp only [arm64_norm]; exact hPack5) (by simp [arm64_norm, hx6])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
         by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_deltaPos_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt} {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p delta new_p len : BitVec 64} {eff : Nat} (hNewEq : new_p = p + delta)
    (hStPlus16 : (g.slotStart idx).toNat + 16 ≤ new_p.toNat) (hNewFitEnd : new_p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    (hRes31 : (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31)
    (hLargeProps : ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff → g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27)
    {bv0 : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut0 : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv0 a = st.byteVal a)
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1d8#64) (hrun : s.status = .Running) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk) (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = p) (hx1 : s.readReg64 .x1 = delta) (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx3 : s.readReg64 .x3 = g.slotEnd idx) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 g.stride)
    (hx6 : s.readReg64 .x6 = g.mem + 16#64) (hx20 : s.readReg64 .x20 = len) (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
  have _ := hb; have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1; have hGWf := hwf.groups_wf g hg
  have ⟨hBand48, _hStorLo, _hNew48, _hBandLo, _hBandHi, _hM8Lo, _hM8Hi, _hM4Lo, _hM4Hi, _hM2Lo, _hM2Hi⟩ :
      (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧ g.storage.toNat ≤ new_p.toNat ∧ new_p.toNat ≤ 2 ^ 48 ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ (g.slotStart idx).toNat ∧ (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (new_p - 8#64).toNat + 8 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 8#64).toNat + 8 ∧
      (new_p - 4#64).toNat + 4 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 4#64).toNat + 4 ∧
      (new_p - 2#64).toNat + 2 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 2#64).toNat + 2 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf; have ⟨_, _hStorNat, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hMul1 := Nat.add_one_mul idx g.stride; have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 8) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 4) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 2) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hNewM8Band := subRegion_of_bounds hBand48 (ea := new_p - 8#64) (subLen := 4) (by omega) (by omega)
  have hNewM4Band := subRegion_of_bounds hBand48 (ea := new_p - 4#64) (subLen := 1) (by omega) (by omega)
  have hNewM2Band := subRegion_of_bounds hBand48 (ea := new_p - 2#64) (subLen := 2) (by omega) (by omega)
  let tot' := (new_p.toNat - g.storage.toNat) / 16
  have hTot27 : tot' < 2 ^ 27 := by by_cases hLe : tot' ≤ 0xffff <;> [omega; exact (hLargeProps hLe).2.2]
  have hNewSymm : p + delta = new_p := hNewEq.symm; clear hNewEq; have hStorEq : g.mem + 16#64 = g.storage := rfl
  have hLsr : (new_p - g.storage) >>> 4 = BitVec.ofNat 64 tot' := tot_lsr4_eq (by omega) (by omega)
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_if hHi
  · have hNotLe : ¬ tot' ≤ 0xffff := by
      have hUlt : (0xffff#32).ult (BitVec.ofNat 32 tot') = true := by simpa using hHi
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hUlt; change 65535 < tot' % 4294967296 at hUlt; omega
    wp_step
    refine step_bm32 (pc := b + 0x2c4#64) (next_pc := b + 0x2c8#64) (ea := new_p - 8#64) (val := BitVec.ofNat 32 tot') hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm]) (by simp only [arm64_norm]; bv_omega)
      (fun a ha => (hInBand a (hNewM8Band a ha)).2) (fun a ha => (hInBand a (hNewM8Band a ha)).1) ?_
    intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1
    refine step_bm8 (pc := b + 0x2c8#64) (next_pc := b + 0x2cc#64) (ea := new_p - 4#64) (val := 1#8) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm]) (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewM4Band a ha)).2) (fun a ha => (hInBand a (hNewM4Band a ha)).1) ?_
    intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
    refine step_bm16 (pc := b + 0x2cc#64) (next_pc := b + 0x2d0#64) (ea := new_p - 2#64) (val := 0#16) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm]) (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewM2Band a ha)).2) (fun a ha => (hInBand a (hNewM2Band a ha)).1) ?_
    intro m3 hm3 hkf3; have hcl3 := hcl2.of_keepsFrozen hkf3; wp_step
    refine alignedAlloc_reframe_deltaPos_tail_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hRes31 hInBand
      (outBand_write hNewM2Band (outBand_write hNewM4Band (outBand_write hNewM8Band hOut0)))
      (by simp only [show ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff from hNotLe, ↓reduceIte]
          refine ⟨by rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) _).mp hIn; omega)]
                     exact writeBytesToMap_self_one _ _ _, readBytesFromMap_writeBytesToMap _ _ (unpack16 0#16) (by simp),
            (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
              have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha
              rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp hIn; omega),
                  writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega)]).trans
              (readBytesFromMap_writeBytesToMap _ _ (unpack32 (BitVec.ofNat 32 tot')) (by simp))⟩)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl3 (hm3.trans (hm2.trans (hm1.trans hperm))) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm]) (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx3]) (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hx6]) (by simp [arm64_norm, hx20])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
  · have hLe : tot' ≤ 0xffff := by
      refine Classical.byContradiction fun hNot => hHi ?_
      suffices (0xffff#32).ult (BitVec.ofNat 32 tot') = true by simpa using this
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change 65535 < tot' % 4294967296; omega
    refine step_bm8 (pc := b + 0x1f0#64) (next_pc := b + 0x1f4#64) (ea := new_p - 4#64) (val := 0#8) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm]) (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewM4Band a ha)).2) (fun a ha => (hInBand a (hNewM4Band a ha)).1) ?_
    intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1
    refine step_bm16 (pc := b + 0x1f4#64) (next_pc := b + 0x1f8#64) (ea := new_p - 2#64) (val := BitVec.ofNat 16 tot') hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl) (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm]) (by simp only [arm64_norm]; bv_omega)
      (fun a ha => (hInBand a (hNewM2Band a ha)).2) (fun a ha => (hInBand a (hNewM2Band a ha)).1) ?_
    intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
    refine alignedAlloc_reframe_deltaPos_tail_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hRes31 hInBand
      (outBand_write hNewM2Band (outBand_write hNewM4Band hOut0))
      (by simp only [show (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff from hLe, ↓reduceIte]
          exact ⟨by rw [writeBytesToMap_out _ _ _ (fun hIn => by have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) _).mp hIn; omega)]
                    exact writeBytesToMap_self_one _ _ _, readBytesFromMap_writeBytesToMap _ _ (unpack16 (BitVec.ofNat 16 tot')) (by simp)⟩)
      rfl (by simp [arm64_norm, hrun]) hcl2 (hm2.trans (hm1.trans hperm)) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm]) (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx3]) (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hx6]) (by simp [arm64_norm, hx20])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩

private theorem sbfm_idx_add1 {idx : Nat} (hIdx31 : idx ≤ 31) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 idx + 1#32) &&& 0xffffffff#64 |||
      (if (BitVec.ofNat 32 idx + 1#32)[31] = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) =
    (((BitVec.ofNat 32 idx).zeroExtend 64 + 1#64).truncate 32).signExtend 64 := by
  have hb31 : (BitVec.ofNat 32 idx + 1#32)[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat]; apply Nat.testBit_lt_two_pow
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; change (idx % 4294967296 + 1) % 4294967296 < 2147483648; omega
  have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
  rw [hb31]; revert hlt; bv_robdd

namespace AlignedReframeHelpers
set_option maxHeartbeats 400000 in
theorem alignedAlloc_reframe_fine_ok [MallocngMultiPlacement] {prog : Program}
    {b : BitVec 64} (hb : BlkBase 12 b) (hprog : prog = mallocngBlockProg mmpl 12 msvc)
    (γ : GhostName) {tp brkStart align len : BitVec 64} {bud : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {bCoarse : MallocngBudget} {st0 st' : MallocngSt} {g' : GroupDesc} {idx : Nat}
    {p : BitVec 64} {bs : List (BitVec 8)} {s0 s4 : State}
    (hwf : MallocngWF maddrs.base brkStart s4.brk bCoarse.liveCost bCoarse.peakCost st')
    (hRaw : MallocImplFineRawRel maddrs.base brkStart bud ivs0 alignMap0 st0 st' g' idx (mallocngAlignedEffSize align.toNat len.toNat) p)
    (hBsLen : bs.length = mallocngAlignedEffSize align.toNat len.toNat)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64) {sp0 : BitVec 64} {oom : State → SepProp}
    (hpc : s4.pc = b + 0x1b4#64) (hrun : s4.status = .Running) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem)
    (hsp : s4.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s4.readReg64 .x0 = p) (hx2 : s4.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s4.readReg64 .x4 = BitVec.ofNat 64 g'.stride) (hx6 : s4.readReg64 .x6 = g'.mem)
    (hx19 : s4.readReg64 .x19 = if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64)
    (hx20 : s4.readReg64 .x20 = len) (hcs21_28 : CalleeSaved21_28 s0 s4) :
    let eff := mallocngAlignedEffSize align.toNat len.toNat; let bf := FineBudget.stepAligned align.toNat len.toNat bud
    SepWP prog (s0.readReg64 .lr) s4
      (ghostMapAuth (fineAlignGam γ) alignMap0 ∗ MallocngRoTablesA maddrs ∗
       MallocngCoreStA (fineBaseGam γ) maddrs brkStart s4.brk bCoarse.liveCost bCoarse.peakCost st' ∗
       MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
       stackFrameAt (sp0 - 32#64) 704 ∗ AlignedSpillSlots sp0 s0)
      (fun sf Pf =>
        (∃ new_p : BitVec 64, sf.readReg64 .x0 = new_p ∧ (FineBlockSem γ).pureWf new_p (len.toNat, max align.toNat 16) ∧
          (Pf ⊢ stackFrameAt sp0 736 ∗ FineCoreImpl γ maddrs brkStart sf.brk bf (dynamicRootRegions st') ∗
            MallocngRuntime maddrs tp ∗ (FineBlockSem γ).interp new_p (len.toNat, max align.toNat 16))) ∧
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem ∧ sf.mem.perm = s4.mem.perm ∧
        sf.brk = s4.brk ∧ MallocngProcPreserved s4 sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  intro eff bf
  have hProgEq : prog = blkPC_b12.rebase b (fun _ => none) := by rw [hprog, mallocngBlockProg_eq_b12, hb]
  subst hProgEq
  have ⟨_, _, _, _, hg', ⟨hIdx, hSlot⟩, hOff255, _, hSc63, _⟩ := hRaw
  have hGWf := hwf.groups_wf g' hg'; have ⟨hStr16, _⟩ := group_stride_pos_and_align hGWf
  have ⟨hEn48, hIdx31⟩ : (g'.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 := by
    have ⟨_hIdxCnt, _, _, _, _, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hLast31 : g'.lastIdx ≤ 31 := hGWf.2.1; have _hCntEq : g'.cnt = g'.lastIdx + 1 := rfl; exact ⟨by omega, by omega⟩
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hBlkP : MallocngBlockWf p eff := hSWf.2.2.2.2.1; have _hPLo := hSWf.2.2.2.2.2.1; have _hPHi := hSWf.2.2.2.2.2.2.1
  let a16 : BitVec 64 := if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
  let delta : BitVec 64 := (0#64 - p) &&& (a16 - 1#64); let new_p : BitVec 64 := p + delta
  obtain ⟨_, hDelta16, _, hNewNat, hNewFitEff, hAlignDvd, hBlkNew, _⟩ := alignedAlloc_snap_props hAlignOk hAlignMax hNoOvf hBlkP
  have ⟨_hNewLo, _hNewHi⟩ : new_p.toNat ≤ p.toNat + delta.toNat ∧ p.toNat + delta.toNat ≤ new_p.toNat := ⟨Nat.le_of_eq hNewNat, Nat.le_of_eq hNewNat.symm⟩
  clear hNewNat; change 16 ∣ delta.toNat at hDelta16; change new_p.toNat + len.toNat ≤ p.toNat + eff at hNewFitEff
  change max align.toNat 16 ∣ new_p.toNat at hAlignDvd; change MallocngBlockWf new_p len.toNat at hBlkNew
  obtain ⟨hRes31, hLargeProps⟩ := alignedAlloc_reframe_bounds hwf hg' hIdx hSlot hOff255 hSc63 hAlignOk hAlignMax hNoOvf
  change (g'.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31 at hRes31
  change ¬ (new_p.toNat - g'.storage.toNat) / 16 ≤ 0xffff → g'.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g'.storage.toNat) / 16 < 2 ^ 27 at hLargeProps
  obtain ⟨hAbsEq, hInBand, hOut0, hLtP0⟩ := alignedAlloc_absorb_user_pre hwf hg' hIdx hSlot hBsLen
  let bv0 := writeBytesToMap st'.byteVal p bs
  let Rest := ghostMapAuth (fineAlignGam γ) alignMap0 ∗ MallocngRoTablesA maddrs ∗
    MallocngLiveAuth (fineBaseGam γ) st'.liveMap ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
    (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState (fineBaseGam γ) st'.auxvPtr st'.auxvSnap ∗
    ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st') ∗
    MallocngRuntime maddrs tp ∗ stackFrameAt (sp0 - 32#64) 704
  have hPreRearr :
      (ghostMapAuth (fineAlignGam γ) alignMap0 ∗ MallocngRoTablesA maddrs ∗
       MallocngCoreStA (fineBaseGam γ) maddrs brkStart s4.brk bCoarse.liveCost bCoarse.peakCost st' ∗
       MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockToken (fineBaseGam γ) p eff ∗
       stackFrameAt (sp0 - 32#64) 704 ∗ AlignedSpillSlots sp0 s0) ⊢
      (ByteMap st'.masterDom (alignedSlotKeep st' p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest) := by
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA, Rest, bv0]; rw [pure_sepConj_of_true hwf, ← hAbsEq]; exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hPreRearr ?_
  have hSlotEndEq : g'.mem + 16#64 + (BitVec.setWidth 64 (BitVec.ofNat 32 idx + 1#32) &&& 0xffffffff#64 |||
      (if (BitVec.ofNat 32 idx + 1#32)[31] = true then 0xffffffffffffffff#64 else 0#64) &&& 0xffffffff00000000#64) *
      BitVec.ofNat 64 g'.stride - 4#64 = g'.slotEnd idx := by rw [sbfm_idx_add1 hIdx31]; exact bv_madd_slotEnd hStr16 hEn48 hIdx31
  have hRun : SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s4
      (ByteMap st'.masterDom (alignedSlotKeep st' p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st' p eff Rest (ReframeBvSpec st' g' idx new_p len)) oom := by
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hDeltaEq0
    · have hD0 : delta = 0#64 := by simpa [arm64_norm, hx0, hx19, delta, a16] using hDeltaEq0
      have hNewP : new_p = p := by dsimp only [new_p]; rw [hD0, BitVec.add_zero]
      rw [hNewP]
      exact alignedAlloc_reframe_delta0_ok hb hprog hwf hg' hIdx hSlot (by rw [← hNewP]; omega) (by rw [← hNewP]; exact hRes31) hInBand hOut0 hLtP0
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl rfl (by simp [arm64_norm]) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2])
        (by simpa [arm64_norm, hx2, hx4, hx6] using hSlotEndEq) (by simp [arm64_norm, hx20])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
    · have hDNe0 : delta ≠ 0#64 := fun hz => hDeltaEq0 (by simpa [arm64_norm, hx0, hx19, delta, a16] using hz)
      have _hDPos : 0 < delta.toNat := Nat.pos_of_ne_zero fun hz => hDNe0 (BitVec.eq_of_toNat_eq hz)
      have ⟨_qD, _hqD⟩ := hDelta16
      exact alignedAlloc_reframe_deltaPos_ok (p := p) (delta := delta) (new_p := new_p) (len := len)
        hb hwf hg' hIdx rfl (by omega) (Nat.le_trans hNewFitEff _hPHi) hRes31 hLargeProps hInBand hOut0
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl rfl (by simp [arm64_norm]) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0]) (by simp [arm64_norm, delta, a16])
        (by simp [arm64_norm, hx2]) (by simpa [arm64_norm, hx2, hx4, hx6] using hSlotEndEq)
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm]) (by simp [arm64_norm, hx20])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
  refine SepWP.seq hRun ?_
  rintro sf Pf hpc_f hrun_f ⟨bv, ⟨hOut, hHdr3, hHdrOff, hTrl1, hTrl5⟩, hEnt, hcl_f, hperm_f, hbrk_f, hproc_f, hx0_f, hsp_f, hcs_f⟩
  refine SepWP.weaken_pre hEnt ?_
  have hFinish := alignedAlloc_reframe_fine_finish (A := maddrs) (brkStart := brkStart) (brk := sf.brk)
    (bCoarse := bCoarse) (b := bud) (ivs0 := ivs0) (alignMap0 := alignMap0) (st0 := st0) (st' := st')
    γ (hbrk_f ▸ hwf) hRaw hAlignOk hAlignMax hNoOvf rfl hOut hHdr3 hHdrOff hTrl1 hTrl5
  refine SepWP.bupd_pre (Q := stackFrameAt sp0 736 ∗ FineCoreImpl γ maddrs brkStart sf.brk bf (dynamicRootRegions st') ∗
      MallocngRuntime maddrs tp ∗ (FineBlockSem γ).interp new_p (len.toNat, max align.toNat 16)) ?_ ?_
  · refine Entails.trans ?_ (Entails.trans (sepConj_mono_left hFinish)
      (Entails.trans (bupd_frame_r _ (MallocngRuntime maddrs tp ∗ stackFrameAt sp0 736)) (bupd_mono ?_)))
    · have hStk := spillSlots_repack_736 sp0 s0; dsimp only [Rest, eff]
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_right hStk))
    · dsimp only [FineBlockSem, bf]; exact Entails.of_eq (by ac_rfl)
  · have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    refine SepWP.done hpc_f hrun_f ⟨⟨new_p, hx0_f, ⟨hBlkNew.1, hAlignDvd, by have := hBlkNew.2.2.1; omega⟩, Entails.refl _⟩,
       hcl_f, hperm_f, hbrk_f, hproc_f, hsp_f, hcs_f⟩
end AlignedReframeHelpers

end LibsignalBinary.Heap.Fine
