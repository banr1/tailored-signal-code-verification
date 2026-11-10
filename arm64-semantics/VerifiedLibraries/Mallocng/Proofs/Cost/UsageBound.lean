/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.UsageForest
public import VerifiedLibraries.Mallocng.Proofs.TryAvailHelpers

/-!
# Per-Class Non-Free Slot Bound

Bounds the number of non-free slots of any size class by the total leaf (`.liveUser` and
`.claimed`) slots in the heap via a nesting-forest injection (`nonFreeSlots_le`), and derives the
`usage_by_class[sc]` bound at `alloc_group` entry (`ctx.active[sc] = 0`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost

open Arm64 VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Forest Injection -/

section Forest

variable {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}

private theorem sum_map_one {α : Type} (xs : List α) : (xs.map fun _ => 1).sum = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]; omega

private theorem nonFree_le_descW
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    ∀ (n : Nat) {g : GroupDesc}, g ∈ st.groups → g.sc < n → groupNonFree g ≤ descW st g.metaPtr
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, g, hg, hlt => by
    rw [groupNonFree_eq]
    have hSplit := accounting_sum_filter_partition (fun x => x.metaPtr == g.metaPtr) groupLeaf
      (st.groups.filter (descB st g.metaPtr))
    have hSelf : groupLeaf g ≤
        (((st.groups.filter (descB st g.metaPtr)).filter
          (fun x => x.metaPtr == g.metaPtr)).map groupLeaf).sum :=
      accounting_le_sum_of_mem (List.mem_map_of_mem (List.mem_filter.mpr
        ⟨List.mem_filter.mpr ⟨hg, descB_iff.mpr ⟨0, rfl⟩⟩, by simp⟩))
    have hdisj : ∀ y₁ ∈ childMetas g, ∀ y₂ ∈ childMetas g, ∀ x,
        descB st y₁ x = true → descB st y₂ x = true → y₁ = y₂ :=
      fun y₁ h₁ y₂ h₂ x hx₁ hx₂ =>
        child_desc_eq hwf hg h₁ h₂ (descB_iff.mp hx₁) (descB_iff.mp hx₂)
    have hsub : ∀ y ∈ childMetas g, ∀ x, descB st y x = true →
        (fun x => descB st g.metaPtr x && !(x.metaPtr == g.metaPtr)) x = true := by
      intro y hy x hx
      obtain ⟨hD, hNe⟩ := child_desc_sub hwf hg hy (descB_iff.mp hx)
      simp [descB_iff.mpr hD, hNe]
    have hFib := sum_fibers_le (descB st) _ groupLeaf st.groups (childMetas_nodup hwf hg) hdisj hsub
    have hFF : ((st.groups.filter (descB st g.metaPtr)).filter
        (fun x => !(x.metaPtr == g.metaPtr))) =
        st.groups.filter (fun x => descB st g.metaPtr x && !(x.metaPtr == g.metaPtr)) := by
      rw [List.filter_filter]; congr 1; funext x; exact Bool.and_comm _ _
    rw [hFF] at hSplit
    have hKids : (childMetas g).length ≤
        ((childMetas g).map fun y => ((st.groups.filter (descB st y)).map groupLeaf).sum).sum := by
      rw [← sum_map_one (childMetas g)]
      refine accounting_sum_map_le fun y hy => ?_
      obtain ⟨cg, hcg, hM, _, hLt, hNE⟩ := child_info hwf hg hy
      have hPos : 1 ≤ groupNonFree cg := by
        obtain ⟨s, hsMem, hsF⟩ : ∃ s ∈ cg.slots, s.isFree = false := by
          unfold GroupDesc.isEmpty at hNE
          simpa using hNE
        have : slotNonFree s = 1 := by cases s <;> simp_all [SlotState.isFree, slotNonFree]
        exact this ▸ accounting_le_sum_of_mem (List.mem_map_of_mem hsMem)
      have hIH := nonFree_le_descW hwf n hcg (by omega)
      rw [hM] at hIH
      exact Nat.le_trans hPos hIH
    unfold descW
    omega

/-- Non-free slots of any size class are bounded by the heap's leaf slots. -/
theorem nonFreeSlots_le
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (sc : Nat) :
    nonFreeSlots st sc ≤ totalLiveCount st + totalClaimedSlots st := by
  rw [← sum_groupLeaf_eq]
  have hEach : ∀ g ∈ st.groups.filter (·.sc == sc), groupNonFree g ≤ descW st g.metaPtr :=
    fun g hg => nonFree_le_descW hwf (g.sc + 1) (List.mem_filter.mp hg).1 (Nat.lt_succ_self _)
  have h1 := accounting_sum_map_le hEach
  have hNd : ((st.groups.filter (·.sc == sc)).map (·.metaPtr)).Nodup :=
    (List.filter_sublist.map _).nodup hwf.groups_nodup.1
  have hdisj : ∀ y₁ ∈ (st.groups.filter (·.sc == sc)).map (·.metaPtr),
      ∀ y₂ ∈ (st.groups.filter (·.sc == sc)).map (·.metaPtr), ∀ x,
        descB st y₁ x = true → descB st y₂ x = true → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ x hx₁ hx₂
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h₁
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h₂
    have ⟨ha1, ha2⟩ := List.mem_filter.mp ha
    have ⟨hb1, hb2⟩ := List.mem_filter.mp hb
    exact same_sc_desc_eq hwf ha1 hb1 (by simp at ha2 hb2; omega)
      (descB_iff.mp hx₁) (descB_iff.mp hx₂)
  have h2 := sum_fibers_le (descB st) (fun _ => true) groupLeaf st.groups hNd hdisj (fun _ _ _ _ => rfl)
  rw [List.filter_eq_self.mpr (fun _ _ => rfl), List.map_map] at h2
  unfold nonFreeSlots
  exact Nat.le_trans h1 h2

end Forest

/-! ## `usage_by_class` at `alloc_group` Entry -/

section Usage

variable {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}

private theorem groupNonFree_of_masks_zero {g : GroupDesc} (hGWf : GroupWf st g)
    (hA : g.availMask = 0#32) (hF : g.freedMask = 0#32) : groupNonFree g = g.cnt := by
  have hAll : ∀ s ∈ g.slots, slotNonFree s = 1 := by
    intro s hs
    obtain ⟨idx, hIdx, hEq⟩ := List.getElem_of_mem hs
    have hSWf := hGWf.slot_wf idx hIdx
    rw [hEq] at hSWf
    have hNA : s ≠ .freeAvail := fun h => by
      have := hSWf.2.1.mpr h; rw [hA] at this; simp at this
    have hNI : s ≠ .freeInactive := fun h => by
      have := hSWf.2.2.1.mpr h; rw [hF] at this; simp at this
    cases s <;> simp_all [slotNonFree]
  unfold groupNonFree
  rw [List.map_congr_left hAll, sum_map_one]
  exact hGWf.2.2.1

/-- With `ctx.active[sc] = 0`, every class-`sc` group is full, so `usage_by_class[sc]` counts
    exactly the non-free slots of class `sc`. -/
theorem usage_eq_nonFreeSlots_of_active_zero
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) {sc : Nat}
    (hscU : sc < st.ctx.usageByClass.length)
    (hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64) :
    (st.ctx.usageByClass[sc]'hscU).toNat = nonFreeSlots st sc := by
  obtain ⟨hLA, hLU, _, _, _, hLL⟩ := hwf.ctx_lens
  have hscA : sc < st.ctx.active.length := by omega
  have hscL : sc < st.activeLists.length := by omega
  have hAct := hwf.active_wf sc hscA hscL
  have hNil : st.activeLists[sc]'hscL = [] := by
    have hN := (CircularDllWf.head_eq_zero_iff hAct.2.1).mp (hAct0 hscA)
    exact List.eq_nil_of_length_eq_zero (hAct.2.2.1.symm.trans (by simp [hN]))
  rw [hwf.usage_wf sc hscU]
  unfold nonFreeSlots
  congr 1
  refine List.map_congr_left fun g hg => ?_
  have ⟨hgIn, hgSc⟩ := List.mem_filter.mp hg
  have hgSc' : g.sc = sc := by simpa using hgSc
  have hOut : g.metaPtr ∉ st.activeLists[sc]'hscL := by rw [hNil]; simp
  obtain ⟨hA, hF, _⟩ := (hAct.2.2.2.1 g hgIn hgSc').2 hOut
  exact (groupNonFree_of_masks_zero (hwf.groups_wf g hgIn) hA hF).symm

theorem usage_le_live_add_claimed_of_active_zero
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) {sc : Nat}
    (hscU : sc < st.ctx.usageByClass.length)
    (hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64) :
    (st.ctx.usageByClass[sc]'hscU).toNat ≤ totalLiveCount st + totalClaimedSlots st := by
  rw [usage_eq_nonFreeSlots_of_active_zero hwf hscU hAct0]
  exact nonFreeSlots_le hwf sc

theorem totalClaimedSlots_le_inflight
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    totalClaimedSlots st ≤ inflight := by
  have := hwf.inflight_wf; omega

theorem usage_le_peak_add_inflight_of_active_zero
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) {sc : Nat}
    (hscU : sc < st.ctx.usageByClass.length)
    (hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64)
    {peakCount : Nat} (hCount : totalLiveCount st ≤ peakCount) :
    (st.ctx.usageByClass[sc]'hscU).toNat ≤ peakCount + inflight := by
  have h1 := usage_le_live_add_claimed_of_active_zero hwf hscU hAct0
  have h2 := totalClaimedSlots_le_inflight hwf
  omega

theorem usage_le_peak_add_six_of_active_zero
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) {sc : Nat}
    (hscU : sc < st.ctx.usageByClass.length)
    (hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64)
    {peakCount : Nat} (hCount : totalLiveCount st ≤ peakCount) (hInfl : inflight ≤ 6) :
    (st.ctx.usageByClass[sc]'hscU).toNat ≤ peakCount + 6 := by
  have := usage_le_peak_add_inflight_of_active_zero hwf hscU hAct0 hCount
  omega

end Usage

end VerifiedLibraries.Mallocng.Proofs.Cost
