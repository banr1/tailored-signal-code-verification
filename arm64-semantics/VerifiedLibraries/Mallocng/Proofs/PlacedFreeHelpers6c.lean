/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedFreeHelpers6b

/-!
# Group Dequeue Invariant and Non-General Dequeue Paths for `nontrivial_free`

Defines the intermediate `DequeueOutcome` invariant reached after unlinking an all-free group `g`
and decrementing `ctx.usageByClass[g.sc]`, and establishes it for `mmap`-backed (`g.sc = 63`),
unqueued (`g.next = 0`), and singleton (`g.next = g.metaPtr`) groups.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `DequeueOutcome` and Group Removal -/

def filterOutGroup (gs : List GroupDesc) (m : BitVec 64) : List GroupDesc :=
  gs.filter fun h => !(h.metaPtr == m)

theorem filterOutGroup_props {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    (hMemNd : (gs.map (·.mem)).Nodup) {g : GroupDesc} (hg : g ∈ gs) :
    let gs' := filterOutGroup gs g.metaPtr
    (gs'.map (·.metaPtr)).Nodup ∧
    (gs'.map (·.mem)).Nodup ∧
    (∀ x, x ∈ gs'.map (·.metaPtr) ↔ (x ∈ gs.map (·.metaPtr) ∧ x ≠ g.metaPtr)) ∧
    (∀ h, h ∈ gs' ↔ (h ∈ gs ∧ h.metaPtr ≠ g.metaPtr)) ∧
    (∀ f : GroupDesc → Nat, (gs'.map f).sum + f g = (gs.map f).sum) ∧
    (∀ sc : Nat,
      ((gs'.filter (·.sc == sc)).map GroupDesc.cnt).sum +
        (if g.sc = sc then g.cnt else 0) =
      ((gs.filter (·.sc == sc)).map GroupDesc.cnt).sum) ∧
    (∀ m : BitVec 64, m ≠ g.metaPtr →
      gs'.find? (·.metaPtr == m) = gs.find? (·.metaPtr == m)) := by
  obtain ⟨pre, post, hEq, hPreNe, hPostNe, _, hFilt⟩ := split_groups_at_mem hNd hg
  dsimp only [filterOutGroup]
  rw [hFilt]
  rw [hEq]
  have hNdMap : ((pre ++ post).map (·.metaPtr)).Nodup := by
    rw [hEq, List.map_append, List.map_cons, List.nodup_append] at hNd
    obtain ⟨h1, h2, hD⟩ := hNd
    rw [List.map_append]
    exact List.nodup_append.mpr ⟨h1, (List.nodup_cons.mp h2).2,
      fun x hx y hy => hD x hx y (List.mem_cons_of_mem _ hy)⟩
  have hNdMem : ((pre ++ post).map (·.mem)).Nodup := by
    rw [hEq, List.map_append, List.map_cons, List.nodup_append] at hMemNd
    obtain ⟨h1, h2, hD⟩ := hMemNd
    rw [List.map_append]
    exact List.nodup_append.mpr ⟨h1, (List.nodup_cons.mp h2).2,
      fun x hx y hy => hD x hx y (List.mem_cons_of_mem _ hy)⟩
  refine ⟨hNdMap, hNdMem, fun x => ?_, fun h => ?_, fun f => ?_, fun sc => ?_, fun m hmNe => ?_⟩
  · constructor
    · intro hx
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hh with hp | hq
      · exact ⟨List.mem_map_of_mem (List.mem_append_left _ hp), hPreNe h hp⟩
      · exact ⟨List.mem_map_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ hq)), hPostNe h hq⟩
    · rintro ⟨hx, hxNe⟩
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hh with hp | hcq
      · exact List.mem_map_of_mem (List.mem_append_left _ hp)
      · rcases List.mem_cons.mp hcq with rfl | hq
        · exact False.elim (hxNe rfl)
        · exact List.mem_map_of_mem (List.mem_append_right _ hq)
  · constructor
    · intro hh
      rcases List.mem_append.mp hh with hp | hq
      · exact ⟨List.mem_append_left _ hp, hPreNe h hp⟩
      · exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _ hq), hPostNe h hq⟩
    · rintro ⟨hh, hNe⟩
      rcases List.mem_append.mp hh with hp | hcq
      · exact List.mem_append_left _ hp
      · rcases List.mem_cons.mp hcq with rfl | hq
        · exact False.elim (hNe rfl)
        · exact List.mem_append_right _ hq
  · simp [List.map_append, List.sum_append]
    omega
  · simp only [List.filter_append, List.filter_cons, List.map_append, List.sum_append]
    by_cases hSc : g.sc = sc
    · subst hSc; simp; omega
    · have hB : (g.sc == sc) = false := beq_false_of_ne hSc
      simp [hSc, hB]
  · rw [List.find?_append, List.find?_append, List.find?_cons]
    have hB : (g.metaPtr == m) = false := beq_false_of_ne (Ne.symm hmNe)
    simp [hB]

private theorem list_filterMap_congr {α β : Type} {f g : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem activeClassWf_congr_groups {stA stB : MallocngSt} {sc : Nat}
    {head : BitVec 64} {ms : List (BitVec 64)}
    (hNdA : (stA.groups.map (·.metaPtr)).Nodup)
    (hNdB : (stB.groups.map (·.metaPtr)).Nodup)
    (hAB : ∀ hA ∈ stA.groups, hA.sc = sc →
      ∃ hB ∈ stB.groups,
        hB.metaPtr = hA.metaPtr ∧ hB.prev = hA.prev ∧ hB.next = hA.next ∧ hB.sc = hA.sc ∧
        hB.availMask = hA.availMask ∧ hB.freedMask = hA.freedMask ∧
        hB.activeIdx = hA.activeIdx ∧ hB.lastIdx = hA.lastIdx)
    (hBA : ∀ hB ∈ stB.groups, hB.sc = sc →
      ∃ hA ∈ stA.groups,
        hA.metaPtr = hB.metaPtr ∧ hA.prev = hB.prev ∧ hA.next = hB.next ∧ hA.sc = hB.sc ∧
        hA.availMask = hB.availMask ∧ hA.freedMask = hB.freedMask ∧
        hA.activeIdx = hB.activeIdx ∧ hA.lastIdx = hB.lastIdx)
    (hWfA : ActiveClassWf stA sc head ms) :
    ActiveClassWf stB sc head ms := by
  obtain ⟨hMemA, hDllA, hLenA, hNotMemA, hTailA, hActUniqA, hActMemA⟩ := hWfA
  have hNodesEq :
      (ms.filterMap fun m =>
        (findGroupByMeta stB m).map fun h => (h.metaPtr, h.prev, h.next)) =
      (ms.filterMap fun m =>
        (findGroupByMeta stA m).map fun h => (h.metaPtr, h.prev, h.next)) := by
    apply list_filterMap_congr
    intro m hm
    obtain ⟨hA, hhA, rfl, hScA⟩ := hMemA m hm
    obtain ⟨hB, hhB, hMB, hPv, hNx, _, _, _, _, _⟩ := hAB hA hhA hScA
    have hFA : findGroupByMeta stA hA.metaPtr = some hA := findGroupByMeta_eq_of_mem hNdA hhA
    have hFB : findGroupByMeta stB hA.metaPtr = some hB := by
      unfold findGroupByMeta; rw [← hMB]; exact findGroupByMeta_eq_of_mem hNdB hhB
    rw [hFA, hFB]
    simp [hMB, hPv, hNx]
  refine ⟨fun m hm => ?_, hNodesEq ▸ hDllA, hNodesEq ▸ hLenA,
    fun hB hhB hScB => ?_, fun i hi hiPos hB hhB hMB => ?_,
    fun h1 hh1 h2 hh2 hSc1 hSc2 hLt1 hLt2 => ?_,
    fun hB hhB hScB hLtB => ?_⟩
  · obtain ⟨hA, hhA, hMA, hScA⟩ := hMemA m hm
    obtain ⟨hB, hhB, hMB, _, _, hScB, _, _, _, _⟩ := hAB hA hhA hScA
    exact ⟨hB, hhB, hMB.trans hMA, hScB.trans hScA⟩
  · obtain ⟨hA, hhA, hMA, hPv, hNx, hScA, hAv, hFr, hAi, hLi⟩ := hBA hB hhB hScB
    have h4 := hNotMemA hA hhA (hScA.trans hScB)
    rw [hMA, hPv, hNx, hAv, hFr, hAi, hLi] at h4
    exact h4
  · obtain ⟨hA, hhA, _⟩ := hMemA (ms[i]'hi) (List.getElem_mem hi)
    have hEqSc : hB.sc = sc := by
      obtain ⟨hA0, hhA0, hM0, hSc0⟩ := hMemA (ms[i]'hi) (List.getElem_mem hi)
      obtain ⟨hB0, hhB0, hMB0, _, _, hScB0, _, _, _, _⟩ := hAB hA0 hhA0 hSc0
      have hEqB := mem_groups_eq_of_metaPtr hNdB hhB hhB0 (hMB.trans (hM0.symm.trans hMB0.symm))
      subst hEqB
      exact hScB0.trans hSc0
    obtain ⟨hA', hhA', hMA', _, _, _, hAv, hFr, _, _⟩ := hBA hB hhB hEqSc
    have h5 := hTailA i hi hiPos hA' hhA' (hMA'.trans hMB)
    rw [hAv, hFr] at h5
    exact h5
  · obtain ⟨a1, ha1, hM1, _, _, _, _, _, hAi1, hLi1⟩ := hBA h1 hh1 hSc1
    obtain ⟨a2, ha2, hM2, _, _, _, _, _, hAi2, hLi2⟩ := hBA h2 hh2 hSc2
    have hEq := hActUniqA a1 ha1 a2 ha2 (by obtain ⟨_, _, _, _, _, s, _⟩ := hBA h1 hh1 hSc1; omega)
      (by obtain ⟨_, _, _, _, _, s, _⟩ := hBA h2 hh2 hSc2; omega)
      (by omega) (by omega)
    exact hM1.symm.trans (hEq.trans hM2)
  · obtain ⟨hA, hhA, hMA, _, _, hScA, _, _, hAi, hLi⟩ := hBA hB hhB hScB
    have h7 := hActMemA hA hhA (hScA.trans hScB) (by omega)
    rwa [hMA] at h7

/-- Post-dequeue structural invariant after `g` has been unlinked from `ctx.active[g.sc]` and
    `ctx.usageByClass[g.sc]` has been decremented when `g.sc < 48`. -/
structure DequeueOutcome (st : MallocngSt) (g : GroupDesc)
    (active1 usage1 : List (BitVec 64)) (actLists1 : List (List (BitVec 64)))
    (gsDeq : List GroupDesc) (bvDeq : BitVec 64 → BitVec 8) : Prop where
  lens : active1.length = 48 ∧ usage1.length = 48 ∧ actLists1.length = 48
  nodup : (gsDeq.map (·.metaPtr)).Nodup ∧ (gsDeq.map (·.mem)).Nodup
  meta_set :
    ∀ x, x ∈ gsDeq.map (·.metaPtr) ↔ (x ∈ st.groups.map (·.metaPtr) ∧ x ≠ g.metaPtr)
  root_filter_eq :
    (gsDeq.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096)) =
      ((filterOutGroup st.groups g.metaPtr).filter (fun h => decide (0 < h.maplen))).map
        (fun h => (h.mem, h.maplen * 4096))
  each_preserved :
    ∀ h ∈ gsDeq,
      h.metaPtr ≠ g.metaPtr ∧
      ∃ h0 ∈ st.groups,
        h.metaPtr = h0.metaPtr ∧ h.mem = h0.mem ∧ h.maplen = h0.maplen ∧
        h.sc = h0.sc ∧ h.lastIdx = h0.lastIdx ∧ h.activeByte = h0.activeByte ∧
        h.parentMeta = h0.parentMeta ∧ h.nestedCap = h0.nestedCap ∧
        h.slots.length = h0.slots.length ∧ h.isEmpty = h0.isEmpty ∧
        (h.availMask = 0#32 ∧ h.freedMask = 0#32 → h0.availMask = 0#32 ∧ h0.freedMask = 0#32) ∧
        (∀ j (hj : j < h.slots.length) (hj0 : j < h0.slots.length),
          (∀ cm, h.slots[j]'hj = .liveNested cm ↔ h0.slots[j]'hj0 = .liveNested cm) ∧
          (∀ p n ec, h.slots[j]'hj = .liveUser p n ec ↔ h0.slots[j]'hj0 = .liveUser p n ec))
  other_sc_mem : ∀ h0 ∈ st.groups, h0.sc ≠ g.sc → h0 ∈ gsDeq
  sum_claimed :
    (gsDeq.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum +
      (g.slots.filter SlotState.isClaimed).length = totalClaimedSlots st
  sum_live :
    (gsDeq.map (fun h => (h.slots.map slotLiveCount).sum)).sum +
      (g.slots.map slotLiveCount).sum = totalLiveCount st
  sum_eff :
    (gsDeq.map (fun h => (h.slots.map slotEffCost).sum)).sum +
      (g.slots.map slotEffCost).sum = totalLiveEffCost st
  usage_eq :
    ∀ sc : Nat, (hsc : sc < usage1.length) →
      (usage1[sc]'hsc).toNat = ((gsDeq.filter (·.sc == sc)).map GroupDesc.cnt).sum
  g_zero_bytes :
    readBytesFromMap bvDeq g.metaPtr 40 = ({ g with prev := 0#64, next := 0#64 } : GroupDesc).metaBytes
  only_group_metas :
    ∀ a : BitVec 64, bvDeq a ≠ st.byteVal a → ∃ u ∈ st.groups, InRegion u.metaPtr 40 a
  each_meta_bytes :
    ∀ h ∈ gsDeq, readBytesFromMap bvDeq h.metaPtr 40 = h.metaBytes
  each_masks :
    ∀ h ∈ gsDeq,
      h.availMask &&& h.freedMask = 0#32 ∧
      (h.availMask ||| h.freedMask).toNat < 2 ^ h.cnt ∧
      (h.sc = 63 → h.prev = 0#64 ∧ h.next = 0#64) ∧
      ∀ j (hj : j < h.slots.length),
        (h.availMask.getLsbD j = true ↔ h.slots[j]'hj = .freeAvail) ∧
        (h.freedMask.getLsbD j = true ↔ h.slots[j]'hj = .freeInactive) ∧
        (h.activeIdx < j → h.slots[j]'hj = .freeInactive)
  active_wf_deq :
    ∀ sc : Nat, (h1 : sc < active1.length) → (h2 : sc < actLists1.length) →
      ActiveClassWf
        { st with
          ctx := { st.ctx with active := active1, usageByClass := usage1 }
          groups := gsDeq
          activeLists := actLists1
          byteVal := bvDeq }
        sc (active1[sc]'h1) (actLists1[sc]'h2)
  empty_act_singleton :
    ∀ h ∈ gsDeq, h.isEmpty = true →
      (∀ (hLt : h.sc < actLists1.length), h.metaPtr ∈ actLists1[h.sc]'hLt) ∧
      (∀ h' ∈ gsDeq, h'.isEmpty = true → h'.sc = h.sc → h'.metaPtr = h.metaPtr)

private theorem filterOut_common_props {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) :
    let gsDeq := filterOutGroup st.groups g.metaPtr
    (gsDeq.map (·.metaPtr)).Nodup ∧
    (gsDeq.map (·.mem)).Nodup ∧
    (∀ x, x ∈ gsDeq.map (·.metaPtr) ↔ (x ∈ st.groups.map (·.metaPtr) ∧ x ≠ g.metaPtr)) ∧
    (∀ h ∈ gsDeq,
      h.metaPtr ≠ g.metaPtr ∧
      ∃ h0 ∈ st.groups,
        h.metaPtr = h0.metaPtr ∧ h.mem = h0.mem ∧ h.maplen = h0.maplen ∧
        h.sc = h0.sc ∧ h.lastIdx = h0.lastIdx ∧ h.activeByte = h0.activeByte ∧
        h.parentMeta = h0.parentMeta ∧ h.nestedCap = h0.nestedCap ∧
        h.slots.length = h0.slots.length ∧ h.isEmpty = h0.isEmpty ∧
        (h.availMask = 0#32 ∧ h.freedMask = 0#32 → h0.availMask = 0#32 ∧ h0.freedMask = 0#32) ∧
        (∀ j (hj : j < h.slots.length) (hj0 : j < h0.slots.length),
          (∀ cm, h.slots[j]'hj = .liveNested cm ↔ h0.slots[j]'hj0 = .liveNested cm) ∧
          (∀ p n ec, h.slots[j]'hj = .liveUser p n ec ↔ h0.slots[j]'hj0 = .liveUser p n ec))) ∧
    (∀ h0 ∈ st.groups, h0.sc ≠ g.sc → h0 ∈ gsDeq) ∧
    (gsDeq.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum +
      (g.slots.filter SlotState.isClaimed).length = totalClaimedSlots st ∧
    (gsDeq.map (fun h => (h.slots.map slotLiveCount).sum)).sum +
      (g.slots.map slotLiveCount).sum = totalLiveCount st ∧
    (gsDeq.map (fun h => (h.slots.map slotEffCost).sum)).sum +
      (g.slots.map slotEffCost).sum = totalLiveEffCost st ∧
    (∀ h ∈ gsDeq,
      h.availMask &&& h.freedMask = 0#32 ∧
      (h.availMask ||| h.freedMask).toNat < 2 ^ h.cnt ∧
      (h.sc = 63 → h.prev = 0#64 ∧ h.next = 0#64) ∧
      ∀ j (hj : j < h.slots.length),
        (h.availMask.getLsbD j = true ↔ h.slots[j]'hj = .freeAvail) ∧
        (h.freedMask.getLsbD j = true ↔ h.slots[j]'hj = .freeInactive) ∧
        (h.activeIdx < j → h.slots[j]'hj = .freeInactive)) := by
  obtain ⟨hNdM, hNdMem, hSet, hMemIff, hSum, _, _⟩ :=
    filterOutGroup_props hwf.groups_nodup.1 hwf.groups_nodup.2 hg
  refine ⟨hNdM, hNdMem, hSet,
    fun h hh => ⟨(hMemIff h).mp hh |>.2, h, (hMemIff h).mp hh |>.1,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id,
      fun _ _ _ => ⟨fun _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩⟩,
    fun h0 hh0 hScNe => (hMemIff h0).mpr ⟨hh0, fun hEq =>
      hScNe (congrArg GroupDesc.sc (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq))⟩,
    hSum _, hSum _, hSum _,
    fun h hh => ?_⟩
  have hHWf := hwf.groups_wf h ((hMemIff h).mp hh).1
  refine ⟨hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun h63 => ⟨(hHWf.2.2.2.1 h63).2.2.1, (hHWf.2.2.2.1 h63).2.2.2⟩,
    fun j hj => ?_⟩
  have hS := hHWf.slot_wf j hj
  exact ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1⟩

theorem usage_sub_cnt_props {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc48 : g.sc < 48) :
    let hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
    let oldUse := st.ctx.usageByClass[g.sc]'hUseLt
    let newUse := oldUse - BitVec.ofNat 64 g.cnt
    let usage1 := st.ctx.usageByClass.set g.sc newUse
    let gsRest := filterOutGroup st.groups g.metaPtr
    g.cnt ≤ oldUse.toNat ∧
    usage1.length = 48 ∧
    ∀ sc : Nat, (hsc : sc < usage1.length) →
      (usage1[sc]'hsc).toNat = ((gsRest.filter (·.sc == sc)).map GroupDesc.cnt).sum := by
  dsimp only []
  have hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
  obtain ⟨_, _, _, _, _, hCntSum, _⟩ :=
    filterOutGroup_props hwf.groups_nodup.1 hwf.groups_nodup.2 hg
  have hOldEq := hwf.usage_wf g.sc hUseLt
  have hSplitG := hCntSum g.sc
  simp only [↓reduceIte] at hSplitG
  have hCntLe : g.cnt ≤ (st.ctx.usageByClass[g.sc]'hUseLt).toNat := by omega
  have hGWf := hwf.groups_wf g hg
  have hCntLt64 : g.cnt < 2 ^ 64 := by
    have := hGWf.2.1; unfold GroupDesc.cnt; omega
  have hSubNat : ((st.ctx.usageByClass[g.sc]'hUseLt) - BitVec.ofNat 64 g.cnt).toNat =
      (st.ctx.usageByClass[g.sc]'hUseLt).toNat - g.cnt := by
    bv_omega
  refine ⟨hCntLe, by simp [hwf.ctx_lens.2.1], fun sc hsc => ?_⟩
  have hsc0 : sc < st.ctx.usageByClass.length := by simpa using hsc
  by_cases hEq : sc = g.sc
  · subst hEq
    simp only [List.getElem_set_self, hSubNat]
    omega
  · simp only [List.getElem_set, Ne.symm hEq, ↓reduceIte]
    have hOther := hCntSum sc
    simp only [Ne.symm hEq, ↓reduceIte, Nat.add_zero] at hOther
    exact (hwf.usage_wf sc hsc0).trans hOther.symm

theorem activeClassWf_other_sc {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st stDeq : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hSc48 : sc < 48)
    (hNdDeq : (stDeq.groups.map (·.metaPtr)).Nodup)
    (hSameSc : ∀ h, (h ∈ stDeq.groups ∧ h.sc = sc) ↔ (h ∈ st.groups ∧ h.sc = sc)) :
    let h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
    ActiveClassWf stDeq sc (st.ctx.active[sc]'h1) (st.activeLists[sc]'h2) := by
  dsimp only []
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  have h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
  exact activeClassWf_congr_groups hwf.groups_nodup.1 hNdDeq
    (fun hA hhA hScA => ⟨hA, ((hSameSc hA).mpr ⟨hhA, hScA⟩).1,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (fun hB hhB hScB => ⟨hB, ((hSameSc hB).mp ⟨hhB, hScB⟩).1,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (hwf.active_wf sc h1 h2)

/-! ## Non-General Dequeue Paths -/

theorem dequeue_sc63 {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc63 : g.sc = 63) :
    let gsDeq := filterOutGroup st.groups g.metaPtr
    g.prev = 0#64 ∧ g.next = 0#64 ∧ 0 < g.maplen ∧
    DequeueOutcome st g st.ctx.active st.ctx.usageByClass st.activeLists gsDeq st.byteVal := by
  dsimp only []
  have hGWf := hwf.groups_wf g hg
  obtain ⟨_, hMpPos, hPv0, hNx0⟩ := hGWf.2.2.2.1 hSc63
  obtain ⟨hNdM, hNdMem, hSet, hEach, hOtherSc, hSumC, hSumL, hSumE, hMasks⟩ :=
    filterOut_common_props hwf hg
  obtain ⟨_, _, _, hMemIff, _, hCntSum, _⟩ :=
    filterOutGroup_props hwf.groups_nodup.1 hwf.groups_nodup.2 hg
  have hGZeroEq : ({ g with prev := 0#64, next := 0#64 } : GroupDesc) = g := by
    cases g; subst hPv0 hNx0; rfl
  refine ⟨hPv0, hNx0, hMpPos,
    { lens := ⟨hwf.ctx_lens.1, hwf.ctx_lens.2.1, hwf.ctx_lens.2.2.2.2.2⟩
      nodup := ⟨hNdM, hNdMem⟩
      meta_set := hSet
      root_filter_eq := rfl
      each_preserved := hEach
      other_sc_mem := hOtherSc
      sum_claimed := hSumC
      sum_live := hSumL
      sum_eff := hSumE
      usage_eq := fun sc hsc => by
        have hSc48 : sc < 48 := by rw [hwf.ctx_lens.2.1] at hsc; exact hsc
        have hNe : g.sc ≠ sc := by omega
        have hS := hCntSum sc
        simp only [hNe, ↓reduceIte, Nat.add_zero] at hS
        exact (hwf.usage_wf sc hsc).trans hS.symm
      g_zero_bytes := by rw [hGZeroEq]; exact hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      only_group_metas := fun _ hNe => False.elim (hNe rfl)
      each_meta_bytes := fun h hh =>
        (hwf.groups_wf h ((hMemIff h).mp hh).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      each_masks := hMasks
      active_wf_deq := fun sc h1 _ => by
        have hSc48 : sc < 48 := by rw [hwf.ctx_lens.1] at h1; exact h1
        exact activeClassWf_other_sc hwf hSc48 hNdM fun h =>
          ⟨fun ⟨hh, hSc⟩ => ⟨((hMemIff h).mp hh).1, hSc⟩,
           fun ⟨hh, hSc⟩ => ⟨(hMemIff h).mpr ⟨hh, fun hEq => by
             have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq
             subst this; omega⟩, hSc⟩⟩
      empty_act_singleton := fun h hh hEmp =>
        ⟨fun hLt => (hwf.empty_groups_bound h ((hMemIff h).mp hh).1 hEmp).2.2.2.2.1 hLt,
         fun h' hh' hEmp' hSc' =>
           (hwf.empty_groups_bound h ((hMemIff h).mp hh).1 hEmp).2.2.2.2.2.1
             h' ((hMemIff h').mp hh').1 hEmp' hSc'⟩ }⟩

theorem dequeue_not_queued {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc48 : g.sc < 48) (hNx0 : g.next = 0#64) :
    let hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
    let oldUse := st.ctx.usageByClass[g.sc]'hUseLt
    let usage1 := st.ctx.usageByClass.set g.sc (oldUse - BitVec.ofNat 64 g.cnt)
    let gsDeq := filterOutGroup st.groups g.metaPtr
    g.prev = 0#64 ∧
    g.cnt ≤ oldUse.toNat ∧
    DequeueOutcome st g st.ctx.active usage1 st.activeLists gsDeq st.byteVal := by
  dsimp only []
  have hProps := activeList_head_and_singleton_props hwf hg hSc48
  have hNotInMs := hProps.2.1.mp hNx0
  have hPv0 := hProps.2.2.1 hNx0
  have hGWf := hwf.groups_wf g hg
  obtain ⟨hCntLe, hUseLen, hUseEq⟩ := usage_sub_cnt_props hwf hg hSc48
  obtain ⟨hNdM, hNdMem, hSet, hEach, hOtherSc, hSumC, hSumL, hSumE, hMasks⟩ :=
    filterOut_common_props hwf hg
  obtain ⟨_, _, _, hMemIff, _, _, hFindEq⟩ :=
    filterOutGroup_props hwf.groups_nodup.1 hwf.groups_nodup.2 hg
  have hGZeroEq : ({ g with prev := 0#64, next := 0#64 } : GroupDesc) = g := by
    cases g; subst hPv0 hNx0; rfl
  let usage1 := st.ctx.usageByClass.set g.sc
    ((st.ctx.usageByClass[g.sc]'(by rw [hwf.ctx_lens.2.1]; exact hSc48)) - BitVec.ofNat 64 g.cnt)
  let gsDeq := filterOutGroup st.groups g.metaPtr
  refine ⟨hPv0, hCntLe,
    { lens := ⟨hwf.ctx_lens.1, hUseLen, hwf.ctx_lens.2.2.2.2.2⟩
      nodup := ⟨hNdM, hNdMem⟩
      meta_set := hSet
      root_filter_eq := rfl
      each_preserved := hEach
      other_sc_mem := hOtherSc
      sum_claimed := hSumC
      sum_live := hSumL
      sum_eff := hSumE
      usage_eq := hUseEq
      g_zero_bytes := by rw [hGZeroEq]; exact hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      only_group_metas := fun _ hNe => False.elim (hNe rfl)
      each_meta_bytes := fun h hh =>
        (hwf.groups_wf h ((hMemIff h).mp hh).1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      each_masks := hMasks
      active_wf_deq := fun sc h1 h2 => by
        have hScLt48 : sc < 48 := by rw [hwf.ctx_lens.1] at h1; exact h1
        by_cases hEqSc : sc = g.sc
        · subst hEqSc
          have hAct0 := hwf.active_wf g.sc h1 h2
          obtain ⟨hMem0, hDll0, hLen0, hNotMem0, hTail0, hUniq0, hActMem0⟩ := hAct0
          let stDeq : MallocngSt :=
            { st with
              ctx := { st.ctx with active := st.ctx.active, usageByClass := usage1 }
              groups := gsDeq
              activeLists := st.activeLists
              byteVal := st.byteVal }
          have hNodesEq :
              ((st.activeLists[g.sc]'h2).filterMap fun m =>
                (findGroupByMeta stDeq m).map fun h => (h.metaPtr, h.prev, h.next)) =
              ((st.activeLists[g.sc]'h2).filterMap fun m =>
                (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
            apply list_filterMap_congr
            intro m hm
            have hmNe : m ≠ g.metaPtr := fun hEq => hNotInMs (hEq ▸ hm)
            change (gsDeq.find? (·.metaPtr == m)).map _ = (st.groups.find? (·.metaPtr == m)).map _
            rw [hFindEq m hmNe]
          exact ⟨fun m hm => by
              obtain ⟨h0, hh0, hM0, hS0⟩ := hMem0 m hm
              have hNeG : h0.metaPtr ≠ g.metaPtr := by
                intro hE; rw [← hE, hM0] at hNotInMs; exact hNotInMs hm
              exact ⟨h0, (hMemIff h0).mpr ⟨hh0, hNeG⟩, hM0, hS0⟩,
            hNodesEq ▸ hDll0,
            hNodesEq ▸ hLen0,
            fun h hh hS => hNotMem0 h ((hMemIff h).mp hh).1 hS,
            fun i hi hiPos h hh hM => hTail0 i hi hiPos h ((hMemIff h).mp hh).1 hM,
            fun h1' hh1' h2' hh2' s1 s2 l1 l2 =>
              hUniq0 h1' ((hMemIff h1').mp hh1').1 h2' ((hMemIff h2').mp hh2').1 s1 s2 l1 l2,
            fun h hh hS hLt => hActMem0 h ((hMemIff h).mp hh).1 hS hLt⟩
        · exact activeClassWf_other_sc hwf hScLt48 hNdM fun h =>
            ⟨fun ⟨hh, hSc⟩ => ⟨((hMemIff h).mp hh).1, hSc⟩,
             fun ⟨hh, hSc⟩ => ⟨(hMemIff h).mpr ⟨hh, fun hEq => by
               have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq
               subst this; exact hEqSc hSc.symm⟩, hSc⟩⟩
      empty_act_singleton := fun h hh hEmp =>
        ⟨fun hLt => (hwf.empty_groups_bound h ((hMemIff h).mp hh).1 hEmp).2.2.2.2.1 hLt,
         fun h' hh' hEmp' hSc' =>
           (hwf.empty_groups_bound h ((hMemIff h).mp hh).1 hEmp).2.2.2.2.2.1
             h' ((hMemIff h').mp hh').1 hEmp' hSc'⟩ }⟩

theorem dequeue_singleton {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc48 : g.sc < 48) (hNxSelf : g.next = g.metaPtr) :
    let hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    let hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
    let hListLt : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
    let oldUse := st.ctx.usageByClass[g.sc]'hUseLt
    let active1 := st.ctx.active.set g.sc 0#64
    let usage1 := st.ctx.usageByClass.set g.sc (oldUse - BitVec.ofNat 64 g.cnt)
    let actLists1 := st.activeLists.set g.sc []
    let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
    let bvDeq := writeBytesToMap st.byteVal g.metaPtr gZero.metaBytes
    let gsDeq := filterOutGroup st.groups g.metaPtr
    st.ctx.active[g.sc]'hActLt = g.metaPtr ∧
    st.activeLists[g.sc]'hListLt = [g.metaPtr] ∧
    g.prev = g.metaPtr ∧
    g.cnt ≤ oldUse.toNat ∧
    (∀ a, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq := by
  dsimp only []
  have hActLt : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  have hUseLt : g.sc < st.ctx.usageByClass.length := by rw [hwf.ctx_lens.2.1]; exact hSc48
  have hListLt : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
  have hProps := activeList_head_and_singleton_props hwf hg hSc48
  have hMsEq := hProps.2.2.2.1.mp hNxSelf
  obtain ⟨hHeadEq, hPvEq⟩ := hProps.2.2.2.2.1 hNxSelf
  have hMetaOwn := (meta_ownedRw_of_mem_groups hwf hg).2.2.2.2
  obtain ⟨hCntLe, hUseLen, hUseEq⟩ := usage_sub_cnt_props hwf hg hSc48
  obtain ⟨hNdM, hNdMem, hSet, hEach, hOtherSc, hSumC, hSumL, hSumE, hMasks⟩ :=
    filterOut_common_props hwf hg
  obtain ⟨_, _, _, hMemIff, _, _, _⟩ :=
    filterOutGroup_props hwf.groups_nodup.1 hwf.groups_nodup.2 hg
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let bvDeq := writeBytesToMap st.byteVal g.metaPtr gZero.metaBytes
  let gsDeq := filterOutGroup st.groups g.metaPtr
  let active1 := st.ctx.active.set g.sc 0#64
  let usage1 := st.ctx.usageByClass.set g.sc
    ((st.ctx.usageByClass[g.sc]'hUseLt) - BitVec.ofNat 64 g.cnt)
  let actLists1 := st.activeLists.set g.sc []
  have hAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  refine ⟨hHeadEq, hMsEq, hPvEq, hCntLe, hMetaOwn,
    { lens := ⟨by simp [hwf.ctx_lens.1], hUseLen, by simp [hwf.ctx_lens.2.2.2.2.2]⟩
      nodup := ⟨hNdM, hNdMem⟩
      meta_set := hSet
      root_filter_eq := rfl
      each_preserved := hEach
      other_sc_mem := hOtherSc
      sum_claimed := hSumC
      sum_live := hSumL
      sum_eff := hSumE
      usage_eq := hUseEq
      g_zero_bytes := readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr gZero.metaBytes (by simp)
      only_group_metas := fun a hNe => by
        by_cases ha : InRegion g.metaPtr 40 a
        · exact ⟨g, hg, ha⟩
        · exact False.elim (hNe (writeBytesToMap_out st.byteVal g.metaPtr gZero.metaBytes (by simpa using ha)))
      each_meta_bytes := fun h hh => by
        obtain ⟨hh0, hNeM⟩ := (hMemIff h).mp hh
        have hAllH : h.metaPtr ∈ allMetaSlots st :=
          (hwf.free_bump_metas_wf.2.2.2.2.2 h.metaPtr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hh0))))
        refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans
          (hwf.groups_wf h hh0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact writeBytesToMap_out st.byteVal g.metaPtr gZero.metaBytes fun haG =>
          metaSlot_disjoint_of_ne hwf hAllH hAllG hNeM ha (by simpa using haG)
      each_masks := hMasks
      active_wf_deq := fun sc h1 h2 => by
        have hScLt48 : sc < 48 := by simp [hwf.ctx_lens.1] at h1; exact h1
        by_cases hEqSc : sc = g.sc
        · subst hEqSc
          simp only [List.getElem_set_self]
          unfold ActiveClassWf
          have hAct0 := hwf.active_wf g.sc hActLt hListLt
          refine ⟨fun _ hm => (nomatch hm), rfl, rfl,
            fun h hh hS => ?_,
            fun _ hi => False.elim (Nat.not_lt_zero _ hi),
            fun h1' hh1' h2' hh2' s1 s2 l1 l2 =>
              hAct0.2.2.2.2.2.1 h1' ((hMemIff h1').mp hh1').1 h2' ((hMemIff h2').mp hh2').1 s1 s2 l1 l2,
            fun h hh hS hLt => ?_⟩
          · obtain ⟨hh0, hNeM⟩ := (hMemIff h).mp hh
            have hNotIn0 : h.metaPtr ∉ st.activeLists[g.sc]'hListLt := by
              rw [hMsEq]; simp [hNeM]
            have h4 := hAct0.2.2.2.1 h hh0 hS
            exact ⟨⟨fun _ => h4.1.mp hNotIn0, fun _ hm => (nomatch hm)⟩,
              fun _ => h4.2 hNotIn0⟩
          · obtain ⟨hh0, hNeM⟩ := (hMemIff h).mp hh
            have ⟨hIn0, _⟩ := hAct0.2.2.2.2.2.2 h hh0 hS hLt
            rw [hMsEq] at hIn0; simp [hNeM] at hIn0
        · simp only [List.getElem_set, Ne.symm hEqSc, ↓reduceIte]
          exact activeClassWf_other_sc hwf hScLt48 hNdM fun h =>
            ⟨fun ⟨hh, hSc⟩ => ⟨((hMemIff h).mp hh).1, hSc⟩,
             fun ⟨hh, hSc⟩ => ⟨(hMemIff h).mpr ⟨hh, fun hEq => by
               have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq
               subst this; exact hEqSc hSc.symm⟩, hSc⟩⟩
      empty_act_singleton := fun h hh hEmp => by
        obtain ⟨hh0, hNeM⟩ := (hMemIff h).mp hh
        have hB := hwf.empty_groups_bound h hh0 hEmp
        refine ⟨fun hLt => ?_, fun h' hh' hEmp' hSc' =>
          hB.2.2.2.2.2.1 h' ((hMemIff h').mp hh').1 hEmp' hSc'⟩
        have hLt0 : h.sc < st.activeLists.length := by simpa using hLt
        have hMem0 := hB.2.2.2.2.1 hLt0
        have hScNe : h.sc ≠ g.sc := fun hEq => by
          have hInG : h.metaPtr ∈ st.activeLists[g.sc]'hListLt := by simpa [hEq] using hMem0
          rw [hMsEq] at hInG
          exact hNeM (List.mem_singleton.mp hInG)
        simp only [List.getElem_set, Ne.symm hScNe, ↓reduceIte]
        exact hMem0 }⟩

end VerifiedLibraries.Mallocng.Proofs
