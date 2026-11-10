/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.Inv
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers5b
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers6f
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers

/-!
# `SameLiveUserSub` Preservation Lemmas for `mallocng` Free Paths

Combinators establishing `SameLiveUserSub` (`GroupsSubGeometry`, live-user slot preservation,
absence of `.liveUser` slots in retired groups, and `metaAreas` / `liveMap` preservation) across
the `mallocng` free-path state transitions in `LibsignalBinary.Heap.Fine.VendorFree`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open LibsignalBinary.Heap.Fine.VendorFree

/-! ## Coarse `MallocngBudget` Witness Synthesis -/

/-- Synthesize a `MallocngBudget` witness for any `(liveCost, peakCost, st)` so coarse
    `VendorFree` lemmas expecting `(bud : MallocngBudget)` and
    `MallocngCountIvsWF bud (dynamicRootRegions st) st` apply directly. -/
def synthCoarseFreeBudget (liveCost peakCost : Nat) (st : MallocngSt) : MallocngBudget :=
  let pk := 128 + totalLiveCount st + (dynamicRootRegions st).length + 101 * st.metaAreas.length
  { liveCost := liveCost
    peakCost := peakCost
    liveCount := totalLiveCount st
    peakCount := pk }

theorem synthCoarseFreeBudget_liveCost (liveCost peakCost : Nat) (st : MallocngSt) :
    (synthCoarseFreeBudget liveCost peakCost st).liveCost = liveCost := rfl

theorem synthCoarseFreeBudget_peakCost (liveCost peakCost : Nat) (st : MallocngSt) :
    (synthCoarseFreeBudget liveCost peakCost st).peakCost = peakCost := rfl

theorem synthCoarseFreeBudget_countIvsWF (liveCost peakCost : Nat) (st : MallocngSt)
    (hGrp : Cost.GroupsGrpBound 128 st.groups) :
    MallocngCountIvsWF (synthCoarseFreeBudget liveCost peakCost st)
      (dynamicRootRegions st) st := by
  refine ⟨?_, ?_, rfl, ?_, ?_, hGrp.mono (by dsimp [synthCoarseFreeBudget]; omega)⟩ <;>
    dsimp [synthCoarseFreeBudget] <;> omega

/-! ## Reflexivity, Transitivity, and Identity-Group Combinators -/

theorem SameLiveUserSub.refl {st : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup) :
    SameLiveUserSub st st where
  geom_sub := GroupsSubGeometry.refl hNd
  live_slots_iff := by
    intro g' hg' g hg hEq
    have hGEq : g' = g := mem_groups_eq_of_metaPtr hNd hg' hg hEq
    subst hGEq
    exact ⟨rfl, fun _ _ _ _ _ _ => Iff.rfl⟩
  retired_no_liveUser := by
    intro g hg hNotIn
    exact False.elim (hNotIn (List.mem_map_of_mem hg))
  metaAreas_eq := rfl
  liveMap_eq := rfl

theorem sameLiveUserSub_of_groups_eq {st' st : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hGs : st'.groups = st.groups)
    (hMa : st'.metaAreas = st.metaAreas)
    (hLm : st'.liveMap = st.liveMap) :
    SameLiveUserSub st' st where
  geom_sub := by
    refine ⟨by rw [hGs]; exact hNd, hNd, ?_⟩
    intro g' hg'
    rw [hGs] at hg'
    exact ⟨g', hg', rfl, rfl, rfl, rfl, rfl, rfl⟩
  live_slots_iff := by
    intro g' hg' g hg hEq
    rw [hGs] at hg'
    exact (SameLiveUserSub.refl hNd).live_slots_iff g' hg' g hg hEq
  retired_no_liveUser := by
    intro g hg hNotIn
    rw [hGs] at hNotIn
    exact False.elim (hNotIn (List.mem_map_of_mem hg))
  metaAreas_eq := hMa
  liveMap_eq := hLm

theorem SameLiveUserSub.trans {st2 st1 st0 : MallocngSt}
    (h21 : SameLiveUserSub st2 st1) (h10 : SameLiveUserSub st1 st0) :
    SameLiveUserSub st2 st0 where
  geom_sub := GroupsSubGeometry.trans h21.geom_sub h10.geom_sub
  live_slots_iff := by
    intro g2 hg2 g0 hg0 hEq20
    obtain ⟨g1, hg1, hEq12, _⟩ := h21.geom_sub.2.2 g2 hg2
    have hEq10 : g1.metaPtr = g0.metaPtr := hEq12.trans hEq20
    obtain ⟨hLen21, hIff21⟩ := h21.live_slots_iff g2 hg2 g1 hg1 hEq12.symm
    obtain ⟨hLen10, hIff10⟩ := h10.live_slots_iff g1 hg1 g0 hg0 hEq10
    refine ⟨hLen21.trans hLen10, fun j hj2 hj0 q rq eq => ?_⟩
    have hj1 : j < g1.slots.length := hLen21 ▸ hj2
    exact (hIff21 j hj2 hj1 q rq eq).trans (hIff10 j hj1 hj0 q rq eq)
  retired_no_liveUser := by
    intro g0 hg0 hNotIn2 j hj0 q rq eq
    by_cases hIn1 : g0.metaPtr ∈ st1.groups.map GroupDesc.metaPtr
    · obtain ⟨g1, hg1, hEq10⟩ := List.mem_map.mp hIn1
      have hNotIn2_1 : g1.metaPtr ∉ st2.groups.map GroupDesc.metaPtr := by
        rw [hEq10]; exact hNotIn2
      obtain ⟨hLen10, hIff10⟩ := h10.live_slots_iff g1 hg1 g0 hg0 hEq10
      have hj1 : j < g1.slots.length := hLen10.symm ▸ hj0
      intro hLive0
      have hLive1 := (hIff10 j hj1 hj0 q rq eq).mpr hLive0
      exact h21.retired_no_liveUser g1 hg1 hNotIn2_1 j hj1 q rq eq hLive1
    · exact h10.retired_no_liveUser g0 hg0 hIn1 j hj0 q rq eq
  metaAreas_eq := h21.metaAreas_eq.trans h10.metaAreas_eq
  liveMap_eq := h21.liveMap_eq.trans h10.liveMap_eq

/-! ## In-Place Group Replacement and Non-`liveUser` Slot Updates -/

theorem sameLiveUserSub_of_replaceGroupByMeta
    {st' st : MallocngSt} {g g1 : GroupDesc}
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hg : g ∈ st.groups)
    (hGs : st'.groups = replaceGroupByMeta st.groups g.metaPtr g1)
    (hMa : st'.metaAreas = st.metaAreas)
    (hLm : st'.liveMap = st.liveMap)
    (hMeta : g1.metaPtr = g.metaPtr)
    (hMem : g1.mem = g.mem)
    (hSc : g1.sc = g.sc)
    (hMaplen : g1.maplen = g.maplen)
    (hNested : g1.nestedCap = g.nestedCap)
    (hLast : g1.lastIdx = g.lastIdx)
    (hSlotsLen : g1.slots.length = g.slots.length)
    (hSlotsIff : ∀ (j : Nat) (hj1 : j < g1.slots.length) (hj : j < g.slots.length)
      (q : BitVec 64) (rq eq : Nat),
      g1.slots[j]'hj1 = .liveUser q rq eq ↔ g.slots[j]'hj = .liveUser q rq eq) :
    SameLiveUserSub st' st := by
  have hProps := replaceGroupByMeta_props hNd hg hMeta hMem hMaplen hSc hLast
  have hMapEq : st'.groups.map (·.metaPtr) = st.groups.map (·.metaPtr) := by
    rw [hGs]; exact hProps.1
  have hCnt : g1.cnt = g.cnt := by simp [GroupDesc.cnt, hLast]
  have hStride : g1.stride = g.stride := by simp [GroupDesc.stride, hSc, hMaplen, hLast]
  refine
    { geom_sub := ?_
      live_slots_iff := ?_
      retired_no_liveUser := ?_
      metaAreas_eq := hMa
      liveMap_eq := hLm }
  · refine ⟨by rw [hMapEq]; exact hNd, hNd, ?_⟩
    intro g' hg'
    rw [hGs] at hg'
    rcases hProps.2.2.2.2.2.1 g' hg' with rfl | ⟨hg'St, _⟩
    · exact ⟨g, hg, hMeta.symm, hSc.symm, hMaplen.symm, hNested.symm, hCnt.symm, hStride.symm⟩
    · exact ⟨g', hg'St, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro g' hg' g0 hg0 hEq
    rw [hGs] at hg'
    rcases hProps.2.2.2.2.2.1 g' hg' with rfl | ⟨hg'St, _⟩
    · have hg0Eq : g0 = g := mem_groups_eq_of_metaPtr hNd hg0 hg (hEq.symm.trans hMeta)
      subst hg0Eq
      exact ⟨hSlotsLen, hSlotsIff⟩
    · have hg0Eq : g' = g0 := mem_groups_eq_of_metaPtr hNd hg'St hg0 hEq
      subst hg0Eq
      exact ⟨rfl, fun _ _ _ _ _ _ => Iff.rfl⟩
  · intro g0 hg0 hNotIn
    rw [hMapEq] at hNotIn
    exact False.elim (hNotIn (List.mem_map_of_mem hg0))

theorem slots_set_nonLiveUser_iff
    {slots : List SlotState} {idx : Nat} (hIdx : idx < slots.length)
    (hOld : ∀ q rq eq, slots[idx]'hIdx ≠ .liveUser q rq eq)
    {sNew : SlotState} (hNew : ∀ q rq eq, sNew ≠ .liveUser q rq eq) :
    ∀ (j : Nat) (hj1 : j < (slots.set idx sNew).length) (hj : j < slots.length)
      (q : BitVec 64) (rq eq : Nat),
      (slots.set idx sNew)[j]'hj1 = .liveUser q rq eq ↔ slots[j]'hj = .liveUser q rq eq := by
  intro j hj1 hj q rq eq
  rw [List.getElem_set]
  split
  · next hEq =>
    subst hEq
    exact ⟨fun h => False.elim (hNew q rq eq h), fun h => False.elim (hOld q rq eq h)⟩
  · exact Iff.rfl

theorem sameLiveUserSub_mkFastFreeGroup
    {st : MallocngSt} (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed) (bv1 : BitVec 64 → BitVec 8) :
    SameLiveUserSub
      { st with
        groups := replaceGroupByMeta st.groups g.metaPtr (mkFastFreeGroup g idx)
        byteVal := bv1 }
      st := by
  refine sameLiveUserSub_of_replaceGroupByMeta hNd hg rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (by simp [mkFastFreeGroup]) ?_
  intro j hj1 hj q rq eq
  exact slots_set_nonLiveUser_iff hIdx
    (by rw [hClaimed]; intro _ _ _ h; cases h)
    (by intro _ _ _ h; cases h) j hj1 hj q rq eq

theorem sameLiveUserSub_mkFreedKeepGroup
    {st : MallocngSt} (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed) (bv1 : BitVec 64 → BitVec 8) :
    SameLiveUserSub
      { st with
        groups := replaceGroupByMeta st.groups g.metaPtr (mkFreedKeepGroup g idx)
        byteVal := bv1 }
      st := by
  refine sameLiveUserSub_of_replaceGroupByMeta hNd hg rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (by simp [mkFreedKeepGroup]) ?_
  intro j hj1 hj q rq eq
  exact slots_set_nonLiveUser_iff hIdx
    (by rw [hClaimed]; intro _ _ _ h; cases h)
    (by intro _ _ _ h; cases h) j hj1 hj q rq eq

theorem sameLiveUserSub_mkQueuedEmptyGroup
    {st : MallocngSt} (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (ctx1 : CtxFields) (act1 : List (List (BitVec 64))) (bv1 : BitVec 64 → BitVec 8) :
    SameLiveUserSub
      { st with
        ctx := ctx1
        groups := replaceGroupByMeta st.groups g.metaPtr (mkQueuedEmptyGroup g idx)
        activeLists := act1
        byteVal := bv1 }
      st := by
  refine sameLiveUserSub_of_replaceGroupByMeta hNd hg rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (by simp [mkQueuedEmptyGroup]) ?_
  intro j hj1 hj q rq eq
  exact slots_set_nonLiveUser_iff hIdx
    (by rw [hClaimed]; intro _ _ _ h; cases h)
    (by intro _ _ _ h; cases h) j hj1 hj q rq eq

theorem sameLiveUserSub_updateQueuedGroups
    {st : MallocngSt} (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (head tailPtr : BitVec 64)
    (act1 : List (List (BitVec 64))) (bv1 : BitVec 64 → BitVec 8) :
    SameLiveUserSub
      { st with
        groups := updateQueuedGroups st.groups head tailPtr (mkQueuedFullGroup g tailPtr head idx)
        activeLists := act1
        byteVal := bv1 }
      st := by
  let g1 := mkQueuedFullGroup g tailPtr head idx
  have hMapEq :
      (updateQueuedGroups st.groups head tailPtr g1).map (·.metaPtr) =
        st.groups.map (·.metaPtr) := by
    have h1 :
        (updateQueuedGroups st.groups head tailPtr g1).map (·.metaPtr) =
          (replaceGroupByMeta st.groups g.metaPtr g1).map (·.metaPtr) := by
      simp only [updateQueuedGroups, replaceGroupByMeta, List.map_map]
      refine List.map_congr_left fun h _ => ?_
      dsimp only [Function.comp, g1, mkQueuedFullGroup]
      by_cases hEq : h.metaPtr == g.metaPtr <;> simp [hEq]
    have hProps := replaceGroupByMeta_props hNd hg (g1 := g1) rfl rfl rfl rfl rfl
    exact h1.trans hProps.1
  have hMemFromUpd :
      ∀ g' ∈ updateQueuedGroups st.groups head tailPtr g1,
        g' = g1 ∨
        ∃ h ∈ st.groups, h.metaPtr ≠ g.metaPtr ∧
          g' = { h with
            prev := if h.metaPtr == head then g.metaPtr else h.prev
            next := if h.metaPtr == tailPtr then g.metaPtr else h.next } := by
    intro g' hg'
    obtain ⟨h, hh, hGEq⟩ := List.mem_map.mp hg'
    dsimp only [g1, mkQueuedFullGroup] at hGEq ⊢
    by_cases hEq : h.metaPtr == g.metaPtr
    · simp only [hEq, ↓reduceIte] at hGEq
      exact Or.inl hGEq.symm
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hGEq
      exact Or.inr ⟨h, hh, fun hE => by simp [hE] at hEq, hGEq.symm⟩
  refine
    { geom_sub := ?_
      live_slots_iff := ?_
      retired_no_liveUser := ?_
      metaAreas_eq := rfl
      liveMap_eq := rfl }
  · refine ⟨by simpa using hMapEq ▸ hNd, hNd, ?_⟩
    intro g' hg'
    rcases hMemFromUpd g' hg' with rfl | ⟨h, hh, _, rfl⟩
    · exact ⟨g, hg, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨h, hh, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro g' hg' g0 hg0 hEq
    rcases hMemFromUpd g' hg' with rfl | ⟨h, hh, _, rfl⟩
    · have hg0Eq : g0 = g := mem_groups_eq_of_metaPtr hNd hg0 hg hEq.symm
      subst hg0Eq
      refine ⟨by simp [g1, mkQueuedFullGroup], fun j hj1 hj q rq eq => ?_⟩
      exact slots_set_nonLiveUser_iff hIdx
        (by rw [hClaimed]; intro _ _ _ hc; cases hc)
        (by intro _ _ _ hc; cases hc) j hj1 hj q rq eq
    · have hg0Eq : h = g0 := mem_groups_eq_of_metaPtr hNd hh hg0 hEq
      subst hg0Eq
      exact ⟨rfl, fun _ _ _ _ _ _ => Iff.rfl⟩
  · intro g0 hg0 hNotIn
    dsimp only [] at hNotIn
    rw [hMapEq] at hNotIn
    exact False.elim (hNotIn (List.mem_map_of_mem hg0))

/-! ## All-Free `DequeueOutcome` and Group Retirement -/

theorem sameLiveUserSub_of_dequeueOutcome
    {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st st' : MallocngSt} {g : GroupDesc} {idx : Nat}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (hGs : st'.groups = gsDeq)
    (hMa : st'.metaAreas = st.metaAreas)
    (hLm : st'.liveMap = st.liveMap) :
    SameLiveUserSub st' st := by
  have hNd0 := hwf.groups_nodup.1
  have hNoLiveG := (free_no_child_groups_of_allFree hwf hg hIdx hClaimed hAllFree).2.2.2.2.1
  refine
    { geom_sub := ?_
      live_slots_iff := ?_
      retired_no_liveUser := ?_
      metaAreas_eq := hMa
      liveMap_eq := hLm }
  · refine ⟨by rw [hGs]; exact hDeq.nodup.1, hNd0, ?_⟩
    intro g' hg'
    rw [hGs] at hg'
    obtain ⟨_, h0, hh0, hM, _, hMp, hSc, hLi, _, _, hNc, _⟩ := hDeq.each_preserved g' hg'
    have hCnt : h0.cnt = g'.cnt := by simp [GroupDesc.cnt, hLi]
    have hStr : h0.stride = g'.stride := by simp [GroupDesc.stride, hSc, hMp, hLi]
    exact ⟨h0, hh0, hM.symm, hSc.symm, hMp.symm, hNc.symm, hCnt, hStr⟩
  · intro g' hg' g0 hg0 hEq
    rw [hGs] at hg'
    obtain ⟨_, h0, hh0, hM, _, _, _, _, _, _, _, hSLen, _, _, hSlotIff⟩ := hDeq.each_preserved g' hg'
    have hh0Eq : h0 = g0 := mem_groups_eq_of_metaPtr hNd0 hh0 hg0 (hM.symm.trans hEq)
    subst hh0Eq
    exact ⟨hSLen, fun j hj' hj0 q rq eq => (hSlotIff j hj' hj0).2 q rq eq⟩
  · intro g0 hg0 hNotIn j hj0 q rq eq
    rw [hGs] at hNotIn
    have hIn0 : g0.metaPtr ∈ st.groups.map (·.metaPtr) := List.mem_map_of_mem hg0
    have hMetaEq : g0.metaPtr = g.metaPtr :=
      Classical.byContradiction fun hNe =>
        hNotIn ((hDeq.meta_set g0.metaPtr).mpr ⟨hIn0, hNe⟩)
    have hg0Eq : g0 = g := mem_groups_eq_of_metaPtr hNd0 hg0 hg hMetaEq
    subst hg0Eq
    exact hNoLiveG (g0.slots[j]'hj0) (List.getElem_mem hj0) q rq eq

theorem sameLiveUserSub_retire_nested_groups
    {inflight : Nat} {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st st' : MallocngSt} {g pg0 : GroupDesc} {idx pIdx : Nat}
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (hpgDeq : pg0 ∈ gsDeq) (hp0 : pIdx < pg0.slots.length)
    (hSlotPg : pg0.slots[pIdx]'hp0 = .liveNested g.metaPtr)
    (hGs : st'.groups = replaceGroupByMeta gsDeq pg0.metaPtr { pg0 with slots := pg0.slots.set pIdx .claimed })
    (hMa : st'.metaAreas = st.metaAreas)
    (hLm : st'.liveMap = st.liveMap) :
    SameLiveUserSub st' st := by
  let stDeq : MallocngSt := { st with groups := gsDeq }
  have hSubDeq : SameLiveUserSub stDeq st :=
    sameLiveUserSub_of_dequeueOutcome hwf hg hIdx hClaimed hAllFree hDeq rfl rfl rfl
  have hSubUpd : SameLiveUserSub st' stDeq := by
    refine sameLiveUserSub_of_replaceGroupByMeta (st := stDeq) hDeq.nodup.1 hpgDeq
      hGs hMa hLm rfl rfl rfl rfl rfl rfl (by simp) ?_
    intro j hj1 hj q rq eq
    exact slots_set_nonLiveUser_iff hp0
      (by rw [hSlotPg]; intro _ _ _ hc; cases hc)
      (by intro _ _ _ hc; cases hc) j hj1 hj q rq eq
  exact SameLiveUserSub.trans hSubUpd hSubDeq

/-! ## Intermediate Nested-Group Retirement State -/

theorem sizeClass_pos_of_lt48 {sc : Nat} (hSc : sc < 48) :
    1 ≤ sizeClass sc ∧ 16 ≤ slotStride sc := by
  have hFin : ∀ s : Fin 48, 1 ≤ sizeClass s.1 := by decide
  have h1 : 1 ≤ sizeClass sc := hFin ⟨sc, hSc⟩
  exact ⟨h1, by unfold slotStride; omega⟩

set_option maxHeartbeats 400000 in
theorem nested_stMid_wf_fine {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {g pg0 : GroupDesc} (hg : g ∈ st.groups) (hpg0 : pg0 ∈ st.groups)
    {idx pIdx : Nat} (hIdx : idx < g.slots.length) (hp0 : pIdx < pg0.slots.length)
    (hSlotG : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMap0 : g.maplen = 0)
    (hParG : g.parentMeta = some pg0.metaPtr)
    (hGScLt : g.sc < pg0.sc)
    (hSlotPg : pg0.slots[pIdx]'hp0 = .liveNested g.metaPtr)
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq) :
    let pg1 : GroupDesc := { pg0 with slots := pg0.slots.set pIdx .claimed }
    let gs1 := replaceGroupByMeta gsDeq pg0.metaPtr pg1
    let stMid : MallocngSt :=
      { st with
        ctx := { st.ctx with active := active1, usageByClass := usage1 }
        reservedMetas := g.metaPtr :: st.reservedMetas
        groups := gs1
        activeLists := actLists1
        byteVal := bvDeq }
    pg0 ∈ gsDeq ∧
    pg1 ∈ stMid.groups ∧
    MallocngWFInflight (k + 2) base brkStart brk liveCost peakCost stMid ∧
    (∀ a : BitVec 64, OwnedRwByte stMid a ↔ (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a)) ∧
    (∀ a : BitVec 64, OwnedMappedByte stMid a ↔ OwnedMappedByte st a) ∧
    totalLiveCount stMid = totalLiveCount st ∧
    dynamicRootRegions stMid = dynamicRootRegions st ∧
    SameLiveUserSub stMid st := by
  dsimp only []
  let pg1 : GroupDesc := { pg0 with slots := pg0.slots.set pIdx .claimed }
  let gs1 := replaceGroupByMeta gsDeq pg0.metaPtr pg1
  let stMid : MallocngSt :=
    { st with
      ctx := { st.ctx with active := active1, usageByClass := usage1 }
      reservedMetas := g.metaPtr :: st.reservedMetas
      groups := gs1
      activeLists := actLists1
      byteVal := bvDeq }
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hpgDeq : pg0 ∈ gsDeq := hDeq.other_sc_mem pg0 hpg0 (by omega)
  have hPgWf0 := hwf.groups_wf pg0 hpg0
  have hPgSWf := hPgWf0.slot_wf pIdx hp0
  rw [hSlotPg] at hPgSWf
  have hPgSc48 : pg0.sc < 48 := hPgSWf.2.2.2.2.1
  have hAvPgF : pg0.availMask.getLsbD pIdx = false := by
    cases hB : pg0.availMask.getLsbD pIdx
    · rfl
    · cases hPgSWf.2.1.mp hB
  have hFrPgF : pg0.freedMask.getLsbD pIdx = false := by
    cases hB : pg0.freedMask.getLsbD pIdx
    · rfl
    · cases hPgSWf.2.2.1.mp hB
  have hActPgLe : ¬ pg0.activeIdx < pIdx := fun hLt => by cases hPgSWf.2.2.2.1 hLt
  obtain ⟨_, hClaimGEq1, hEffG0, hLiveG0, hNoLiveUserG, hNoChildG⟩ :=
    free_no_child_groups_of_allFree hwf hg hIdx hSlotG hAllFree
  have hUniqueParentSlot :
      ∀ h0 ∈ st.groups, ∀ j (hj0 : j < h0.slots.length),
        h0.slots[j]'hj0 = .liveNested g.metaPtr → h0 = pg0 ∧ j = pIdx := by
    intro h0 hh0 j hj0 hSL
    have hHWf := hwf.groups_wf h0 hh0
    have hSW := hHWf.slot_wf j hj0; rw [hSL] at hSW
    obtain ⟨hHSc48, cg, hcg, hCgM, hCgP, hLoJ, _, hHiJ, hCEq, _⟩ := hSW.2.2.2.2
    have hCgEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hCgM
    subst hCgEqG
    have hMetaEq : h0.metaPtr = pg0.metaPtr := Option.some.inj (hCgP.symm.trans hParG)
    have hH0Eq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hpg0 hMetaEq
    subst hH0Eq
    refine ⟨rfl, Classical.byContradiction fun hNe => ?_⟩
    obtain ⟨_, cg', hcg', hCgM', _, hLoP, _, hHiP, _⟩ := hPgSWf.2.2.2.2
    have hCgEqG' := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg' hg hCgM'
    subst hCgEqG'
    have ⟨_, _, hStJ, _, hEnJ, _, _, _, _⟩ := group_slot_bounds hPgWf0 hj0
    have ⟨_, _, hStP, _, hEnP, _, _, _, _⟩ := group_slot_bounds hPgWf0 hp0
    have ⟨hStrGe, _⟩ := group_stride_pos_and_align hPgWf0
    have hCapPos : 0 < cg'.nestedCap := by
      have := (sizeClass_pos_of_lt48 hHSc48).2; omega
    have hSMJ : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hSMP : (pIdx + 1) * h0.stride = pIdx * h0.stride + h0.stride := Nat.succ_mul pIdx h0.stride
    by_cases hLt : j < pIdx
    · have : (j + 1) * h0.stride ≤ pIdx * h0.stride := Nat.mul_le_mul_right _ hLt
      omega
    · have : (pIdx + 1) * h0.stride ≤ j * h0.stride := Nat.mul_le_mul_right _ (by omega)
      omega
  have hRep := replaceGroupByMeta_props hDeq.nodup.1 hpgDeq rfl rfl rfl rfl rfl (g1 := pg1)
  have hGs1MetaSet : ∀ x, x ∈ gs1.map (·.metaPtr) ↔ (x ∈ st.groups.map (·.metaPtr) ∧ x ≠ g.metaPtr) := by
    intro x; rw [hRep.1]; exact hDeq.meta_set x
  have ⟨_, hUf1Nd, hUf1Iff⟩ :=
    retire_usedAndFree_props hwf hg (hRep.1 ▸ hDeq.nodup.1) hGs1MetaSet
  have hDisjDeq := groupMetaMod_disjoint hwf hDeq.only_group_metas
  have hFltNotG : (filterOutGroup st.groups g.metaPtr).filter (fun h => decide (0 < h.maplen)) =
      st.groups.filter (fun h => decide (0 < h.maplen)) := by
    unfold filterOutGroup
    rw [List.filter_filter]
    refine List.filter_congr fun h hh => ?_
    by_cases hMp : 0 < h.maplen
    · have hNe : h.metaPtr ≠ g.metaPtr := fun hE => by
        have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hE
        subst hEq; omega
      simp [hMp, hNe]
    · simp [hMp]
  have hRootMapEq :
      (gs1.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096)) =
        (st.groups.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096)) := by
    rw [hRep.2.2.1, hDeq.root_filter_eq, hFltNotG]
  have hDynEq : dynamicRootRegions stMid = dynamicRootRegions st := by
    unfold dynamicRootRegions; simp only [stMid, hRootMapEq]
  have hRootMemIff : ∀ a : BitVec 64,
      (∃ h ∈ stMid.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
      (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) := by
    intro a
    have hViaMap : ∀ gs : List GroupDesc,
        (∃ h ∈ gs, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
        ∃ iv ∈ (gs.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096)),
          InRegion iv.1 iv.2 a := by
      intro gs
      simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨h, hh, hMp, ha⟩; exact ⟨(h.mem, h.maplen * 4096), ⟨h, ⟨hh, hMp⟩, rfl⟩, ha⟩
      · rintro ⟨_, ⟨h, ⟨hh, hMp⟩, rfl⟩, ha⟩; exact ⟨h, hh, hMp, ha⟩
    rw [hViaMap stMid.groups, hViaMap st.groups, show stMid.groups = gs1 from rfl, hRootMapEq]
  have hCarvedUserIff : ∀ a : BitVec 64, CarvedUserByte stMid a ↔ CarvedUserByte st a := by
    intro a; unfold CarvedUserByte
    constructor
    · rintro ⟨h, hh, s, hs, hSub⟩
      obtain ⟨j, hj, hEqS⟩ := List.getElem_of_mem hs
      cases hS : s with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS] at hSub
      | liveUser p n ec =>
        simp only [hS] at hSub
        rcases hRep.2.2.2.2.2.1 h hh with rfl | ⟨hhDeq, _⟩
        · have hj0 : j < pg0.slots.length := by simpa [pg1] using hj
          by_cases hjEq : j = pIdx
          · subst hjEq
            simp only [pg1, List.getElem_set_self] at hEqS
            rw [← hEqS] at hS; cases hS
          · simp only [pg1, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hEqS
            exact ⟨pg0, hpg0, .liveUser p n ec, (hEqS.trans hS) ▸ List.getElem_mem hj0, hSub⟩
        · obtain ⟨_, h0, hh0, _, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ := hDeq.each_preserved h hhDeq
          have hj0 : j < h0.slots.length := hSLen ▸ hj
          have hSj0 : h0.slots[j]'hj0 = .liveUser p n ec :=
            ((hSP j hj hj0).2 p n ec).mp (hEqS.trans hS)
          exact ⟨h0, hh0, .liveUser p n ec, hSj0 ▸ List.getElem_mem hj0, hSub⟩
    · rintro ⟨h0, hh0, s, hs, hSub⟩
      obtain ⟨j, hj0, hEqS⟩ := List.getElem_of_mem hs
      cases hS : s with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS] at hSub
      | liveUser p n ec =>
        simp only [hS] at hSub
        have hNeG : h0.metaPtr ≠ g.metaPtr := fun hE => by
          have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hE
          subst hEq; exact hNoLiveUserG s hs p n ec hS
        by_cases hEqPg : h0.metaPtr = pg0.metaPtr
        · have hH0Eq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hpg0 hEqPg
          subst hH0Eq
          have hjNe : j ≠ pIdx := fun hJ => by
            subst hJ; rw [hSlotPg] at hEqS; rw [← hEqS] at hS; cases hS
          have hj1 : j < pg1.slots.length := by simp [pg1, hj0]
          have hGet1 : pg1.slots[j]'hj1 = .liveUser p n ec := by
            simp only [pg1, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hEqS, hS]
          exact ⟨pg1, hRep.2.2.2.2.1, .liveUser p n ec, hGet1 ▸ List.getElem_mem hj1, hSub⟩
        · obtain ⟨h, hhDeq, hHM, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ :=
            dequeue_origin_bijection hwf hDeq h0 hh0 hNeG
          have hj : j < h.slots.length := hSLen.symm ▸ hj0
          have hSj : h.slots[j]'hj = .liveUser p n ec :=
            ((hSP j hj hj0).2 p n ec).mpr (hEqS.trans hS)
          exact ⟨h, hRep.2.2.2.2.2.2.1 h hhDeq (fun hE => hEqPg (hHM ▸ hE)),
            .liveUser p n ec, hSj ▸ List.getElem_mem hj, hSub⟩
  have hOwnRwIff : ∀ a : BitVec 64,
      OwnedRwByte stMid a ↔ (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) := by
    intro a; unfold OwnedRwByte CarvedMetaByte
    rw [show stMid.metaAreas = st.metaAreas from rfl, hRootMemIff a, hCarvedUserIff a]
    simp only [stMid, List.mem_cons, exists_eq_or_imp, not_or]
    exact ⟨fun ⟨s, u, ng, nc⟩ => ⟨⟨s, u, nc⟩, ng⟩, fun ⟨⟨s, u, nc⟩, ng⟩ => ⟨s, u, ng, nc⟩⟩
  have hOwnMapIff : ∀ a : BitVec 64, OwnedMappedByte stMid a ↔ OwnedMappedByte st a := by
    intro a; unfold OwnedMappedByte
    change (_ ∨ _ ∨ _ ∨ (∃ h ∈ stMid.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ↔ _
    rw [hRootMemIff a]
  have hLiftNonG : ∀ c0 ∈ st.groups, c0.metaPtr ≠ g.metaPtr →
      ∃ c1 ∈ stMid.groups, c1.metaPtr = c0.metaPtr ∧ c1.parentMeta = c0.parentMeta ∧
        c1.mem = c0.mem ∧ c1.nestedCap = c0.nestedCap ∧ c1.sc = c0.sc := by
    intro c0 hc0 hNeG
    by_cases hEqPg : c0.metaPtr = pg0.metaPtr
    · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hc0 hpg0 hEqPg
      subst hE
      exact ⟨pg1, hRep.2.2.2.2.1, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨c, hcDeq, hM, hMem, _, hSc, _, _, hPar, hCap, _⟩ :=
        dequeue_origin_bijection hwf hDeq c0 hc0 hNeG
      exact ⟨c, hRep.2.2.2.2.2.2.1 c hcDeq (fun hE => hEqPg (hM ▸ hE)), hM, hPar, hMem, hCap, hSc⟩
  have hGroupsWfMid : ∀ h ∈ gs1, GroupWf stMid h := by
    intro h hh
    have ⟨h0, hh0, hMeta, hMem, hMp, hSc, hLast, hActB, hPar, hCap, hSLen, hMetaB, hAvFrDisj,
        hMaskBnd, hSc63Z, hMasksAndPres⟩ :
        ∃ h0 ∈ st.groups,
          h.metaPtr = h0.metaPtr ∧ h.mem = h0.mem ∧ h.maplen = h0.maplen ∧
          h.sc = h0.sc ∧ h.lastIdx = h0.lastIdx ∧ h.activeByte = h0.activeByte ∧
          h.parentMeta = h0.parentMeta ∧ h.nestedCap = h0.nestedCap ∧
          h.slots.length = h0.slots.length ∧
          readBytesFromMap bvDeq h.metaPtr 40 = h.metaBytes ∧
          h.availMask &&& h.freedMask = 0#32 ∧
          (h.availMask ||| h.freedMask).toNat < 2 ^ h.cnt ∧
          (h.sc = 63 → h.prev = 0#64 ∧ h.next = 0#64) ∧
          (∀ j (hj : j < h.slots.length) (hj0 : j < h0.slots.length),
            ((h.availMask.getLsbD j = true ↔ h.slots[j]'hj = .freeAvail) ∧
             (h.freedMask.getLsbD j = true ↔ h.slots[j]'hj = .freeInactive) ∧
             (h.activeIdx < j → h.slots[j]'hj = .freeInactive)) ∧
            (∀ cm, h.slots[j]'hj = .liveNested cm → h0.slots[j]'hj0 = .liveNested cm ∧ cm ≠ g.metaPtr) ∧
            (∀ p n ec, h.slots[j]'hj = .liveUser p n ec ↔ h0.slots[j]'hj0 = .liveUser p n ec)) := by
      rcases hRep.2.2.2.2.2.1 h hh with rfl | ⟨hhDeq, hNePg⟩
      · refine ⟨pg0, hpg0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [pg1],
          hDeq.each_meta_bytes pg0 hpgDeq,
          hPgWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hPgWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          fun h63 => False.elim (by change pg0.sc = 63 at h63; omega), fun j hj hj0 => ?_⟩
        by_cases hjEq : j = pIdx
        · subst hjEq
          have hGet1 : pg1.slots[j]'hj = SlotState.claimed := by simp [pg1]
          rw [hGet1]
          refine ⟨⟨by simp [pg1, hAvPgF], by simp [pg1, hFrPgF], fun hLt => False.elim (hActPgLe hLt)⟩, ?_, ?_⟩
          · intro _ hC; cases hC
          · intro p n ec
            exact Iff.intro (fun hC => nomatch hC) (fun hU => by rw [hSlotPg] at hU; cases hU)
        · have hGet1 : pg1.slots[j]'hj = pg0.slots[j]'hj0 := by simp [pg1, Ne.symm hjEq]
          rw [hGet1]
          have hSWj := hPgWf0.slot_wf j hj0
          refine ⟨⟨hSWj.2.1, hSWj.2.2.1, hSWj.2.2.2.1⟩, ?_, fun _ _ _ => Iff.rfl⟩
          intro cm hLN
          exact ⟨hLN, fun hEqG => hjEq (hUniqueParentSlot pg0 hpg0 j hj0 (hEqG ▸ hLN)).2⟩
      · obtain ⟨hNeG, h0, hh0, hM, hMe, hMp, hSc, hL, hAb, hPa, hCp, hSL, _, _, hSP⟩ :=
          hDeq.each_preserved h hhDeq
        have hMasks := hDeq.each_masks h hhDeq
        refine ⟨h0, hh0, hM, hMe, hMp, hSc, hL, hAb, hPa, hCp, hSL,
          hDeq.each_meta_bytes h hhDeq, hMasks.1, hMasks.2.1, hMasks.2.2.1, fun j hj hj0 => ?_⟩
        exact ⟨hMasks.2.2.2 j hj,
          fun cm hLN =>
            have hLN0 := ((hSP j hj hj0).1 cm).mp hLN
            ⟨hLN0, fun hEqG => hNePg (hM.trans (congrArg GroupDesc.metaPtr
              (hUniqueParentSlot h0 hh0 j hj0 (hEqG ▸ hLN0)).1))⟩,
          (hSP j hj hj0).2⟩
    have hGWf0 := hwf.groups_wf h0 hh0
    have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hMem8_0, hActB_0, _⟩ := hGWf0
    have hNeG0 : h0.metaPtr ≠ g.metaPtr := by
      have hHIn : h.metaPtr ∈ gs1.map (·.metaPtr) := List.mem_map_of_mem hh
      exact hMeta ▸ ((hGs1MetaSet h.metaPtr).mp hHIn).2
    have ⟨hCnt, hStr, hTot, hSto, hSlotSE⟩ := group_stride_total_slot_eq hMem hMp hSc hLast hCap
    have ⟨hBvData0, hBvEnd0⟩ := hDisjDeq.2.2.2.2.2 h0 hh0
    have hActIdxEq : h.activeIdx = h0.activeIdx := by simp [GroupDesc.activeIdx, hActB]
    have hFit64 : h0.mem.toNat + h0.totalBytes ≤ 2 ^ 64 := by
      have := hGWf0.2.2.2.2.2.2.1; omega
    have hTotGe16 : 16 ≤ h0.totalBytes := by
      have := hGWf0.2.2.2.2.2.2.2.1
      have ⟨hSG, _⟩ := group_slot_toNat hGWf0
      have : 1 ≤ h0.cnt := by unfold GroupDesc.cnt; omega
      have : 16 ≤ h0.cnt * h0.stride := Nat.le_trans hSG (Nat.le_mul_of_pos_left _ this)
      omega
    have hMem8 : readBytesFromMap stMid.byteVal h.mem 8 = unpack64 h.metaPtr := by
      change readBytesFromMap bvDeq h.mem 8 = unpack64 h.metaPtr
      rw [hMem, hMeta, ← hMem8_0]
      exact readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
        exact hBvData0 a ((inRegion_iff_toNat hFit64 a).mpr ⟨h1, by omega⟩)
    have hMemActB : stMid.byteVal (h.mem + 8#64) = h.activeByte := by
      change bvDeq (h.mem + 8#64) = h.activeByte
      rw [hMem, hActB, ← hActB_0]
      have hAdd8 : (h0.mem + 8#64).toNat = h0.mem.toNat + 8 := bv64_add_toNat (by omega)
      exact hBvData0 _ ((inRegion_iff_toNat hFit64 _).mpr ⟨by omega, by omega⟩)
    refine ⟨hSc ▸ hGWf0.1, hLast ▸ hGWf0.2.1, hSLen.trans (hCnt ▸ hGWf0.2.2.1),
      fun hSc63 => ?_,
      hMem ▸ hGWf0.2.2.2.2.1, hMem ▸ hGWf0.2.2.2.2.2.1,
      by rw [hMem, hTot]; exact hGWf0.2.2.2.2.2.2.1,
      by rw [hCnt, hStr, hTot]; exact hGWf0.2.2.2.2.2.2.2.1,
      fun hMpH => by rw [hCnt, hStr, hTot]; exact hGWf0.2.2.2.2.2.2.2.2.1 (hMp ▸ hMpH),
      by rw [hLast, (hSlotSE h0.lastIdx).2]; exact hBvEnd0.trans hGWf0.2.2.2.2.2.2.2.2.2.1,
      by rw [hMp, hPar]; exact hGWf0.2.2.2.2.2.2.2.2.2.2.1,
      fun hMpH => ?_,
      fun hMp0 => ?_,
      hAvFrDisj, hMaskBnd,
      by rw [hActIdxEq, hLast]; exact hGWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hMetaB, hMem8, hMemActB,
      fun j hj => ?_⟩
    · have ⟨hL0, hM0, _⟩ := hGWf0.2.2.2.1 (hSc ▸ hSc63)
      exact ⟨hLast ▸ hL0, hMp ▸ hM0, (hSc63Z hSc63).1, (hSc63Z hSc63).2⟩
    · have ⟨r1, r2, r3, r4⟩ := hGWf0.2.2.2.2.2.2.2.2.2.2.2.1 (hMp ▸ hMpH)
      exact ⟨hMem ▸ r1, hCap ▸ r2,
        fun hLe => hMp ▸ r3 (hSc ▸ hLe),
        fun hLt => ⟨hMp ▸ (r4 (hSc ▸ hLt)).1,
          fun hL0 => by
            rw [hStr, hSc, hMp]
            exact (r4 (hSc ▸ hLt)).2 (hLast ▸ hL0)⟩⟩
    · obtain ⟨hL1, pg, hpg, pIdx', hp', hPar0, hPg48, hLtSc, hPg24, hPSlot, hStLe, hEnLe, hCap0⟩ :=
        hGWf0.2.2.2.2.2.2.2.2.2.2.2.2.1 (hMp ▸ hMp0)
      have hPgNeG : pg.metaPtr ≠ g.metaPtr := fun hEq =>
        hNoChildG h0 hh0 (hPar0.trans (congrArg some hEq))
      have hPSlotNe : pIdx' ≠ pIdx ∨ pg.metaPtr ≠ pg0.metaPtr := by
        by_cases hEqP : pg.metaPtr = pg0.metaPtr
        · have hPE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hpg0 hEqP
          subst hPE
          exact Or.inl fun hIdxEq => by
            subst hIdxEq; rw [hSlotPg] at hPSlot; exact hNeG0 (SlotState.liveNested.inj hPSlot).symm
        · exact Or.inr hEqP
      by_cases hEqPg0 : pg.metaPtr = pg0.metaPtr
      · have hPE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hpg0 hEqPg0
        subst hPE
        have hpNe : pIdx' ≠ pIdx := hPSlotNe.resolve_right (by intro hc; exact hc rfl)
        have hp1' : pIdx' < pg1.slots.length := by simp [pg1, hp']
        have hGet1 : pg1.slots[pIdx']'hp1' = .liveNested h.metaPtr := by
          simp only [pg1, List.getElem_set, Ne.symm hpNe, ↓reduceIte, hMeta, hPSlot]
        exact ⟨hLast ▸ hL1, pg1, hRep.2.2.2.2.1, pIdx', hp1',
          hPar.trans hPar0, hPg48, hSc ▸ hLtSc, hPg24, hGet1,
          hMem ▸ hStLe, by rw [hMem, hCap]; exact hEnLe, hCap ▸ hCap0⟩
      · obtain ⟨pgD, hpgD, hPgM, hPgMe, hPgMp, hPgSc, hPgL, _, _, hPgCp, hPgSL, _, _, hPgSP⟩ :=
          dequeue_origin_bijection hwf hDeq pg hpg hPgNeG
        have ⟨_, _, _, _, hPgSE⟩ := group_stride_total_slot_eq hPgMe hPgMp hPgSc hPgL hPgCp
        have hpD : pIdx' < pgD.slots.length := hPgSL.symm ▸ hp'
        have hPSlotD : pgD.slots[pIdx']'hpD = .liveNested h.metaPtr :=
          hMeta ▸ ((hPgSP pIdx' hpD hp').1 h0.metaPtr).mpr hPSlot
        exact ⟨hLast ▸ hL1, pgD, hRep.2.2.2.2.2.2.1 pgD hpgD (fun hE => hEqPg0 (hPgM ▸ hE)),
          pIdx', hpD, hPar.trans (hPgM ▸ hPar0), hPgSc ▸ hPg48,
          by rw [hSc, hPgSc]; exact hLtSc, hPgSc ▸ hPg24, hPSlotD,
          by rw [(hPgSE pIdx').1, hMem]; exact hStLe,
          by rw [hMem, hCap, (hPgSE pIdx').2]; exact hEnLe,
          by rw [hCap, hPgSc]; exact hCap0⟩
    · have hj0 : j < h0.slots.length := hSLen ▸ hj
      have ⟨hMaskJ, hLNImp, hLUIff⟩ := hMasksAndPres j hj hj0
      have hS0 := hGWf0.slot_wf j hj0
      cases hSj : h.slots[j]'hj with
      | freeAvail | freeInactive | claimed =>
        have ⟨hStrGe0, _, _, hEndLast0, _, hSlotCalc0⟩ := group_slot_toNat hGWf0
        have hjCnt0 : j < h0.cnt := hGWf0.2.2.1 ▸ hj0
        have ⟨_, _, hSub40⟩ := hSlotCalc0 j hjCnt0
        have hSucc0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
        have hMulLe0 : (j + 1) * h0.stride ≤ h0.cnt * h0.stride := Nat.mul_le_mul_right _ hjCnt0
        have hEndLeTot0 : (h0.slotEnd h0.lastIdx).toNat ≤ h0.mem.toNat + h0.totalBytes := by
          have := hGWf0.2.2.2.2.2.2.2.1; omega
        have hStartM4 : stMid.byteVal (h.slotStart j - 4#64) = 0#8 := by
          change bvDeq (h.slotStart j - 4#64) = 0#8
          rw [(hSlotSE j).1, hBvData0 _ ((inRegion_iff_toNat hFit64 _).mpr ⟨by omega, by omega⟩)]
          exact hS0.1
        rw [hSj] at hMaskJ
        exact ⟨hStartM4, hMaskJ.1, hMaskJ.2.1, hMaskJ.2.2, trivial⟩
      | liveNested cm =>
        have ⟨hSj0, hCmNeG⟩ := hLNImp cm hSj
        rw [hSj0] at hS0; rw [hSj] at hMaskJ
        exact slotWf_of_groupDataEq hGWf0 hj0 hS0 hBvData0 hMeta hMem hSc hLast hMp hActB
          hMaskJ.1 hMaskJ.2.1 hMaskJ.2.2 fun cm' hEq => by
            cases hEq; intro cg hcg hCgM
            obtain ⟨cg1, hcg1, m1, p1, me1, cp1, _⟩ := hLiftNonG cg hcg (hCgM ▸ hCmNeG)
            exact ⟨cg1, hcg1, m1, p1, me1, cp1⟩
      | liveUser p req ec =>
        have hSj0 : h0.slots[j]'hj0 = .liveUser p req ec := (hLUIff p req ec).mp hSj
        rw [hSj0] at hS0; rw [hSj] at hMaskJ
        exact slotWf_of_groupDataEq hGWf0 hj0 hS0 hBvData0 hMeta hMem hSc hLast hMp hActB
          hMaskJ.1 hMaskJ.2.1 hMaskJ.2.2 fun _ hEq => by cases hEq
  have hClaimPg1 : (pg1.slots.filter SlotState.isClaimed).length =
      (pg0.slots.filter SlotState.isClaimed).length + 1 := by
    have hF := list_set_filter_len pg0.slots hp0 SlotState.claimed SlotState.isClaimed
    rw [hSlotPg] at hF; simpa [pg1, SlotState.isClaimed] using hF
  have hClaimGs1 :
      (gs1.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum =
        (gsDeq.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum + 1 := by
    have hSum : (gs1.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum +
        (pg0.slots.filter SlotState.isClaimed).length =
        (gsDeq.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum +
        (pg1.slots.filter SlotState.isClaimed).length :=
      replaceGroupByMeta_map_sum hDeq.nodup.1 hpgDeq
        (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := pg1)
    omega
  have hLivePg1 : (pg1.slots.map slotLiveCount).sum = (pg0.slots.map slotLiveCount).sum := by
    have hS := list_set_map_sum pg0.slots hp0 SlotState.claimed slotLiveCount
    rw [hSlotPg] at hS; simpa [pg1, slotLiveCount] using hS
  have hEffPg1 : (pg1.slots.map slotEffCost).sum = (pg0.slots.map slotEffCost).sum := by
    have hS := list_set_map_sum pg0.slots hp0 SlotState.claimed slotEffCost
    rw [hSlotPg] at hS; simpa [pg1, slotEffCost] using hS
  have hLiveCntEq : totalLiveCount stMid = totalLiveCount st := by
    have hSum1 : (gs1.map (fun h => (h.slots.map slotLiveCount).sum)).sum +
        (pg0.slots.map slotLiveCount).sum =
        (gsDeq.map (fun h => (h.slots.map slotLiveCount).sum)).sum +
        (pg1.slots.map slotLiveCount).sum :=
      replaceGroupByMeta_map_sum hDeq.nodup.1 hpgDeq
        (fun h => (h.slots.map slotLiveCount).sum) (g1 := pg1)
    have hSumD := hDeq.sum_live
    change (gs1.map (fun h => (h.slots.map slotLiveCount).sum)).sum = totalLiveCount st
    omega
  have hEffSumEq : totalLiveEffCost stMid = totalLiveEffCost st := by
    have hSum1 : (gs1.map (fun h => (h.slots.map slotEffCost).sum)).sum +
        (pg0.slots.map slotEffCost).sum =
        (gsDeq.map (fun h => (h.slots.map slotEffCost).sum)).sum +
        (pg1.slots.map slotEffCost).sum :=
      replaceGroupByMeta_map_sum hDeq.nodup.1 hpgDeq
        (fun h => (h.slots.map slotEffCost).sum) (g1 := pg1)
    have hSumD := hDeq.sum_eff
    change (gs1.map (fun h => (h.slots.map slotEffCost).sum)).sum = totalLiveEffCost st
    omega
  have hPg1EmpEq : pg1.isEmpty = pg0.isEmpty := by
    unfold GroupDesc.isEmpty
    exact isEmpty_set_of_not_free hp0 (by rw [hSlotPg]; rfl) rfl
  have hWfMid : MallocngWFInflight (k + 2) base brkStart brk liveCost peakCost stMid :=
    { base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := ⟨hDeq.lens.1, hDeq.lens.2.1, hwf.ctx_lens.2.2.1, hwf.ctx_lens.2.2.2.1,
        hwf.ctx_lens.2.2.2.2.1, hDeq.lens.2.2⟩
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun hZ => by
        obtain ⟨_, _, _, _, _, _, _, _, _, hGsEmpty, _⟩ := hwf.initZero_wf hZ
        exact False.elim (List.not_mem_nil (hGsEmpty ▸ hg))
      bounces_wf := hwf.bounces_wf
      usage_wf := fun sc hsc => by
        rw [show stMid.groups = gs1 from rfl, hRep.2.2.2.1 sc]
        exact hDeq.usage_eq sc hsc
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
        obtain ⟨h1, h2, h3, hHdr⟩ := hwf.metaAreas_wf.2.1 ma hma
        exact ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          hDisjDeq.1 ma hma a ha).trans hHdr⟩,
        hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
        fun ap hap => by
          obtain ⟨h1, h2, h3, hZ⟩ := hwf.guard_avail_wf.2.2.2 ap hap
          exact ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
            hDisjDeq.2.1 ap hap a ha).trans hZ⟩⟩
      inflight_wf := by
        have hInf := hwf.inflight_wf
        have hSumC := hDeq.sum_claimed
        change (g.metaPtr :: st.reservedMetas).length +
          (gs1.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum ≤ k + 2
        simp only [List.length_cons]; omega
      free_bump_metas_wf := ⟨hwf.free_bump_metas_wf.1,
        fun fm hfm => (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          hDisjDeq.2.2.2.1 fm hfm a ha).trans (hwf.free_bump_metas_wf.2.1 fm hfm),
        hwf.free_bump_metas_wf.2.2.1,
        fun bm hbm => (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          hDisjDeq.2.2.2.2.1 bm hbm a ha).trans (hwf.free_bump_metas_wf.2.2.2.1 bm hbm),
        hUf1Nd, hUf1Iff⟩
      groups_nodup := ⟨hRep.1 ▸ hDeq.nodup.1, hRep.2.1 ▸ hDeq.nodup.2⟩
      groups_wf := hGroupsWfMid
      regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
      active_wf := fun sc h1 h2 => by
        refine activeClassWf_congr_groups hDeq.nodup.1 (hRep.1 ▸ hDeq.nodup.1)
          (fun hA hhA _ => ?_) (fun hB hhB _ => ?_) (hDeq.active_wf_deq sc h1 h2)
        · by_cases hEq : hA.metaPtr = pg0.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hDeq.nodup.1 hhA hpgDeq hEq
            subst hE
            exact ⟨pg1, hRep.2.2.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · exact ⟨hA, hRep.2.2.2.2.2.2.1 hA hhA hEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rcases hRep.2.2.2.2.2.1 hB hhB with rfl | ⟨hhDeq, _⟩
          · exact ⟨pg0, hpgDeq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · exact ⟨hB, hhDeq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      liveMap_wf := fun p n => by
        rw [hwf.liveMap_wf p n]
        constructor
        · rintro ⟨h0, hh0, j, hj0, ec, hSj0⟩
          have hNeG : h0.metaPtr ≠ g.metaPtr := fun hE => by
            have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hE
            subst hEq; exact hNoLiveUserG _ (List.getElem_mem hj0) p n ec hSj0
          by_cases hEqPg : h0.metaPtr = pg0.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hpg0 hEqPg
            subst hE
            have hjNe : j ≠ pIdx := fun hJ => by
              subst hJ; rw [hSlotPg] at hSj0; cases hSj0
            have hj1 : j < pg1.slots.length := by simp [pg1, hj0]
            exact ⟨pg1, hRep.2.2.2.2.1, j, hj1, ec, by
              simp only [pg1, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hSj0]⟩
          · obtain ⟨h, hhDeq, hM, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ :=
              dequeue_origin_bijection hwf hDeq h0 hh0 hNeG
            have hj : j < h.slots.length := hSLen.symm ▸ hj0
            exact ⟨h, hRep.2.2.2.2.2.2.1 h hhDeq (fun hE => hEqPg (hM ▸ hE)), j, hj, ec,
              ((hSP j hj hj0).2 p n ec).mpr hSj0⟩
        · rintro ⟨h, hh, j, hj, ec, hSj⟩
          rcases hRep.2.2.2.2.2.1 h hh with rfl | ⟨hhDeq, _⟩
          · have hj0 : j < pg0.slots.length := by simpa [pg1] using hj
            by_cases hjEq : j = pIdx
            · subst hjEq; simp only [pg1, List.getElem_set_self] at hSj; cases hSj
            · simp only [pg1, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSj
              exact ⟨pg0, hpg0, j, hj0, ec, hSj⟩
          · obtain ⟨_, h0, hh0, _, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ :=
              hDeq.each_preserved h hhDeq
            have hj0 : j < h0.slots.length := hSLen ▸ hj
            exact ⟨h0, hh0, j, hj0, ec, ((hSP j hj hj0).2 p n ec).mp hSj⟩
      live_le_peak := hwf.live_le_peak
      effCost_le_live := hEffSumEq ▸ hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun h hh hEmp => by
        have hToDeq : ∀ u ∈ replaceGroupByMeta gsDeq pg0.metaPtr pg1, u.isEmpty = true →
            ∃ d ∈ gsDeq, u.metaPtr = d.metaPtr ∧ u.sc = d.sc ∧ d.isEmpty = true := by
          intro u hu huEmp
          rcases hRep.2.2.2.2.2.1 u hu with rfl | ⟨huDeq, _⟩
          · exact ⟨pg0, hpgDeq, rfl, rfl, hPg1EmpEq ▸ huEmp⟩
          · exact ⟨u, huDeq, rfl, rfl, huEmp⟩
        rcases hRep.2.2.2.2.2.1 h hh with rfl | ⟨hhDeq, _⟩
        · have hEmp0 : pg0.isEmpty = true := hPg1EmpEq ▸ hEmp
          have ⟨e1, e2, e3, e4, _, _, e7⟩ := hwf.empty_groups_bound pg0 hpg0 hEmp0
          have ⟨hMemAct, hUniqDeq⟩ := hDeq.empty_act_singleton pg0 hpgDeq hEmp0
          exact ⟨e1, e2, e3, e4, hMemAct, fun g' hg' hEmp' hSc' => by
            obtain ⟨d', hd', hM', hScD', hEmpD'⟩ := hToDeq g' hg' hEmp'
            exact hM'.trans (hUniqDeq d' hd' hEmpD' (hScD'.symm.trans hSc')), e7⟩
        · obtain ⟨_, h0, hh0, _, _, hMp, hSc, hLast, _, _, _, _, hEmpEq, _⟩ :=
            hDeq.each_preserved h hhDeq
          have ⟨e1, e2, e3, e4, _, _, e7⟩ := hwf.empty_groups_bound h0 hh0 (hEmpEq ▸ hEmp)
          have ⟨hMemAct, hUniqDeq⟩ := hDeq.empty_act_singleton h hhDeq hEmp
          exact ⟨hMp ▸ e1, hSc ▸ e2, hSc ▸ e3, hMp ▸ e4, hMemAct, fun g' hg' hEmp' hSc' => by
            obtain ⟨d', hd', hM', hScD', hEmpD'⟩ := hToDeq g' hg' hEmp'
            exact hM'.trans (hUniqDeq d' hd' hEmpD' (hScD'.symm.trans hSc')),
            fun hL0 => by rw [hSc, hMp]; exact e7 (hLast ▸ hL0)⟩
      masterDom_wf := ⟨hwf.masterDom_wf.1,
        fun a hOwn => by
          rcases hOwn with hRw1 | hPn1 | hMp1
          · exact hwf.masterDom_wf.2.1 a (Or.inl ((hOwnRwIff a).mp hRw1).1)
          · exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn1))
          · exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inr ((hOwnMapIff a).mp hMp1))),
        fun a ha => by rw [hDynEq]; exact hwf.masterDom_wf.2.2 a ha⟩ }
  have hSubMid : SameLiveUserSub stMid st :=
    sameLiveUserSub_retire_nested_groups hwf hg hIdx hSlotG hAllFree hDeq hpgDeq hp0 hSlotPg rfl rfl rfl
  exact ⟨hpgDeq, hRep.2.2.2.2.1, hWfMid, hOwnRwIff, hOwnMapIff, hLiveCntEq, hDynEq, hSubMid⟩

end LibsignalBinary.Heap.Fine
