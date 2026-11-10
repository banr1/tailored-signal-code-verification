/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers

/-!
# Placed Free Invariant-Transition Helpers (Part 2)

Defines the recursion measure `groupNestBound` (`≤ 6`) for nested group freeing, entry `.liveUser`
slot release (`free_release_userSlot`), and fast-path and keep-group invariant transitions
(`free_set_availMask_fast`, `free_set_freedMask_keep`, `free_queue_fullGroup`) for `__libc_free`
and `nontrivial_free`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

@[expose] public section

/-! ## Recursion Measure `groupNestBound` -/

/-- State-independent upper bound (`0..6`) on the remaining parent-group recursion depth of
    `nontrivial_free` starting at group `g`. Root groups (`0 < g.maplen`) have bound `0`; nested
    groups (`g.maplen = 0`) satisfy `2 * sizeClass g.sc + 1 ≤ sizeClass pg.sc ≤ 146`, strictly
    decreasing `groupNestBound` at every parent step. -/
def groupNestBound (g : GroupDesc) : Nat :=
  if 0 < g.maplen then 0
  else if 36 ≤ sizeClass g.sc then 1
  else if 18 ≤ sizeClass g.sc then 2
  else if 9 ≤ sizeClass g.sc then 3
  else if 4 ≤ sizeClass g.sc then 4
  else if 2 ≤ sizeClass g.sc then 5
  else 6

theorem groupNestBound_le_six (g : GroupDesc) : groupNestBound g ≤ 6 := by
  unfold groupNestBound
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

private theorem nested_sizeClass_step_of_wf {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {cg : GroupDesc} (hcg : cg ∈ st.groups) (hMap0 : cg.maplen = 0) :
    1 ≤ sizeClass cg.sc ∧ sizeClass cg.sc ≤ 72 ∧
    ∃ pg ∈ st.groups, cg.parentMeta = some pg.metaPtr ∧
      pg.sc ≤ 24 ∧ 2 * sizeClass cg.sc + 1 ≤ sizeClass pg.sc := by
  have hGWf := hwf.groups_wf cg hcg
  have ⟨hLastGe1, pg, hpg, _, _, hPar, hPgSc48, hCgLtPg, hPgLe24, _, _, _, hCapEq⟩ :=
    hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
  have hCgSc48 : cg.sc < 48 := Nat.lt_trans hCgLtPg hPgSc48
  have hCgGe1 : 1 ≤ sizeClass cg.sc := (sizeClass_bounds hCgSc48).1
  have hFit : 12 + cg.cnt * cg.stride ≤ cg.totalBytes := hGWf.2.2.2.2.2.2.2.1
  have hStride : cg.stride = 16 * sizeClass cg.sc := by
    simp [GroupDesc.stride, hMap0, slotStride]
  have hTot : cg.totalBytes = 16 * sizeClass pg.sc - 4 := by
    simp [GroupDesc.totalBytes, hMap0, hCapEq, slotStride]
  have hPgLe146 : sizeClass pg.sc ≤ 146 := by
    by_cases hEq24 : pg.sc = 24
    · rw [hEq24]; decide
    · have hLt24 : pg.sc < 24 := by omega
      have hMono := sizeClass_strictMono hLt24 (by decide)
      have h24 : sizeClass 24 = 146 := by decide
      omega
  have hCntGe2 : 2 ≤ cg.cnt := by unfold GroupDesc.cnt; omega
  have hMulGe : 2 * (16 * sizeClass cg.sc) ≤ cg.cnt * cg.stride := by
    rw [hStride]
    exact Nat.mul_le_mul_right _ hCntGe2
  exact ⟨hCgGe1, by omega, pg, hpg, hPar, hPgLe24, by omega⟩

/-- Every nested group `g ∈ st.groups` (`g.maplen = 0`) has strictly larger `groupNestBound` than
    its parent `pg ∈ st.groups`. -/
theorem groupNestBound_parent_lt {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g pg : GroupDesc} (hg : g ∈ st.groups) (hMap0 : g.maplen = 0)
    (hpg : pg ∈ st.groups) (hPar : g.parentMeta = some pg.metaPtr) :
    groupNestBound pg < groupNestBound g := by
  obtain ⟨hGe1, _, pg', hpg', hPar', _, hStep⟩ := nested_sizeClass_step_of_wf hwf hg hMap0
  have hMetaEq : pg'.metaPtr = pg.metaPtr := Option.some.inj (hPar'.symm.trans hPar)
  have hPgEq : pg' = pg := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg' hpg hMetaEq
  subst hPgEq
  by_cases hPgPos : 0 < pg'.maplen
  · unfold groupNestBound
    simp only [hPgPos, hMap0, Nat.lt_irrefl, ↓reduceIte]
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> omega
  · have hPgMap0 : pg'.maplen = 0 := by omega
    obtain ⟨_, hPgLe72, _⟩ := nested_sizeClass_step_of_wf hwf hpg' hPgMap0
    have hGLe35 : sizeClass g.sc ≤ 35 := by omega
    have hNot36 : ¬ 36 ≤ sizeClass g.sc := by omega
    by_cases h18 : 18 ≤ sizeClass g.sc
    · have hPg36 : 36 ≤ sizeClass pg'.sc := by omega
      simp [groupNestBound, hPgPos, hMap0, hNot36, h18, hPg36]
    · by_cases h9 : 9 ≤ sizeClass g.sc
      · have hPg18 : 18 ≤ sizeClass pg'.sc := by omega
        unfold groupNestBound
        simp only [hPgPos, hMap0, Nat.lt_irrefl, hNot36, h18, h9, ↓reduceIte]
        split <;> omega
      · by_cases h4 : 4 ≤ sizeClass g.sc
        · have hPg9 : 9 ≤ sizeClass pg'.sc := by omega
          unfold groupNestBound
          simp only [hPgPos, hMap0, Nat.lt_irrefl, hNot36, h18, h9, h4, ↓reduceIte]
          split <;> try omega
          split <;> omega
        · by_cases h2 : 2 ≤ sizeClass g.sc
          · have hPg4 : 4 ≤ sizeClass pg'.sc := by omega
            unfold groupNestBound
            simp only [hPgPos, hMap0, Nat.lt_irrefl, hNot36, h18, h9, h4, h2, ↓reduceIte]
            split <;> try omega
            split <;> try omega
            split <;> omega
          · have hPg2 : 2 ≤ sizeClass pg'.sc := by omega
            unfold groupNestBound
            simp only [hPgPos, hMap0, Nat.lt_irrefl, hNot36, h18, h9, h4, h2, ↓reduceIte]
            split <;> try omega
            split <;> try omega
            split <;> try omega
            split <;> omega

/-- Root-group `mmap` cap matching `Common.lean`'s `empty_groups_bound` (`1048576` B; implied
    by `GroupWf`). -/
def EmptyGroupKeepWf (st : MallocngSt) : Prop :=
  ∀ g ∈ st.groups, 0 < g.maplen → 7 ≤ g.sc → g.sc ≤ 38 → g.maplen * 4096 ≤ 1048576

theorem emptyGroupKeepWf_of_wf {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight k base brkStart brk liveCost peakCost st) :
    EmptyGroupKeepWf st := by
  intro g hg hMp _ h38
  exact (((hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.1 hMp).2.2.2 (by omega)).1

/-! ## In-Place Group Replacement Combinators -/

/-- Replace the unique group matching `m` in `gs` with `g1`. -/
def replaceGroupByMeta (gs : List GroupDesc) (m : BitVec 64) (g1 : GroupDesc) : List GroupDesc :=
  gs.map fun h => if h.metaPtr == m then g1 else h

/-- In-place replacement by a group of the same class and mapped length keeps
    `Cost.GroupsGrpBound`. -/
theorem groupsGrpBound_replaceGroupByMeta {U : Nat} {gs : List GroupDesc}
    (h : Cost.GroupsGrpBound U gs) {g g1 : GroupDesc} (hg : g ∈ gs) (m : BitVec 64)
    (hSc : g1.sc = g.sc) (hMl : g1.maplen = g.maplen) :
    Cost.GroupsGrpBound U (replaceGroupByMeta gs m g1) :=
  h.map_ite m fun hm hs => by
    rw [hMl] at hm; rw [hSc] at hs; rw [hSc, hMl]; exact h g hg hm hs

/-- Split `gs` around `g ∈ gs` using `(gs.map (·.metaPtr)).Nodup`, giving closed forms for both
    `replaceGroupByMeta` (`pre ++ g1 :: post`) and `filter` removal (`pre ++ post`). -/
theorem split_groups_at_mem {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ gs) :
    ∃ pre post : List GroupDesc,
      gs = pre ++ g :: post ∧
      (∀ h ∈ pre, h.metaPtr ≠ g.metaPtr) ∧
      (∀ h ∈ post, h.metaPtr ≠ g.metaPtr) ∧
      (∀ g1 : GroupDesc, replaceGroupByMeta gs g.metaPtr g1 = pre ++ g1 :: post) ∧
      gs.filter (fun h => !(h.metaPtr == g.metaPtr)) = pre ++ post := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  rw [List.map_append, List.map_cons, List.nodup_append] at hNd
  obtain ⟨hNdPre, hNdCons, hDisj⟩ := hNd
  obtain ⟨hNotPost, _⟩ := List.nodup_cons.mp hNdCons
  have hPreNe : ∀ h ∈ pre, h.metaPtr ≠ g.metaPtr := fun h hh hEq =>
    hDisj h.metaPtr (List.mem_map_of_mem hh) g.metaPtr (List.mem_cons_self ..) hEq
  have hPostNe : ∀ h ∈ post, h.metaPtr ≠ g.metaPtr := fun h hh hEq =>
    hNotPost (hEq ▸ List.mem_map_of_mem hh)
  refine ⟨pre, post, rfl, hPreNe, hPostNe, fun g1 => ?_, ?_⟩
  · unfold replaceGroupByMeta
    rw [List.map_append, List.map_cons]
    have h1 : (pre.map fun h => if h.metaPtr == g.metaPtr then g1 else h) = pre := by
      conv => rhs; rw [← List.map_id pre]
      refine List.map_congr_left fun h hh => ?_
      simp [hPreNe h hh]
    have h2 : (post.map fun h => if h.metaPtr == g.metaPtr then g1 else h) = post := by
      conv => rhs; rw [← List.map_id post]
      refine List.map_congr_left fun h hh => ?_
      simp [hPostNe h hh]
    rw [h1, h2]
    simp
  · rw [List.filter_append, List.filter_cons]
    have h1 : pre.filter (fun h => !(h.metaPtr == g.metaPtr)) = pre :=
      List.filter_eq_self.mpr fun h hh => by simp [hPreNe h hh]
    have h2 : post.filter (fun h => !(h.metaPtr == g.metaPtr)) = post :=
      List.filter_eq_self.mpr fun h hh => by simp [hPostNe h hh]
    simp [h1, h2]

theorem replaceGroupByMeta_props {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g g1 : GroupDesc} (hg : g ∈ gs)
    (hMeta : g1.metaPtr = g.metaPtr) (hMem : g1.mem = g.mem)
    (hMaplen : g1.maplen = g.maplen) (hSc : g1.sc = g.sc) (hLast : g1.lastIdx = g.lastIdx) :
    let gs' := replaceGroupByMeta gs g.metaPtr g1
    gs'.map (·.metaPtr) = gs.map (·.metaPtr) ∧
    gs'.map (·.mem) = gs.map (·.mem) ∧
    (gs'.filter fun h => decide (0 < h.maplen)).map (fun h => (h.mem, h.maplen * 4096)) =
      (gs.filter fun h => decide (0 < h.maplen)).map (fun h => (h.mem, h.maplen * 4096)) ∧
    (∀ sc : Nat, ((gs'.filter (·.sc == sc)).map GroupDesc.cnt).sum =
      ((gs.filter (·.sc == sc)).map GroupDesc.cnt).sum) ∧
    g1 ∈ gs' ∧
    (∀ h ∈ gs', h = g1 ∨ (h ∈ gs ∧ h.metaPtr ≠ g.metaPtr)) ∧
    (∀ h ∈ gs, h.metaPtr ≠ g.metaPtr → h ∈ gs') ∧
    (∀ m : BitVec 64, gs'.find? (·.metaPtr == m) =
      if m == g.metaPtr then some g1 else gs.find? (·.metaPtr == m)) := by
  obtain ⟨pre, post, hGsEq, hPreNe, hPostNe, hRep, _⟩ := split_groups_at_mem hNd hg
  dsimp only []
  rw [hRep g1, hGsEq]
  have hCnt : g1.cnt = g.cnt := by simp [GroupDesc.cnt, hLast]
  refine ⟨?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
  · simp [List.map_append, hMeta]
  · simp [List.map_append, hMem]
  · simp only [List.filter_append, List.filter_cons, List.map_append, hMaplen]
    split <;> simp [hMem, hMaplen]
  · intro sc
    simp only [List.filter_append, List.filter_cons, List.map_append, List.sum_append, hSc]
    split <;> simp [hCnt]
  · intro h hh
    rcases List.mem_append.mp hh with hPre | hCons
    · exact Or.inr ⟨List.mem_append_left _ hPre, hPreNe h hPre⟩
    · rcases List.mem_cons.mp hCons with rfl | hPost
      · exact Or.inl rfl
      · exact Or.inr ⟨List.mem_append_right _ (List.mem_cons_of_mem _ hPost), hPostNe h hPost⟩
  · intro h hh hNe
    rcases List.mem_append.mp hh with hPre | hCons
    · exact List.mem_append_left _ hPre
    · rcases List.mem_cons.mp hCons with rfl | hPost
      · exact False.elim (hNe rfl)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hPost)
  · intro m
    rw [List.find?_append, List.find?_append, List.find?_cons, List.find?_cons]
    by_cases hmEq : m == g.metaPtr
    · have hmP : m = g.metaPtr := beq_iff_eq.mp hmEq
      subst hmP
      have hPreNone : pre.find? (·.metaPtr == g.metaPtr) = none :=
        List.find?_eq_none.mpr fun h hh => by simp [hPreNe h hh]
      simp [hPreNone, hMeta]
    · have hBeqG : (g.metaPtr == m) = false :=
        Bool.eq_false_iff.mpr fun hE => hmEq (beq_iff_eq.mpr (beq_iff_eq.mp hE).symm)
      simp [hmEq, hMeta, hBeqG]

theorem list_set_map_sum {α : Type} (xs : List α) {idx : Nat} (hIdx : idx < xs.length)
    (v : α) (w : α → Nat) :
    ((xs.set idx v).map w).sum + w (xs[idx]'hIdx) = (xs.map w).sum + w v := by
  induction xs generalizing idx with
  | nil => simp at hIdx
  | cons x tl ih =>
    cases idx with
    | zero => simp [Nat.add_comm, Nat.add_left_comm]
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hIdx
      have hSub := ih hk
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

theorem list_set_filter_len {α : Type} (xs : List α) {idx : Nat} (hIdx : idx < xs.length)
    (v : α) (p : α → Bool) :
    ((xs.set idx v).filter p).length + (if p (xs[idx]'hIdx) then 1 else 0) =
      (xs.filter p).length + (if p v then 1 else 0) := by
  induction xs generalizing idx with
  | nil => simp at hIdx
  | cons x tl ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons, List.getElem_cons_zero]
      by_cases hpv : p v = true <;> by_cases hpx : p x = true <;> simp [hpv, hpx] <;> omega
    | succ k =>
      have hk : k < tl.length := Nat.lt_of_succ_lt_succ hIdx
      have hSub := ih hk
      simp only [List.set_cons_succ, List.filter_cons, List.getElem_cons_succ]
      by_cases hpx : p x = true <;> simp [hpx] <;> omega

theorem readBytesFromMap_eq_of_inRegion {v₁ v₂ : BitVec 64 → BitVec 8}
    {b : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : ∀ a : BitVec 64, InRegion b n a → v₁ a = v₂ a) :
    readBytesFromMap v₁ b n = readBytesFromMap v₂ b n := by
  unfold readBytesFromMap
  exact List.map_congr_left fun a ha => h a ((mem_rangeAddrs_iff_inRegion b hn a).mp ha)

set_option maxHeartbeats 400000 in
/-- Preserve `SlotWf` on any other slot `(h, j) ≠ (g, idx)` across any modification confined to
    `SlotWriteMod g idx`. -/
theorem slotWf_other_of_slotWriteMod {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm)
    (hBvOut : ∀ a : BitVec 64, ¬ SlotWriteMod g idx a → st'.byteVal a = st.byteVal a)
    (hNestedMap : ∀ cg ∈ st.groups, cg.maplen = 0 →
      ∃ cg' ∈ st'.groups, cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
        cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap)
    {h h' : GroupDesc} (hh : h ∈ st.groups) {j : Nat} (hj : j < h.slots.length)
    (hDiff : h.metaPtr ≠ g.metaPtr ∨ j ≠ idx)
    (hMetaEq : h'.metaPtr = h.metaPtr) (hMemEq : h'.mem = h.mem)
    (hScEq : h'.sc = h.sc) (hLastEq : h'.lastIdx = h.lastIdx)
    (hMapEq : h'.maplen = h.maplen) (hActEq : h'.activeByte = h.activeByte)
    (hAvailJ : h'.availMask.getLsbD j = h.availMask.getLsbD j)
    (hFreedJ : h'.freedMask.getLsbD j = h.freedMask.getLsbD j)
    {s : SlotState} (hs : h.slots[j]'hj = s)
    (hOv : ∀ u r e, s = .liveUser u r e → st'.liveMap.ov u = st.liveMap.ov u := by
      intros; rfl) :
    SlotWf st' h' j s := by
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hStrideEq : h'.stride = h.stride := by simp [GroupDesc.stride, hLastEq, hMapEq, hScEq]
  have hStorEq : h'.storage = h.storage := by simp [GroupDesc.storage, hMemEq]
  have hStartEq : h'.slotStart j = h.slotStart j := by simp [GroupDesc.slotStart, hStorEq, hStrideEq]
  have hEndEq : h'.slotEnd j = h.slotEnd j := by simp [GroupDesc.slotEnd, hStartEq, hStrideEq]
  have hActIdxEq : h'.activeIdx = h.activeIdx := by simp [GroupDesc.activeIdx, hActEq]
  have hHWf := hwf.groups_wf h hh
  have ⟨_, hStorNat, hStNat, hSub4Nat, hEnNat, _, hEn48, _, _⟩ := group_slot_bounds hHWf hj
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hHWf
  have hSMH : (j + 1) * h.stride = j * h.stride + h.stride := Nat.succ_mul j h.stride
  have hSWf := hHWf.slot_wf j hj
  rw [hs] at hSWf
  have hDisj := (slotWriteMod_disjoint hwf hg hIdx hNotNested).2.2.2 h hh j hj hDiff
  dsimp only [SlotWf] at hSWf ⊢
  rw [hStartEq, hEndEq, hAvailJ, hFreedJ, hActIdxEq, hScEq, hStorEq]
  rcases s with _ | _ | _ | cm | ⟨u, r, c⟩
  · have hIn0 : InRegion (h.slotStart j - 4#64) h.stride (h.slotStart j - 4#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    rw [hBvOut _ (hDisj.1 (by simp [hs]) _ hIn0)]; exact hSWf
  · have hIn0 : InRegion (h.slotStart j - 4#64) h.stride (h.slotStart j - 4#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    rw [hBvOut _ (hDisj.1 (by simp [hs]) _ hIn0)]; exact hSWf
  · have hIn0 : InRegion (h.slotStart j - 4#64) h.stride (h.slotStart j - 4#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    rw [hBvOut _ (hDisj.1 (by simp [hs]) _ hIn0)]; exact hSWf
  · obtain ⟨hB0, hAv, hFr, hAc, hSc48, cg, hcg, hCgM, hCgPar, hCgLo, hCgAl, hCgHi, hCgCap,
      hTot16, hCgM4, hCgM3, hCgM2⟩ := hSWf
    have hCgMap0 : cg.maplen = 0 := Classical.byContradiction fun hP => by
      have hNone := (hwf.groups_wf cg hcg).2.2.2.2.2.2.2.2.2.2.1.mp (by omega)
      rw [hNone] at hCgPar; cases hCgPar
    have ⟨hN0, hNCg⟩ := hDisj.2 cm cg hs hcg hCgM hCgPar
    obtain ⟨cg', hcg', hM', hP', hMem', hCap'⟩ := hNestedMap cg hcg hCgMap0
    have hCgGe := (hwf.groups_wf cg hcg).2.2.2.2.1
    have hCgSub4 := bv64_sub_toNat (a := cg.mem) (n := 4) (by omega)
    have hCgSub3 := bv64_sub_toNat (a := cg.mem) (n := 3) (by omega)
    have hCgSub2 := bv64_sub_toNat (a := cg.mem) (n := 2) (by omega)
    refine ⟨(hBvOut _ hN0).trans hB0, hAv, hFr, hAc, hSc48, cg', hcg', hM'.trans hCgM,
      hMetaEq ▸ hP'.trans hCgPar, hMem' ▸ hCgLo, hMem' ▸ hCgAl,
      by rw [hMem', hCap']; exact hCgHi, hCap'.trans hCgCap, ?_⟩
    rw [hMem']
    refine ⟨hTot16, ?_, ?_, ?_⟩
    · exact (hBvOut _ (hNCg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))).trans hCgM4
    · exact (hBvOut _ (hNCg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩))).trans hCgM3
    · rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
        exact hBvOut a (hNCg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩))]
      exact hCgM2
  · have hSliceAg : ∀ a : BitVec 64, InRegion (h.slotStart j - 4#64) h.stride a →
        st'.byteVal a = st.byteVal a :=
      fun a ha => hBvOut a (hDisj.1 (by simp [hs]) a ha)
    obtain ⟨hB0, hAv, hFr, hAc, hBlkWf, hULo, hUHi, hEffLo, hOffB, hRes31, hScProps, hSc63Prop,
      hUM3, hHdrIte, hRes1, hRes5⟩ := hSWf
    have hUSub3 := bv64_sub_toNat (a := u) (n := 3) (by omega)
    have hUSub4 := bv64_sub_toNat (a := u) (n := 4) (by omega)
    have hUSub2 := bv64_sub_toNat (a := u) (n := 2) (by omega)
    have hIn0 : InRegion (h.slotStart j - 4#64) h.stride (h.slotStart j - 4#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    have hInM3 : InRegion (h.slotStart j - 4#64) h.stride (u - 3#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    refine ⟨(hSliceAg _ hIn0).trans hB0, hAv, hFr, hAc, hBlkWf, hULo, hUHi, hEffLo,
      ⟨hOffB.1, hOffB.2.1, by rw [hOv u r c rfl]; exact hOffB.2.2⟩,
      hRes31, hScProps, fun h63 => hMapEq ▸ hSc63Prop h63, (hSliceAg _ hInM3).trans hUM3,
      ?_, ?_, ?_⟩
    · by_cases hTotLe : (u.toNat - h.storage.toNat) / 16 ≤ 0xffff
      · simp only [hTotLe, ↓reduceIte] at hHdrIte ⊢
        refine ⟨(hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans hHdrIte.1, ?_⟩
        rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)]
        exact hHdrIte.2
      · simp only [hTotLe, ↓reduceIte] at hHdrIte ⊢
        obtain ⟨h63, hj0, hLt27, hM4, hM2, hM8⟩ := hHdrIte
        have hSt0 : (h.slotStart j).toNat = h.storage.toNat := by
          rw [hj0]; simp [GroupDesc.slotStart]
        have hUGt : (h.slotStart j).toNat + 16 ≤ u.toNat := by rw [hSt0]; omega
        have hUSub8 := bv64_sub_toNat (a := u) (n := 8) (by omega)
        refine ⟨h63, hj0, hLt27,
          (hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans hM4, ?_, ?_⟩
        · rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
            exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)]
          exact hM2
        · rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
            exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)]
          exact hM8
    · intro hR1
      have hUAdd := bv64_add_toNat (a := u) (n := r) (by omega)
      exact (hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans (hRes1 hR1)
    · intro hR5
      have hEnSub5 := bv64_sub_toNat (a := h.slotEnd j) (n := 5) (by omega)
      have hEnSub4 := bv64_sub_toNat (a := h.slotEnd j) (n := 4) (by omega)
      refine ⟨(hSliceAg _ ((inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩)).trans (hRes5 hR5).1, ?_⟩
      rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
        exact hSliceAg a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)]
      exact (hRes5 hR5).2

/-! ## `__libc_free` Entry `.liveUser` Slot Release -/

def mkReleasedGroup (g : GroupDesc) (idx : Nat) : GroupDesc :=
  { g with slots := g.slots.set idx .claimed, freshZero := false }

def mkReleasedSt (st : MallocngSt) (g : GroupDesc) (idx : Nat) (p : BitVec 64)
    (bs : List (BitVec 8)) : MallocngSt :=
  let g1 := mkReleasedGroup g idx
  let bv0 := writeBytesToMap st.byteVal (p - 3#64) [0xff#8, 0#8, 0#8]
  let bv1 := writeBytesToMap bv0 p bs
  { st with
    groups  := replaceGroupByMeta st.groups g.metaPtr g1
    byteVal := bv1
    liveMap := st.liveMap.erase p }

/-- Spatial ownership and ghost-map update for `__libc_free`'s IB header clear (`p[-3] := 0xff`,
    `p[-2..-1] := 0`) and caller payload absorption `(p ↦ₛ bs)`. -/
theorem free_release_userSlot_spatial {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} (γ : GhostName)
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {n effCost : Nat} (hSlot : g.slots[idx]'hIdx = .liveUser p n effCost)
    {bs : List (BitVec 8)} (hBsLen : bs.length = n) :
    let st1 := mkReleasedSt st g idx p bs
    (∀ a : BitVec 64, InRegion (p - 3#64) 3 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    (∀ a : BitVec 64, OwnedRwByte st1 a ↔ (OwnedRwByte st a ∨ InRegion p n a)) ∧
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) ∧
    (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p n ∗
      ((p - 3#64) ↦ₛ [0xff#8, 0#8, 0#8]) ∗ (p ↦ₛ bs) ∗
      ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 3#64) 3 a) st.byteVal ⊢
      |==> (MallocngLiveAuth γ st1.liveMap ∗ ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal)) := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let g1 := mkReleasedGroup g idx
  let st1 := mkReleasedSt st g idx p bs
  have hGWf := hwf.groups_wf g hg
  have ⟨_, _, hStNat, hSub4Nat, hEnNat, hEnLeTot, hEn48, _, _⟩ := group_slot_bounds hGWf hIdx
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSWf := hGWf.slot_wf idx hIdx
  rw [hSlot] at hSWf
  have hPLo : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
  have hPHi : p.toNat + n ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
  have hPSub3 := bv64_sub_toNat (a := p) (n := 3) (by omega)
  have hBand := liveUser_band_ownedRw hwf hg hIdx hSlot
  have hHdr3Own : ∀ a : BitVec 64, InRegion (p - 3#64) 3 a → OwnedRwByte st a ∧ a ∈ st.masterDom := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    refine hBand.2.2.2 a ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) fun hInP => ?_
    have ⟨hp1, _⟩ := (inRegion_iff_toNat (by omega) a).mp hInP
    omega
  have hNoRes : st.reservedMetas = [] := by
    have h := hwf.inflight_wf
    cases hR : st.reservedMetas with
    | nil => rfl
    | cons _ _ => simp [hR] at h
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g1)
  obtain ⟨rg, hrg, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rg.mem.toNat + rg.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
  have hPInRg : ∀ a : BitVec 64, InRegion p n a → InRegion rg.mem (rg.maplen * 4096) a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hRootEq : ∀ a : BitVec 64,
      (∃ h ∈ st1.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
      (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) := by
    intro a; constructor
    · rintro ⟨h, hh, hMp, hIn⟩
      rcases hRep.2.2.2.2.2.1 h hh with rfl | ⟨hh0, _⟩
      · exact ⟨g, hg, hMp, hIn⟩
      · exact ⟨h, hh0, hMp, hIn⟩
    · rintro ⟨h, hh, hMp, hIn⟩
      by_cases hEq : h.metaPtr = g.metaPtr
      · rw [mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq] at hMp hIn
        exact ⟨g1, hRep.2.2.2.2.1, hMp, hIn⟩
      · exact ⟨h, hRep.2.2.2.2.2.2.1 h hh hEq, hMp, hIn⟩
  have hCarvedSplit : ∀ a : BitVec 64,
      (CarvedUserByte st a ↔ CarvedUserByte st1 a ∨ InRegion p n a) ∧
      (InRegion p n a → ¬ CarvedUserByte st1 a) := by
    intro a; constructor
    · constructor
      · rintro ⟨h, hh, s, hs, hSub⟩
        obtain ⟨j, hj, hEqS⟩ := List.getElem_of_mem hs
        by_cases hSame : h.metaPtr = g.metaPtr ∧ j = idx
        · rcases hSame with ⟨hMetaSame, rfl⟩
          have hHEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hMetaSame
          subst hHEq
          rw [← hEqS, hSlot] at hSub
          exact Or.inr hSub
        · refine Or.inl ?_
          by_cases hMetaEq : h.metaPtr = g.metaPtr
          · have hHEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hMetaEq
            subst hHEq
            have hjNe : j ≠ idx := fun hJ => hSame ⟨rfl, hJ⟩
            refine ⟨g1, hRep.2.2.2.2.1, s, ?_, hSub⟩
            have hj1 : j < g1.slots.length := by simp [g1, mkReleasedGroup, hj]
            have hGet1 : g1.slots[j]'hj1 = s := by
              simp only [g1, mkReleasedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hEqS]
            exact hGet1 ▸ List.getElem_mem hj1
          · exact ⟨h, hRep.2.2.2.2.2.2.1 h hh hMetaEq, s, hs, hSub⟩
      · rintro (⟨h1, hh1, s, hs, hSub⟩ | hInP)
        · rcases hRep.2.2.2.2.2.1 h1 hh1 with rfl | ⟨hh0, _⟩
          · obtain ⟨j, hj1, hEqS⟩ := List.getElem_of_mem hs
            have hj : j < g.slots.length := by simpa [g1, mkReleasedGroup] using hj1
            by_cases hjEq : j = idx
            · subst hjEq
              simp only [g1, mkReleasedGroup, List.getElem_set_self] at hEqS
              subst hEqS; simp at hSub
            · simp only [g1, mkReleasedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hEqS
              exact ⟨g, hg, s, hEqS ▸ List.getElem_mem hj, hSub⟩
          · exact ⟨h1, hh0, s, hs, hSub⟩
        · exact ⟨g, hg, .liveUser p n effCost, hSlot ▸ List.getElem_mem hIdx, hInP⟩
    · intro hInP ⟨h1, hh1, s, hs, hSub⟩
      obtain ⟨j, hj1, hEqS⟩ := List.getElem_of_mem hs
      cases hS : s with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS] at hSub
      | liveUser u r c =>
        simp only [hS] at hSub
        have ⟨h0, hh0, hj0, hDiff, hSlot0⟩ :
            ∃ h0 ∈ st.groups, ∃ hj0 : j < h0.slots.length,
              (h0 ≠ g ∨ j ≠ idx) ∧ h0.slots[j]'hj0 = .liveUser u r c := by
          rcases hRep.2.2.2.2.2.1 h1 hh1 with rfl | ⟨hh0, hNeM⟩
          · have hj0 : j < g.slots.length := by simpa [g1, mkReleasedGroup] using hj1
            by_cases hjEq : j = idx
            · subst hjEq
              simp only [g1, mkReleasedGroup, List.getElem_set_self] at hEqS
              rw [← hEqS] at hS; cases hS
            · simp only [g1, mkReleasedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hEqS
              exact ⟨g, hg, hj0, Or.inr hjEq, hEqS.trans hS⟩
          · exact ⟨h1, hh0, hj1, Or.inl (fun hE => hNeM (congrArg GroupDesc.metaPtr hE)), hEqS.trans hS⟩
        have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0
        rw [hSlot0] at hSWf0
        have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, _⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
        have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
        have hULo : (h0.slotStart j).toNat ≤ u.toNat := hSWf0.2.2.2.2.2.1
        have hUHi : u.toNat + r ≤ (h0.slotEnd j).toNat := hSWf0.2.2.2.2.2.2.1
        have ⟨haP1, haP2⟩ := (inRegion_iff_toNat (by omega) a).mp hInP
        have ⟨haU1, haU2⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
        exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0])
          (hDiff.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm))
          ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
          ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
  have hOwnIff : ∀ a : BitVec 64, OwnedRwByte st1 a ↔ (OwnedRwByte st a ∨ InRegion p n a) := by
    intro a
    have ⟨hCIff, hCDisj⟩ := hCarvedSplit a
    have hCM1 : ¬ CarvedMetaByte st1 a := by simp [CarvedMetaByte, st1, mkReleasedSt, hNoRes]
    have hCM0 : ¬ CarvedMetaByte st a := by simp [CarvedMetaByte, hNoRes]
    unfold OwnedRwByte
    have hMaEq : st1.metaAreas = st.metaAreas := rfl
    rw [hMaEq, hRootEq a, hCIff]
    constructor
    · rintro ⟨hSrc, hNC1, _⟩
      by_cases hInP : InRegion p n a
      · exact Or.inr hInP
      · exact Or.inl ⟨hSrc, fun hCu => by rcases hCu with h1 | h2; exact hNC1 h1; exact hInP h2, hCM0⟩
    · rintro (⟨hSrc, hNC0, _⟩ | hInP)
      · exact ⟨hSrc, fun h1 => hNC0 (Or.inl h1), hCM1⟩
      · exact ⟨Or.inr ⟨rg, hrg, hRgMp, hPInRg a hInP⟩, hCDisj hInP, hCM1⟩
  have hMappedEq : ∀ a : BitVec 64, OwnedMappedByte st1 a ↔ OwnedMappedByte st a := by
    intro a; unfold OwnedMappedByte
    change (_ ∨ _ ∨ _ ∨ (∃ h ∈ st1.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ↔ _
    rw [hRootEq a]; rfl
  have hProtEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun _ _ => Iff.rfl) fun a _ hProt => ?_
    have hDisjRg : ∀ b4 : BitVec 64, (b4 ∈ st.guardPages ∨ b4 ∈ st.availMetaPages) →
        DisjointRegions b4 4096 rg.mem (rg.maplen * 4096) := by
      intro b4 hb4
      have ⟨_, _, hCross⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
      exact hCross (b4, 4096) (by
        rcases hb4 with hG | hA
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hG))
        · exact List.mem_append_right _ (List.mem_map_of_mem hA))
        (rg.mem, rg.maplen * 4096)
        (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrg, decide_eq_true hRgMp⟩))
    have hNotRg : ¬ InRegion rg.mem (rg.maplen * 4096) a := by
      intro hInRg
      rcases hProt with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
      · exact not_both_inRegion_of_disjointRegions (hDisjRg gp (Or.inl hgp)) haGp hInRg
      · exact not_both_inRegion_of_disjointRegions (hDisjRg ap (Or.inr hap)) haAp hInRg
    have hNotP : ¬ InRegion p n a := fun hInP => hNotRg (hPInRg a hInP)
    have hNotH3 : ¬ InRegion (p - 3#64) 3 a := fun hInH3 => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hInH3
      exact hNotRg ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    simp only [st1, mkReleasedSt]
    rw [writeBytesToMap_out _ _ _ (hBsLen.symm ▸ hNotP),
      writeBytesToMap_out _ _ _ hNotH3]
  have hMapSetEq : MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) :=
    SetSep_congr (fun a _ => hMappedEq a) (fun _ _ _ => rfl)
  refine ⟨hHdr3Own, hOwnIff, hProtEq, hMapSetEq, ?_⟩
  let bv0 := writeBytesToMap st.byteVal (p - 3#64) [0xff#8, 0#8, 0#8]
  have hAbs1Eq : ((p - 3#64) ↦ₛ [0xff#8, 0#8, 0#8]) ∗
      ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 3#64) 3 a) st.byteVal =
      ByteMap st.masterDom (OwnedRwByte st) bv0 := by
    rw [ByteMap_absorb_slice hwf.masterDom_wf.1 st.byteVal (p - 3#64) [0xff#8, 0#8, 0#8]
      (by decide) (fun a ha => (hHdr3Own a ha).2) (fun _ hIn ⟨_, hN⟩ => hN hIn)]
    exact SetSep_congr (fun a _ =>
      ⟨fun h => h.elim And.left (fun ha => (hHdr3Own a ha).1),
       fun h => by by_cases ha : InRegion (p - 3#64) 3 a; exact Or.inr ha; exact Or.inl ⟨h, ha⟩⟩)
      (fun _ _ _ => rfl)
  have hAbs2Eq : (p ↦ₛ bs) ∗ ByteMap st.masterDom (OwnedRwByte st) bv0 =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
    rw [ByteMap_absorb_slice hwf.masterDom_wf.1 bv0 p bs (by omega)
      (fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr ⟨rg, hrg, hRgMp, hPInRg a (hBsLen ▸ ha)⟩))))))
      (fun a hIn hOwn => hOwn.2.1 ⟨g, hg, .liveUser p n effCost, hSlot ▸ List.getElem_mem hIdx, hBsLen ▸ hIn⟩)]
    exact SetSep_congr (fun a _ => by rw [hBsLen]; exact (hOwnIff a).symm) (fun _ _ _ => rfl)
  have hGhost := mallocngBlock_delete_bupd γ st.liveMap p n
  have hRearr :
      MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p n ∗
        ((p - 3#64) ↦ₛ [0xff#8, 0#8, 0#8]) ∗ (p ↦ₛ bs) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 3#64) 3 a) st.byteVal =
      (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p n) ∗
        ((p ↦ₛ bs) ∗ (((p - 3#64) ↦ₛ [0xff#8, 0#8, 0#8]) ∗
          ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 3#64) 3 a) st.byteVal)) := by
    ac_rfl
  rw [hRearr, hAbs1Eq, hAbs2Eq]
  exact Entails.trans (sepConj_mono_left hGhost) (bupd_frame_r _ _)



end

end LibsignalBinary.Heap.Fine.VendorFree
