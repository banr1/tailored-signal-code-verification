/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.AllocSlotFine
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers3

/-!
# Fine-Grained Deallocation and Reallocation Invariant Transitions

Preservation of `MallocngFineInv` across non-null `__libc_free` (`free_preserves_fineInv`,
retiring released `sc = 63` groups at `inflight = 0`), Stage 2 in-place slab `realloc`
(`realloc_inplace_preserves_fineInv`), and Stage 3 `mremap` `realloc`
(`realloc_mremap_preserves_fineInv`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine

open Arm64 ProofLib SepProp
open VerifiedLibraries.Mallocng
open VerifiedLibraries.Mallocng.Proofs

/-! ## List and Slot-Filter Monotonicity -/

private theorem map_eq_self_of_mem_local {α : Type} {xs : List α} {f : α → α}
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

private theorem filter_liveUser_set_nonlive {xs : List SlotState} {idx : Nat}
    (hIdx : idx < xs.length) (sNew : SlotState)
    (hNotLive : isLiveUserSlot sNew = false) :
    ((xs.set idx sNew).filter isLiveUserSlot).length ≤
      (xs.filter isLiveUserSlot).length := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hIdx)
  | cons hd tl ih =>
    cases idx with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons, hNotLive, Bool.false_eq_true, ↓reduceIte]
      cases isLiveUserSlot hd <;> simp
    | succ idx' =>
      have ihLe := ih (Nat.lt_of_succ_lt_succ hIdx)
      simp only [List.set_cons_succ, List.filter_cons]
      cases isLiveUserSlot hd <;> simp [ihLe]

private theorem filter_liveUser_set_both_live {xs : List SlotState} {idx : Nat}
    (hIdx : idx < xs.length)
    (hOld : isLiveUserSlot (xs[idx]'hIdx) = true)
    (sNew : SlotState) (hNew : isLiveUserSlot sNew = true) :
    ((xs.set idx sNew).filter isLiveUserSlot).length =
      (xs.filter isLiveUserSlot).length := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hIdx)
  | cons hd tl ih =>
    cases idx with
    | zero =>
      dsimp only [List.getElem_cons_zero] at hOld
      simp only [List.set_cons_zero, List.filter_cons, hOld, hNew, ↓reduceIte, List.length_cons]
    | succ idx' =>
      have ihEq := ih (Nat.lt_of_succ_lt_succ hIdx) hOld
      simp only [List.set_cons_succ, List.filter_cons]
      cases isLiveUserSlot hd <;> simp [ihEq]

private theorem slotDecl63_congr_update_local {alignMap : BitVec 64 → Option Nat}
    {p : BitVec 64} {alNew : Option Nat} {s : SlotState}
    (hNotP : ∀ req eff, s ≠ .liveUser p req eff) :
    slotDecl63 (fun k => if k = p then alNew else alignMap k) s = slotDecl63 alignMap s := by
  cases s with
  | liveUser p0 req0 eff0 =>
    have hNe : p0 ≠ p := fun hEq => hNotP req0 eff0 (hEq ▸ rfl)
    simp [slotDecl63, hNe]
  | _ => rfl

private theorem sub_map_sum_le {gs' gs : List GroupDesc}
    (hnd' : (gs'.map GroupDesc.metaPtr).Nodup)
    (w' w : GroupDesc → Nat)
    (hMatch : ∀ g' ∈ gs', ∃ g ∈ gs, g.metaPtr = g'.metaPtr ∧ w' g' ≤ w g) :
    (gs'.map w').sum ≤ (gs.map w).sum := by
  induction gs' generalizing gs with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd'
    obtain ⟨g, hg, hMeta, hW⟩ := hMatch hd List.mem_cons_self
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hg
    have hTlMatch : ∀ g' ∈ tl, ∃ x ∈ l1 ++ l2, x.metaPtr = g'.metaPtr ∧ w' g' ≤ w x := by
      intro g' hg'
      obtain ⟨x, hx, hxMeta, hxW⟩ := hMatch g' (List.mem_cons_of_mem _ hg')
      rcases List.mem_append.mp hx with hL1 | hCons
      · exact ⟨x, List.mem_append_left _ hL1, hxMeta, hxW⟩
      · rcases List.mem_cons.mp hCons with rfl | hL2
        · exfalso
          exact hnd'.1 ((hMeta.symm.trans hxMeta) ▸ List.mem_map_of_mem hg')
        · exact ⟨x, List.mem_append_right _ hL2, hxMeta, hxW⟩
    have ihLe := ih hnd'.2 hTlMatch
    rw [List.map_append, List.sum_append] at ihLe
    simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
    omega

private theorem bij_metaPtr_sum_eq {gs' gs : List GroupDesc}
    (hnd' : (gs'.map GroupDesc.metaPtr).Nodup)
    (hnd : (gs.map GroupDesc.metaPtr).Nodup)
    (w' w : GroupDesc → Nat)
    (hFwd : ∀ g' ∈ gs', ∃ g ∈ gs, g.metaPtr = g'.metaPtr ∧ w' g' = w g)
    (hBwd : ∀ g ∈ gs, ∃ g' ∈ gs', g'.metaPtr = g.metaPtr) :
    (gs'.map w').sum = (gs.map w).sum ∧ gs'.length = gs.length := by
  have hLe1 : (gs'.map w').sum ≤ (gs.map w).sum :=
    sub_map_sum_le hnd' w' w fun g' hg' => by
      obtain ⟨g, hg, hM, hEq⟩ := hFwd g' hg'
      exact ⟨g, hg, hM, Nat.le_of_eq hEq⟩
  have hLe2 : (gs.map w).sum ≤ (gs'.map w').sum :=
    sub_map_sum_le hnd w w' fun g hg => by
      obtain ⟨g', hg', hM⟩ := hBwd g hg
      obtain ⟨g2, hg2, hM2, hEq⟩ := hFwd g' hg'
      have hgEq : g2 = g := nodup_metaPtr_eq hnd hg2 hg (hM2.trans hM)
      subst hgEq
      exact ⟨g', hg', hM, Nat.le_of_eq hEq.symm⟩
  have hLen1 : gs'.length ≤ gs.length := by
    have h1 := sub_map_sum_le hnd' (fun _ => 1) (fun _ => 1) fun g' hg' => by
      obtain ⟨g, hg, hM, _⟩ := hFwd g' hg'
      exact ⟨g, hg, hM, Nat.le_refl 1⟩
    have hOnes : ∀ xs : List GroupDesc, (xs.map fun _ => 1).sum = xs.length := by
      intro xs; induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega
    rwa [hOnes, hOnes] at h1
  have hLen2 : gs.length ≤ gs'.length := by
    have h2 := sub_map_sum_le hnd (fun _ => 1) (fun _ => 1) fun g hg => by
      obtain ⟨g', hg', hM⟩ := hBwd g hg
      exact ⟨g', hg', hM, Nat.le_refl 1⟩
    have hOnes : ∀ xs : List GroupDesc, (xs.map fun _ => 1).sum = xs.length := by
      intro xs; induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega
    rwa [hOnes, hOnes] at h2
  exact ⟨Nat.le_antisymm hLe1 hLe2, Nat.le_antisymm hLen1 hLen2⟩

private theorem sameLiveSlots_congr {g' g : GroupDesc}
    (hLen : g'.slots.length = g.slots.length)
    (hIff : ∀ (j : Nat) (hj' : j < g'.slots.length) (hj : j < g.slots.length)
      (q : BitVec 64) (rq eq : Nat),
      g'.slots[j]'hj' = .liveUser q rq eq ↔ g.slots[j]'hj = .liveUser q rq eq) :
    groupLiveUserCount g' = groupLiveUserCount g ∧
    isLarge63Group g' = isLarge63Group g ∧
    (∀ alignMap, (g'.slots.map (slotDecl63 alignMap)).sum =
      (g.slots.map (slotDecl63 alignMap)).sum) := by
  have hPointwise : ∀ (j : Nat) (hj' : j < g'.slots.length) (hj : j < g.slots.length),
      isLiveUserSlot (g'.slots[j]'hj') = isLiveUserSlot (g.slots[j]'hj) ∧
      slotIs63Large (g'.slots[j]'hj') = slotIs63Large (g.slots[j]'hj) ∧
      ∀ alignMap, slotDecl63 alignMap (g'.slots[j]'hj') = slotDecl63 alignMap (g.slots[j]'hj) := by
    intro j hj' hj
    cases hs' : g'.slots[j]'hj' with
    | liveUser q rq eq =>
      have hs : g.slots[j]'hj = .liveUser q rq eq := (hIff j hj' hj q rq eq).mp hs'
      rw [hs]; exact ⟨rfl, rfl, fun _ => rfl⟩
    | freeAvail | freeInactive | claimed | liveNested _ =>
      cases hs : g.slots[j]'hj with
      | liveUser q rq eq =>
        have hs2 : g'.slots[j]'hj' = .liveUser q rq eq := (hIff j hj' hj q rq eq).mpr hs
        rw [hs'] at hs2; cases hs2
      | freeAvail | freeInactive | claimed | liveNested _ =>
        exact ⟨rfl, rfl, fun _ => rfl⟩
  have hAux : ∀ (xs ys : List SlotState) (hL : xs.length = ys.length),
      (∀ (j : Nat) (hx : j < xs.length) (hy : j < ys.length),
        isLiveUserSlot (xs[j]'hx) = isLiveUserSlot (ys[j]'hy) ∧
        slotIs63Large (xs[j]'hx) = slotIs63Large (ys[j]'hy) ∧
        ∀ alignMap, slotDecl63 alignMap (xs[j]'hx) = slotDecl63 alignMap (ys[j]'hy)) →
      (xs.filter isLiveUserSlot).length = (ys.filter isLiveUserSlot).length ∧
      xs.any slotIs63Large = ys.any slotIs63Large ∧
      ∀ alignMap, (xs.map (slotDecl63 alignMap)).sum = (ys.map (slotDecl63 alignMap)).sum := by
    intro xs
    induction xs with
    | nil =>
      intro ys hL _
      cases ys with
      | nil => exact ⟨rfl, rfl, fun _ => rfl⟩
      | cons _ _ => cases hL
    | cons x xtl ih =>
      intro ys hL hP
      cases ys with
      | nil => cases hL
      | cons y ytl =>
        have h0 := hP 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        dsimp only [List.getElem_cons_zero] at h0
        have ihR := ih ytl (Nat.succ.inj hL) fun j hx hy =>
          hP (j + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy)
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.filter_cons, h0.1]
          cases isLiveUserSlot y <;> simp [ihR.1]
        · simp only [List.any_cons, h0.2.1, ihR.2.1]
        · intro am
          simp only [List.map_cons, List.sum_cons, h0.2.2 am, ihR.2.2 am]
  have hRes := hAux g'.slots g.slots hLen hPointwise
  rw [groupLiveUserCount_eq_filter, groupLiveUserCount_eq_filter]
  exact hRes

/-! ## Quiescent Retirement of `sc = 63` Groups and `free` Preservation -/

/-- An `sc = 63` group whose sole slot was released to `.claimed` in `st1` cannot survive into any
    quiescent (`inflight = 0`) state `st'` related by `SameLiveUserSub st' st1`. -/
private theorem sc63_released_absent_in_quiescent
    {base brkStart brk' : BitVec 64} {live' peak' : Nat}
    {st1 st' : MallocngSt} {g1 : GroupDesc}
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hSub : SameLiveUserSub st' st1)
    (hg1 : g1 ∈ st1.groups) (hg1Sc : g1.sc = 63)
    (hg1NoLive : ∀ (j : Nat) (hj : j < g1.slots.length) (q : BitVec 64) (rq eq : Nat),
      g1.slots[j]'hj ≠ .liveUser q rq eq) :
    ∀ g' ∈ st'.groups, g'.metaPtr ≠ g1.metaPtr := by
  intro g' hg' hMetaEq
  obtain ⟨gMatch, hgMatch, hM, hSc, _⟩ := hSub.geom_sub.2.2 g' hg'
  have hgMatchEq : gMatch = g1 :=
    nodup_metaPtr_eq hSub.geom_sub.2.1 hgMatch hg1 (hM.trans hMetaEq)
  subst hgMatchEq
  have hg'Sc : g'.sc = 63 := hSc.symm.trans hg1Sc
  have hGWf' := hwf'.groups_wf g' hg'
  have hLast0 : g'.lastIdx = 0 := (hGWf'.2.2.2.1 hg'Sc).1
  have hLen1 : 0 < g'.slots.length := by
    rw [hGWf'.2.2.1]; unfold GroupDesc.cnt; omega
  obtain ⟨hSlotLenEq, hIff⟩ := hSub.live_slots_iff g' hg' gMatch hg1 hMetaEq
  have hIdx1 : 0 < gMatch.slots.length := hSlotLenEq ▸ hLen1
  have hSWf := hGWf'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hLen1
  have hMmap : g'.isMmapped = true := by simp [GroupDesc.isMmapped, hg'Sc]
  have hNotFree : (g'.slots[0]'hLen1).isFree = false :=
    not_isFree_of_isMmapped hwf' hg' hMmap (List.getElem_mem hLen1)
  cases hs' : g'.slots[0]'hLen1 with
  | freeAvail => rw [hs'] at hNotFree; cases hNotFree
  | freeInactive => rw [hs'] at hNotFree; cases hNotFree
  | liveUser q rq eq =>
    exact hg1NoLive 0 hIdx1 q rq eq ((hIff 0 hLen1 hIdx1 q rq eq).mp hs')
  | liveNested cm =>
    dsimp only [SlotWf] at hSWf
    rw [hs'] at hSWf
    have hLt48 : g'.sc < 48 := hSWf.2.2.2.2.1
    omega
  | claimed =>
    have hInflight := hwf'.inflight_wf
    unfold totalClaimedSlots at hInflight
    have hMemG' : (g'.slots.filter SlotState.isClaimed).length ≤
        (st'.groups.map fun x => (x.slots.filter SlotState.isClaimed).length).sum := by
      obtain ⟨l1, l2, hEqG⟩ := List.append_of_mem hg'
      rw [hEqG, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      omega
    have hMemS : SlotState.claimed ∈ g'.slots := hs' ▸ List.getElem_mem hLen1
    have hPos : 1 ≤ (g'.slots.filter SlotState.isClaimed).length := by
      obtain ⟨s1, s2, hEqS⟩ := List.append_of_mem hMemS
      rw [hEqS, List.filter_append, List.filter_cons]
      simp [SlotState.isClaimed]; omega
    omega

/-- Non-null `__libc_free(p)` preserves `MallocngFineInv 0` under `FineBudget.stepFree align req b`. -/
theorem free_preserves_fineInv
    {base brkStart brk0 brk' : BitVec 64} {live0 peak0 live' peak' : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st' : MallocngSt}
    {g0 : GroupDesc} {idx0 align req eff : Nat} {p : BitVec 64} {bs : List (BitVec 8)}
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hwf0 : MallocngWF base brkStart brk0 live0 peak0 st0)
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hg0 : g0 ∈ st0.groups)
    (hIdx0 : idx0 < g0.slots.length)
    (hSlot0 : g0.slots[idx0]'hIdx0 = .liveUser p req eff)
    (hBsLen : bs.length = req)
    (hAlign0 : alignMap p = some (max align 16))
    (hSub : SameLiveUserSub st' (VendorFree.mkReleasedSt st0 g0 idx0 p bs)) :
    let alignMap' := fun k => if k = p then none else alignMap k
    MallocngFineInv 0 (FineBudget.stepFree align req b) (dynamicRootRegions st') alignMap' st' := by
  intro alignMap'
  let st1 := VendorFree.mkReleasedSt st0 g0 idx0 p bs
  let g1 := VendorFree.mkReleasedGroup g0 idx0
  let b' := FineBudget.stepFree align req b
  have hRelWf := VendorFree.free_release_userSlot_wf (b := synthCoarseBudget live0 peak0 st0)
    (ivs := dynamicRootRegions st0) 0 hwf0
    (synthCoarseBudget_countIvsWF st0 (groupsGrpBound_128_of_geom hInv0.groups_geom))
    hg0 hIdx0 hSlot0 hBsLen
  obtain ⟨hg1Mem1, hg1Len, hg1Claimed, _, hwf1, _⟩ := hRelWf
  have hNd0 : (st0.groups.map GroupDesc.metaPtr).Nodup := hwf0.groups_nodup.1
  have hRepProps := VendorFree.replaceGroupByMeta_props hNd0 hg0
    (g1 := g1) rfl rfl rfl rfl rfl
  have hNoP1 : ∀ g ∈ st1.groups, ∀ (j : Nat) (hj : j < g.slots.length) (r0 e0 : Nat),
      g.slots[j]'hj ≠ .liveUser p r0 e0 := by
    intro g hg j hj r0 e0 hEq
    have hL1 : st1.liveMap p = some r0 := (hwf1.liveMap_wf p r0).mpr ⟨g, hg, j, hj, e0, hEq⟩
    have hNone : st1.liveMap p = none := by
      change (st0.liveMap.erase p).req p = none
      simp [MallocngLiveMap.erase_req]
    rw [hNone] at hL1; cases hL1
  have hNoPOther0 : ∀ g ∈ st0.groups, ∀ (j : Nat) (hj : j < g.slots.length) (r0 e0 : Nat),
      (g.metaPtr ≠ g0.metaPtr ∨ j ≠ idx0) → g.slots[j]'hj ≠ .liveUser p r0 e0 := by
    intro g hg j hj r0 e0 hDiff hEq
    by_cases hMeta : g.metaPtr = g0.metaPtr
    · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hMeta
      subst hgEq
      have hjNe : j ≠ idx0 := hDiff.resolve_left (not_not.mpr rfl)
      have hj1 : j < g1.slots.length := hg1Len ▸ hj
      have hS1 : g1.slots[j]'hj1 = .liveUser p r0 e0 := by
        dsimp only [g1, VendorFree.mkReleasedGroup]
        exact (List.getElem_set_ne (Ne.symm hjNe) hj1).trans hEq
      exact hNoP1 g1 hg1Mem1 j hj1 r0 e0 hS1
    · have hgMem1 : g ∈ st1.groups := hRepProps.2.2.2.2.2.2.1 g hg hMeta
      exact hNoP1 g hgMem1 j hj r0 e0 hEq
  have hSub10 : GroupsSubGeometry st1 st0 := by
    refine ⟨hRepProps.1 ▸ hNd0, hNd0, ?_⟩
    intro x hx
    rcases hRepProps.2.2.2.2.2.1 x hx with rfl | ⟨hx0, _⟩
    · exact ⟨g0, hg0, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨x, hx0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hSub'0 : GroupsSubGeometry st' st0 := GroupsSubGeometry.trans hSub.geom_sub hSub10
  have hGeom' : ∀ g' ∈ st'.groups, GroupFineGeom g' :=
    hSub'0.groupFineGeom hInv0.groups_geom
  have hAlignWf' : FineAlignWf st' alignMap' := by
    refine ⟨?_, ?_⟩
    · intro q al hAl
      dsimp only [alignMap'] at hAl
      by_cases hq : q = p
      · subst hq; simp at hAl
      · simp only [hq, ↓reduceIte] at hAl
        obtain ⟨h16, n, hL0⟩ := hInv0.alignMap_wf.1 q al hAl
        have hL' : st'.liveMap q = some n := by
          rw [hSub.liveMap_eq]
          change (st0.liveMap.erase p).req q = some n
          simp [MallocngLiveMap.erase_req, hq, hL0]
        exact ⟨h16, n, hL'⟩
    · intro g' hg' j hj' q r0 e0 hS'
      obtain ⟨x1, hx1, hxMeta, hxSc, hxMap, _⟩ := hSub.geom_sub.2.2 g' hg'
      obtain ⟨hLenEq, hIff⟩ := hSub.live_slots_iff g' hg' x1 hx1 hxMeta.symm
      have hj1 : j < x1.slots.length := hLenEq ▸ hj'
      have hS1 : x1.slots[j]'hj1 = .liveUser q r0 e0 := (hIff j hj' hj1 q r0 e0).mp hS'
      have hqNe : q ≠ p := fun hEq => hNoP1 x1 hx1 j hj1 r0 e0 (hEq ▸ hS1)
      rcases hRepProps.2.2.2.2.2.1 x1 hx1 with rfl | ⟨hx0, _⟩
      · have hjNe : j ≠ idx0 := by
          intro hEqJ; subst hEqJ
          rw [hg1Claimed hj1] at hS1; cases hS1
        have hj0 : j < g0.slots.length := hg1Len.symm ▸ hj1
        have hS0 : g0.slots[j]'hj0 = .liveUser q r0 e0 := by
          dsimp only [g1, VendorFree.mkReleasedGroup] at hS1
          exact (List.getElem_set_ne (Ne.symm hjNe) hj1).symm.trans hS1
        obtain ⟨al, hAl, hBnd⟩ := hInv0.alignMap_wf.2 g0 hg0 j hj0 q r0 e0 hS0
        exact ⟨al, by simp [alignMap', hqNe, hAl], fun h63' => by
          have h63 : g0.sc = 63 := hxSc.trans h63'
          have hB := hBnd h63
          exact ⟨hB.1, hxMap ▸ hB.2⟩⟩
      · obtain ⟨al, hAl, hBnd⟩ := hInv0.alignMap_wf.2 x1 hx0 j hj1 q r0 e0 hS1
        exact ⟨al, by simp [alignMap', hqNe, hAl], fun h63' => by
          have h63 : x1.sc = 63 := hxSc.trans h63'
          have hB := hBnd h63
          exact ⟨hB.1, hxMap ▸ hB.2⟩⟩
  have hLiveLe : ∀ k < 48, liveSlotsInClass st' k ≤ liveSlotsInClass st0 k := by
    intro k _
    unfold liveSlotsInClass allGroups
    have hNdF' : ((st'.groups.filter (·.sc == k)).map GroupDesc.metaPtr).Nodup :=
      hSub'0.1.sublist (List.Sublist.map GroupDesc.metaPtr List.filter_sublist)
    refine sub_map_sum_le hNdF' groupLiveUserCount groupLiveUserCount ?_
    intro g' hg'F
    obtain ⟨hg', hSc'⟩ := List.mem_filter.mp hg'F
    obtain ⟨x1, hx1, hxMeta, hxSc, _⟩ := hSub.geom_sub.2.2 g' hg'
    obtain ⟨hLenEq, hIff⟩ := hSub.live_slots_iff g' hg' x1 hx1 hxMeta.symm
    have hCntEq := (sameLiveSlots_congr hLenEq hIff).1
    rcases hRepProps.2.2.2.2.2.1 x1 hx1 with rfl | ⟨hx0, _⟩
    · have hSc0 : (g0.sc == k) = true := by rw [← hxSc] at hSc'; exact hSc'
      have hg1Le : groupLiveUserCount g1 ≤ groupLiveUserCount g0 := by
        rw [groupLiveUserCount_eq_filter, groupLiveUserCount_eq_filter]
        exact filter_liveUser_set_nonlive hIdx0 .claimed rfl
      exact ⟨g0, List.mem_filter.mpr ⟨hg0, hSc0⟩, hxMeta, hCntEq ▸ hg1Le⟩
    · have hSc0 : (x1.sc == k) = true := by rw [← hxSc] at hSc'; exact hSc'
      exact ⟨x1, List.mem_filter.mpr ⟨hx0, hSc0⟩, hxMeta, Nat.le_of_eq hCntEq⟩
  have hg1Absent63 : g0.sc = 63 → ∀ g' ∈ st'.groups, g'.metaPtr ≠ g0.metaPtr := by
    intro hg0Sc63
    have hLast0 : g0.lastIdx = 0 := ((hwf0.groups_wf g0 hg0).2.2.2.1 hg0Sc63).1
    have hg0Len1 : g0.slots.length = 1 := by
      rw [(hwf0.groups_wf g0 hg0).2.2.1]; unfold GroupDesc.cnt; omega
    have hg1Sc63 : g1.sc = 63 := hg0Sc63
    refine sc63_released_absent_in_quiescent (g1 := g1) hwf' hSub hg1Mem1 hg1Sc63 ?_
    intro j hj q rq eq hS
    have hjEqIdx0 : j = idx0 := by rw [hg1Len, hg0Len1] at hj; rw [hg0Len1] at hIdx0; omega
    subst hjEqIdx0
    rw [hg1Claimed hj] at hS; cases hS
  have hFwd63 : ∀ g' ∈ groups63 st', ∃ g ∈ groups63 st0,
      g.metaPtr = g'.metaPtr ∧ g.metaPtr ≠ g0.metaPtr ∧
      g'.maplen = g.maplen ∧
      isLarge63Group g' = isLarge63Group g ∧
      (g'.slots.map (slotDecl63 alignMap')).sum = (g.slots.map (slotDecl63 alignMap)).sum := by
    intro g' hg'63
    obtain ⟨hg', hSc63'⟩ := List.mem_filter.mp hg'63
    have hg'Sc : g'.sc = 63 := beq_iff_eq.mp hSc63'
    obtain ⟨x1, hx1, hxMeta, hxSc, hxMap, _⟩ := hSub.geom_sub.2.2 g' hg'
    obtain ⟨hLenEq, hIff⟩ := hSub.live_slots_iff g' hg' x1 hx1 hxMeta.symm
    have hCongr := sameLiveSlots_congr hLenEq hIff
    have hx1Sc : x1.sc = 63 := hxSc.trans hg'Sc
    rcases hRepProps.2.2.2.2.2.1 x1 hx1 with rfl | ⟨hx0, hxNe⟩
    · exact False.elim (hg1Absent63 hx1Sc g' hg' hxMeta.symm)
    · have hDeclEq : (x1.slots.map (slotDecl63 alignMap')).sum =
          (x1.slots.map (slotDecl63 alignMap)).sum := by
        congr 1
        refine List.map_congr_left fun s hs => ?_
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
        exact slotDecl63_congr_update_local fun r0 e0 hS =>
          hNoPOther0 x1 hx0 j hj r0 e0 (Or.inl hxNe) hS
      exact ⟨x1, List.mem_filter.mpr ⟨hx0, beq_iff_eq.mpr hx1Sc⟩,
        hxMeta, hxNe, hxMap.symm, hCongr.2.1, (hCongr.2.2 alignMap').trans hDeclEq⟩
  have hBwdLarge63 : ∀ g ∈ large63Groups st0, g.metaPtr ≠ g0.metaPtr →
      ∃ g' ∈ large63Groups st', g'.metaPtr = g.metaPtr := by
    intro g hgL hNeMeta
    obtain ⟨hg63, hIsL⟩ := List.mem_filter.mp hgL
    obtain ⟨hgMem0, hSc63⟩ := List.mem_filter.mp hg63
    have hgMem1 : g ∈ st1.groups := hRepProps.2.2.2.2.2.2.1 g hgMem0 hNeMeta
    obtain ⟨s, hsMem, hsLarge⟩ := List.any_eq_true.mp hIsL
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsMem
    have hHasLive : ∃ q rq eq, g.slots[j]'hj = .liveUser q rq eq := by
      cases hs : g.slots[j]'hj with
      | liveUser q rq eq => exact ⟨q, rq, eq, rfl⟩
      | _ => rw [hs] at hsLarge; cases hsLarge
    obtain ⟨q, rq, eq, hSlotJ⟩ := hHasLive
    have hInMap' : g.metaPtr ∈ st'.groups.map GroupDesc.metaPtr := by
      by_contra hNotIn
      exact hSub.retired_no_liveUser g hgMem1 hNotIn j hj q rq eq hSlotJ
    obtain ⟨g', hg', hg'Meta⟩ := List.mem_map.mp hInMap'
    obtain ⟨gMatch, hgMatch, hM, _, _, hIsL', _⟩ :=
      hFwd63 g' (List.mem_filter.mpr ⟨hg', by
        obtain ⟨y, hy, hyM, hySc, _⟩ := hSub.geom_sub.2.2 g' hg'
        have hyEq : y = g := nodup_metaPtr_eq hSub.geom_sub.2.1 hy hgMem1 (hyM.trans hg'Meta)
        subst hyEq
        exact beq_iff_eq.mpr (hySc.symm.trans (beq_iff_eq.mp hSc63))⟩)
    have hgMatchEq : gMatch = g :=
      nodup_metaPtr_eq hNd0 (List.mem_filter.mp hgMatch).1 hgMem0 (hM.trans hg'Meta)
    subst hgMatchEq
    have hg'63 : g' ∈ groups63 st' := by
      obtain ⟨y, hy, hyM, hySc, _⟩ := hSub.geom_sub.2.2 g' hg'
      have hyEq : y = gMatch := nodup_metaPtr_eq hSub.geom_sub.2.1 hy hgMem1 (hyM.trans hg'Meta)
      subst hyEq
      exact List.mem_filter.mpr ⟨hg', beq_iff_eq.mpr (hySc.symm.trans (beq_iff_eq.mp hSc63))⟩
    exact ⟨g', List.mem_filter.mpr ⟨hg'63, hIsL'.trans hIsL⟩, hg'Meta⟩
  have hNdStr' : ((straddle63Groups st').map GroupDesc.metaPtr).Nodup :=
    hSub'0.1.sublist (List.Sublist.map GroupDesc.metaPtr
      (List.Sublist.trans List.filter_sublist List.filter_sublist))
  have hStrCntLe : (straddle63Groups st').length ≤ (straddle63Groups st0).length := by
    have h1 := sub_map_sum_le hNdStr' (fun _ => 1) (fun _ => 1) fun g' hg'S => by
      obtain ⟨hg'63, hNotL'⟩ := List.mem_filter.mp hg'S
      obtain ⟨g, hg63, hM, _, _, hIsLEq, _⟩ := hFwd63 g' hg'63
      have hNotL : (!isLarge63Group g) = true := hIsLEq ▸ hNotL'
      exact ⟨g, List.mem_filter.mpr ⟨hg63, hNotL⟩, hM, Nat.le_refl 1⟩
    have hOnes : ∀ xs : List GroupDesc, (xs.map fun _ => 1).sum = xs.length := by
      intro xs; induction xs with | nil => rfl | cons _ _ ih => simp [ih]; omega
    rwa [hOnes, hOnes] at h1
  have hStrBytesLe : straddle63Bytes st' ≤ straddle63Bytes st0 := by
    unfold straddle63Bytes
    refine sub_map_sum_le hNdStr' (fun g => g.maplen * 4096) (fun g => g.maplen * 4096) ?_
    intro g' hg'S
    obtain ⟨hg'63, hNotL'⟩ := List.mem_filter.mp hg'S
    obtain ⟨g, hg63, hM, _, hMapEq, hIsLEq, _⟩ := hFwd63 g' hg'63
    have hNotL : (!isLarge63Group g) = true := hIsLEq ▸ hNotL'
    exact ⟨g, List.mem_filter.mpr ⟨hg63, hNotL⟩, hM, Nat.le_of_eq (by rw [hMapEq])⟩
  have hNdL' : ((large63Groups st').map GroupDesc.metaPtr).Nodup :=
    hSub'0.1.sublist (List.Sublist.map GroupDesc.metaPtr
      (List.Sublist.trans List.filter_sublist List.filter_sublist))
  have hNdL0 : ((large63Groups st0).map GroupDesc.metaPtr).Nodup :=
    hNd0.sublist (List.Sublist.map GroupDesc.metaPtr
      (List.Sublist.trans List.filter_sublist List.filter_sublist))
  have hLarge63 :
      large63DeclBytes st' alignMap' = b'.live63Bytes ∧
      (large63Groups st').length = b'.live63Count ∧
      b'.live63Bytes ≤ b'.peak63Bytes ∧
      b'.live63Count ≤ b'.peak63Count := by
    by_cases hBig : Guaranteed63Threshold ≤ req
    ·
      have hg0Sc63 : g0.sc = 63 :=
        no_slab_slot_ge_guaranteed63 (hwf0.groups_wf g0 hg0)
          (hInv0.groups_geom g0 hg0) hIdx0 hSlot0 hBig
      have hg0Last0 : g0.lastIdx = 0 := ((hwf0.groups_wf g0 hg0).2.2.2.1 hg0Sc63).1
      have hg0Slots1 : g0.slots = [.liveUser p req eff] := by
        have hLen1 : g0.slots.length = 1 := by
          rw [(hwf0.groups_wf g0 hg0).2.2.1]; unfold GroupDesc.cnt; omega
        cases hL : g0.slots with
        | nil => rw [hL] at hLen1; cases hLen1
        | cons s0 tl =>
          cases tl with
          | nil =>
            have hIdxEq0 : idx0 = 0 := by omega
            subst hIdxEq0
            have hEqS : s0 = .liveUser p req eff := by
              have h := hSlot0; simp only [hL, List.getElem_cons_zero] at h; exact h
            rw [hEqS]
          | cons _ _ => rw [hL] at hLen1; cases hLen1
      have hg0InL0 : g0 ∈ large63Groups st0 := by
        refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hg0, beq_iff_eq.mpr hg0Sc63⟩, ?_⟩
        simp [isLarge63Group, hg0Slots1, slotIs63Large, hBig]
      obtain ⟨l1, l2, hSplitL0⟩ := List.append_of_mem hg0InL0
      have hNdSplit : (((l1 ++ g0 :: l2).map GroupDesc.metaPtr)).Nodup := hSplitL0 ▸ hNdL0
      have hNotInRest : ∀ x ∈ l1 ++ l2, x.metaPtr ≠ g0.metaPtr := by
        intro x hx hEq
        rw [List.map_append, List.map_cons, List.nodup_append] at hNdSplit
        rcases List.mem_append.mp hx with h1 | h2
        · exact hNdSplit.2.2 _ (List.mem_map_of_mem h1) _ (List.mem_cons_self) hEq
        · rw [List.nodup_cons] at hNdSplit
          exact hNdSplit.2.1.1 (hEq ▸ List.mem_map_of_mem h2)
      have hNdRest : ((l1 ++ l2).map GroupDesc.metaPtr).Nodup := by
        have hSubL : (l1 ++ l2).Sublist (l1 ++ g0 :: l2) :=
          List.Sublist.append (List.Sublist.refl l1) (List.sublist_cons_self g0 l2)
        exact hNdSplit.sublist (List.Sublist.map GroupDesc.metaPtr hSubL)
      have hBij := bij_metaPtr_sum_eq hNdL' hNdRest
        (fun g => (g.slots.map (slotDecl63 alignMap')).sum)
        (fun g => (g.slots.map (slotDecl63 alignMap)).sum)
        (fun g' hg'L => by
          obtain ⟨hg'63, hIsL'⟩ := List.mem_filter.mp hg'L
          obtain ⟨g, hg63, hM, hNe, _, hIsLEq, hDeclEq⟩ := hFwd63 g' hg'63
          have hgL0 : g ∈ large63Groups st0 :=
            List.mem_filter.mpr ⟨hg63, hIsLEq ▸ hIsL'⟩
          rw [hSplitL0] at hgL0
          rcases List.mem_append.mp hgL0 with h1 | hCons
          · exact ⟨g, List.mem_append_left _ h1, hM, hDeclEq⟩
          · rcases List.mem_cons.mp hCons with rfl | h2
            · exact False.elim (hNe rfl)
            · exact ⟨g, List.mem_append_right _ h2, hM, hDeclEq⟩)
        (fun g hgRest => by
          have hgL0 : g ∈ large63Groups st0 := by
            rw [hSplitL0]
            rcases List.mem_append.mp hgRest with h1 | h2
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
          exact hBwdLarge63 g hgL0 (hNotInRest g hgRest))
      have hg0Decl : (g0.slots.map (slotDecl63 alignMap)).sum = declCost63 req (max align 16) := by
        simp [hg0Slots1, slotDecl63, hBig, hAlign0]
      have hTotalBytes : large63DeclBytes st0 alignMap =
          large63DeclBytes st' alignMap' + declCost63 req (max align 16) := by
        unfold large63DeclBytes
        rw [hSplitL0, List.map_append, List.map_cons, List.sum_append, List.sum_cons, hg0Decl]
        have hRestSum : (((l1 ++ l2).map fun g => (g.slots.map (slotDecl63 alignMap)).sum)).sum =
            ((l1.map fun g => (g.slots.map (slotDecl63 alignMap)).sum)).sum +
            ((l2.map fun g => (g.slots.map (slotDecl63 alignMap)).sum)).sum := by
          rw [List.map_append, List.sum_append]
        have := hBij.1
        omega
      have hTotalCnt : (large63Groups st0).length = (large63Groups st').length + 1 := by
        rw [hSplitL0, List.length_append, List.length_cons]
        have hRestLen : (l1 ++ l2).length = l1.length + l2.length := List.length_append
        have := hBij.2
        omega
      have hBBytes := hInv0.live63_eq.1
      have hBCnt := hInv0.live63_eq.2
      dsimp only [b', FineBudget.stepFree]
      simp only [hBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      exact ⟨by omega, by omega, by omega, by omega⟩
    ·
      have hg0NotInL0 : ∀ g ∈ large63Groups st0, g.metaPtr ≠ g0.metaPtr := by
        intro g hgL hMetaEq
        have hgEq : g = g0 := nodup_metaPtr_eq hNd0
          (List.mem_filter.mp (List.mem_filter.mp hgL).1).1 hg0 hMetaEq
        subst hgEq
        obtain ⟨hg63, hIsL⟩ := List.mem_filter.mp hgL
        have hgSc63 : g.sc = 63 := beq_iff_eq.mp (List.mem_filter.mp hg63).2
        have hgLast0 : g.lastIdx = 0 := ((hwf0.groups_wf g hg0).2.2.2.1 hgSc63).1
        have hLen1 : g.slots.length = 1 := by
          rw [(hwf0.groups_wf g hg0).2.2.1]; unfold GroupDesc.cnt; omega
        obtain ⟨s, hsMem, hsLarge⟩ := List.any_eq_true.mp hIsL
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hsMem
        have hjEq : j = idx0 := by omega
        subst hjEq
        rw [hSlot0] at hsLarge
        simp [slotIs63Large, hBig] at hsLarge
      have hBij := bij_metaPtr_sum_eq hNdL' hNdL0
        (fun g => (g.slots.map (slotDecl63 alignMap')).sum)
        (fun g => (g.slots.map (slotDecl63 alignMap)).sum)
        (fun g' hg'L => by
          obtain ⟨hg'63, hIsL'⟩ := List.mem_filter.mp hg'L
          obtain ⟨g, hg63, hM, _, _, hIsLEq, hDeclEq⟩ := hFwd63 g' hg'63
          exact ⟨g, List.mem_filter.mpr ⟨hg63, hIsLEq ▸ hIsL'⟩, hM, hDeclEq⟩)
        (fun g hgL0 => hBwdLarge63 g hgL0 (hg0NotInL0 g hgL0))
      have hBBytes := hInv0.live63_eq.1
      have hBCnt := hInv0.live63_eq.2
      dsimp only [b', FineBudget.stepFree]
      simp only [hBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      exact ⟨hBij.1.trans hBBytes, hBij.2.trans hBCnt, by omega, by omega⟩
  obtain ⟨pk, pkSC, pkSB, hPkLen, hPkLive, hPkAll, hPkEdge, hPkRoot,
    hPkSC, hPkSB, hPkCumG, hPkCumB⟩ := hInv0.small_witness
  have hCumEq : b'.cumSmallBytes = b.cumSmallBytes ∧ b'.cumSmallGroupsS = b.cumSmallGroupsS := by
    dsimp only [b', FineBudget.stepFree]
    by_cases hBig : Guaranteed63Threshold ≤ req <;> simp [hBig]
  have hMetaMono : fineMaxMetaAreas b ≤ fineMaxMetaAreas b' :=
    fineMaxMetaAreas_mono (.free align req) b
  refine {
    ivs_eq := fun _ => rfl
    groups_geom := hGeom'
    alignMap_wf := hAlignWf'
    live63_eq := ⟨hLarge63.1, hLarge63.2.1⟩
    live63_le_peak := ⟨hLarge63.2.2.1, hLarge63.2.2.2⟩
    metaAreas_le := by
      rw [hSub.metaAreas_eq]
      exact Nat.le_trans hInv0.metaAreas_le hMetaMono
    small_witness := ⟨pk, pkSC, pkSB, hPkLen,
      fun k hk => Nat.le_trans (hLiveLe k hk) (hPkLive k hk),
      fun k hk => Nat.le_trans (hSub'0.allGroups_length_le k) (hPkAll k hk),
      fun ch hch pSc hpSc => Nat.le_trans (hSub'0.nestedEdge_length_le ch pSc) (hPkEdge ch hch pSc hpSc),
      fun k hk => Nat.le_trans (hSub'0.rootBytes_le k) (hPkRoot k hk),
      Nat.le_trans hStrCntLe hPkSC,
      Nat.le_trans hStrBytesLe hPkSB,
      hCumEq.2 ▸ hPkCumG,
      hCumEq.1 ▸ hPkCumB⟩
  }

/-! ## Stage 2 In-Place `realloc` Preservation -/

/-- Stage 2 in-place `realloc` (`g0.sc < 48`, `newSz ≤ 131051`, updating `g0.slots[idx0]` from
    `.liveUser p oldSz oldEff` to `.liveUser p newSz newEff`) preserves `MallocngFineInv 0`
    under `FineBudget.stepRealloc align oldSz newSz b` with `alignMap` unchanged. -/
theorem realloc_inplace_preserves_fineInv
    {base brkStart brk0 : BitVec 64} {live0 peak0 : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st' : MallocngSt}
    {g0 g0' : GroupDesc} {idx0 align oldSz oldEff newSz newEff : Nat} {p : BitVec 64}
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hwf0 : MallocngWF base brkStart brk0 live0 peak0 st0)
    (hg0 : g0 ∈ st0.groups) (hg0Sc : g0.sc < 48)
    (hIdx0 : idx0 < g0.slots.length)
    (hSlot0 : g0.slots[idx0]'hIdx0 = .liveUser p oldSz oldEff)
    (hAlign0 : alignMap p = some (max align 16))
    (hNewSmall : newSz ≤ MmapThresholdReq)
    (hg0Same : FineGroupSameGeom g0' g0)
    (hg0'Slots : g0'.slots = g0.slots.set idx0 (.liveUser p newSz newEff))
    (hGroups' : st'.groups = st0.groups.map fun x =>
      if x.metaPtr == g0.metaPtr then g0' else x)
    (hMetaEq : st'.metaAreas = st0.metaAreas)
    (hLiveMap' : ∀ k, st'.liveMap k = if k = p then some newSz else st0.liveMap k) :
    MallocngFineInv 0 (FineBudget.stepRealloc align oldSz newSz b)
      (dynamicRootRegions st') alignMap st' := by
  let f (x : GroupDesc) : GroupDesc := if x.metaPtr == g0.metaPtr then g0' else x
  have hGroupsF : st'.groups = st0.groups.map f := hGroups'
  have hNd0 : (st0.groups.map GroupDesc.metaPtr).Nodup := hwf0.groups_nodup.1
  have hfHit : f g0 = g0' := by simp [f]
  have hfMiss : ∀ x, x.metaPtr ≠ g0.metaPtr → f x = x := fun x hNe => by simp [f, hNe]
  have hg0'Sc : g0'.sc < 48 := hg0Same.2.1 ▸ hg0Sc
  have hNot63Old : ¬ Guaranteed63Threshold ≤ oldSz := by
    intro hBig
    have h63 := no_slab_slot_ge_guaranteed63 (hwf0.groups_wf g0 hg0)
      (hInv0.groups_geom g0 hg0) hIdx0 hSlot0 hBig
    omega
  have hNot63New : ¬ Guaranteed63Threshold ≤ newSz := by
    unfold MmapThresholdReq at hNewSmall
    unfold Guaranteed63Threshold
    omega
  have hGeom' : ∀ g' ∈ st'.groups, GroupFineGeom g' := by
    intro g' hg'
    rw [hGroupsF] at hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    by_cases hMeta : g.metaPtr = g0.metaPtr
    · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hMeta
      subst hgEq; rw [hfHit]
      exact hg0Same.groupFineGeom_iff.mpr (hInv0.groups_geom g hg)
    · rw [hfMiss g hMeta]; exact hInv0.groups_geom g hg
  have hIdx0' : idx0 < g0'.slots.length := by rw [hg0'Slots, List.length_set]; exact hIdx0
  have hSlot0' : g0'.slots[idx0]'hIdx0' = .liveUser p newSz newEff := by
    cases g0'; dsimp only at hg0'Slots hIdx0' ⊢; subst hg0'Slots; exact List.getElem_set_self hIdx0'
  have hAlignWf' : FineAlignWf st' alignMap := by
    refine ⟨?_, ?_⟩
    · intro q al hAl
      obtain ⟨h16, n0, hL0⟩ := hInv0.alignMap_wf.1 q al hAl
      by_cases hq : q = p
      · subst hq; exact ⟨h16, newSz, by simp [hLiveMap']⟩
      · exact ⟨h16, n0, by simp [hLiveMap', hq, hL0]⟩
    · intro g' hg' j hj q r0 e0 hS
      rw [hGroupsF] at hg'
      obtain ⟨g, hg, hg'Eq⟩ := List.mem_map.mp hg'
      by_cases hMeta : g.metaPtr = g0.metaPtr
      · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hMeta
        subst hgEq
        have hg'Eq0 : g' = g0' := hg'Eq.symm.trans hfHit
        subst hg'Eq0
        by_cases hjEq : j = idx0
        · subst hjEq
          rw [hSlot0'] at hS
          injection hS with hq hr he
          subst hq hr he
          exact ⟨max align 16, hAlign0, fun h63 => by omega⟩
        · have hj0 : j < g.slots.length := by rwa [hg0'Slots, List.length_set] at hj
          have hS0 : g.slots[j]'hj0 = .liveUser q r0 e0 := by
            have hGet : g'.slots[j]'hj = g.slots[j]'hj0 := by
              cases g'; dsimp only at hg0'Slots hj ⊢; subst hg0'Slots
              exact List.getElem_set_ne (Ne.symm hjEq) _
            exact hGet.symm.trans hS
          obtain ⟨al, hAl, _⟩ := hInv0.alignMap_wf.2 g hg j hj0 q r0 e0 hS0
          exact ⟨al, hAl, fun h63 => by omega⟩
      · have hg'EqG : g' = g := hg'Eq.symm.trans (hfMiss g hMeta)
        subst hg'EqG
        exact hInv0.alignMap_wf.2 g' hg j hj q r0 e0 hS
  have hg0'CntEq : groupLiveUserCount g0' = groupLiveUserCount g0 := by
    rw [groupLiveUserCount_eq_filter, groupLiveUserCount_eq_filter, hg0'Slots]
    exact filter_liveUser_set_both_live hIdx0 (by rw [hSlot0]; rfl) _ rfl
  have hPointwise : ∀ g ∈ st0.groups,
      FineGroupSameGeom (f g) g ∧ groupLiveUserCount (f g) = groupLiveUserCount g := by
    intro g hg
    by_cases hMeta : g.metaPtr = g0.metaPtr
    · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hMeta
      subst hgEq; rw [hfHit]; exact ⟨hg0Same, hg0'CntEq⟩
    · rw [hfMiss g hMeta]; exact ⟨FineGroupSameGeom.refl g, rfl⟩
  have hGroups63Eq : groups63 st' = groups63 st0 := by
    unfold groups63; rw [hGroupsF]
    have hNd := hNd0
    generalize st0.groups = gs at hNd hPointwise ⊢
    induction gs with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.nodup_cons] at hNd
      have hA := (hPointwise a List.mem_cons_self).1
      have ihEq := ih hNd.2 fun g hg => hPointwise g (List.mem_cons_of_mem _ hg)
      by_cases hM : a.metaPtr = g0.metaPtr
      · have hfA : f a = g0' := by simp [f, hM]
        have h63A' : (g0'.sc == 63) = false := by rw [beq_eq_false_iff_ne]; omega
        have h63A : (a.sc == 63) = false := by rw [← hA.2.1, hfA]; exact h63A'
        rw [List.map_cons, hfA]
        simp only [List.filter_cons, h63A', h63A, Bool.false_eq_true, ↓reduceIte, ihEq]
      · simp only [List.map_cons, hfMiss a hM, List.filter_cons]
        cases a.sc == 63 <;> simp [ihEq]
  have hSub'0 : GroupsSubGeometry st' st0 := by
    refine ⟨?_, hNd0, ?_⟩
    · rw [hGroupsF]
      have hMapMeta : (st0.groups.map f).map GroupDesc.metaPtr = st0.groups.map GroupDesc.metaPtr := by
        rw [List.map_map]
        refine List.map_congr_left fun g hg => (hPointwise g hg).1.1
      rwa [hMapMeta]
    · intro g' hg'
      rw [hGroupsF] at hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      have hS := (hPointwise g hg).1
      exact ⟨g, hg, hS.1.symm, hS.2.1.symm, hS.2.2.1.symm, hS.2.2.2.1.symm,
        by unfold GroupDesc.cnt; rw [hS.2.2.2.2],
        by unfold GroupDesc.stride; rw [hS.2.1, hS.2.2.1, hS.2.2.2.2]⟩
  have hLiveEq : ∀ k, liveSlotsInClass st' k = liveSlotsInClass st0 k := by
    intro k; unfold liveSlotsInClass allGroups; rw [hGroupsF]
    have hNd := hNd0
    generalize st0.groups = gs at hNd hPointwise ⊢
    induction gs with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.nodup_cons] at hNd
      have hA := hPointwise a List.mem_cons_self
      have ihEq := ih hNd.2 fun g hg => hPointwise g (List.mem_cons_of_mem _ hg)
      simp only [List.map_cons, List.filter_cons, hA.1.2.1]
      cases a.sc == k
      · exact ihEq
      · simp only [↓reduceIte, List.map_cons, List.sum_cons, hA.2, ihEq]
  let b' := FineBudget.stepRealloc align oldSz newSz b
  have hBud :
      b'.live63Bytes = b.live63Bytes ∧
      b'.live63Count = b.live63Count ∧
      b'.live63Bytes ≤ b'.peak63Bytes ∧
      b'.live63Count ≤ b'.peak63Count ∧
      b.cumSmallBytes ≤ b'.cumSmallBytes ∧
      b.cumSmallGroupsS ≤ b'.cumSmallGroupsS := by
    dsimp only [b', FineBudget.stepRealloc, FineBudget.stepFree, FineBudget.stepReallocAdd]
    simp only [hNot63New, hNot63Old, ↓reduceIte, finePeak63Bytes, finePeak63Count]
    exact ⟨trivial, trivial, Nat.le_max_right _ _, Nat.le_max_right _ _, by omega, by omega⟩
  obtain ⟨pk, pkSC, pkSB, hPkLen, hPkLive, hPkAll, hPkEdge, hPkRoot,
    hPkSC, hPkSB, hPkCumG, hPkCumB⟩ := hInv0.small_witness
  have hLargeEq : large63Groups st' = large63Groups st0 := by
    unfold large63Groups; rw [hGroups63Eq]
  have hLD : large63DeclBytes st' alignMap = large63DeclBytes st0 alignMap := by
    unfold large63DeclBytes; rw [hLargeEq]
  have hStrEq : straddle63Groups st' = straddle63Groups st0 := by
    unfold straddle63Groups; rw [hGroups63Eq]
  refine {
    ivs_eq := fun _ => rfl
    groups_geom := hGeom'
    alignMap_wf := hAlignWf'
    live63_eq := ⟨by rw [hLD, hInv0.live63_eq.1, hBud.1],
      by rw [hLargeEq, hInv0.live63_eq.2, hBud.2.1]⟩
    live63_le_peak := ⟨hBud.2.2.1, hBud.2.2.2.1⟩
    metaAreas_le := by
      rw [hMetaEq]
      exact Nat.le_trans hInv0.metaAreas_le (fineMaxMetaAreas_mono (.realloc align oldSz newSz) b)
    small_witness := ⟨pk, pkSC, pkSB, hPkLen,
      fun k hk => (hLiveEq k).symm ▸ hPkLive k hk,
      fun k hk => Nat.le_trans (hSub'0.allGroups_length_le k) (hPkAll k hk),
      fun ch hch pSc hpSc => Nat.le_trans (hSub'0.nestedEdge_length_le ch pSc) (hPkEdge ch hch pSc hpSc),
      fun k hk => Nat.le_trans (hSub'0.rootBytes_le k) (hPkRoot k hk),
      hStrEq ▸ hPkSC,
      by unfold straddle63Bytes; rw [hStrEq]; exact hPkSB,
      Nat.le_trans hPkCumG hBud.2.2.2.2.2,
      Nat.le_trans hPkCumB hBud.2.2.2.2.1⟩
  }

/-! ## Stage 3 `mremap` `realloc` Preservation -/

/-- Stage 3 `mremap` `realloc` (`g0.sc = 63`, `131051 < newSz`, updating `g0` to `g0'` with
    `g0'.maplen * 4096 = ((newSz + (p.toNat - (g0.slotStart 0).toNat) + 4115) / 4096) * 4096` and
    `g0'.slots = [.liveUser newQ newSz newEff]`) preserves `MallocngFineInv 0` across all four
    `(oldSz, newSz) ≶ Guaranteed63Threshold` regimes. -/
theorem realloc_mremap_preserves_fineInv
    {base brkStart brk0 brk' : BitVec 64} {live0 peak0 live' peak' : Nat}
    {b : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat} {st0 st' : MallocngSt}
    {g0 g0' : GroupDesc} {idx0 align oldSz oldEff newSz newEff : Nat} {p newQ : BitVec 64}
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap st0)
    (hwf0 : MallocngWF base brkStart brk0 live0 peak0 st0)
    (hwf' : MallocngWF base brkStart brk' live' peak' st')
    (hg0 : g0 ∈ st0.groups) (hg0Sc : g0.sc = 63)
    (hIdx0 : idx0 < g0.slots.length)
    (hSlot0 : g0.slots[idx0]'hIdx0 = .liveUser p oldSz oldEff)
    (hAlign0 : alignMap p = some (max align 16))
    (hg0'Meta : g0'.metaPtr = g0.metaPtr)
    (hg0'Sc : g0'.sc = 63)
    (hg0'Map : g0'.maplen * 4096 =
      ((newSz + (p.toNat - (g0.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hg0'Slots : g0'.slots = [.liveUser newQ newSz newEff])
    (hEffDiff : newEff - max newSz MallocngMinBlockCost =
      oldEff - max oldSz MallocngMinBlockCost)
    (hFreshNewQ : newQ ≠ p → st0.liveMap newQ = none)
    (hGroups' : st'.groups = st0.groups.map fun x =>
      if x.metaPtr == g0.metaPtr then g0' else x)
    (hMetaEq : st'.metaAreas = st0.metaAreas)
    (hLiveMap' : ∀ k, st'.liveMap k =
      if k = newQ then some newSz else if k = p then none else st0.liveMap k) :
    let alignMap' := fun k =>
      if k = newQ then some (max align 16) else if k = p then none else alignMap k
    MallocngFineInv 0 (FineBudget.stepRealloc align oldSz newSz b)
      (dynamicRootRegions st') alignMap' st' := by
  intro alignMap'
  let effAlign := max align 16
  let f (x : GroupDesc) : GroupDesc := if x.metaPtr == g0.metaPtr then g0' else x
  have hGroupsF : st'.groups = st0.groups.map f := hGroups'
  have hNd0 : (st0.groups.map GroupDesc.metaPtr).Nodup := hwf0.groups_nodup.1
  have hfHit : f g0 = g0' := by simp [f]
  have hfMiss : ∀ x, x.metaPtr ≠ g0.metaPtr → f x = x := fun x hNe => by simp [f, hNe]
  have hg0Last0 : g0.lastIdx = 0 := ((hwf0.groups_wf g0 hg0).2.2.2.1 hg0Sc).1
  have hg0Slots1 : g0.slots = [.liveUser p oldSz oldEff] := by
    have hLen1 : g0.slots.length = 1 := by
      rw [(hwf0.groups_wf g0 hg0).2.2.1]; unfold GroupDesc.cnt; omega
    cases hL : g0.slots with
    | nil => rw [hL] at hLen1; cases hLen1
    | cons s0 tl =>
      cases tl with
      | nil =>
        have hIdxEq0 : idx0 = 0 := by omega
        subst hIdxEq0
        have hEqS : s0 = .liveUser p oldSz oldEff := by
          have h := hSlot0; simp only [hL, List.getElem_cons_zero] at h; exact h
        rw [hEqS]
      | cons _ _ => rw [hL] at hLen1; cases hLen1
  have hIdxEq0 : idx0 = 0 := by rw [hg0Slots1, List.length_singleton] at hIdx0; omega
  obtain ⟨al0, hAl0, hBnd0⟩ := hInv0.alignMap_wf.2 g0 hg0 idx0 hIdx0 p oldSz oldEff hSlot0
  have hAlEq : al0 = effAlign := Option.some.inj (hAl0.symm.trans hAlign0)
  subst hAlEq
  have hOldSlack : oldEff - max oldSz MallocngMinBlockCost ≤ effAlign - 16 := (hBnd0 hg0Sc).1
  have hNewSlack : newEff - max newSz MallocngMinBlockCost ≤ effAlign - 16 :=
    hEffDiff ▸ hOldSlack
  have hSWf0 := (hwf0.groups_wf g0 hg0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx0 hIdx0
  have hOffLe : p.toNat - (g0.slotStart 0).toNat ≤
      (oldEff - max oldSz MallocngMinBlockCost) + 255 * 16 := by
    subst hIdxEq0
    dsimp only [SlotWf] at hSWf0
    rw [hSlot0] at hSWf0
    exact hSWf0.2.2.2.2.2.2.2.2.1.1
  have hg0'MapLe : g0'.maplen * 4096 ≤ declCost63 newSz effAlign := by
    rw [hg0'Map]; unfold declCost63; omega
  have hAlignEqOther : ∀ x ∈ st0.groups, x.metaPtr ≠ g0.metaPtr →
      ∀ (j : Nat) (hj : j < x.slots.length) (q : BitVec 64) (r0 e0 : Nat),
      x.slots[j]'hj = .liveUser q r0 e0 → alignMap' q = alignMap q := by
    intro x hx hxNe j hj q r0 e0 hS
    have hxIn' : x ∈ st'.groups := by
      rw [hGroupsF]; exact (hfMiss x hxNe) ▸ List.mem_map_of_mem hx
    by_cases hQP : newQ = p
    · subst hQP
      by_cases hq : q = newQ
      · subst hq; simp [alignMap', hAlign0]
      · simp [alignMap', hq]
    · have hqNeNew : q ≠ newQ := by
        intro hEq; subst hEq
        have hL0 : st0.liveMap q = some r0 := (hwf0.liveMap_wf q r0).mpr ⟨x, hx, j, hj, e0, hS⟩
        rw [hFreshNewQ hQP] at hL0; cases hL0
      have hqNeOld : q ≠ p := by
        intro hEq; subst hEq
        have hL' : st'.liveMap q = some r0 := (hwf'.liveMap_wf q r0).mpr ⟨x, hxIn', j, hj, e0, hS⟩
        have hNone' : st'.liveMap q = none := by simp [hLiveMap', Ne.symm hQP]
        rw [hNone'] at hL'; cases hL'
      simp [alignMap', hqNeNew, hqNeOld]
  have hGeom' : ∀ g' ∈ st'.groups, GroupFineGeom g' := by
    intro g' hg'
    rw [hGroupsF] at hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    by_cases hM : g.metaPtr = g0.metaPtr
    · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hM
      subst hgEq; rw [hfHit]
      exact ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩
    · rw [hfMiss g hM]; exact hInv0.groups_geom g hg
  have hAlignWf' : FineAlignWf st' alignMap' := by
    refine ⟨?_, ?_⟩
    · intro q al hAl
      dsimp only [alignMap'] at hAl
      by_cases hq1 : q = newQ
      · subst hq1
        simp only [↓reduceIte, Option.some.injEq] at hAl
        subst hAl
        exact ⟨Nat.le_max_right align 16, newSz, by simp [hLiveMap']⟩
      · simp only [hq1, ↓reduceIte] at hAl
        by_cases hq2 : q = p
        · subst hq2; simp at hAl
        · simp only [hq2, ↓reduceIte] at hAl
          obtain ⟨h16, n0, hL0⟩ := hInv0.alignMap_wf.1 q al hAl
          exact ⟨h16, n0, by simp [hLiveMap', hq1, hq2, hL0]⟩
    · intro g' hg' j hj q r0 e0 hS
      rw [hGroupsF] at hg'
      obtain ⟨g, hg, hg'Eq⟩ := List.mem_map.mp hg'
      by_cases hM : g.metaPtr = g0.metaPtr
      · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hM
        subst hgEq
        have hg'Eq0 : g' = g0' := hg'Eq.symm.trans hfHit
        subst hg'Eq0
        have hj0 : j = 0 := by rw [hg0'Slots, List.length_singleton] at hj; omega
        subst hj0
        have hS0 : g'.slots[0]'hj = .liveUser newQ newSz newEff := by
          cases g'; dsimp only at hg0'Slots hj ⊢; subst hg0'Slots; rfl
        rw [hS0] at hS
        injection hS with hq hr he
        subst hq hr he
        exact ⟨effAlign, by simp [alignMap', effAlign], fun _ => ⟨hNewSlack, hg0'MapLe⟩⟩
      · have hg'EqG : g' = g := hg'Eq.symm.trans (hfMiss g hM)
        subst hg'EqG
        obtain ⟨al, hAl, hBnd⟩ := hInv0.alignMap_wf.2 g' hg j hj q r0 e0 hS
        have hAmEq := hAlignEqOther g' hg hM j hj q r0 e0 hS
        exact ⟨al, hAmEq.trans hAl, hBnd⟩
  have hSlabEq :
      (∀ k < 48, allGroups st' k = allGroups st0 k) ∧
      (∀ ch < 48, ∀ pSc < 48, nestedEdge st' ch pSc = nestedEdge st0 ch pSc) ∧
      (∀ k < 48, rootBytes st' k = rootBytes st0 k) := by
    have hAuxAll : ∀ k < 48, ∀ {gs : List GroupDesc},
        (∀ g ∈ gs, g.metaPtr = g0.metaPtr → g.sc = 63) →
        (gs.map f).filter (·.sc == k) = gs.filter (·.sc == k) := by
      intro k hk gs hSc63
      induction gs with
      | nil => rfl
      | cons a l ih =>
        have ihEq := ih fun g hg => hSc63 g (List.mem_cons_of_mem _ hg)
        by_cases hM : a.metaPtr = g0.metaPtr
        · have ha63 : a.sc = 63 := hSc63 a List.mem_cons_self hM
          have hfA : f a = g0' := by simp [f, hM]
          have hFA : (a.sc == k) = false := by rw [beq_eq_false_iff_ne, ha63]; omega
          have hFA' : (g0'.sc == k) = false := by rw [beq_eq_false_iff_ne, hg0'Sc]; omega
          simp only [List.map_cons, hfA, List.filter_cons, hFA, hFA', Bool.false_eq_true, ↓reduceIte, ihEq]
        · simp only [List.map_cons, hfMiss a hM, List.filter_cons]
          cases a.sc == k <;> simp [ihEq]
    have hAuxPred : ∀ (P : GroupDesc → Bool),
        (∀ x, x.sc = 63 → P x = false) →
        ∀ {gs : List GroupDesc},
        (∀ g ∈ gs, g.metaPtr = g0.metaPtr → g.sc = 63) →
        (gs.map f).filter P = gs.filter P := by
      intro P hP63 gs hSc63
      induction gs with
      | nil => rfl
      | cons a l ih =>
        have ihEq := ih fun g hg => hSc63 g (List.mem_cons_of_mem _ hg)
        by_cases hM : a.metaPtr = g0.metaPtr
        · have ha63 : a.sc = 63 := hSc63 a List.mem_cons_self hM
          have hfA : f a = g0' := by simp [f, hM]
          simp only [List.map_cons, hfA, List.filter_cons, hP63 a ha63, hP63 g0' hg0'Sc,
            Bool.false_eq_true, ↓reduceIte, ihEq]
        · simp only [List.map_cons, hfMiss a hM, List.filter_cons]
          cases P a <;> simp [ihEq]
    have hSc630 : ∀ g ∈ st0.groups, g.metaPtr = g0.metaPtr → g.sc = 63 :=
      fun g hg hM => (nodup_metaPtr_eq hNd0 hg hg0 hM) ▸ hg0Sc
    refine ⟨fun k hk => ?_, fun ch hch pSc _ => ?_, fun k hk => ?_⟩
    · unfold allGroups; rw [hGroupsF]; exact hAuxAll k hk hSc630
    · unfold nestedEdge; rw [hGroupsF]
      exact hAuxPred _ (fun x hx => by rw [decide_eq_false_iff_not]; intro h; omega) hSc630
    · unfold rootBytes; rw [hGroupsF]
      rw [hAuxPred _ (fun x hx => by rw [decide_eq_false_iff_not]; intro h; omega) hSc630]
  have hg0In63 : g0 ∈ groups63 st0 :=
    List.mem_filter.mpr ⟨hg0, beq_iff_eq.mpr hg0Sc⟩
  obtain ⟨l1, l2, hSplit63⟩ := List.append_of_mem hg0In63
  have hNd630 : ((groups63 st0).map GroupDesc.metaPtr).Nodup :=
    hNd0.sublist (List.Sublist.map GroupDesc.metaPtr List.filter_sublist)
  have hRestNe63 : ∀ x ∈ l1 ++ l2, x ∈ st0.groups ∧ x.metaPtr ≠ g0.metaPtr := by
    intro x hx
    have hx63 : x ∈ groups63 st0 := by
      rw [hSplit63]
      rcases List.mem_append.mp hx with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
    have hNdSp : (((l1 ++ g0 :: l2).map GroupDesc.metaPtr)).Nodup := hSplit63 ▸ hNd630
    refine ⟨(List.mem_filter.mp hx63).1, fun hEq => ?_⟩
    rw [List.map_append, List.map_cons, List.nodup_append] at hNdSp
    rcases List.mem_append.mp hx with h1 | h2
    · exact hNdSp.2.2 _ (List.mem_map_of_mem h1) _ List.mem_cons_self hEq
    · rw [List.nodup_cons] at hNdSp
      exact hNdSp.2.1.1 (hEq ▸ List.mem_map_of_mem h2)
  have hGroups63' : groups63 st' = l1 ++ g0' :: l2 := by
    have hMapFilter : (st0.groups.map f).filter (·.sc == 63) = (st0.groups.filter (·.sc == 63)).map f := by
      have hScEq : ∀ g ∈ st0.groups, ((f g).sc == 63) = (g.sc == 63) := by
        intro g hg
        by_cases hM : g.metaPtr = g0.metaPtr
        · have hgEq : g = g0 := nodup_metaPtr_eq hNd0 hg hg0 hM
          subst hgEq; rw [hfHit, hg0'Sc, hg0Sc]
        · rw [hfMiss g hM]
      generalize st0.groups = gs at hScEq
      induction gs with
      | nil => rfl
      | cons a l ih =>
        have hA := hScEq a List.mem_cons_self
        have ihEq := ih fun g hg => hScEq g (List.mem_cons_of_mem _ hg)
        simp only [List.map_cons, List.filter_cons, hA]
        cases a.sc == 63 <;> simp [ihEq]
    unfold groups63
    rw [hGroupsF, hMapFilter]
    change (groups63 st0).map f = l1 ++ g0' :: l2
    rw [hSplit63, List.map_append, List.map_cons, hfHit]
    have hL1Eq : l1.map f = l1 := map_eq_self_of_mem_local fun x hx =>
      hfMiss x (hRestNe63 x (List.mem_append_left _ hx)).2
    have hL2Eq : l2.map f = l2 := map_eq_self_of_mem_local fun x hx =>
      hfMiss x (hRestNe63 x (List.mem_append_right _ hx)).2
    rw [hL1Eq, hL2Eq]
  have hRestDeclEq : ∀ x ∈ l1 ++ l2,
      (x.slots.map (slotDecl63 alignMap')).sum = (x.slots.map (slotDecl63 alignMap)).sum := by
    intro x hx
    obtain ⟨hx0, hxNe⟩ := hRestNe63 x hx
    congr 1
    refine List.map_congr_left fun s hs => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    cases hsEq : x.slots[j]'hj with
    | liveUser q r0 e0 =>
      have hAm := hAlignEqOther x hx0 hxNe j hj q r0 e0 hsEq
      simp [slotDecl63, hAm]
    | _ => rfl
  let restL := (l1 ++ l2).filter isLarge63Group
  let restS := (l1 ++ l2).filter (fun g => !isLarge63Group g)
  have hRestLDeclEq :
      (restL.map fun g => (g.slots.map (slotDecl63 alignMap')).sum).sum =
      (restL.map fun g => (g.slots.map (slotDecl63 alignMap)).sum).sum := by
    congr 1
    exact List.map_congr_left fun x hx => hRestDeclEq x (List.mem_filter.mp hx).1
  let b' := FineBudget.stepRealloc align oldSz newSz b
  obtain ⟨pk, pkSC, pkSB, hPkLen, hPkLive, hPkAll, hPkEdge, hPkRoot,
    hPkSC, hPkSB, hPkCumG, hPkCumB⟩ := hInv0.small_witness
  have hMain :
      large63DeclBytes st' alignMap' = b'.live63Bytes ∧
      (large63Groups st').length = b'.live63Count ∧
      b'.live63Bytes ≤ b'.peak63Bytes ∧
      b'.live63Count ≤ b'.peak63Count ∧
      (∃ pkSC' pkSB',
        (straddle63Groups st').length ≤ pkSC' ∧
        straddle63Bytes st' ≤ pkSB' ∧
        linForm grpWtS pk + FineScale * pkSC' ≤ b'.cumSmallGroupsS ∧
        linForm slotWt pk + pkSB' ≤ b'.cumSmallBytes) := by
    have hL0Split :
        large63DeclBytes st0 alignMap =
          (if isLarge63Group g0 then (g0.slots.map (slotDecl63 alignMap)).sum else 0) +
          (restL.map fun g => (g.slots.map (slotDecl63 alignMap)).sum).sum ∧
        (large63Groups st0).length = (if isLarge63Group g0 then 1 else 0) + restL.length := by
      unfold large63DeclBytes large63Groups
      rw [hSplit63]
      simp only [restL, List.filter_append, List.filter_cons, List.map_append, List.sum_append,
        List.length_append]
      (cases isLarge63Group g0 <;> simp [List.map_cons, List.sum_cons, List.length_cons]); omega
    have hL'Split :
        large63DeclBytes st' alignMap' =
          (if isLarge63Group g0' then (g0'.slots.map (slotDecl63 alignMap')).sum else 0) +
          (restL.map fun g => (g.slots.map (slotDecl63 alignMap)).sum).sum ∧
        (large63Groups st').length = (if isLarge63Group g0' then 1 else 0) + restL.length := by
      unfold large63DeclBytes large63Groups
      rw [hGroups63', ← hRestLDeclEq]
      simp only [restL, List.filter_append, List.filter_cons, List.map_append, List.sum_append,
        List.length_append]
      (cases isLarge63Group g0' <;> simp [List.map_cons, List.sum_cons, List.length_cons]); omega
    have hS0Split :
        (straddle63Groups st0).length = (if !isLarge63Group g0 then 1 else 0) + restS.length ∧
        straddle63Bytes st0 = (if !isLarge63Group g0 then g0.maplen * 4096 else 0) +
          (restS.map fun g => g.maplen * 4096).sum := by
      unfold straddle63Bytes straddle63Groups
      rw [hSplit63]
      simp only [restS, List.filter_append, List.filter_cons, List.map_append, List.sum_append,
        List.length_append]
      (cases isLarge63Group g0 <;> simp [List.map_cons, List.sum_cons, List.length_cons]); omega
    have hS'Split :
        (straddle63Groups st').length = (if !isLarge63Group g0' then 1 else 0) + restS.length ∧
        straddle63Bytes st' = (if !isLarge63Group g0' then g0'.maplen * 4096 else 0) +
          (restS.map fun g => g.maplen * 4096).sum := by
      unfold straddle63Bytes straddle63Groups
      rw [hGroups63']
      simp only [restS, List.filter_append, List.filter_cons, List.map_append, List.sum_append,
        List.length_append]
      (cases isLarge63Group g0' <;> simp [List.map_cons, List.sum_cons, List.length_cons]); omega
    have hBBytes0 := hInv0.live63_eq.1
    have hBCnt0 := hInv0.live63_eq.2
    have hg0'MapLe0 : g0'.maplen * 4096 ≤ declCost63 newSz (max align 16) := hg0'MapLe
    by_cases hOldBig : Guaranteed63Threshold ≤ oldSz <;>
      by_cases hNewBig : Guaranteed63Threshold ≤ newSz
    ·
      have hIs0 : isLarge63Group g0 = true := by simp [isLarge63Group, hg0Slots1, slotIs63Large, hOldBig]
      have hIs' : isLarge63Group g0' = true := by simp [isLarge63Group, hg0'Slots, slotIs63Large, hNewBig]
      have hD0 : (g0.slots.map (slotDecl63 alignMap)).sum = declCost63 oldSz (max align 16) := by
        simp [hg0Slots1, slotDecl63, hOldBig, hAlign0]
      have hD' : (g0'.slots.map (slotDecl63 alignMap')).sum = declCost63 newSz (max align 16) := by
        simp [hg0'Slots, slotDecl63, hNewBig, alignMap']
      rw [hD0] at hL0Split
      rw [hD'] at hL'Split
      simp only [hIs0, hIs', ↓reduceIte, Bool.not_true, Bool.false_eq_true, Nat.zero_add]
        at hL0Split hL'Split hS0Split hS'Split
      dsimp only [b', FineBudget.stepRealloc, FineBudget.stepFree, FineBudget.stepReallocAdd,
        FineBudget.stepAligned]
      simp only [hNewBig, hOldBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      exact ⟨by omega, by omega, by omega, by omega,
        pkSC, pkSB, by omega, by omega, hPkCumG, hPkCumB⟩
    ·
      have hIs0 : isLarge63Group g0 = true := by simp [isLarge63Group, hg0Slots1, slotIs63Large, hOldBig]
      have hIs' : isLarge63Group g0' = false := by simp [isLarge63Group, hg0'Slots, slotIs63Large, hNewBig]
      have hD0 : (g0.slots.map (slotDecl63 alignMap)).sum = declCost63 oldSz (max align 16) := by
        simp [hg0Slots1, slotDecl63, hOldBig, hAlign0]
      rw [hD0] at hL0Split
      simp only [hIs0, hIs', ↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_eq_true, Nat.zero_add]
        at hL0Split hL'Split hS0Split hS'Split
      dsimp only [b', FineBudget.stepRealloc, FineBudget.stepFree, FineBudget.stepReallocAdd]
      simp only [hNewBig, hOldBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      refine ⟨by omega, by omega, by omega, by omega,
        pkSC + 1, pkSB + declCost63 newSz (max align 16), by omega, by omega, ?_, ?_⟩
      · rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
        exact Nat.add_le_add hPkCumG (Nat.le_max_right _ _)
      · rw [← Nat.add_assoc]
        exact Nat.add_le_add hPkCumB (Nat.le_max_right _ _)
    ·
      have hIs0 : isLarge63Group g0 = false := by simp [isLarge63Group, hg0Slots1, slotIs63Large, hOldBig]
      have hIs' : isLarge63Group g0' = true := by simp [isLarge63Group, hg0'Slots, slotIs63Large, hNewBig]
      have hD' : (g0'.slots.map (slotDecl63 alignMap')).sum = declCost63 newSz (max align 16) := by
        simp [hg0'Slots, slotDecl63, hNewBig, alignMap']
      rw [hD'] at hL'Split
      simp only [hIs0, hIs', ↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_eq_true, Nat.zero_add]
        at hL0Split hL'Split hS0Split hS'Split
      dsimp only [b', FineBudget.stepRealloc, FineBudget.stepFree, FineBudget.stepReallocAdd,
        FineBudget.stepAligned]
      simp only [hNewBig, hOldBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      exact ⟨by omega, by omega, by omega, by omega,
        pkSC, pkSB, by omega, by omega, hPkCumG, hPkCumB⟩
    ·
      have hIs0 : isLarge63Group g0 = false := by simp [isLarge63Group, hg0Slots1, slotIs63Large, hOldBig]
      have hIs' : isLarge63Group g0' = false := by simp [isLarge63Group, hg0'Slots, slotIs63Large, hNewBig]
      simp only [hIs0, hIs', ↓reduceIte, Bool.not_false, Bool.false_eq_true, Nat.zero_add]
        at hL0Split hL'Split hS0Split hS'Split
      dsimp only [b', FineBudget.stepRealloc, FineBudget.stepFree, FineBudget.stepReallocAdd]
      simp only [hNewBig, hOldBig, ↓reduceIte, finePeak63Bytes, finePeak63Count]
      refine ⟨by omega, by omega, by omega, by omega,
        pkSC + 1, pkSB + declCost63 newSz (max align 16), by omega, by omega, ?_, ?_⟩
      · rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
        exact Nat.add_le_add hPkCumG (Nat.le_max_right _ _)
      · rw [← Nat.add_assoc]
        exact Nat.add_le_add hPkCumB (Nat.le_max_right _ _)
  obtain ⟨hLBytes, hLCnt, hLPeakB, hLPeakC, pkSC', pkSB', hSC', hSB', hCumG', hCumB'⟩ := hMain
  refine {
    ivs_eq := fun _ => rfl
    groups_geom := hGeom'
    alignMap_wf := hAlignWf'
    live63_eq := ⟨hLBytes, hLCnt⟩
    live63_le_peak := ⟨hLPeakB, hLPeakC⟩
    metaAreas_le := by
      rw [hMetaEq]
      exact Nat.le_trans hInv0.metaAreas_le (fineMaxMetaAreas_mono (.realloc align oldSz newSz) b)
    small_witness := ⟨pk, pkSC', pkSB', hPkLen,
      fun k hk => by unfold liveSlotsInClass; rw [hSlabEq.1 k hk]; exact hPkLive k hk,
      fun k hk => by rw [hSlabEq.1 k hk]; exact hPkAll k hk,
      fun ch hch pSc hpSc => by rw [hSlabEq.2.1 ch hch pSc hpSc]; exact hPkEdge ch hch pSc hpSc,
      fun k hk => by rw [hSlabEq.2.2 k hk]; exact hPkRoot k hk,
      hSC', hSB', hCumG', hCumB'⟩
  }

end LibsignalBinary.Heap.Fine
