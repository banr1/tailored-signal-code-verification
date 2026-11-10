/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotHelpers

/-!
# Group Metadata Update Lifts and `try_avail` Absorption Helpers

`MallocngWFInflight`, `ByteMap`, and `CtxFields` transition and absorption lemmas for `try_avail`
dequeue, `activate_group` `freedMask`-to-`availMask` transfer, and `pageSpanSteps` `activeIdx`
updates in `alloc_slot`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Shared `meta`-Only Group Update Lift -/

def SlotSameKind (s1 s2 : SlotState) : Prop :=
  s1 = s2 ∨ (s1.isFree = true ∧ s2.isFree = true)

theorem slotSameKind_props {s1 s2 : SlotState} (h : SlotSameKind s1 s2) :
    s1.isFree = s2.isFree ∧
    s1.isClaimed = s2.isClaimed ∧
    slotLiveCount s1 = slotLiveCount s2 ∧
    slotEffCost s1 = slotEffCost s2 ∧
    (∀ cm, s1 = .liveNested cm ↔ s2 = .liveNested cm) ∧
    (∀ p n e, s1 = .liveUser p n e ↔ s2 = .liveUser p n e) := by
  rcases h with rfl | ⟨hf1, hf2⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  · cases s1 <;> cases s2 <;> simp_all [SlotState.isFree, SlotState.isClaimed, slotLiveCount, slotEffCost]

theorem list_slotSameKind_eqs {xs ys : List SlotState} (hLen : xs.length = ys.length)
    (hAll : ∀ j (hj1 : j < xs.length) (hj2 : j < ys.length), SlotSameKind (xs[j]'hj1) (ys[j]'hj2)) :
    xs.all SlotState.isFree = ys.all SlotState.isFree ∧
    (xs.filter SlotState.isClaimed).length = (ys.filter SlotState.isClaimed).length ∧
    (xs.map slotLiveCount).sum = (ys.map slotLiveCount).sum ∧
    (xs.map slotEffCost).sum = (ys.map slotEffCost).sum ∧
    (∀ p n e, .liveUser p n e ∈ xs ↔ .liveUser p n e ∈ ys) := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => simp | cons _ _ => simp at hLen
  | cons x xt ih =>
    cases ys with
    | nil => simp at hLen
    | cons y yt =>
      have hHead := slotSameKind_props (hAll 0 (by simp) (by simp))
      simp only [List.getElem_cons_zero] at hHead
      have hTail := ih (by simpa using hLen)
        (fun j hj1 hj2 => hAll (j + 1) (Nat.succ_lt_succ hj1) (Nat.succ_lt_succ hj2))
      refine ⟨by simp [hHead.1, hTail.1],
        by simp only [List.filter_cons, hHead.2.1]; split <;> simp [hTail.2.1],
        by simp [hHead.2.2.1, hTail.2.2.1], by simp [hHead.2.2.2.1, hTail.2.2.2.1], fun p n e => ?_⟩
      simp only [List.mem_cons]
      exact ⟨fun h => h.elim (fun hE => Or.inl ((hHead.2.2.2.2.2 p n e).mp hE.symm).symm)
        (fun hM => Or.inr ((hTail.2.2.2.2 p n e).mp hM)),
        fun h => h.elim (fun hE => Or.inl ((hHead.2.2.2.2.2 p n e).mpr hE.symm).symm)
        (fun hM => Or.inr ((hTail.2.2.2.2 p n e).mpr hM))⟩

theorem group_metaMod_disjoint {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) :
    (∀ u ∈ st.groups, ∀ v ∈ st.groups, ∀ a : BitVec 64,
      v.mem.toNat ≤ a.toNat → a.toNat ≤ (v.slotEnd v.lastIdx).toNat → ¬ InRegion u.metaPtr 40 a) ∧
    (∀ u ∈ st.groups, ∀ ma ∈ st.metaAreas, ∀ a : BitVec 64,
      InRegion ma.base 24 a → ¬ InRegion u.metaPtr 40 a) ∧
    (∀ u ∈ st.groups, ∀ fm ∈ st.freeMetas, ∀ a : BitVec 64,
      InRegion fm.ptr 40 a → ¬ InRegion u.metaPtr 40 a) ∧
    (∀ u ∈ st.groups, ∀ bm ∈ st.bumpMetas, ∀ a : BitVec 64,
      InRegion bm 40 a → ¬ InRegion u.metaPtr 40 a) ∧
    (∀ u ∈ st.groups, ∀ ap ∈ st.availMetaPages, ∀ a : BitVec 64,
      InRegion ap 4096 a → ¬ InRegion u.metaPtr 40 a) ∧
    (∀ u ∈ st.groups, ∀ gp ∈ st.guardPages, ∀ a : BitVec 64,
      InRegion gp 4096 a → ¬ InRegion u.metaPtr 40 a) := by
  have huAllOf : ∀ u ∈ st.groups, u.metaPtr ∈ allMetaSlots st := fun u hu =>
    (hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu))))
  refine ⟨fun u hu v hv a hLo hHi hInU => ?_, fun u hu ma hma a haMa24 hInU => ?_,
    fun u hu fm hfm a haFm hInU => ?_, fun u hu bm hbm a haBm hInU => ?_,
    fun u hu ap hap a haAp hInU => ?_, fun u hu gp hgp a haGp hInU => ?_⟩
  · obtain ⟨_, _, _, ⟨ma, hma, hInMa⟩, _⟩ := allMetaSlots_info hwf (huAllOf u hu)
    obtain ⟨rg, hrg, hrgPos, hRgLo, _, hRgEndLt⟩ := group_root_containment hwf hv
    have hRgBound : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
      have h := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1; simp [GroupDesc.totalBytes, hrgPos] at h; exact h
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hrg hrgPos) (hInMa a hInU)
      ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
  · have hm := huAllOf u hu; unfold allMetaSlots at hm
    obtain ⟨ma₁, hma₁, hm₁⟩ := List.mem_flatMap.mp hm; obtain ⟨k₁, hk₁r, hEqU⟩ := List.mem_map.mp hm₁
    obtain ⟨hLo₁, hAl₁, hHi₁, _⟩ := hwf.metaAreas_wf.2.1 ma₁ hma₁
    obtain ⟨hEqN, _, _, _, hSub₁⟩ := slotAddr_bounds hLo₁ hAl₁ hHi₁ (List.mem_range.mp hk₁r)
    obtain ⟨hLoM, _, hHiM, _⟩ := hwf.metaAreas_wf.2.1 ma hma
    have ha24 := (inRegion_bounds (by omega)).mp haMa24
    have haU := (inRegion_bounds (by rw [← hEqU, hEqN]; omega)).mp hInU
    by_cases hEqMa : ma₁ = ma
    · subst hEqMa; rw [hEqU] at hEqN; omega
    · obtain ⟨i₁, hi₁, hg₁⟩ := List.getElem_of_mem hma₁; obtain ⟨i₂, hi₂, hg₂⟩ := List.getElem_of_mem hma
      have hij : i₁ ≠ i₂ := fun h => hEqMa (hg₁.symm.trans (h ▸ hg₂))
      have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
      rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
      let mRegs := st.metaAreas.map fun x => (x.base, 4096)
      have hlen : mRegs.length = st.metaAreas.length := List.length_map _
      have hdisj := PairwiseDisjointRegions.getElem_disjoint hpd.1 (hlen ▸ hi₁) (hlen ▸ hi₂) hij
      have hm1 : mRegs[i₁]'(hlen ▸ hi₁) = (ma₁.base, 4096) := by simp [mRegs, hg₁]
      have hm2 : mRegs[i₂]'(hlen ▸ hi₂) = (ma.base, 4096) := by simp [mRegs, hg₂]
      rw [hm1, hm2] at hdisj; dsimp only at hdisj
      exact DisjointRegions.not_both hdisj (hSub₁ a (hEqU ▸ hInU))
        ((inRegion_bounds (by omega)).mpr ⟨ha24.1, by omega⟩)
  · obtain ⟨_, _, _, _, hNd, hAll⟩ := hwf.free_bump_metas_wf
    have hFmAll : fm.ptr ∈ allMetaSlots st := (hAll fm.ptr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
    have hNe : fm.ptr ≠ u.metaPtr := fun hE => by
      rw [List.nodup_append, List.nodup_append, List.nodup_append] at hNd
      exact hNd.1.1.2.2 u.metaPtr (List.mem_map_of_mem hu) fm.ptr (List.mem_map_of_mem hfm) hE.symm
    exact DisjointRegions.not_both ((allMetaSlots_info hwf (huAllOf u hu)).2.2.2.2 fm.ptr hFmAll hNe) hInU haFm
  · obtain ⟨_, _, _, _, hNd, hAll⟩ := hwf.free_bump_metas_wf
    have hBmAll : bm ∈ allMetaSlots st := (hAll bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
    have hNe : bm ≠ u.metaPtr := fun hE => by
      rw [List.nodup_append, List.nodup_append] at hNd
      exact hNd.1.2.2 u.metaPtr (List.mem_append_left _ (List.mem_map_of_mem hu)) bm hbm hE.symm
    exact DisjointRegions.not_both ((allMetaSlots_info hwf (huAllOf u hu)).2.2.2.2 bm hBmAll hNe) hInU haBm
  · have h0 : 0 < u.slots.length := by rw [(hwf.groups_wf u hu).2.2.1]; unfold GroupDesc.cnt; omega
    exact (MallocImplH1.protNone_disjoint_slotWriteMod hwf hu h0).1 ap hap a haAp (Or.inl hInU)
  · have h0 : 0 < u.slots.length := by rw [(hwf.groups_wf u hu).2.2.1]; unfold GroupDesc.cnt; omega
    exact (MallocImplH1.protNone_disjoint_slotWriteMod hwf hu h0).2 gp hgp a haGp (Or.inl hInU)

theorem filterMap_congr_mem {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xt ih =>
    simp [List.filterMap_cons, h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem metaOnly_list_eqs {gs : List GroupDesc} {fG : GroupDesc → GroupDesc}
    (hF : ∀ u ∈ gs, (fG u).metaPtr = u.metaPtr ∧ (fG u).mem = u.mem ∧
      (fG u).lastIdx = u.lastIdx ∧ (fG u).sc = u.sc ∧ (fG u).maplen = u.maplen ∧
      ((fG u).slots.filter SlotState.isClaimed).length = (u.slots.filter SlotState.isClaimed).length ∧
      ((fG u).slots.map slotLiveCount).sum = (u.slots.map slotLiveCount).sum ∧
      ((fG u).slots.map slotEffCost).sum = (u.slots.map slotEffCost).sum) :
    (gs.map fG).map (·.metaPtr) = gs.map (·.metaPtr) ∧
    (gs.map fG).map (·.mem) = gs.map (·.mem) ∧
    (∀ sc', ((gs.map fG).filter (·.sc == sc')).map GroupDesc.cnt =
      (gs.filter (·.sc == sc')).map GroupDesc.cnt) ∧
    ((gs.map fG).filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) =
      (gs.filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) ∧
    ((gs.map fG).map (fun x => (x.slots.filter SlotState.isClaimed).length)).sum =
      (gs.map (fun x => (x.slots.filter SlotState.isClaimed).length)).sum ∧
    ((gs.map fG).map (fun x => (x.slots.map slotLiveCount).sum)).sum =
      (gs.map (fun x => (x.slots.map slotLiveCount).sum)).sum ∧
    ((gs.map fG).map (fun x => (x.slots.map slotEffCost).sum)).sum =
      (gs.map (fun x => (x.slots.map slotEffCost).sum)).sum := by
  induction gs with
  | nil => simp
  | cons u ut ih =>
    obtain ⟨hm, hmem, hlast, hsc, hmap, hcl, hlc, hec⟩ := hF u (List.mem_cons_self ..)
    have hcnt : (fG u).cnt = u.cnt := by simp [GroupDesc.cnt, hlast]
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ := ih (fun x hx => hF x (List.mem_cons_of_mem _ hx))
    refine ⟨by simp [hm, ih1], by simp [hmem, ih2], fun sc' => ?_, ?_,
      by simp only [List.map_cons, List.sum_cons, hcl, ih5],
      by simp only [List.map_cons, List.sum_cons, hlc, ih6],
      by simp only [List.map_cons, List.sum_cons, hec, ih7]⟩
    · simp only [List.map_cons, List.filter_cons, hsc]; split <;> simp [hcnt, ih3 sc']
    · simp only [List.map_cons, List.filter_cons, hmap]; split <;> simp [hmem, hmap, ih4]

theorem metaOnly_map_wf {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (_hsc : sc < 48) {gWitness : GroupDesc} (hgWitness : gWitness ∈ st.groups)
    {newHead : BitVec 64} {newMs : List (BitVec 64)}
    {fG : GroupDesc → GroupDesc} {bv1 : BitVec 64 → BitVec 8}
    (hFields : ∀ u ∈ st.groups,
      (fG u).metaPtr = u.metaPtr ∧ (fG u).mem = u.mem ∧ (fG u).lastIdx = u.lastIdx ∧
      (fG u).sc = u.sc ∧ (fG u).maplen = u.maplen ∧ (fG u).activeByte = u.activeByte ∧
      (fG u).parentMeta = u.parentMeta ∧ (fG u).nestedCap = u.nestedCap ∧
      (fG u).slots.length = u.slots.length ∧
      (u.sc ≠ sc → fG u = u))
    (hBitmaps : ∀ u ∈ st.groups,
      (fG u).availMask &&& (fG u).freedMask = 0#32 ∧
      ((fG u).availMask ||| (fG u).freedMask).toNat < 2 ^ u.cnt ∧
      ((fG u).sc = 63 → (fG u).prev = 0#64 ∧ (fG u).next = 0#64))
    (hSlots : ∀ u ∈ st.groups, ∀ j (hj1 : j < (fG u).slots.length) (hj2 : j < u.slots.length),
      let s' := (fG u).slots[j]'hj1
      SlotSameKind s' (u.slots[j]'hj2) ∧
      ((fG u).availMask.getLsbD j = true ↔ s' = .freeAvail) ∧
      ((fG u).freedMask.getLsbD j = true ↔ s' = .freeInactive) ∧
      (u.activeIdx < j → s' = .freeInactive))
    (hBvOut : ∀ a : BitVec 64, (∀ u ∈ st.groups, ¬ InRegion u.metaPtr 40 a) → bv1 a = st.byteVal a)
    (hBvMeta : ∀ u ∈ st.groups, readBytesFromMap bv1 u.metaPtr 40 = (fG u).metaBytes)
    (hActSc : ActiveClassWf
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc newHead }
        groups := st.groups.map fG
        activeLists := st.activeLists.set sc newMs
        byteVal := bv1 } sc newHead newMs)
    (hEmptySc : ∀ u ∈ st.groups, u.sc = sc → u.isEmpty = true → u.metaPtr ∈ newMs) :
    let st1 : MallocngSt :=
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc newHead }
        groups := st.groups.map fG
        activeLists := st.activeLists.set sc newMs
        byteVal := bv1 }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 ∧
    totalLiveCount st1 = totalLiveCount st ∧
    totalLiveEffCost st1 = totalLiveEffCost st ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    (∀ a, OwnedRwByte st1 a ↔ OwnedRwByte st a) ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) := by
  intro st1
  obtain ⟨hDisjGrp, hDisjMa24, hDisjFm, hDisjBm, hDisjAp, hDisjGp⟩ := group_metaMod_disjoint hwf
  have hSlotLists : ∀ u ∈ st.groups,
      (fG u).isEmpty = u.isEmpty ∧
      ((fG u).slots.filter SlotState.isClaimed).length = (u.slots.filter SlotState.isClaimed).length ∧
      ((fG u).slots.map slotLiveCount).sum = (u.slots.map slotLiveCount).sum ∧
      ((fG u).slots.map slotEffCost).sum = (u.slots.map slotEffCost).sum ∧
      (∀ p n e, .liveUser p n e ∈ (fG u).slots ↔ .liveUser p n e ∈ u.slots) := fun u hu => by
    have hE := list_slotSameKind_eqs (hFields u hu).2.2.2.2.2.2.2.2.1
      (fun j hj1 hj2 => (hSlots u hu j hj1 hj2).1)
    exact ⟨hE.1, hE.2⟩
  obtain ⟨hMetaMap, hMemMap, hCntFilt, hRootFilt, hClaimSum, hLiveSum, hEffSum⟩ :=
    metaOnly_list_eqs (gs := st.groups) (fG := fG) (fun u hu => by
      obtain ⟨h1, h2, h3, h4, h5, _, _, _, _, _⟩ := hFields u hu
      obtain ⟨_, hc, hl, he, _⟩ := hSlotLists u hu
      exact ⟨h1, h2, h3, h4, h5, hc, hl, he⟩)
  have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
    simp only [dynamicRootRegions, st1, hRootFilt]
  have hCarvIff : ∀ a, CarvedUserByte st1 a ↔ CarvedUserByte st a := fun a => by
    simp only [CarvedUserByte, st1, List.mem_map]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, s', hs', hIn⟩
      cases s' with
      | liveUser p n e =>
        exact ⟨u, hu, .liveUser p n e, ((hSlotLists u hu).2.2.2.2 p n e).mp hs', hIn⟩
      | _ => cases hIn
    · rintro ⟨u, hu, s0, hs0, hIn⟩
      cases s0 with
      | liveUser p n e =>
        exact ⟨fG u, ⟨u, hu, rfl⟩, .liveUser p n e, ((hSlotLists u hu).2.2.2.2 p n e).mpr hs0, hIn⟩
      | _ => cases hIn
  have hRootIff : ∀ a, (∃ x ∈ st1.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) ↔
      (∃ u ∈ st.groups, 0 < u.maplen ∧ InRegion u.mem (u.maplen * 4096) a) := fun a => by
    simp only [st1, List.mem_map]
    exact ⟨fun ⟨_, ⟨u, hu, rfl⟩, hp, hi⟩ => by
      obtain ⟨_, hmem, _, _, hmap, _⟩ := hFields u hu; rw [hmap] at hp; rw [hmem, hmap] at hi; exact ⟨u, hu, hp, hi⟩,
      fun ⟨u, hu, hp, hi⟩ => by
      obtain ⟨_, hmem, _, _, hmap, _⟩ := hFields u hu; exact ⟨fG u, ⟨u, hu, rfl⟩, hmap ▸ hp, by rwa [hmem, hmap]⟩⟩
  have hOwnIff : ∀ a, OwnedRwByte st1 a ↔ OwnedRwByte st a := fun a => by
    unfold OwnedRwByte; simp only [hRootIff a, hCarvIff a]; rfl
  have hMpIff : ∀ a, OwnedMappedByte st1 a ↔ OwnedMappedByte st a := fun a => by
    unfold OwnedMappedByte; simp only [hRootIff a]; rfl
  have hBvAtGrp : ∀ v ∈ st.groups, ∀ a : BitVec 64,
      v.mem.toNat ≤ a.toNat → a.toNat ≤ (v.slotEnd v.lastIdx).toNat → bv1 a = st.byteVal a :=
    fun v hv a hLo hHi => hBvOut a (fun u hu => hDisjGrp u hu v hv a hLo hHi)
  have hGroupsWf1 : ∀ x ∈ st1.groups, GroupWf st1 x := by
    simp only [st1, List.mem_map]; rintro _ ⟨u, hu, rfl⟩
    have huWf := hwf.groups_wf u hu; have hGs := group_slot_toNat huWf
    obtain ⟨hm, hmem, hlast, hscU, hmap, hactB, hpar, hnCap, hlenS, _⟩ := hFields u hu
    obtain ⟨hAnd0, hOrLt, h63⟩ := hBitmaps u hu
    have hCntEq : (fG u).cnt = u.cnt := by simp [GroupDesc.cnt, hlast]
    have hStrEq : (fG u).stride = u.stride := by simp [GroupDesc.stride, hlast, hmap, hscU]
    have hStoEq : (fG u).storage = u.storage := by simp [GroupDesc.storage, hmem]
    have hTotEq : (fG u).totalBytes = u.totalBytes := by simp [GroupDesc.totalBytes, hmap, hnCap]
    have hEndLastEq : (fG u).slotEnd (fG u).lastIdx = u.slotEnd u.lastIdx := by
      simp [GroupDesc.slotEnd, GroupDesc.slotStart, hStoEq, hStrEq, hlast]
    have hActIdxEq : (fG u).activeIdx = u.activeIdx := by simp [GroupDesc.activeIdx, hactB]
    have hEndGe16 : u.mem.toNat + 16 ≤ (u.slotEnd u.lastIdx).toNat := by
      rw [hGs.2.2.2.1]; have : 1 * 16 ≤ u.cnt * u.stride := Nat.mul_le_mul hGs.2.1 hGs.1; omega
    have hEndLim : (u.slotEnd u.lastIdx).toNat ≤ 2 ^ 48 := by
      have := hGs.2.2.2.1; have := hGs.2.2.2.2.1; have := huWf.2.2.2.2.2.2.1; omega
    refine ⟨hscU ▸ huWf.1, hlast ▸ huWf.2.1, hlenS.trans (huWf.2.2.1.trans hCntEq.symm),
      fun hSc63 => ?_, hmem ▸ huWf.2.2.2.2.1, hmem ▸ huWf.2.2.2.2.2.1,
      by rw [hmem, hTotEq]; exact huWf.2.2.2.2.2.2.1,
      by rw [hCntEq, hStrEq, hTotEq]; exact huWf.2.2.2.2.2.2.2.1,
      fun hPos => by rw [hCntEq, hStrEq, hTotEq]; exact huWf.2.2.2.2.2.2.2.2.1 (hmap ▸ hPos),
      by change bv1 ((fG u).slotEnd (fG u).lastIdx) = 0#8
         rw [hEndLastEq, hBvAtGrp u hu _ (by omega) (Nat.le_refl _)]; exact huWf.2.2.2.2.2.2.2.2.2.1,
      by rw [hmap, hpar]; exact huWf.2.2.2.2.2.2.2.2.2.2.1,
      fun hPos => ?_, fun hZero => ?_, hAnd0, hCntEq ▸ hOrLt,
      by rw [hActIdxEq, hlast]; exact huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hm ▸ hBvMeta u hu, ?_, ?_, fun j hj1 => ?_⟩
    · have hOld63 := huWf.2.2.2.1 (hscU ▸ hSc63)
      exact ⟨hlast ▸ hOld63.1, hmap ▸ hOld63.2.1, (h63 hSc63).1, (h63 hSc63).2⟩
    · rw [hmem, hnCap, hscU, hmap, hlast, hStrEq]; exact huWf.2.2.2.2.2.2.2.2.2.2.2.1 (hmap ▸ hPos)
    · obtain ⟨h1Last, pg, hpg, pIdx, hp, hParPg, hPgSc, hScLt, hPg24, hPgSl, hStLe, hCapLe, hCapEq⟩ :=
        huWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (hmap ▸ hZero)
      obtain ⟨pgM, _, _, hpgSc, _, _, _, _, hpgLen, _⟩ := hFields pg hpg
      have hp1 : pIdx < (fG pg).slots.length := hpgLen.symm ▸ hp
      have hSl1 : (fG pg).slots[pIdx]'hp1 = .liveNested (fG u).metaPtr :=
        hm ▸ ((slotSameKind_props (hSlots pg hpg pIdx hp1 hp).1).2.2.2.2.1 u.metaPtr).mpr hPgSl
      have hPgStr : (fG pg).stride = pg.stride := by
        obtain ⟨_, _, hlP, hsP, hmP, _⟩ := hFields pg hpg; simp [GroupDesc.stride, hlP, hmP, hsP]
      have hPgSto : (fG pg).storage = pg.storage := by
        obtain ⟨_, hmemP, _⟩ := hFields pg hpg; simp [GroupDesc.storage, hmemP]
      refine ⟨hlast ▸ h1Last, fG pg, List.mem_map_of_mem hpg, pIdx, hp1, ?_⟩
      rw [hpar, pgM, hpgSc, hscU, hmem, hnCap]
      simp only [GroupDesc.slotStart, GroupDesc.slotEnd, hPgSto, hPgStr]
      exact ⟨hParPg, hPgSc, hScLt, hPg24, hSl1, hStLe, hCapLe, hCapEq⟩
    · change readBytesFromMap bv1 (fG u).mem 8 = unpack64 (fG u).metaPtr; rw [hmem, hm]
      refine (readBytesFromMap_congr (by decide) fun a ha => ?_).trans
        huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have haB := (inRegion_bounds (by omega)).mp ha; exact hBvAtGrp u hu a haB.1 (by omega)
    · change bv1 ((fG u).mem + 8#64) = (fG u).activeByte; rw [hmem, hactB]
      have hAdd8 : (u.mem + 8#64).toNat = u.mem.toNat + 8 := add_ofNat_toNat (by omega)
      exact (hBvAtGrp u hu (u.mem + 8#64) (by omega) (by omega)).trans
        huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have hj2 : j < u.slots.length := hlenS ▸ hj1
      have hjCnt : j < u.cnt := huWf.2.2.1 ▸ hj2
      obtain ⟨hStJ, hEndJ, _⟩ := hGs.2.2.2.2.2 j hjCnt
      have hMulJ : (j + 1) * u.stride = j * u.stride + u.stride := Nat.succ_mul j u.stride
      have hEndMono : (u.slotEnd j).toNat ≤ (u.slotEnd u.lastIdx).toNat := by
        rw [hEndJ, hGs.2.2.2.1]
        have : (j + 1) * u.stride ≤ u.cnt * u.stride := Nat.mul_le_mul_right _ hjCnt; omega
      have hSubS4 : (u.slotStart j - 4#64).toNat = (u.slotStart j).toNat - 4 :=
        sub_ofNat_toNat (by omega)
      obtain ⟨hSK, hAvIff, hFrIff, hInactJ⟩ := hSlots u hu j hj1 hj2
      have hsw0 := huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj2
      rcases hSK with hEqS | ⟨hFree', _⟩
      · have hAvEq : (fG u).availMask.getLsbD j = u.availMask.getLsbD j := by
          rw [Bool.eq_iff_iff, hAvIff, hEqS, hsw0.2.1]
        have hFrEq : (fG u).freedMask.getLsbD j = u.freedMask.getLsbD j := by
          rw [Bool.eq_iff_iff, hFrIff, hEqS, hsw0.2.2.1]
        rw [hEqS]
        exact MallocImplH1.slotWf_congr_local hwf hu hj2 hm hmem hlast hscU hmap hActIdxEq
          hAvEq hFrEq
          (fun cg hcg => by
            obtain ⟨cgM, cgMem, _, _, _, _, cgPar, cgCap, _, _⟩ := hFields cg hcg
            exact ⟨fG cg, List.mem_map_of_mem hcg, cgM, cgPar, cgMem, cgCap⟩)
          (fun _ a ha => by
            have haB := (inRegion_bounds (by have := hGs.1; omega)).mp ha
            exact hBvAtGrp u hu a (by omega) (by have := hGs.1; omega))
          (fun _ cg _ hcg _ hParCg => by
            obtain ⟨_, _, _, k, hk, _, hCgLo, hCgEndLe, _⟩ := parent_step_info hwf hcg hu hParCg
            have hkCnt : k < u.cnt := huWf.2.2.1 ▸ hk
            obtain ⟨hStK, hEndK, _⟩ := hGs.2.2.2.2.2 k hkCnt
            have hEndKLe : (u.slotEnd k).toNat ≤ (u.slotEnd u.lastIdx).toNat := by
              rw [hEndK, hGs.2.2.2.1]
              have : (k + 1) * u.stride ≤ u.cnt * u.stride := Nat.mul_le_mul_right _ hkCnt; omega
            have hCgGs := group_slot_toNat (hwf.groups_wf cg hcg)
            have hCg16 : cg.mem.toNat + 16 ≤ (cg.slotEnd cg.lastIdx).toNat := by
              rw [hCgGs.2.2.2.1]
              have : 1 * 16 ≤ cg.cnt * cg.stride := Nat.mul_le_mul hCgGs.2.1 hCgGs.1; omega
            have hSubCg4 : (cg.mem - 4#64).toNat = cg.mem.toNat - 4 := sub_ofNat_toNat (by omega)
            exact ⟨hBvAtGrp u hu _ (by omega) (by have := hGs.1; omega), fun a ha => by
              have haB := (inRegion_bounds (by omega)).mp ha
              exact hBvAtGrp u hu a (by omega) (by omega)⟩)
      · have hStartEq : (fG u).slotStart j = u.slotStart j := by
          simp [GroupDesc.slotStart, hStoEq, hStrEq]
        refine ⟨by change bv1 ((fG u).slotStart j - 4#64) = 0#8
                   rw [hStartEq, hBvAtGrp u hu _ (by omega) (by have := hGs.1; omega)]; exact hsw0.1,
          hAvIff, hFrIff, hActIdxEq ▸ hInactJ, ?_⟩
        cases hs' : (fG u).slots[j]'hj1 <;> simp [SlotState.isFree, hs'] at hFree' ⊢
  have hWf1 : MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 := {
    base_wf := trivial
    brk_bounds := hwf.brk_bounds
    ctx_lens := by
      obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hwf.ctx_lens
      exact ⟨by simp [st1, l1], l2, l3, l4, l5, by simp [st1, l6]⟩
    initDone_wf := hwf.initDone_wf
    initZero_wf := fun hZ => by
      have hGsNil := (hwf.initZero_wf hZ).2.2.2.2.2.2.2.2.2.1
      rw [hGsNil] at hgWitness; cases hgWitness
    bounces_wf := hwf.bounces_wf
    usage_wf := fun sc' hsc' => by
      have hOld := hwf.usage_wf sc' hsc'
      simpa [st1, hCntFilt sc'] using hOld
    brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
      obtain ⟨h1, h2, h3, h4⟩ := hwf.metaAreas_wf.2.1 ma hma
      refine ⟨h1, h2, h3, (readBytesFromMap_congr (by decide) fun a ha => ?_).trans h4⟩
      exact hBvOut a (fun u hu => hDisjMa24 u hu ma hma a ha),
      hwf.metaAreas_wf.2.2⟩
    guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
      fun ap hap => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 ap hap
        refine ⟨h1, h2, h3, (readBytesFromMap_congr (by decide) fun a ha => ?_).trans h4⟩
        exact hBvOut a (fun u hu => hDisjAp u hu ap hap a ha)⟩
    inflight_wf := by unfold totalClaimedSlots; dsimp only [st1]; rw [hClaimSum]; exact hwf.inflight_wf
    free_bump_metas_wf := by
      obtain ⟨hDll, hFmB, hBumpC, hBmB, hNd, hAll⟩ := hwf.free_bump_metas_wf
      exact ⟨hDll, fun fm hfm => (readBytesFromMap_congr (by decide) fun a ha =>
          hBvOut a (fun u hu => hDisjFm u hu fm hfm a ha)).trans (hFmB fm hfm),
        hBumpC, fun bm hbm => (readBytesFromMap_congr (by decide) fun a ha =>
          hBvOut a (fun u hu => hDisjBm u hu bm hbm a ha)).trans (hBmB bm hbm),
        by simpa [st1, hMetaMap] using hNd, fun m => by simpa [st1, hMetaMap, allMetaSlots] using hAll m⟩
    groups_nodup := ⟨by simpa [st1, hMetaMap] using hwf.groups_nodup.1,
      by simpa [st1, hMemMap] using hwf.groups_nodup.2⟩
    groups_wf := hGroupsWf1
    regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
    active_wf := fun sc' h1' h2' => by
      have h1 : sc' < st.ctx.active.length := by simpa [st1] using h1'
      have h2 : sc' < st.activeLists.length := by simpa [st1] using h2'
      by_cases hEq : sc' = sc
      · subst hEq; simpa [st1] using hActSc
      · change ActiveClassWf st1 sc' (st1.ctx.active[sc']'h1') (st1.activeLists[sc']'h2')
        have hHdEq : st1.ctx.active[sc']'h1' = st.ctx.active[sc']'h1 := List.getElem_set_ne (Ne.symm hEq) h1'
        have hMsEq : st1.activeLists[sc']'h2' = st.activeLists[sc']'h2 := List.getElem_set_ne (Ne.symm hEq) h2'
        rw [hHdEq, hMsEq]
        have hOld := hwf.active_wf sc' h1 h2
        let ms' := st.activeLists[sc']'h2
        have hNd1 : (st1.groups.map (·.metaPtr)).Nodup := by simpa [st1, hMetaMap] using hwf.groups_nodup.1
        have hFindEq : ∀ m ∈ ms', findGroupByMeta st1 m = findGroupByMeta st m := fun m hm => by
          obtain ⟨u, hu, rfl, hScU⟩ := hOld.1 m hm
          have hFu : fG u = u := (hFields u hu).2.2.2.2.2.2.2.2.2 (hScU ▸ hEq)
          have hu1 : u ∈ st1.groups := hFu ▸ List.mem_map_of_mem (f := fG) hu
          rw [slot_findGroupByMeta_eq_of_mem hNd1 hu1, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hu]
        have hFmEq : (ms'.filterMap fun m => (findGroupByMeta st1 m).map fun x => (x.metaPtr, x.prev, x.next)) =
            (ms'.filterMap fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) :=
          filterMap_congr_mem fun m hm => by rw [hFindEq m hm]
        have hMemSc' : ∀ x : GroupDesc, (x ∈ st1.groups ∧ x.sc = sc') ↔ (x ∈ st.groups ∧ x.sc = sc') := fun x => by
          simp only [st1, List.mem_map]
          constructor
          · rintro ⟨⟨u, hu, rfl⟩, hScF⟩
            have hScU : u.sc = sc' := (hFields u hu).2.2.2.1.symm.trans hScF
            rw [(hFields u hu).2.2.2.2.2.2.2.2.2 (hScU ▸ hEq)]
            exact ⟨hu, hScU⟩
          · rintro ⟨hx, hScX⟩
            exact ⟨⟨x, hx, (hFields x hx).2.2.2.2.2.2.2.2.2 (hScX ▸ hEq)⟩, hScX⟩
        refine ⟨fun m hm => ?_, hFmEq ▸ hOld.2.1, hFmEq ▸ hOld.2.2.1,
          fun x hx hScX => hOld.2.2.2.1 x ((hMemSc' x).mp ⟨hx, hScX⟩).1 hScX,
          fun i hi hiPos x hx hMX => ?_,
          fun x₁ hx₁ x₂ hx₂ hs₁ hs₂ hl₁ hl₂ => hOld.2.2.2.2.2.1 x₁ ((hMemSc' x₁).mp ⟨hx₁, hs₁⟩).1
            x₂ ((hMemSc' x₂).mp ⟨hx₂, hs₂⟩).1 hs₁ hs₂ hl₁ hl₂,
          fun x hx hScX hlX => hOld.2.2.2.2.2.2 x ((hMemSc' x).mp ⟨hx, hScX⟩).1 hScX hlX⟩
        · obtain ⟨u, hu, hMU, hScU⟩ := hOld.1 m hm
          exact ⟨u, ((hMemSc' u).mpr ⟨hu, hScU⟩).1, hMU, hScU⟩
        · obtain ⟨u, hu, hMU, hScU⟩ := hOld.1 (ms'[i]'hi) (List.getElem_mem hi)
          have hu1 : u ∈ st1.groups := ((hMemSc' u).mpr ⟨hu, hScU⟩).1
          have rflX := mem_groups_eq_of_metaPtr hNd1 hx hu1 (hMX.trans hMU.symm)
          rw [rflX]; exact hOld.2.2.2.2.1 i hi hiPos u hu hMU
    liveMap_wf := fun p n => by
      rw [hwf.liveMap_wf p n]; simp only [st1, List.mem_map]
      exact ⟨fun ⟨u, hu, idx, hIdx, ef, hSl⟩ => by
        obtain ⟨idx', hIdx', hSl'⟩ := List.getElem_of_mem
          (((hSlotLists u hu).2.2.2.2 p n ef).mpr (hSl ▸ List.getElem_mem hIdx))
        exact ⟨fG u, ⟨u, hu, rfl⟩, idx', hIdx', ef, hSl'⟩,
        fun ⟨_, ⟨u, hu, rfl⟩, idx', hIdx', ef, hSl'⟩ => by
        obtain ⟨idx, hIdx, hSl⟩ := List.getElem_of_mem
          (((hSlotLists u hu).2.2.2.2 p n ef).mp (hSl' ▸ List.getElem_mem hIdx'))
        exact ⟨u, hu, idx, hIdx, ef, hSl⟩⟩
    live_le_peak := hwf.live_le_peak
    effCost_le_live := by unfold totalLiveEffCost; dsimp only [st1]; rw [hEffSum]; exact hwf.effCost_le_live
    meta_pages_bound := hwf.meta_pages_bound
    empty_groups_bound := fun g1 hg1 hEmpF => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg1
      have hEmpU : u.isEmpty = true := (hSlotLists u hu).1.symm.trans hEmpF
      obtain ⟨hm, _, hlast, hscU, hmap, _⟩ := hFields u hu
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hwf.empty_groups_bound u hu hEmpU
      refine ⟨hmap ▸ h1, hscU ▸ h2, hscU ▸ h3, hmap ▸ h4, fun hLt => ?_,
        fun g1' hg1' hEmpF' hScF' => ?_, fun hL0 => hscU ▸ hmap ▸ h7 (hlast ▸ hL0)⟩
      · dsimp only [st1] at hLt ⊢
        by_cases hEq : (fG u).sc = sc
        · have hEqU : u.sc = sc := hscU.symm.trans hEq
          simp [hEq, hm, hEmptySc u hu hEqU hEmpU]
        · rw [List.getElem_set_ne (Ne.symm hEq), hm]
          have hLtU : u.sc < st.activeLists.length := by simp [hscU] at hLt; exact hLt
          simpa [hscU] using h5 hLtU
      · obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hg1'
        obtain ⟨hm', _, _, hscU', _⟩ := hFields u' hu'
        have hEmpU' : u'.isEmpty = true := (hSlotLists u' hu').1.symm.trans hEmpF'
        rw [hm', hm]; exact h6 u' hu' hEmpU' (hscU'.symm.trans (hScF'.trans hscU))
    masterDom_wf := ⟨hwf.masterDom_wf.1,
      fun a hAny => hwf.masterDom_wf.2.1 a (hAny.elim (fun hR => Or.inl ((hOwnIff a).mp hR))
        (fun hPM => hPM.elim (Or.inr ∘ Or.inl) (fun hM => Or.inr (Or.inr ((hMpIff a).mp hM))))),
      fun a ha => hDynEq ▸ hwf.masterDom_wf.2.2 a ha⟩
  }
  have hPnEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := by
    unfold ProtNoneByteMap; refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => ?_)
    congr 1; symm; refine hBvOut a (fun u hu => ?_)
    exact hPn.elim (fun ⟨gp, hgp, ha⟩ => hDisjGp u hu gp hgp a ha) (fun ⟨ap, hap, ha⟩ => hDisjAp u hu ap hap a ha)
  have hMpEq : MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) := by
    unfold MappedSet; exact SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl)
  exact ⟨hWf1, by unfold totalLiveCount; dsimp only [st1]; exact hLiveSum,
    by unfold totalLiveEffCost; dsimp only [st1]; exact hEffSum, hDynEq, hOwnIff, hPnEq, hMpEq⟩

/-! ## `try_avail` Dequeue and `activate_group` Absorption Corollaries -/

theorem freed0_eq_lastIdx_not_empty {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hAv0 : g.availMask = 0#32) (hFr0 : g.freedMask = 0#32) :
    g.activeIdx = g.lastIdx ∧ g.isEmpty = false := by
  have hgWf := hwf.groups_wf g hg
  have hActLe : g.activeIdx ≤ g.lastIdx := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLen : g.slots.length = g.lastIdx + 1 := hgWf.2.2.1
  have hActEq : g.activeIdx = g.lastIdx :=
    Classical.byContradiction fun hNe => by
      have hj : g.activeIdx + 1 < g.slots.length := by omega
      have hsw := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (g.activeIdx + 1) hj
      have hIn : g.slots[g.activeIdx + 1]'hj = .freeInactive := hsw.2.2.2.1 (by omega)
      have hBit : g.freedMask.getLsbD (g.activeIdx + 1) = true := hsw.2.2.1.mpr hIn
      simp [hFr0] at hBit
  have h0 : 0 < g.slots.length := by omega
  have hsw0 := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 h0
  have hNotF : (g.slots[0]'h0).isFree = false := by
    cases hs : g.slots[0]'h0 with
    | freeAvail => have hb := hsw0.2.1.mpr hs; simp [hAv0] at hb
    | freeInactive => have hb := hsw0.2.2.1.mpr hs; simp [hFr0] at hb
    | _ => rfl
  refine ⟨hActEq, Bool.eq_false_iff.mpr fun hAll => ?_⟩
  unfold GroupDesc.isEmpty at hAll
  have hMem0 := List.all_eq_true.mp hAll (g.slots[0]'h0) (List.getElem_mem h0)
  rw [hNotF] at hMem0; cases hMem0

theorem writeBytes40_props {bv : BitVec 64 → BitVec 8} {m : BitVec 64} {bs : List (BitVec 8)}
    (hLen : bs.length = 40) (_hBound : m.toNat + 40 ≤ 2 ^ 48) :
    (∀ a : BitVec 64, ¬ InRegion m 40 a → writeBytesToMap bv m bs a = bv a) ∧
    readBytesFromMap (writeBytesToMap bv m bs) m 40 = bs :=
  ⟨fun a hNot => writeBytesToMap_out bv m bs (hLen ▸ hNot),
    hLen ▸ readBytesFromMap_writeBytesToMap bv m bs (by omega)⟩

theorem tryAvail_dequeue_singleton_absorb {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < 48) {g : GroupDesc} (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : st.ctx.active[sc]'(by rw [hwf.ctx_lens.1]; exact hsc) = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hFr0 : g.freedMask = 0#32) (hNxSelf : g.next = g.metaPtr) :
    let g' : GroupDesc := { g with prev := 0#64, next := 0#64 }
    let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g' else u
    let bv1 := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
    let st1 : MallocngSt :=
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc 0#64 }
        groups := st.groups.map fG
        activeLists := st.activeLists.set sc []
        byteVal := bv1 }
    let Rest := ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 ∧
    totalLiveCount st1 = totalLiveCount st ∧
    totalLiveEffCost st1 = totalLiveEffCost st ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((g.metaPtr ↦ₛ g.metaBytes) ∗ Rest) ∧
    (((g.metaPtr ↦ₛ g'.metaBytes) ∗ Rest) = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) := by
  intro g' fG bv1 st1 Rest
  obtain ⟨hActEq, hNotEmp⟩ := freed0_eq_lastIdx_not_empty hwf hg hAv0 hFr0
  obtain ⟨_, _, hMBound, hMRead, hMOwn⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hGLen : g'.metaBytes.length = 40 := by simp [GroupDesc.metaBytes]
  obtain ⟨hWOut, hWRead⟩ := writeBytes40_props (bv := st.byteVal) hGLen hMBound
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
  have hActOld := hwf.active_wf sc h1 h2
  have hMsEq : st.activeLists[sc]'h2 = [g.metaPtr] := by
    cases hMs : st.activeLists[sc]'h2 with
    | nil =>
      have hDll := hActOld.2.1; rw [hMs, hHead] at hDll
      have h0 : g.metaPtr = 0#64 := hDll
      have hLo := (meta_ownedRw_of_mem_groups hwf hg).1; rw [h0] at hLo; simp at hLo
    | cons m0 tl =>
      obtain ⟨g0, hg0, rfl, _⟩ := hActOld.1 m0 (hMs ▸ List.mem_cons_self ..)
      have hDll := hActOld.2.1
      rw [hMs] at hDll; simp only [List.filterMap_cons, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg0,
        Option.map_some] at hDll
      have rflG0 : g0 = g := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg0 hg (hDll.1.symm.trans hHead)
      subst rflG0
      have hTlNil : (tl.filterMap fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) = [] :=
        (CircularDllWf.singleton_iff_next_eq hDll).1.mp hNxSelf
      have hMapFst := activeList_nodes_map_fst hwf.groups_nodup.1
        (fun m hm => let ⟨x, hx, hmX, _⟩ := hActOld.1 m (hMs ▸ List.mem_cons_of_mem _ hm); ⟨x, hx, hmX⟩)
      rw [hTlNil] at hMapFst; simp at hMapFst; simp [hMapFst]
  have hFuEq : ∀ u ∈ st.groups, fG u = if u = g then g' else u := fun u hu => by
    dsimp only [fG]; by_cases hE : u = g
    · rw [hE]; simp
    · have hNeM : (u.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne (fun hM => hE (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM))
      simp [hE, hNeM]
  have hMain := metaOnly_map_wf hwf hsc hg (newHead := 0#64) (newMs := []) (fG := fG) (bv1 := bv1)
    (fun u hu => by
      by_cases hE : u = g
      · rw [hE, hFuEq g hg]; simp [g', hScEq]
      · simp [hFuEq u hu, hE])
    (fun u hu => by
      have huWf := hwf.groups_wf u hu
      by_cases hE : u = g
      · rw [hE] at huWf ⊢; rw [hFuEq g hg]; simp only [↓reduceIte]
        exact ⟨by simp [g', hAv0, hFr0], huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun _ => ⟨rfl, rfl⟩⟩
      · rw [hFuEq u hu]; simp only [hE, ↓reduceIte]
        exact ⟨huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1, huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          fun h63 => (huWf.2.2.2.1 h63).2.2⟩)
    (fun u hu j hj1 hj2 => by
      have hsw := (hwf.groups_wf u hu).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj2
      have hSlEq : (fG u).slots = u.slots := by
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp [g']
        · simp [hFuEq u hu, hE]
      have hAvEq : (fG u).availMask = u.availMask := by
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp [g']
        · simp [hFuEq u hu, hE]
      have hFrEq : (fG u).freedMask = u.freedMask := by
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp [g']
        · simp [hFuEq u hu, hE]
      have hGetEq : (fG u).slots[j]'hj1 = u.slots[j]'hj2 := by simp [hSlEq]
      dsimp only; rw [hGetEq, hAvEq, hFrEq]
      exact ⟨Or.inl rfl, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1⟩)
    (fun a hOut => hWOut a (hOut g hg))
    (fun u hu => by
      by_cases hE : u = g
      · rw [hE]; simp only [fG, beq_self_eq_true, ↓reduceIte]; exact hWRead
      · have hNeM : u.metaPtr ≠ g.metaPtr := fun hM => hE (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM)
        have hDisj := (allMetaSlots_info hwf ((hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu)))))).2.2.2.2
          g.metaPtr ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
          hNeM.symm
        simp only [hFuEq u hu, hE, ↓reduceIte]
        exact (readBytesFromMap_congr (by decide) fun a ha =>
          hWOut a (fun hInG => DisjointRegions.not_both hDisj ha hInG)).trans (meta_ownedRw_of_mem_groups hwf hu).2.2.2.1)
    (by
      have hSubF : ∀ u ∈ st.groups, (fG u).metaPtr = u.metaPtr ∧ (fG u).sc = u.sc ∧
          (fG u).activeIdx = u.activeIdx ∧ (fG u).lastIdx = u.lastIdx := fun u hu => by
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp [g', GroupDesc.activeIdx]
        · simp [hFuEq u hu, hE]
      refine ⟨by simp, rfl, rfl, ?_, by simp, ?_, ?_⟩
      · simp only [List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hScF
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp only [↓reduceIte]
          exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun _ h => List.not_mem_nil h⟩, fun _ => ⟨hAv0, hFr0, hActEq⟩⟩
        · simp only [hFuEq u hu, hE, ↓reduceIte] at hScF ⊢
          have hNotMem : u.metaPtr ∉ st.activeLists[sc]'h2 := by
            rw [hMsEq, List.mem_singleton]
            exact fun hM => hE (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM)
          have hOff := hActOld.2.2.2.1 u hu hScF
          exact ⟨⟨fun _ => hOff.1.mp hNotMem, fun _ h => List.not_mem_nil h⟩, fun _ => hOff.2 hNotMem⟩
      · simp only [List.mem_map]
        rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ hs₁ hs₂ hl₁ hl₂
        obtain ⟨hm1, hsc1, ha1, hl1'⟩ := hSubF u₁ hu₁
        obtain ⟨hm2, hsc2, ha2, hl2'⟩ := hSubF u₂ hu₂
        rw [hm1, hm2]
        exact hActOld.2.2.2.2.2.1 u₁ hu₁ u₂ hu₂ (hsc1 ▸ hs₁) (hsc2 ▸ hs₂)
          (by rw [← ha1, ← hl1']; exact hl₁) (by rw [← ha2, ← hl2']; exact hl₂)
      · simp only [List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hsF hlF
        obtain ⟨_, hscU, haU, hlU⟩ := hSubF u hu
        have hul : u.activeIdx < u.lastIdx := by rw [← haU, ← hlU]; exact hlF
        have hInMs := (hActOld.2.2.2.2.2.2 u hu (hscU ▸ hsF) hul).1
        rw [hMsEq, List.mem_singleton] at hInMs
        have rflU := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hInMs
        rw [rflU] at hul; omega)
    (fun u hu hScU hEmpU => by
      have hLtU : u.sc < st.activeLists.length := hScU ▸ h2
      have hInMs := (hwf.empty_groups_bound u hu hEmpU).2.2.2.2.1 hLtU
      have hMsEq' : st.activeLists[u.sc]'hLtU = [g.metaPtr] := by cases hScU; exact hMsEq
      rw [hMsEq', List.mem_singleton] at hInMs
      have rflU := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hInMs
      rw [rflU, hNotEmp] at hEmpU; cases hEmpU)
  obtain ⟨hWf1, hCnt1, hEff1, hDyn1, hOwn1, hPn1, hMp1⟩ := hMain
  have hUpd := slot_byteMap_update40 hwf.masterDom_wf.1 (P := OwnedRwByte st) st.byteVal hGLen hMOwn
  have hBmEq : ByteMap st.masterDom (OwnedRwByte st) bv1 = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal :=
    SetSep_congr (fun a _ => (hOwn1 a).symm) (fun _ _ _ => rfl)
  exact ⟨hWf1, hCnt1, hEff1, hDyn1, hPn1, hMp1, hMRead ▸ hUpd.1, hUpd.2.trans hBmEq⟩

theorem tryAvail_activate_group_absorb {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < 48) {g : GroupDesc} (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : st.ctx.active[sc]'(by rw [hwf.ctx_lens.1]; exact hsc) = g.metaPtr)
    (hAv0 : g.availMask = 0#32) :
    let cntMask : BitVec 32 := (2#32 <<< g.activeIdx) - 1#32
    let hiMask : BitVec 32 := -(2#32 <<< g.activeIdx)
    let newAvail : BitVec 32 := cntMask &&& g.freedMask
    let newFreed : BitVec 32 := g.freedMask &&& hiMask
    let newSlots : List SlotState :=
      List.ofFn fun i : Fin g.slots.length =>
        if i.1 ≤ g.activeIdx ∧ g.slots[i.1]'i.2 = .freeInactive then .freeAvail else g.slots[i.1]'i.2
    let g' : GroupDesc := { g with availMask := newAvail, freedMask := newFreed, slots := newSlots }
    let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g' else u
    let bv1 := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
    let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
    let st1 : MallocngSt :=
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc g.metaPtr }
        groups := st.groups.map fG
        activeLists := st.activeLists.set sc (st.activeLists[sc]'h2)
        byteVal := bv1 }
    let Rest := ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal
    g' ∈ st1.groups ∧
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 ∧
    totalLiveCount st1 = totalLiveCount st ∧
    totalLiveEffCost st1 = totalLiveEffCost st ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = ((g.metaPtr ↦ₛ g.metaBytes) ∗ Rest) ∧
    (((g.metaPtr ↦ₛ g'.metaBytes) ∗ Rest) = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) := by
  intro cntMask hiMask newAvail newFreed newSlots g' fG bv1 h2 st1 Rest
  have hgWf := hwf.groups_wf g hg
  have hLast : g.lastIdx ≤ 31 := hgWf.2.1
  have hActLe : g.activeIdx ≤ g.lastIdx := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOrBnd : (g.availMask ||| g.freedMask).toNat < 2 ^ g.cnt :=
    hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFrLt : g.freedMask.toNat < 2 ^ (g.lastIdx + 1) := by
    rw [hAv0, BitVec.zero_or] at hOrBnd; simpa [GroupDesc.cnt] using hOrBnd
  obtain ⟨hBits, hAnd0, _, hOrLt⟩ := activateMask_props hActLe hLast hFrLt
  obtain ⟨_, _, hMBound, hMRead, hMOwn⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hGLen : g'.metaBytes.length = 40 := by simp [GroupDesc.metaBytes]
  obtain ⟨hWOut, hWRead⟩ := writeBytes40_props (bv := st.byteVal) hGLen hMBound
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have hActOld := hwf.active_wf sc h1 h2
  have hFuEq : ∀ u ∈ st.groups, fG u = if u = g then g' else u := fun u hu => by
    dsimp only [fG]; by_cases hE : u = g
    · rw [hE]; simp
    · have hNeM : (u.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne (fun hM => hE (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM))
      simp [hE, hNeM]
  have hNd1 : ((st.groups.map fG).map (·.metaPtr)).Nodup := by
    have hMapEq : (st.groups.map fG).map (·.metaPtr) = st.groups.map (·.metaPtr) := by
      rw [List.map_map]
      have : ∀ u ∈ st.groups, (fG u).metaPtr = u.metaPtr := fun u hu => by
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp [g']
        · simp [hFuEq u hu, hE]
      exact List.map_congr_left this
    rw [hMapEq]; exact hwf.groups_nodup.1
  have hMain := metaOnly_map_wf hwf hsc hg (newHead := g.metaPtr) (newMs := st.activeLists[sc]'h2)
    (fG := fG) (bv1 := bv1)
    (fun u hu => by
      by_cases hE : u = g
      · rw [hE, hFuEq g hg]; simp [g', newSlots, hScEq]
      · simp [hFuEq u hu, hE])
    (fun u hu => by
      have huWf := hwf.groups_wf u hu
      by_cases hE : u = g
      · rw [hE] at huWf ⊢; rw [hFuEq g hg]; simp only [↓reduceIte, g']
        exact ⟨hAnd0, by unfold GroupDesc.cnt; exact hOrLt, fun h63 => (huWf.2.2.2.1 h63).2.2⟩
      · rw [hFuEq u hu]; simp only [hE, ↓reduceIte]
        exact ⟨huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1, huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          fun h63 => (huWf.2.2.2.1 h63).2.2⟩)
    (fun u hu j hj1 hj2 => by
      have hsw := (hwf.groups_wf u hu).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj2
      by_cases hE : u = g
      · have hjG : j < g.slots.length := hE ▸ hj2
        have hswG := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hjG
        have hj32 : j < 32 := by have := hgWf.2.2.1; unfold GroupDesc.cnt at this; omega
        obtain ⟨hcB, hhB⟩ := hBits j hj32
        have hNotAv : g.slots[j]'hjG ≠ .freeAvail := fun hA => by
          have hb := hswG.2.1.mpr hA; simp [hAv0] at hb
        have hSlJ : (fG u).slots[j]'hj1 =
            if j ≤ g.activeIdx ∧ g.slots[j]'hjG = .freeInactive then .freeAvail else g.slots[j]'hjG := by
          have hSlEq : (fG u).slots = newSlots := by rw [hE, hFuEq g hg]; simp [g']
          simp [hSlEq, newSlots]
        have hUG : u.slots[j]'hj2 = g.slots[j]'hjG := by cases hE; rfl
        have hAvM : (fG u).availMask = newAvail := by rw [hE, hFuEq g hg]; simp [g']
        have hFrM : (fG u).freedMask = newFreed := by rw [hE, hFuEq g hg]; simp [g']
        have hActU : u.activeIdx = g.activeIdx := by rw [hE]
        dsimp only; rw [hSlJ, hUG, hAvM, hFrM, hActU]
        refine ⟨?_, ?_, ?_, fun hGt => ?_⟩
        · split
          · rename_i hCond; exact Or.inr ⟨rfl, by simp [hCond.2, SlotState.isFree]⟩
          · exact Or.inl rfl
        · dsimp only [newAvail]; rw [BitVec.getLsbD_and, hcB, Bool.and_eq_true, decide_eq_true_eq, hswG.2.2.1]
          split <;> simp_all
        · dsimp only [newFreed]; rw [BitVec.getLsbD_and, hhB, Bool.and_eq_true, decide_eq_true_eq, hswG.2.2.1]
          split
          · rename_i hCond
            exact ⟨fun ⟨_, hLt⟩ => False.elim (by omega), fun h => nomatch h⟩
          · rename_i hCond
            exact ⟨fun ⟨hIn, _⟩ => hIn, fun hIn => ⟨hIn, Nat.lt_of_not_ge fun hLe => hCond ⟨hLe, hIn⟩⟩⟩
        · split
          · rename_i hC; omega
          · exact hswG.2.2.2.1 hGt
      · have hSlEq : (fG u).slots = u.slots := by simp [hFuEq u hu, hE]
        have hAvEq : (fG u).availMask = u.availMask := by simp [hFuEq u hu, hE]
        have hFrEq : (fG u).freedMask = u.freedMask := by simp [hFuEq u hu, hE]
        have hGetEq : (fG u).slots[j]'hj1 = u.slots[j]'hj2 := by simp [hSlEq]
        dsimp only; rw [hGetEq, hAvEq, hFrEq]
        exact ⟨Or.inl rfl, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1⟩)
    (fun a hOut => hWOut a (hOut g hg))
    (fun u hu => by
      by_cases hE : u = g
      · rw [hE]; simp only [fG, beq_self_eq_true, ↓reduceIte]; exact hWRead
      · have hNeM : u.metaPtr ≠ g.metaPtr := fun hM => hE (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM)
        have hDisj := (allMetaSlots_info hwf ((hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu)))))).2.2.2.2
          g.metaPtr ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
          hNeM.symm
        simp only [hFuEq u hu, hE, ↓reduceIte]
        exact (readBytesFromMap_congr (by decide) fun a ha =>
          hWOut a (fun hInG => DisjointRegions.not_both hDisj ha hInG)).trans (meta_ownedRw_of_mem_groups hwf hu).2.2.2.1)
    (by
      have hHeadNe0 : st.ctx.active[sc]'h1 ≠ 0#64 := by
        rw [hHead]; intro h0; have hLo := (meta_ownedRw_of_mem_groups hwf hg).1; rw [h0] at hLo; simp at hLo
      obtain ⟨g0, _, hG0M, _, msTl, hMsCons⟩ := active_head_group_of_nonzero hwf h1 h2 hHeadNe0
      have hMsG : st.activeLists[sc]'h2 = g.metaPtr :: msTl := by rw [hMsCons, hG0M, hHead]
      have hHeadInMs : g.metaPtr ∈ st.activeLists[sc]'h2 := by rw [hMsG]; exact List.mem_cons_self ..
      have hSubF : ∀ u ∈ st.groups, (fG u).metaPtr = u.metaPtr ∧ (fG u).prev = u.prev ∧
          (fG u).next = u.next ∧ (fG u).sc = u.sc ∧ (fG u).activeIdx = u.activeIdx ∧
          (fG u).lastIdx = u.lastIdx := fun u hu => by
        by_cases hE : u = g
        · rw [hE, hFuEq g hg]; simp [g', GroupDesc.activeIdx]
        · simp [hFuEq u hu, hE]
      have hFmEq : ((st.activeLists[sc]'h2).filterMap fun m =>
          (findGroupByMeta st1 m).map fun x => (x.metaPtr, x.prev, x.next)) =
          ((st.activeLists[sc]'h2).filterMap fun m =>
            (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) :=
        filterMap_congr_mem fun m hm => by
          obtain ⟨u, hu, rfl, _⟩ := hActOld.1 m hm
          obtain ⟨hmU, hpvU, hnxU, _⟩ := hSubF u hu
          have hu1 : fG u ∈ st1.groups := List.mem_map_of_mem hu
          rw [← hmU, slot_findGroupByMeta_eq_of_mem hNd1 hu1, hmU, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hu]
          simp [hmU, hpvU, hnxU]
      refine ⟨fun m hm => ?_, hFmEq ▸ hHead ▸ hActOld.2.1, hFmEq ▸ hActOld.2.2.1, ?_, ?_, ?_, ?_⟩
      · obtain ⟨u, hu, rfl, hScU⟩ := hActOld.1 m hm
        obtain ⟨hmU, _, _, hscU, _⟩ := hSubF u hu
        exact ⟨fG u, List.mem_map_of_mem hu, hmU, hscU.trans hScU⟩
      · simp only [List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hScF
        obtain ⟨hmU, hpvU, hnxU, hscU, _⟩ := hSubF u hu
        have hOff := hActOld.2.2.2.1 u hu (hscU ▸ hScF)
        refine ⟨by rw [hmU, hpvU, hnxU]; exact hOff.1, fun hNotMem => ?_⟩
        rw [hmU] at hNotMem
        have hNeG : u ≠ g := fun hE => hNotMem (hE ▸ hHeadInMs)
        simp only [hFuEq u hu, hNeG, ↓reduceIte]
        exact hOff.2 hNotMem
      · intro i hi hiPos _ hMemF hMF
        simp only [List.mem_map] at hMemF; obtain ⟨u, hu, rfl⟩ := hMemF
        obtain ⟨hmU, _⟩ := hSubF u hu; rw [hmU] at hMF
        have hNeG : u ≠ g := fun hE => by
          have hDll := hActOld.2.1
          have hMapFst := activeList_nodes_map_fst hwf.groups_nodup.1
            (fun m hm => let ⟨x, hx, hmX, _⟩ := hActOld.1 m hm; ⟨x, hx, hmX⟩)
          rw [hMsG] at hDll hMapFst
          simp only [List.filterMap_cons, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg,
            Option.map_some] at hDll hMapFst
          have hNdCons : (g.metaPtr :: msTl).Nodup := hMapFst ▸ hDll.2.1
          cases i with
          | zero => omega
          | succ k =>
            have hk : k < msTl.length := by rw [hMsG, List.length_cons] at hi; omega
            have hGetTl : u.metaPtr = msTl[k]'hk := by simp [hMsG] at hMF; exact hMF
            have hInTl : u.metaPtr ∈ msTl := hGetTl ▸ List.getElem_mem hk
            exact (List.nodup_cons.mp hNdCons).1 (hE ▸ hInTl)
        simp only [hFuEq u hu, hNeG, ↓reduceIte]
        exact hActOld.2.2.2.2.1 i hi hiPos u hu hMF
      · simp only [List.mem_map]
        rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ hs₁ hs₂ hl₁ hl₂
        obtain ⟨hm1, _, _, hsc1, ha1, hl1'⟩ := hSubF u₁ hu₁
        obtain ⟨hm2, _, _, hsc2, ha2, hl2'⟩ := hSubF u₂ hu₂
        rw [hm1, hm2]
        exact hActOld.2.2.2.2.2.1 u₁ hu₁ u₂ hu₂ (hsc1 ▸ hs₁) (hsc2 ▸ hs₂)
          (by rw [← ha1, ← hl1']; exact hl₁) (by rw [← ha2, ← hl2']; exact hl₂)
      · simp only [List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hsF hlF
        obtain ⟨hmU, _, _, hscU, haU, hlU⟩ := hSubF u hu
        rw [hmU]
        exact hActOld.2.2.2.2.2.2 u hu (hscU ▸ hsF) (by rw [← haU, ← hlU]; exact hlF))
    (fun u hu hScU hEmpU => by
      have hLtU : u.sc < st.activeLists.length := hScU ▸ h2
      have hSingleton := (hwf.empty_groups_bound u hu hEmpU).2.2.2.2.1 hLtU
      cases hScU; exact hSingleton)
  obtain ⟨hWf1, hCnt1, hEff1, hDyn1, hOwn1, hPn1, hMp1⟩ := hMain
  have hg1 : g' ∈ st1.groups := by
    have : fG g = g' := by simp [hFuEq g hg]
    exact this ▸ List.mem_map_of_mem (f := fG) hg
  have hUpd := slot_byteMap_update40 hwf.masterDom_wf.1 (P := OwnedRwByte st) st.byteVal hGLen hMOwn
  have hBmEq : ByteMap st.masterDom (OwnedRwByte st) bv1 = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal :=
    SetSep_congr (fun a _ => (hOwn1 a).symm) (fun _ _ _ => rfl)
  exact ⟨hg1, hWf1, hCnt1, hEff1, hDyn1, hPn1, hMp1, hMRead ▸ hUpd.1, hUpd.2.trans hBmEq⟩

end VerifiedLibraries.Mallocng.Proofs

