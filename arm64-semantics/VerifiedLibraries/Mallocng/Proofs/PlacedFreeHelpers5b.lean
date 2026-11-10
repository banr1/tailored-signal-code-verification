/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedFreeHelpers5

/-!
# Active-Queue Insertion Helpers for `nontrivial_free`

Invariant-transition helpers (`byteMap_update40`, `mkQueuedFullGroup`, `updateQueuedGroups`, and
`free_queue_nonempty_active`) for appending a previously full group behind a non-empty circular
doubly linked list `ctx.active[g.sc]` during `nontrivial_free`.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

theorem byteMap_update40 {dom : List (BitVec 64)} (hNd : dom.Nodup)
    {P : BitVec 64 → Prop} [DecidablePred P] (bv : BitVec 64 → BitVec 8)
    {m : BitVec 64} {bs : List (BitVec 8)} (hLen : bs.length = 40)
    (hSub : ∀ a, InRegion m 40 a → P a ∧ a ∈ dom) :
    ByteMap dom P bv =
      ((m ↦ₛ readBytesFromMap bv m 40) ∗
        ByteMap dom (fun a => P a ∧ ¬ InRegion m 40 a) bv) ∧
    (((m ↦ₛ bs) ∗ ByteMap dom (fun a => P a ∧ ¬ InRegion m 40 a) bv) =
      ByteMap dom P (writeBytesToMap bv m bs)) := by
  refine ⟨ByteMap_extract_slice hNd bv m (by decide : 40 ≤ 2 ^ 64)
    (fun a ha => (hSub a ha).2) (fun a ha => (hSub a ha).1), ?_⟩
  rw [ByteMap_absorb_slice hNd bv m bs (by rw [hLen]; decide)
    (fun a ha => (hSub a (hLen ▸ ha)).2)
    (fun _ hIn ⟨_, hN⟩ => hN (hLen ▸ hIn))]
  exact SetSep_congr (fun a _ => by
    rw [hLen]
    exact ⟨fun h => h.elim And.left (fun ha => (hSub a ha).1),
      fun h => if ha : InRegion m 40 a then Or.inr ha else Or.inl ⟨h, ha⟩⟩)
    (fun _ _ _ => rfl)

def mkQueuedFullGroup (g : GroupDesc) (tailPtr head : BitVec 64) (idx : Nat) : GroupDesc :=
  { g with
    prev      := tailPtr
    next      := head
    freedMask := g.freedMask ||| (1#32 <<< idx)
    slots     := g.slots.set idx .freeInactive }

def updateQueuedGroups (gs : List GroupDesc) (head tailPtr : BitVec 64)
    (g1 : GroupDesc) : List GroupDesc :=
  gs.map fun h =>
    if h.metaPtr == g1.metaPtr then g1
    else
      { h with
        prev := if h.metaPtr == head then g1.metaPtr else h.prev
        next := if h.metaPtr == tailPtr then g1.metaPtr else h.next }

private theorem updateQueuedGroups_map_eq {α : Type} (gs : List GroupDesc)
    (head tailPtr : BitVec 64) (g1 : GroupDesc) (f : GroupDesc → α)
    (hInv : ∀ (h : GroupDesc) (pv nx : BitVec 64), f { h with prev := pv, next := nx } = f h) :
    (updateQueuedGroups gs head tailPtr g1).map f =
      (replaceGroupByMeta gs g1.metaPtr g1).map f := by
  simp only [updateQueuedGroups, replaceGroupByMeta, List.map_map]
  apply List.map_congr_left
  intro h _
  dsimp only [Function.comp]
  split
  · rfl
  · exact hInv h _ _

private theorem updateQueuedGroups_filter_map_eq {α : Type} (gs : List GroupDesc)
    (head tailPtr : BitVec 64) (g1 : GroupDesc)
    (p : GroupDesc → Bool) (f : GroupDesc → α)
    (hp : ∀ (h : GroupDesc) (pv nx : BitVec 64), p { h with prev := pv, next := nx } = p h)
    (hf : ∀ (h : GroupDesc) (pv nx : BitVec 64), f { h with prev := pv, next := nx } = f h) :
    ((updateQueuedGroups gs head tailPtr g1).filter p).map f =
      ((replaceGroupByMeta gs g1.metaPtr g1).filter p).map f := by
  induction gs with
  | nil => rfl
  | cons x xs ih =>
    change (((if x.metaPtr == g1.metaPtr then g1
        else { x with
          prev := if x.metaPtr == head then g1.metaPtr else x.prev
          next := if x.metaPtr == tailPtr then g1.metaPtr else x.next }) ::
        updateQueuedGroups xs head tailPtr g1).filter p).map f =
      (((if x.metaPtr == g1.metaPtr then g1 else x) ::
        replaceGroupByMeta xs g1.metaPtr g1).filter p).map f
    by_cases hG : x.metaPtr == g1.metaPtr
    · simp only [hG, ↓reduceIte, List.filter_cons]; split <;> simp [ih]
    · simp only [hG, Bool.false_eq_true, ↓reduceIte, List.filter_cons, hp x _ _]
      split <;> simp [hf x _ _, ih]

set_option maxHeartbeats 400000 in
/-- Transition for `nontrivial_free` queueing a previously full group `g` (`availMask = 0`,
    `freedMask = 0`) behind a non-empty `ctx.active[g.sc]` (`head ≠ 0#64`, `head ≠ g.metaPtr`,
    `+0x45c..+0x484`). Transitions `MallocngWFInflight (k + 1)` to `MallocngWFInflight k`. -/
theorem free_queue_nonempty_active {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    (_hFq : FullQueueKeepWf st)
    {g : GroupDesc} {idx : Nat}
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48)
    (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAv0 : g.availMask = 0#32) (hFr0 : g.freedMask = 0#32)
    (hNotAllFree : (g.availMask ||| (g.freedMask ||| (1#32 <<< idx))).toNat ≠ 2 ^ g.cnt - 1)
    (hHeadNe0 : st.ctx.active[g.sc]'(by rw [hwf.ctx_lens.1]; exact hSc48) ≠ 0#64)
    (hHeadNeG : st.ctx.active[g.sc]'(by rw [hwf.ctx_lens.1]; exact hSc48) ≠ g.metaPtr) :
    let h1 : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    let h2 : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
    let head := st.ctx.active[g.sc]'h1
    let ms := st.activeLists[g.sc]'h2
    g.prev = 0#64 ∧ g.next = 0#64 ∧
    ∃ hdG ∈ st.groups, ∃ tlG ∈ st.groups,
      hdG.metaPtr = head ∧ hdG.sc = g.sc ∧
      tlG.metaPtr = hdG.prev ∧ tlG.sc = g.sc ∧
      hdG.metaPtr ≠ g.metaPtr ∧ tlG.metaPtr ≠ g.metaPtr ∧
      let g1 := mkQueuedFullGroup g hdG.prev head idx
      let tlUpd : GroupDesc := { tlG with next := g.metaPtr }
      let hdUpd : GroupDesc :=
        { hdG with
          prev := g.metaPtr
          next := if head == hdG.prev then g.metaPtr else hdG.next }
      let bv1 :=
        writeBytesToMap
          (writeBytesToMap
            (writeBytesToMap st.byteVal tlG.metaPtr tlUpd.metaBytes)
            head hdUpd.metaBytes)
          g.metaPtr g1.metaBytes
      let st1 : MallocngSt :=
        { st with
          groups      := updateQueuedGroups st.groups head hdG.prev g1
          activeLists := st.activeLists.set g.sc (ms ++ [g.metaPtr])
          byteVal     := bv1 }
      readBytesFromMap (writeBytesToMap st.byteVal tlG.metaPtr tlUpd.metaBytes) head 40 =
        ({ hdG with next := if head == hdG.prev then g.metaPtr else hdG.next } : GroupDesc).metaBytes ∧
      MallocngWFInflight k base brkStart brk liveCost peakCost st1 ∧
      (∀ a, OwnedRwByte st1 a ↔ OwnedRwByte st a) ∧
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
      MappedSet st1.masterDom (OwnedMappedByte st1) =
        MappedSet st.masterDom (OwnedMappedByte st) ∧
      dynamicRootRegions st1 = dynamicRootRegions st ∧
      totalLiveCount st1 = totalLiveCount st := by
  dsimp only []
  have h1 : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  have h2 : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
  let head := st.ctx.active[g.sc]'h1
  let ms := st.activeLists[g.sc]'h2
  have hActProps := activeList_head_and_singleton_props hwf hg hSc48
  have hmNe0 := hActProps.1
  have ⟨hNotMemG, hPv0, hNx0⟩ := hActProps.2.2.2.2.2.2 hHeadNeG hFr0
  have hActG := hwf.active_wf g.sc h1 h2
  have hMemW : ∀ m ∈ ms, ∃ h ∈ st.groups, h.metaPtr = m := fun m hm =>
    let ⟨h, hh, hM, _⟩ := hActG.1 m hm; ⟨h, hh, hM⟩
  let ns := ms.filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)
  have hDll : CircularDllWf head ns := hActG.2.1
  have hMapFst : ns.map Prod.fst = ms := activeList_nodes_eq_map hwf.groups_nodup.1 hMemW
  cases hNs : ns with
  | nil =>
    exact False.elim (hHeadNe0 ((CircularDllWf.head_eq_zero_iff (hNs ▸ hDll)).mpr rfl))
  | cons hdNode tlNodes =>
    rcases hdNode with ⟨p0, pv0, nx0⟩
    have hDllC : CircularDllWf head ((p0, pv0, nx0) :: tlNodes) := hNs ▸ hDll
    have hp0Eq : head = p0 := hDllC.1; subst p0
    have h0Ms : 0 < ms.length := by
      have : ms.length = ns.length := by rw [← hMapFst, List.length_map]
      rw [this, hNs]; simp
    obtain ⟨h0N, hdG, hhdG, hHdGM, hNs0⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW h0Ms
    have h0N' : 0 < ns.length := h0N
    have hNs0Opt : ns[0]? = some (hdG.metaPtr, hdG.prev, hdG.next) :=
      (List.getElem?_eq_getElem h0N').trans (congrArg some hNs0)
    rw [hNs] at hNs0Opt
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hNs0Opt
    obtain ⟨hHdMeta, hHdPrev, _⟩ := hNs0Opt
    have hHeadInMs : head ∈ ms := by rw [← hMapFst, hNs]; simp
    have hHdSc : hdG.sc = g.sc := by
      obtain ⟨h', hh', hM', hSc'⟩ := hActG.1 head hHeadInMs
      exact (congrArg GroupDesc.sc (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hhdG hh'
        (hHdMeta.symm.trans hM'.symm))).trans hSc'
    have hPv0InMs : hdG.prev ∈ ms := by
      have hLinks0 := (hDllC.2.2.2 0 (by simp)).2
      simp only [List.getElem_cons_zero] at hLinks0
      rw [← hHdPrev, hLinks0, ← hMapFst, hNs]
      exact List.mem_map_of_mem (List.getElem_mem _)
    obtain ⟨tlG, htlG, hTlMeta, hTlSc⟩ := hActG.1 hdG.prev hPv0InMs
    have hHdNeG : hdG.metaPtr ≠ g.metaPtr := hHdMeta.symm ▸ hHeadNeG
    have hTlNeG : tlG.metaPtr ≠ g.metaPtr := fun hEq => hNotMemG (hEq ▸ hTlMeta ▸ hPv0InMs)
    refine ⟨hPv0, hNx0, hdG, hhdG, tlG, htlG, hHdMeta.symm, hHdSc, hTlMeta, hTlSc,
      hHdNeG, hTlNeG, ?_⟩
    let g1 := mkQueuedFullGroup g hdG.prev head idx
    have hG1Meta : g1.metaPtr = g.metaPtr := rfl
    let tlUpd : GroupDesc := { tlG with next := g.metaPtr }
    let hdUpd : GroupDesc :=
      { hdG with prev := g.metaPtr, next := if head == hdG.prev then g.metaPtr else hdG.next }
    let bv_tl := writeBytesToMap st.byteVal tlG.metaPtr tlUpd.metaBytes
    let bv_hd := writeBytesToMap bv_tl head hdUpd.metaBytes
    let bv1 := writeBytesToMap bv_hd g.metaPtr g1.metaBytes
    let st1 : MallocngSt :=
      { st with
        groups      := updateQueuedGroups st.groups head hdG.prev g1
        activeLists := st.activeLists.set g.sc (ms ++ [g.metaPtr])
        byteVal     := bv1 }
    let updOther : GroupDesc → GroupDesc := fun h0 =>
      { h0 with
        prev := if h0.metaPtr == head then g.metaPtr else h0.prev
        next := if h0.metaPtr == hdG.prev then g.metaPtr else h0.next }
    have hGroupInAll : ∀ u ∈ st.groups, u.metaPtr ∈ allMetaSlots st := fun u hu =>
      (hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu))))
    have hAllG := hGroupInAll g hg; have hAllHd := hGroupInAll hdG hhdG; have hAllTl := hGroupInAll tlG htlG
    have hFitG := (allMetaSlots_info hwf hAllG).2.2.1
    have hFitHd : head.toNat + 40 ≤ 2 ^ 48 := hHdMeta ▸ (allMetaSlots_info hwf hAllHd).2.2.1
    have hFitTl := (allMetaSlots_info hwf hAllTl).2.2.1
    have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hReadHdAfterTl : readBytesFromMap bv_tl head 40 =
        ({ hdG with next := if head == hdG.prev then g.metaPtr else hdG.next } : GroupDesc).metaBytes := by
      by_cases hEqHT : head = hdG.prev
      · have hTlEqHd := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 htlG hhdG
          (hTlMeta.trans (hEqHT.symm.trans hHdMeta))
        subst tlG
        simp only [hEqHT, beq_self_eq_true, ↓reduceIte]
        have hPtrEq : hdG.metaPtr = hdG.prev := hHdMeta.symm.trans hEqHT
        dsimp only [bv_tl, tlUpd]; rw [← hPtrEq]
        exact readBytesFromMap_writeBytesToMap st.byteVal hdG.metaPtr _
          (by rw [GroupDesc.metaBytes_length]; omega)
      · have hRhsEq : ({ hdG with next := if head == hdG.prev then g.metaPtr else hdG.next } : GroupDesc) = hdG := by
          simp only [beq_false_of_ne hEqHT, Bool.false_eq_true, ↓reduceIte]
        rw [hRhsEq, readBytesFromMap_eq_of_inRegion (by omega) fun a ha =>
          writeBytesToMap_out st.byteVal tlG.metaPtr tlUpd.metaBytes (fun haTl =>
            DisjointRegions.not_both
              ((allMetaSlots_info hwf hAllTl).2.2.2.2 head (hHdMeta ▸ hAllHd)
                (fun hE => hEqHT (hE.trans hTlMeta)))
              (by simpa [GroupDesc.metaBytes_length] using haTl) ha), hHdMeta]
        exact (hwf.groups_wf hdG hhdG).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hOnlyMetas : ∀ a, bv1 a ≠ st.byteVal a → ∃ u ∈ st.groups, InRegion u.metaPtr 40 a := fun a hNe => by
      dsimp only [bv1] at hNe
      by_cases haG : InRegion g.metaPtr 40 a
      · exact ⟨g, hg, haG⟩
      · rw [writeBytesToMap_out bv_hd g.metaPtr g1.metaBytes
          (by simpa [GroupDesc.metaBytes_length] using haG)] at hNe
        dsimp only [bv_hd] at hNe
        by_cases haHd : InRegion head 40 a
        · exact ⟨hdG, hhdG, hHdMeta ▸ haHd⟩
        · rw [writeBytesToMap_out bv_tl head hdUpd.metaBytes
            (by simpa [GroupDesc.metaBytes_length] using haHd)] at hNe
          dsimp only [bv_tl] at hNe
          exact ⟨tlG, htlG, Classical.byContradiction fun haTl =>
            hNe (writeBytesToMap_out st.byteVal tlG.metaPtr tlUpd.metaBytes
              (by simpa [GroupDesc.metaBytes_length] using haTl))⟩
    have hDisj := groupMetaMod_disjoint hwf hOnlyMetas
    have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg (g1 := g1) rfl rfl rfl rfl rfl
    have hMetaMapEq : st1.groups.map (·.metaPtr) = st.groups.map (·.metaPtr) := by
      dsimp only [st1]
      rw [updateQueuedGroups_map_eq st.groups head hdG.prev g1 _ fun _ _ _ => rfl, hG1Meta]
      exact hRep.1
    have hMemMapEq : st1.groups.map (·.mem) = st.groups.map (·.mem) := by
      dsimp only [st1]
      rw [updateQueuedGroups_map_eq st.groups head hdG.prev g1 _ fun _ _ _ => rfl, hG1Meta]
      exact hRep.2.1
    have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
      unfold dynamicRootRegions; dsimp only [st1]
      rw [updateQueuedGroups_filter_map_eq st.groups head hdG.prev g1 _ _
        (fun _ _ _ => rfl) (fun _ _ _ => rfl), hG1Meta, hRep.2.2.1]
    have hMemGs1 : g1 ∈ st1.groups ∧
        (∀ h' ∈ st1.groups, h' = g1 ∨ ∃ h0 ∈ st.groups, h0.metaPtr ≠ g.metaPtr ∧ h' = updOther h0) ∧
        (∀ h0 ∈ st.groups, h0.metaPtr ≠ g.metaPtr → updOther h0 ∈ st1.groups) := by
      refine ⟨?_, fun h' hh' => ?_, fun h0 hh0 hNe => ?_⟩
      · have hEq : (if g.metaPtr == g1.metaPtr then g1 else updOther g) = g1 := by simp [g1, mkQueuedFullGroup]
        rw [← hEq]; exact List.mem_map_of_mem hg
      · obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh'
        by_cases hEq : h0.metaPtr = g.metaPtr
        · left; simp [g1, mkQueuedFullGroup, hEq]
        · right; exact ⟨h0, hh0, hEq, by simp [g1, mkQueuedFullGroup, beq_false_of_ne hEq, updOther]⟩
      · have hEq : (if h0.metaPtr == g1.metaPtr then g1 else updOther h0) = updOther h0 := by
          simp [g1, mkQueuedFullGroup, beq_false_of_ne hNe]
        rw [← hEq]; exact List.mem_map_of_mem hh0
    have hSlotsG1 : g1.slots = g.slots.set idx .freeInactive := rfl
    have hCntEq : totalLiveCount st1 = totalLiveCount st := by
      unfold totalLiveCount; dsimp only [st1]
      rw [updateQueuedGroups_map_eq st.groups head hdG.prev g1 _ fun _ _ _ => rfl, hG1Meta]
      have h1Sum := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (g1 := g1)
        (fun g => (g.slots.map slotLiveCount).sum)
      rw [hSlotsG1] at h1Sum
      have h2Sum := list_set_map_sum g.slots hIdx .freeInactive slotLiveCount
      simp only [hClaimed, slotLiveCount] at h2Sum; omega
    have hEffEq : totalLiveEffCost st1 = totalLiveEffCost st := by
      unfold totalLiveEffCost; dsimp only [st1]
      rw [updateQueuedGroups_map_eq st.groups head hdG.prev g1 _ fun _ _ _ => rfl, hG1Meta]
      have h1Sum := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg (g1 := g1)
        (fun g => (g.slots.map slotEffCost).sum)
      rw [hSlotsG1] at h1Sum
      have h2Sum := list_set_map_sum g.slots hIdx .freeInactive slotEffCost
      simp only [hClaimed, slotEffCost] at h2Sum; omega
    have hClaimSum : totalClaimedSlots st = totalClaimedSlots st1 + 1 := by
      unfold totalClaimedSlots; dsimp only [st1]
      rw [updateQueuedGroups_map_eq st.groups head hdG.prev g1 _ fun _ _ _ => rfl, hG1Meta]
      have hGSet := list_set_filter_len g.slots hIdx .freeInactive SlotState.isClaimed
      simp only [hClaimed, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hGSet
      obtain ⟨pre, post, hGsEq, _, _, hRepEq, _⟩ := split_groups_at_mem hwf.groups_nodup.1 hg
      rw [hRepEq]; conv => lhs; rw [hGsEq]
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, g1, mkQueuedFullGroup]
      omega
    have hSpatRef := metaBytes_update_spatial hwf (g1 := g1) hg hIdx hClaimed
      (s1 := .freeInactive) (fun _ _ _ h => by cases h) rfl rfl rfl rfl rfl rfl
    have hRwEq : ∀ a, OwnedRwByte st1 a ↔ OwnedRwByte st a := fun a => by
      let stMid : MallocngSt :=
        { st with
          groups := replaceGroupByMeta st.groups g.metaPtr g1
          byteVal := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes }
      refine Iff.trans ?_ (hSpatRef.2.1 a)
      unfold OwnedRwByte
      have hR : (∃ h ∈ st1.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
          (∃ h ∈ stMid.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) := by
        constructor
        · rintro ⟨h', hh', hP, hI⟩
          rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, hNe, rfl⟩
          · exact ⟨g1, hRep.2.2.2.2.1, hP, hI⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hNe, hP, hI⟩
        · rintro ⟨h', hh', hP, hI⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨h0, hNe⟩
          · exact ⟨g1, hMemGs1.1, hP, hI⟩
          · exact ⟨updOther h', hMemGs1.2.2 h' h0 hNe, hP, hI⟩
      have hC : CarvedUserByte st1 a ↔ CarvedUserByte stMid a := by
        unfold CarvedUserByte
        constructor
        · rintro ⟨h', hh', s, hs, hSub⟩
          rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, hNe, rfl⟩
          · exact ⟨g1, hRep.2.2.2.2.1, s, hs, hSub⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hNe, s, hs, hSub⟩
        · rintro ⟨h', hh', s, hs, hSub⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨h0, hNe⟩
          · exact ⟨g1, hMemGs1.1, s, hs, hSub⟩
          · exact ⟨updOther h', hMemGs1.2.2 h' h0 hNe, s, hs, hSub⟩
      rw [hR, hC]; rfl
    have hMapEq : ∀ a, OwnedMappedByte st1 a ↔ OwnedMappedByte st a := fun a => by
      unfold OwnedMappedByte; dsimp only [st1]
      refine or_congr_right (or_congr_right (or_congr_right ⟨?_, ?_⟩))
      · rintro ⟨h', hh', hP, hI⟩
        rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
        · exact ⟨g, hg, hP, hI⟩
        · exact ⟨h0, hh0, hP, hI⟩
      · rintro ⟨h0, hh0, hP, hI⟩
        by_cases hEq : h0.metaPtr = g.metaPtr
        · have hEG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq; subst h0
          exact ⟨g1, hMemGs1.1, hP, hI⟩
        · exact ⟨updOther h0, hMemGs1.2.2 h0 hh0 hEq, hP, hI⟩
    have hProtEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal :=
      SetSep_congr (fun _ _ => Iff.rfl) fun a _ hProt => by
        rcases hProt with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
        · exact congrArg (a ↦₈ₙ ·) (hDisj.2.2.1 gp hgp a haGp)
        · exact congrArg (a ↦₈ₙ ·) (hDisj.2.1 ap hap a haAp)
    have hHgWf := hwf.groups_wf g hg
    have hSlotWf := hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
    have hAvBitF : g.availMask.getLsbD idx = false := by simp [hAv0]
    have hFrBitF : g.freedMask.getLsbD idx = false := by simp [hFr0]
    have hIdxCnt : idx < g.cnt := by rw [← hHgWf.2.2.1]; exact hIdx
    have hIdxLeLast : idx ≤ g.lastIdx := by unfold GroupDesc.cnt at hIdxCnt; omega
    have hMaskProps := freeSlot_mask_props hIdxLeLast hHgWf.2.1 hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hAvBitF hFrBitF
    have hFrNe0 : g1.freedMask ≠ 0#32 := fun h0 => by
      have hb := congrArg (fun x : BitVec 32 => x.getLsbD idx) h0
      simp [g1, mkQueuedFullGroup, hMaskProps.2.2.2.2.2.1 idx] at hb
    have hG1SlotMasks : ∀ j : Nat, (hj1 : j < g1.slots.length) →
        (g1.availMask.getLsbD j = true ↔ g1.slots[j]'hj1 = .freeAvail) ∧
        (g1.freedMask.getLsbD j = true ↔ g1.slots[j]'hj1 = .freeInactive) := fun j hj1 => by
      have hj : j < g.slots.length := by simpa [g1, mkQueuedFullGroup] using hj1
      by_cases hjEq : j = idx
      · subst hjEq
        simp only [g1, mkQueuedFullGroup, List.getElem_set_self, reduceCtorEq, iff_false, iff_true,
          Bool.not_eq_true]
        exact ⟨hAvBitF, by simpa using hMaskProps.2.2.2.2.2.1 j⟩
      · simp only [g1, mkQueuedFullGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte]
        have hSWf := hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
        have hB := hMaskProps.2.2.2.2.2.1 j; simp only [hjEq, ↓reduceIte] at hB
        exact ⟨hSWf.2.1, by rw [hB]; exact hSWf.2.2.1⟩
    have hG1NotEmp : g1.isEmpty = false :=
      isEmpty_false_of_mask_ne hHgWf.2.1 (by simp [g1, mkQueuedFullGroup, hHgWf.2.2.1])
        hMaskProps.2.2.2.2.1 hG1SlotMasks hNotAllFree
    have hChildLift : ∀ cm : BitVec 64, ∀ cg ∈ st.groups, cg.metaPtr = cm →
        ∃ cg1 ∈ st1.groups, cg1.metaPtr = cg.metaPtr ∧ cg1.parentMeta = cg.parentMeta ∧
          cg1.mem = cg.mem ∧ cg1.nestedCap = cg.nestedCap := fun _ cg hcg _ => by
      by_cases hEqC : cg.metaPtr = g.metaPtr
      · have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hEqC; subst cg
        exact ⟨g1, hMemGs1.1, rfl, rfl, rfl, rfl⟩
      · exact ⟨updOther cg, hMemGs1.2.2 cg hcg hEqC, rfl, rfl, rfl, rfl⟩
    have hParentLift : ∀ h0 ∈ st.groups, h0.maplen = 0 →
        1 ≤ h0.lastIdx ∧
        ∃ pg ∈ st1.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
          h0.parentMeta = some pg.metaPtr ∧ pg.sc < 48 ∧ h0.sc < pg.sc ∧ pg.sc ≤ 24 ∧
          pg.slots[pIdx]'hp = .liveNested h0.metaPtr ∧
          (pg.slotStart pIdx).toNat ≤ h0.mem.toNat ∧
          h0.mem.toNat + h0.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
          h0.nestedCap = slotStride pg.sc - 4 := fun h0 hh0 hM0 => by
      obtain ⟨hLast1, pg, hpg, pIdx, hp, hPM, hP48, hScLt, hP24, hPSlot, hSLe, hELe, hNCap⟩ :=
        (hwf.groups_wf h0 hh0).2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
      refine ⟨hLast1, ?_⟩
      by_cases hEqPg : pg.metaPtr = g.metaPtr
      · have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hEqPg; subst pg
        have hpNe : pIdx ≠ idx := fun hEqI => by subst hEqI; rw [hClaimed] at hPSlot; cases hPSlot
        refine ⟨g1, hMemGs1.1, pIdx, by simpa [g1, mkQueuedFullGroup] using hp,
          hPM, hP48, hScLt, hP24, ?_, hSLe, hELe, hNCap⟩
        simp [g1, mkQueuedFullGroup, Ne.symm hpNe, hPSlot]
      · exact ⟨updOther pg, hMemGs1.2.2 pg hpg hEqPg, pIdx, hp, hPM, hP48, hScLt, hP24,
          hPSlot, hSLe, hELe, hNCap⟩
    have hInit1 : st.ctx.initDone = 1#32 := by
      rcases hwf.initDone_wf with h0 | h1'
      · have := (hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1; rw [this] at hg; cases hg
      · exact h1'
    have hWf1 : MallocngWFInflight k base brkStart brk liveCost peakCost st1 :=
      { base_wf := trivial
        brk_bounds := hwf.brk_bounds
        ctx_lens := ⟨hwf.ctx_lens.1, hwf.ctx_lens.2.1, hwf.ctx_lens.2.2.1,
          hwf.ctx_lens.2.2.2.1, hwf.ctx_lens.2.2.2.2.1, by simp [st1, hwf.ctx_lens.2.2.2.2.2]⟩
        initDone_wf := hwf.initDone_wf
        initZero_wf := fun h0 => by rw [hInit1] at h0; cases h0
        bounces_wf := hwf.bounces_wf
        usage_wf := fun sc hsc => by
          dsimp only [st1] at hsc ⊢
          rw [updateQueuedGroups_filter_map_eq st.groups head hdG.prev g1 _ _
            (fun _ _ _ => rfl) (fun _ _ _ => rfl), hG1Meta, hRep.2.2.2.1 sc]
          exact hwf.usage_wf sc hsc
        brk_mode_wf := hwf.brk_mode_wf
        metaAreas_wf := ⟨hwf.metaAreas_wf.1,
          fun ma hma => by
            have hM := hwf.metaAreas_wf.2.1 ma hma
            exact ⟨hM.1, hM.2.1, hM.2.2.1,
              (readBytesFromMap_eq_of_inRegion (by have := hM.2.2.1; omega)
                (hDisj.1 ma hma)).trans hM.2.2.2⟩,
          hwf.metaAreas_wf.2.2⟩
        guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
          fun ap hap => by
            have hA := hwf.guard_avail_wf.2.2.2 ap hap
            exact ⟨hA.1, hA.2.1, hA.2.2.1,
              (readBytesFromMap_eq_of_inRegion (by have := hA.2.2.1; omega)
                (hDisj.2.1 ap hap)).trans hA.2.2.2⟩⟩
        inflight_wf := by have := hwf.inflight_wf; dsimp only [st1] at hClaimSum ⊢; omega
        free_bump_metas_wf := by
          obtain ⟨hFmDll, hFmBytes, hBmMode, hBmBytes, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
          refine ⟨hFmDll, fun fm hfm => ?_, hBmMode, fun bm hbm => ?_,
            by simpa only [st1, hMetaMapEq] using hUfNd,
            fun m => by simpa only [st1, hMetaMapEq, allMetaSlots] using hUfIff m⟩
          · have hAllFm := (hUfIff fm.ptr).mp
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
            have ⟨_, _, hFit, _⟩ := allMetaSlots_info hwf hAllFm
            exact (readBytesFromMap_eq_of_inRegion (by omega) (hDisj.2.2.2.1 fm hfm)).trans (hFmBytes fm hfm)
          · have hAllBm := (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
            have ⟨_, _, hFit, _⟩ := allMetaSlots_info hwf hAllBm
            exact (readBytesFromMap_eq_of_inRegion (by omega) (hDisj.2.2.2.2.1 bm hbm)).trans (hBmBytes bm hbm)
        groups_nodup := ⟨hMetaMapEq ▸ hwf.groups_nodup.1, hMemMapEq ▸ hwf.groups_nodup.2⟩
        groups_wf := fun h' hh' => by
          rcases hMemGs1.2.1 h' hh' with hEq | ⟨h0, hh0, hNeG0, hEqUpd⟩
          · subst h'
            have hHdrDisj := hDisj.2.2.2.2.2 g hg
            have hFit64 : g.mem.toNat + g.totalBytes ≤ 2 ^ 64 := by
              have := hHgWf.2.2.2.2.2.2.1; omega
            have hTotGe12 : 12 ≤ g.totalBytes := by
              have := hHgWf.2.2.2.2.2.2.2.1; omega
            refine ⟨hHgWf.1, hHgWf.2.1, by simp [g1, mkQueuedFullGroup, hHgWf.2.2.1],
              fun h63 => by dsimp only [g1, mkQueuedFullGroup] at h63; omega,
              hHgWf.2.2.2.2.1, hHgWf.2.2.2.2.2.1, hHgWf.2.2.2.2.2.2.1, hHgWf.2.2.2.2.2.2.2.1,
              hHgWf.2.2.2.2.2.2.2.2.1, hHdrDisj.2.trans hHgWf.2.2.2.2.2.2.2.2.2.1,
              hHgWf.2.2.2.2.2.2.2.2.2.2.1, hHgWf.2.2.2.2.2.2.2.2.2.2.2.1,
              hParentLift g hg, hMaskProps.2.2.2.1, hMaskProps.2.2.2.2.1,
              hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              readBytesFromMap_writeBytesToMap bv_hd g.metaPtr g1.metaBytes
                (by rw [GroupDesc.metaBytes_length]; omega),
              by dsimp only [st1, g1, mkQueuedFullGroup]
                 rw [readBytesFromMap_eq_of_inRegion (by omega) fun a ha => by
                   have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
                   exact hHdrDisj.1 a ((inRegion_iff_toNat hFit64 a).mpr ⟨x1, by omega⟩)]
                 exact hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              (hHdrDisj.1 (g.mem + 8#64) ((inRegion_iff_toNat hFit64 _).mpr
                ⟨by rw [bv64_add_toNat (by omega)]; omega,
                 by rw [bv64_add_toNat (by omega)]; omega⟩)).trans
                hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              fun j hj1 => ?_⟩
            have hj : j < g.slots.length := by simpa [g1, mkQueuedFullGroup] using hj1
            by_cases hjEq : j = idx
            · subst hjEq
              have ⟨hStrGe, _, _, _, hEndTot, hSlotCalc⟩ := group_slot_toNat hHgWf
              have ⟨_, hEndNat, hSub4Nat⟩ := hSlotCalc j hIdxCnt
              have hMulLe : (j + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt
              have hSuccMul : (j + 1) * g.stride = j * g.stride + g.stride := Nat.succ_mul j g.stride
              have hSetSelf : g1.slots[j]'hj1 = .freeInactive := by simp [g1, mkQueuedFullGroup]
              have hAv1 := hSetSelf ▸ (hG1SlotMasks j hj1).1
              have hFr1 := hSetSelf ▸ (hG1SlotMasks j hj1).2
              rw [hSetSelf]
              refine ⟨?_, hAv1, hFr1, fun _ => rfl, trivial⟩
              change bv1 (g.slotStart j - 4#64) = 0#8
              exact (hHdrDisj.1 _ ((inRegion_iff_toNat hFit64 _).mpr ⟨by omega, by omega⟩)).trans hSlotWf.1
            · have hGet : g1.slots[j]'hj1 = g.slots[j]'hj := by
                simp [g1, mkQueuedFullGroup, Ne.symm hjEq]
              rw [hGet]
              have hSWf := hHgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
              exact slotWf_of_groupDataEq hHgWf hj hSWf hHdrDisj.1 rfl rfl rfl rfl rfl rfl
                (hGet ▸ (hG1SlotMasks j hj1).1) (hGet ▸ (hG1SlotMasks j hj1).2) hSWf.2.2.2.1
                (fun cm _ => hChildLift cm)
          · subst h'
            have hHWf := hwf.groups_wf h0 hh0
            have hAllH := hGroupInAll h0 hh0
            have hFitH := (allMetaSlots_info hwf hAllH).2.2.1
            have hOutG : ∀ a, InRegion h0.metaPtr 40 a → bv1 a = bv_hd a := fun a ha =>
              writeBytesToMap_out bv_hd g.metaPtr g1.metaBytes (fun haG =>
                DisjointRegions.not_both
                  ((allMetaSlots_info hwf hAllG).2.2.2.2 h0.metaPtr hAllH hNeG0)
                  (by simpa [GroupDesc.metaBytes_length] using haG) ha)
            have hMetaEq : readBytesFromMap bv1 h0.metaPtr 40 = (updOther h0).metaBytes := by
              rw [readBytesFromMap_eq_of_inRegion (by omega) hOutG]
              by_cases hEqHd : h0.metaPtr = head
              · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hhdG (hEqHd.trans hHdMeta)
                subst h0
                have hUpdEq : updOther hdG = hdUpd := by
                  dsimp only [updOther, hdUpd]
                  simp only [← hHdMeta, beq_self_eq_true, ↓reduceIte]
                rw [hUpdEq, ← hHdMeta]
                exact readBytesFromMap_writeBytesToMap bv_tl head hdUpd.metaBytes
                  (by rw [GroupDesc.metaBytes_length]; omega)
              · rw [readBytesFromMap_eq_of_inRegion (by omega) fun a ha =>
                  writeBytesToMap_out bv_tl head hdUpd.metaBytes (fun haHd =>
                    DisjointRegions.not_both
                      ((allMetaSlots_info hwf (hHdMeta ▸ hAllHd)).2.2.2.2 h0.metaPtr hAllH hEqHd)
                      (by simpa [GroupDesc.metaBytes_length] using haHd) ha)]
                by_cases hEqTl : h0.metaPtr = hdG.prev
                · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 htlG
                    (hEqTl.trans hTlMeta.symm)
                  subst h0
                  have hUpdEq : updOther tlG = tlUpd := by
                    dsimp only [updOther, tlUpd]
                    simp only [beq_false_of_ne hEqHd, Bool.false_eq_true, ↓reduceIte]
                    simp only [hTlMeta, beq_self_eq_true, ↓reduceIte]
                  rw [hUpdEq]
                  exact readBytesFromMap_writeBytesToMap st.byteVal tlG.metaPtr tlUpd.metaBytes
                    (by rw [GroupDesc.metaBytes_length]; omega)
                · rw [readBytesFromMap_eq_of_inRegion (by omega) fun a ha =>
                    writeBytesToMap_out st.byteVal tlG.metaPtr tlUpd.metaBytes (fun haTl =>
                      DisjointRegions.not_both
                        ((allMetaSlots_info hwf hAllTl).2.2.2.2 h0.metaPtr hAllH (hTlMeta.symm ▸ hEqTl))
                        (by simpa [GroupDesc.metaBytes_length] using haTl) ha)]
                  have hUpdEq : updOther h0 = h0 := by
                    dsimp only [updOther]
                    simp only [beq_false_of_ne hEqHd, beq_false_of_ne hEqTl, Bool.false_eq_true, ↓reduceIte]
                  rw [hUpdEq]
                  exact hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            exact groupWf_of_metaOnlyMod hHWf
              (fun h63 => by
                have hNeHd : h0.metaPtr ≠ head := fun hE => by
                  have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hhdG (hE.trans hHdMeta)
                  subst h0; omega
                have hNeTl : h0.metaPtr ≠ hdG.prev := fun hE => by
                  have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 htlG (hE.trans hTlMeta.symm)
                  subst h0; omega
                simp [beq_false_of_ne hNeHd, beq_false_of_ne hNeTl,
                  (hHWf.2.2.2.1 h63).2.2.1, (hHWf.2.2.2.1 h63).2.2.2])
              hMetaEq (hDisj.2.2.2.2.2 h0 hh0).1 (hDisj.2.2.2.2.2 h0 hh0).2
              (hParentLift h0 hh0) (fun _ _ cm _ => hChildLift cm)
        regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
        active_wf := fun sc h1' h2' => by
          have h2_0 : sc < st.activeLists.length := by simpa [st1] using h2'
          by_cases hScEq : sc = g.sc
          · subst hScEq
            have hMs1 : st1.activeLists[g.sc]'h2' = ms ++ [g.metaPtr] := by simp [st1, ms]
            have hFindG1 : findGroupByMeta st1 g.metaPtr = some g1 :=
              findGroupByMeta_eq_of_mem (hMetaMapEq ▸ hwf.groups_nodup.1) hMemGs1.1
            have hFMapMs :
                (ms.filterMap fun m => (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
                ns.map fun d =>
                  (d.1, if d.1 == head then g.metaPtr else d.2.1,
                    if d.1 == hdG.prev then g.metaPtr else d.2.2) := by
              have hStep : ∀ l : List (BitVec 64), (∀ m ∈ l, m ∈ ms) →
                  (l.filterMap fun m => (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
                  (l.filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)).map
                    fun d => (d.1, if d.1 == head then g.metaPtr else d.2.1,
                      if d.1 == hdG.prev then g.metaPtr else d.2.2) := by
                intro l hl; induction l with
                | nil => rfl
                | cons m rest ih =>
                  obtain ⟨h0, hh0, hM0⟩ := hMemW m (hl m List.mem_cons_self)
                  have hNeG0 : h0.metaPtr ≠ g.metaPtr := fun hE =>
                    hNotMemG (hE ▸ hM0 ▸ hl m List.mem_cons_self)
                  have hF0 : findGroupByMeta st m = some h0 :=
                    hM0 ▸ findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hh0
                  have hF1 : findGroupByMeta st1 m = some (updOther h0) := by
                    rw [← hM0]
                    exact findGroupByMeta_eq_of_mem (hMetaMapEq ▸ hwf.groups_nodup.1)
                      (hMemGs1.2.2 h0 hh0 hNeG0)
                  simp only [List.filterMap_cons, hF0, hF1, Option.map_some, List.map_cons,
                    updOther, ih fun x hx => hl x (List.mem_cons_of_mem m hx)]
              exact hStep ms fun _ hm => hm
            have hSnoc := CircularDllWf.snoc hmNe0 (by rw [← hNs, hMapFst]; exact hNotMemG) hDllC
            dsimp only [] at hSnoc
            have hSnocNs : CircularDllWf head
                (ns.map (fun d => (d.1, if d.1 == head then g.metaPtr else d.2.1,
                  if d.1 == hdG.prev then g.metaPtr else d.2.2)) ++ [(g.metaPtr, hdG.prev, head)]) := by
              rw [hNs]; simpa only [← hHdPrev] using hSnoc
            rw [ActiveClassWf, show st1.ctx.active[g.sc]'h1' = head from rfl, hMs1,
              List.filterMap_append, hFMapMs]
            simp only [List.filterMap_cons, List.filterMap_nil, hFindG1, Option.map_some,
              g1, mkQueuedFullGroup]
            refine ⟨fun m hm => ?_, hSnocNs,
              by simp only [List.length_append, List.length_map, List.length_singleton]
                 exact congrArg (· + 1) hActG.2.2.1,
              fun h' hh' hSc' => ?_, fun i hi hPos h' hh' hEqM => ?_,
              fun h₁ hh₁ h₂ hh₂ hSc₁ hSc₂ hLt₁ hLt₂ => ?_,
              fun h' hh' hSc' hLt => ?_⟩
            · rcases List.mem_append.mp hm with hm0 | hmG
              · obtain ⟨h0, hh0, hM0, hSc0⟩ := hActG.1 m hm0
                have hNe : h0.metaPtr ≠ g.metaPtr := fun hE => hNotMemG (hE ▸ hM0 ▸ hm0)
                exact ⟨updOther h0, hMemGs1.2.2 h0 hh0 hNe, hM0, hSc0⟩
              · have hmEq : m = g.metaPtr := by simpa using hmG
                subst hmEq; exact ⟨g1, hMemGs1.1, rfl, rfl⟩
            · rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, hNe, rfl⟩
              · have hIn : g1.metaPtr ∈ ms ++ [g.metaPtr] := by simp [hG1Meta]
                exact ⟨⟨fun hN => False.elim (hN hIn), fun ⟨_, hN0⟩ => False.elim (hHeadNe0 hN0)⟩,
                  fun hN => False.elim (hN hIn)⟩
              · by_cases hIn0 : h0.metaPtr ∈ ms
                · have hIn : (updOther h0).metaPtr ∈ ms ++ [g.metaPtr] :=
                    List.mem_append_left _ hIn0
                  refine ⟨⟨fun hN => False.elim (hN hIn), fun ⟨hP0, hN0⟩ => ?_⟩,
                    fun hN => False.elim (hN hIn)⟩
                  by_cases hEH : h0.metaPtr == head
                  · simp [updOther, hEH] at hP0; exact False.elim (hmNe0 hP0)
                  · by_cases hET : h0.metaPtr == hdG.prev
                    · simp [updOther, hET] at hN0; exact False.elim (hmNe0 hN0)
                    · simp only [updOther, hEH, hET, Bool.false_eq_true, ↓reduceIte] at hP0 hN0
                      exact False.elim (((hActG.2.2.2.1 h0 hh0 hSc').1.mpr ⟨hP0, hN0⟩) hIn0)
                · have hNeHd : (h0.metaPtr == head) = false :=
                    beq_false_of_ne fun hE => hIn0 (hE ▸ hHeadInMs)
                  have hNeTl : (h0.metaPtr == hdG.prev) = false :=
                    beq_false_of_ne fun hE => hIn0 (hE ▸ hPv0InMs)
                  have hUpdId : updOther h0 = h0 := by
                    dsimp only [updOther]
                    simp only [hNeHd, hNeTl, Bool.false_eq_true, ↓reduceIte]
                  rw [hUpdId]
                  have hNotApp : h0.metaPtr ∉ ms ++ [g.metaPtr] := by simp [hIn0, hNe]
                  have hSub := hActG.2.2.2.1 h0 hh0 hSc'
                  exact ⟨⟨fun _ => hSub.1.mp hIn0, fun _ => hNotApp⟩, fun _ => hSub.2 hIn0⟩
            · simp only [List.length_append, List.length_singleton] at hi
              by_cases hiLt : i < ms.length
              · rw [List.getElem_append_left hiLt] at hEqM
                rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
                · exact False.elim (hNotMemG (hEqM ▸ List.getElem_mem hiLt))
                · exact hActG.2.2.2.2.1 i hiLt hPos h0 hh0 hEqM
              · have hiEq : i = ms.length := by omega
                subst hiEq
                simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
                  List.getElem_cons_zero] at hEqM
                rcases hMemGs1.2.1 h' hh' with rfl | ⟨_, _, hNe, rfl⟩
                · exact ⟨hAv0, hFrNe0⟩
                · exact False.elim (hNe hEqM)
            · have ⟨u1, hu1, hM1, hS1, hL1⟩ :
                  ∃ u1 ∈ st.groups, h₁.metaPtr = u1.metaPtr ∧ u1.sc = g.sc ∧ u1.activeIdx < u1.lastIdx := by
                rcases hMemGs1.2.1 h₁ hh₁ with rfl | ⟨h0, hh0, _, rfl⟩
                · exact ⟨g, hg, rfl, rfl, hLt₁⟩
                · exact ⟨h0, hh0, rfl, hSc₁, hLt₁⟩
              have ⟨u2, hu2, hM2, hS2, hL2⟩ :
                  ∃ u2 ∈ st.groups, h₂.metaPtr = u2.metaPtr ∧ u2.sc = g.sc ∧ u2.activeIdx < u2.lastIdx := by
                rcases hMemGs1.2.1 h₂ hh₂ with rfl | ⟨h0, hh0, _, rfl⟩
                · exact ⟨g, hg, rfl, rfl, hLt₂⟩
                · exact ⟨h0, hh0, rfl, hSc₂, hLt₂⟩
              exact hM1.trans ((hActG.2.2.2.2.2.1 u1 hu1 u2 hu2 hS1 hS2 hL1 hL2).trans hM2.symm)
            · rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
              · have ⟨hIn0, hPos0⟩ := hActG.2.2.2.2.2.2 g hg rfl hLt
                exact ⟨List.mem_append_left _ hIn0, hPos0⟩
              · have ⟨hIn0, hPos0⟩ := hActG.2.2.2.2.2.2 h0 hh0 hSc' hLt
                exact ⟨List.mem_append_left _ hIn0, hPos0⟩
          · have hAct0 := hwf.active_wf sc h1' h2_0
            have hMs1 : st1.activeLists[sc]'h2' = st.activeLists[sc]'h2_0 := by
              simp [st1, Ne.symm hScEq]
            have hIdOther : ∀ h0 ∈ st.groups, h0.sc = sc → updOther h0 = h0 := fun h0 hh0 hSc0 => by
              have hNeHd : (h0.metaPtr == head) = false := beq_false_of_ne fun hE =>
                hScEq (hSc0.symm.trans ((congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hhdG (hE.trans hHdMeta))).trans hHdSc))
              have hNeTl : (h0.metaPtr == hdG.prev) = false := beq_false_of_ne fun hE =>
                hScEq (hSc0.symm.trans ((congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 htlG (hE.trans hTlMeta.symm))).trans hTlSc))
              dsimp only [updOther]
              simp only [hNeHd, hNeTl, Bool.false_eq_true, ↓reduceIte]
            have hFMapEq :
                ((st.activeLists[sc]'h2_0).filterMap fun m =>
                  (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
                ((st.activeLists[sc]'h2_0).filterMap fun m =>
                  (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
              have hStep : ∀ l : List (BitVec 64), (∀ m ∈ l, m ∈ st.activeLists[sc]'h2_0) →
                  (l.filterMap fun m => (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
                  (l.filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
                intro l hl; induction l with
                | nil => rfl
                | cons m rest ih =>
                  obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct0.1 m (hl m List.mem_cons_self)
                  have hNeG0 : h0.metaPtr ≠ g.metaPtr := fun hE =>
                    hScEq (hSc0.symm.trans (congrArg GroupDesc.sc
                      (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hE)))
                  have hF0 : findGroupByMeta st h0.metaPtr = some h0 :=
                    findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hh0
                  have hF1 : findGroupByMeta st1 h0.metaPtr = some h0 :=
                    findGroupByMeta_eq_of_mem (hMetaMapEq ▸ hwf.groups_nodup.1)
                      (hIdOther h0 hh0 hSc0 ▸ hMemGs1.2.2 h0 hh0 hNeG0)
                  rw [← hM0]
                  simp [hF0, hF1, ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]
              exact hStep _ fun _ hm => hm
            rw [ActiveClassWf, show st1.ctx.active[sc]'h1' = st.ctx.active[sc]'h1' from rfl, hMs1]
            refine ⟨fun m hm => ?_, hFMapEq ▸ hAct0.2.1, hFMapEq ▸ hAct0.2.2.1,
              fun h' hh' hSc' => ?_, fun i hi hPos h' hh' hEqM => ?_,
              fun h₁ hh₁ h₂ hh₂ hSc₁ hSc₂ hLt₁ hLt₂ => ?_,
              fun h' hh' hSc' hLt => ?_⟩
            · obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct0.1 m hm
              have hNeG0 : h0.metaPtr ≠ g.metaPtr := fun hE =>
                hScEq (hSc0.symm.trans (congrArg GroupDesc.sc
                  (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hE)))
              exact ⟨h0, hIdOther h0 hh0 hSc0 ▸ hMemGs1.2.2 h0 hh0 hNeG0, hM0, hSc0⟩
            · rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
              · exact False.elim (hScEq hSc'.symm)
              · rw [hIdOther h0 hh0 hSc']; exact hAct0.2.2.2.1 h0 hh0 hSc'
            · rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
              · obtain ⟨u, hu, hMU, hScU⟩ := hAct0.1 _ (List.getElem_mem hi)
                have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg (hMU.trans hEqM.symm)
                subst u; exact False.elim (hScEq hScU.symm)
              · exact hAct0.2.2.2.2.1 i hi hPos h0 hh0 hEqM
            · rcases hMemGs1.2.1 h₁ hh₁ with rfl | ⟨u1, hu1, _, rfl⟩
              · exact False.elim (hScEq hSc₁.symm)
              · rcases hMemGs1.2.1 h₂ hh₂ with rfl | ⟨u2, hu2, _, rfl⟩
                · exact False.elim (hScEq hSc₂.symm)
                · exact hAct0.2.2.2.2.2.1 u1 hu1 u2 hu2 hSc₁ hSc₂ hLt₁ hLt₂
            · rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
              · exact False.elim (hScEq hSc'.symm)
              · exact hAct0.2.2.2.2.2.2 h0 hh0 hSc' hLt
        liveMap_wf := fun p req => by
          rw [show st1.liveMap = st.liveMap from rfl, hwf.liveMap_wf]
          constructor
          · rintro ⟨h0, hh0, j, hj0, ec, hS0⟩
            by_cases hEqM : h0.metaPtr = g.metaPtr
            · have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEqM; subst h0
              have hjNe : j ≠ idx := fun hEqJ => by subst hEqJ; rw [hClaimed] at hS0; cases hS0
              refine ⟨g1, hMemGs1.1, j, by simpa [g1, mkQueuedFullGroup] using hj0, ec, ?_⟩
              simp [g1, mkQueuedFullGroup, Ne.symm hjNe, hS0]
            · exact ⟨updOther h0, hMemGs1.2.2 h0 hh0 hEqM, j, hj0, ec, hS0⟩
          · rintro ⟨h', hh', j, hj', ec, hS'⟩
            rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
            · have hj0 : j < g.slots.length := by simpa [g1, mkQueuedFullGroup] using hj'
              have hjNe : j ≠ idx := fun hEqJ => by subst hEqJ; simp [g1, mkQueuedFullGroup] at hS'
              simp only [g1, mkQueuedFullGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte] at hS'
              exact ⟨g, hg, j, hj0, ec, hS'⟩
            · exact ⟨h0, hh0, j, hj', ec, hS'⟩
        live_le_peak := hwf.live_le_peak
        effCost_le_live := hEffEq ▸ hwf.effCost_le_live
        meta_pages_bound := hwf.meta_pages_bound
        empty_groups_bound := fun h' hh' hEmp => by
          rcases hMemGs1.2.1 h' hh' with rfl | ⟨h0, hh0, _, rfl⟩
          · rw [hG1NotEmp] at hEmp; cases hEmp
          · have hEmp0 : h0.isEmpty = true := hEmp
            have ⟨hPos, h7, h38, hCap, hActMem, hUniq, hSlk⟩ := hwf.empty_groups_bound h0 hh0 hEmp0
            refine ⟨hPos, h7, h38, hCap, fun hL => ?_, fun g' hg' hEmp' hSc' => ?_, hSlk⟩
            · have hL0 : h0.sc < st.activeLists.length := by simpa [st1, updOther] using hL
              by_cases hScEq : h0.sc = g.sc
              · have hInMs : h0.metaPtr ∈ ms := by simpa [ms, hScEq] using hActMem hL0
                have hSetEq : st1.activeLists[(updOther h0).sc]'hL = ms ++ [g.metaPtr] := by
                  simp [st1, updOther, hScEq]
                rw [hSetEq]; exact List.mem_append_left _ hInMs
              · have hSetEq : st1.activeLists[(updOther h0).sc]'hL = st.activeLists[h0.sc]'hL0 := by
                  simp [st1, updOther, Ne.symm hScEq]
                exact hSetEq ▸ hActMem hL0
            · rcases hMemGs1.2.1 g' hg' with rfl | ⟨u0, hu0, _, rfl⟩
              · rw [hG1NotEmp] at hEmp'; cases hEmp'
              · exact hUniq u0 hu0 hEmp' hSc'
        masterDom_wf := ⟨hwf.masterDom_wf.1,
          fun a hOwn => hwf.masterDom_wf.2.1 a (by
            rcases hOwn with hRw | hPn | hMp
            · exact Or.inl ((hRwEq a).mp hRw)
            · exact Or.inr (Or.inl hPn)
            · exact Or.inr (Or.inr ((hMapEq a).mp hMp))),
          by rw [hDynEq]; exact hwf.masterDom_wf.2.2⟩ }
    exact And.intro hReadHdAfterTl (And.intro hWf1 (And.intro hRwEq (And.intro hProtEq
      (And.intro (SetSep_congr (fun a _ => hMapEq a) (fun _ _ _ => rfl))
        (And.intro hDynEq hCntEq)))))

end VerifiedLibraries.Mallocng.Proofs
