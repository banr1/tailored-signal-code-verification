/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedFreeHelpers6

/-!
# Non-Empty Free-Meta Recycling for Placed `free`

Proves the `+0x224` `free_meta` invariant transition (`free_recycle_reserved_meta_nonempty`) when
`ctx.free_meta_head ≠ 0#64`, linking a reserved `meta` node onto `freeMetas` via
`CircularDllWf.snoc` without importing instruction-fetch modules.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

def updateFreeMetasSnoc (fms : List FreeMetaDesc) (head tailPtr m : BitVec 64) :
    List FreeMetaDesc :=
  fms.map fun fm =>
    { fm with
      prev := if fm.ptr == head then m else fm.prev
      next := if fm.ptr == tailPtr then m else fm.next }

set_option maxHeartbeats 400000 in
/-- Transition `MallocngWFInflight (k + 1)` to `MallocngWFInflight k` across `free_meta`
    (`+0x224 .. +0x254`) when `head = st.ctx.freeMetaHead ≠ 0#64`: links `m` between
    `st.freeMetas.getLast` (`tailPtr = hdFm.prev`) and `hdFm` (`head`), pops `m` from
    `st.reservedMetas`, and absorbs `(m ↦ₛ ⟨m, tailPtr, head⟩.toBytes)` into `ByteMap`. -/
theorem free_recycle_reserved_meta_nonempty {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {m : BitVec 64} (hmRes : m ∈ st.reservedMetas)
    (hHeadNe0 : st.ctx.freeMetaHead ≠ 0#64) :
    let head := st.ctx.freeMetaHead
    ∃ hdFm ∈ st.freeMetas, ∃ tlFm ∈ st.freeMetas,
      hdFm.ptr = head ∧
      tlFm.ptr = hdFm.prev ∧
      (∀ a, InRegion head 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
      (∀ a, InRegion hdFm.prev 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
      readBytesFromMap st.byteVal head 40 = hdFm.toBytes ∧
      readBytesFromMap st.byteVal hdFm.prev 40 = tlFm.toBytes ∧
      let fmNew : FreeMetaDesc := ⟨m, hdFm.prev, head⟩
      let tlUpd : FreeMetaDesc := { tlFm with next := m }
      let hdUpd : FreeMetaDesc :=
        { hdFm with
          prev := m
          next := if head == hdFm.prev then m else hdFm.next }
      let dom1 := extendDom40 st.masterDom m
      let bvTl := writeBytesToMap st.byteVal hdFm.prev tlUpd.toBytes
      let bvHd := writeBytesToMap bvTl head hdUpd.toBytes
      let bv1 := writeBytesToMap bvHd m fmNew.toBytes
      let st1 : MallocngSt :=
        { st with
          freeMetas     := updateFreeMetasSnoc st.freeMetas head hdFm.prev m ++ [fmNew]
          reservedMetas := st.reservedMetas.erase m
          masterDom     := dom1
          byteVal       := bv1 }
      readBytesFromMap bvTl head 40 =
        ({ hdFm with next := if head == hdFm.prev then m else hdFm.next } : FreeMetaDesc).toBytes ∧
      (((m ↦ₛ fmNew.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) bvHd) =
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) ∧
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
      MappedSet st1.masterDom (OwnedMappedByte st1) =
        MappedSet st.masterDom (OwnedMappedByte st) ∧
      MallocngWFInflight k base brkStart brk liveCost peakCost st1 ∧
      st1.reservedMetas = st.reservedMetas.erase m ∧
      dynamicRootRegions st1 = dynamicRootRegions st ∧
      totalLiveCount st1 = totalLiveCount st := by
  dsimp only []
  let head := st.ctx.freeMetaHead
  have ⟨hmNe0, hmAll, ⟨maM, hmaM, hSubMa⟩, hNotRwCu, hCarvedEr, hDisjMa, hDisjAp, hDisjGp,
    hDisjFmM, hDisjBm, hDisjGrp⟩ := reservedMeta_common_props hwf hmRes
  have ⟨hDomNd1, hMInDom1, hDom1Split, hSetSepExt⟩ := extendDom40_props hwf.masterDom_wf.1 m
  have ⟨hDll0, hFmBytes, hBumpOr, _, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
  have ⟨_, _, hLeftDisj⟩ := List.nodup_append.mp hUfNd
  have ⟨_, _, hErLen⟩ := erase_nodup_and_mem (List.nodup_append.mp hUfNd).2.1 m
  have hLenRes := hErLen hmRes
  have hInit1 : st.ctx.initDone = 1#32 := by
    rcases hwf.initDone_wf with h0 | h1
    · have := (hwf.initZero_wf h0).2.2.2.2.2.2.2.2.1; rw [this] at hmRes; cases hmRes
    · exact h1
  have hFmOwn : ∀ fm ∈ st.freeMetas, ∀ a, InRegion fm.ptr 40 a →
      OwnedRwByte st a ∧ a ∈ st.masterDom := by
    intro fm hfm a ha
    have hfmUfL : fm.ptr ∈ st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))
    have hfmAll : fm.ptr ∈ allMetaSlots st := (hUfIff fm.ptr).mp (List.mem_append_left _ hfmUfL)
    obtain ⟨_, ⟨maF, hmaF, hSubF⟩, hNoCu, _, _, _, _⟩ := allMetaSlot_disjoint_other hwf hfmAll
    have hNoCm : ¬ CarvedMetaByte st a := by
      rintro ⟨r, hrRes, haR⟩
      exact metaSlot_disjoint_of_ne hwf hfmAll ((hUfIff r).mp (List.mem_append_right _ hrRes))
        (fun hEq => hLeftDisj fm.ptr hfmUfL r hrRes hEq) ha haR
    have hRw : OwnedRwByte st a := ⟨Or.inl ⟨maF, hmaF, hSubF a ha⟩, hNoCu a ha, hNoCm⟩
    exact ⟨hRw, hwf.masterDom_wf.2.1 a (Or.inl hRw)⟩
  have hNonEmpty : ∃ hdFm restFms, st.freeMetas = hdFm :: restFms := by
    cases hF : st.freeMetas with
    | nil => exact False.elim (hHeadNe0 (by simpa [hF, CircularDllWf] using hDll0))
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  match hNonEmpty with
  | ⟨hdFm, restFms, hFms⟩ =>
    let fNode : FreeMetaDesc → BitVec 64 × BitVec 64 × BitVec 64 :=
      fun fm => (fm.ptr, fm.prev, fm.next)
    let ns := (hdFm :: restFms).map fNode
    have hDllNs : CircularDllWf head ns := by simpa [ns, hFms, fNode] using hDll0
    have hDllC : CircularDllWf head ((hdFm.ptr, hdFm.prev, hdFm.next) :: restFms.map fNode) :=
      hDllNs
    have hHdPtr : head = hdFm.ptr := hDllC.1
    have hLenPos : 0 < (hdFm :: restFms).length := by simp
    let lastIdx := (hdFm :: restFms).length - 1
    have hLastLt : lastIdx < (hdFm :: restFms).length := Nat.sub_lt hLenPos Nat.zero_lt_one
    obtain ⟨tlFm, htlEq⟩ : ∃ t, (hdFm :: restFms)[lastIdx]'hLastLt = t := ⟨_, rfl⟩
    have hhdMem : hdFm ∈ st.freeMetas := hFms ▸ List.mem_cons_self ..
    have htlMem : tlFm ∈ st.freeMetas := hFms ▸ htlEq ▸ List.getElem_mem hLastLt
    have hModLast : (0 + ns.length - 1) % ns.length = lastIdx := by
      simp only [ns, List.length_map, Nat.zero_add]
      exact Nat.mod_eq_of_lt hLastLt
    have hPrv0 : hdFm.prev = tlFm.ptr := by
      have h2 := (hDllNs.2.2.2 0 (by simp [ns])).2
      simp only [hModLast] at h2
      simpa only [ns, List.getElem_cons_zero, List.getElem_map, htlEq, fNode] using h2
    have hFmPtrNd : (st.freeMetas.map (·.ptr)).Nodup := by
      have hMapEq : ns.map Prod.fst = st.freeMetas.map (·.ptr) := by
        simp [ns, fNode, hFms, List.map_map, Function.comp_def]
      exact hMapEq ▸ hDllC.2.1
    have hFmEqOfPtr : ∀ u ∈ st.freeMetas, ∀ v ∈ st.freeMetas, u.ptr = v.ptr → u = v := by
      intro u hu v hv hEqP
      obtain ⟨i1, hi1, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨i2, hi2, rfl⟩ := List.getElem_of_mem hv
      have hIdxEq := nodup_idx_eq hFmPtrNd
        (by rw [List.length_map]; exact hi1) (by rw [List.length_map]; exact hi2)
        (by simpa using hEqP)
      subst hIdxEq; rfl
    have hmNotFm : m ∉ (hdFm :: restFms).map (·.ptr) := fun hmIn =>
      hLeftDisj m (List.mem_append_left _ (List.mem_append_right _ (hFms ▸ hmIn))) m hmRes rfl
    have hSnocDll := CircularDllWf.snoc hmNe0
      (by simpa [fNode, List.map_map, Function.comp_def] using hmNotFm) hDllC
    dsimp only [] at hSnocDll
    let fmNew : FreeMetaDesc := ⟨m, hdFm.prev, head⟩
    let tlUpd : FreeMetaDesc := { tlFm with next := m }
    let hdUpd : FreeMetaDesc :=
      { hdFm with
        prev := m
        next := if head == hdFm.prev then m else hdFm.next }
    let dom1 := extendDom40 st.masterDom m
    let bvTl := writeBytesToMap st.byteVal hdFm.prev tlUpd.toBytes
    let bvHd := writeBytesToMap bvTl head hdUpd.toBytes
    let bv1 := writeBytesToMap bvHd m fmNew.toBytes
    let st1 : MallocngSt :=
      { st with
        freeMetas     := updateFreeMetasSnoc st.freeMetas head hdFm.prev m ++ [fmNew]
        reservedMetas := st.reservedMetas.erase m
        masterDom     := dom1
        byteVal       := bv1 }
    have hReadHdAfterTl : readBytesFromMap bvTl head 40 =
        ({ hdFm with next := if head == hdFm.prev then m else hdFm.next } : FreeMetaDesc).toBytes := by
      by_cases hSameHT : head = hdFm.prev
      · have hEqFm : hdFm = tlFm := hFmEqOfPtr hdFm hhdMem tlFm htlMem (hHdPtr.symm.trans (hSameHT.trans hPrv0))
        have hBeqT : (head == hdFm.prev) = true := beq_iff_eq.mpr hSameHT
        rw [hBeqT]
        simp only [↓reduceIte]
        rw [hEqFm]
        change readBytesFromMap (writeBytesToMap st.byteVal hdFm.prev tlUpd.toBytes) head 40 = tlUpd.toBytes
        rw [← hSameHT]
        simpa only [FreeMetaDesc.toBytes_length] using
          readBytesFromMap_writeBytesToMap st.byteVal head tlUpd.toBytes (by simp)
      · have hBeqF : (head == hdFm.prev) = false := beq_false_of_ne hSameHT
        simp only [hBeqF, Bool.false_eq_true, ↓reduceIte]
        refine (readBytesFromMap_eq_of_inRegion (by decide) fun a haHd => ?_).trans (hHdPtr ▸ hFmBytes hdFm hhdMem)
        refine writeBytesToMap_out st.byteVal hdFm.prev tlUpd.toBytes fun haTl => ?_
        have hhdAll : head ∈ allMetaSlots st := (hUfIff head).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (hHdPtr ▸ List.mem_map_of_mem hhdMem))))
        have htlAll : hdFm.prev ∈ allMetaSlots st := (hUfIff hdFm.prev).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (hPrv0 ▸ List.mem_map_of_mem htlMem))))
        exact metaSlot_disjoint_of_ne hwf htlAll hhdAll (Ne.symm hSameHT) (by simpa using haTl) haHd
    have hOnlyFmOrM : ∀ a, bv1 a ≠ st.byteVal a →
        InRegion m 40 a ∨ (∃ fm ∈ st.freeMetas, InRegion fm.ptr 40 a) := by
      intro a hNe
      by_cases haM : InRegion m 40 a
      · exact Or.inl haM
      · rw [show bv1 a = bvHd a from writeBytesToMap_out bvHd m fmNew.toBytes (by simpa using haM)] at hNe
        by_cases haHd : InRegion head 40 a
        · exact Or.inr ⟨hdFm, hhdMem, hHdPtr ▸ haHd⟩
        · rw [show bvHd a = bvTl a from writeBytesToMap_out bvTl head hdUpd.toBytes (by simpa using haHd)] at hNe
          by_cases haTl : InRegion hdFm.prev 40 a
          · exact Or.inr ⟨tlFm, htlMem, hPrv0 ▸ haTl⟩
          · rw [show bvTl a = st.byteVal a from writeBytesToMap_out st.byteVal hdFm.prev tlUpd.toBytes (by simpa using haTl)] at hNe
            exact False.elim (hNe rfl)
    have hDisjOtherFm : ∀ fm ∈ st.freeMetas, ∀ u ∈ st.freeMetas, fm.ptr ≠ u.ptr →
        ∀ a, InRegion fm.ptr 40 a → ¬ InRegion u.ptr 40 a := by
      intro fm hfm u hu hNeP a haF haU
      have hfAll := (hUfIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem hfm))))
      have huAll := (hUfIff u.ptr).mp (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map_of_mem hu))))
      exact metaSlot_disjoint_of_ne hwf hfAll huAll hNeP haF haU
    have hUnchangedOut :
        (∀ ma ∈ st.metaAreas, ∀ a, InRegion ma.base 24 a → bv1 a = st.byteVal a) ∧
        (∀ ap ∈ st.availMetaPages, ∀ a, InRegion ap 4096 a → bv1 a = st.byteVal a) ∧
        (∀ gp ∈ st.guardPages, ∀ a, InRegion gp 4096 a → bv1 a = st.byteVal a) ∧
        (∀ bm ∈ st.bumpMetas, ∀ a, InRegion bm 40 a → bv1 a = st.byteVal a) ∧
        (∀ g ∈ st.groups, ∀ a,
          (InRegion g.metaPtr 40 a ∨ (0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) →
            bv1 a = st.byteVal a) := by
      have hFmAllOf : ∀ fm ∈ st.freeMetas, fm.ptr ∈ allMetaSlots st := fun fm hfm =>
        (hUfIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map_of_mem hfm))))
      refine ⟨fun ma hma a ha => Classical.byContradiction fun hNe => ?_,
        fun ap hap a ha => Classical.byContradiction fun hNe => ?_,
        fun gp hgp a ha => Classical.byContradiction fun hNe => ?_,
        fun bm hbm a ha => Classical.byContradiction fun hNe => ?_,
        fun g hg a hGA => Classical.byContradiction fun hNe => ?_⟩
      · rcases hOnlyFmOrM a hNe with haM | ⟨fm, hfm, haFm⟩
        · exact hDisjMa ma hma a ha haM
        · exact (allMetaSlot_disjoint_other hwf (hFmAllOf fm hfm)).2.2.2.1 ma hma a ha haFm
      · rcases hOnlyFmOrM a hNe with haM | ⟨fm, hfm, haFm⟩
        · exact hDisjAp ap hap a ha haM
        · exact (allMetaSlot_disjoint_other hwf (hFmAllOf fm hfm)).2.2.2.2.1 ap hap a ha haFm
      · rcases hOnlyFmOrM a hNe with haM | ⟨fm, hfm, haFm⟩
        · exact hDisjGp gp hgp a ha haM
        · exact (allMetaSlot_disjoint_other hwf (hFmAllOf fm hfm)).2.2.2.2.2.1 gp hgp a ha haFm
      · rcases hOnlyFmOrM a hNe with haM | ⟨fm, hfm, haFm⟩
        · exact hDisjBm bm hbm a ha haM
        · have ⟨_, _, hDisjBmFm⟩ := List.nodup_append.mp (List.nodup_append.mp hUfNd).1
          have hbAll := (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
          exact metaSlot_disjoint_of_ne hwf (hFmAllOf fm hfm) hbAll
            (fun hEq => hDisjBmFm fm.ptr (List.mem_append_right _ (List.mem_map_of_mem hfm)) bm hbm hEq) haFm ha
      · rcases hOnlyFmOrM a hNe with haM | ⟨fm, hfm, haFm⟩
        · exact hDisjGrp g hg a hGA haM
        · rcases hGA with haMeta | ⟨hMp, haMem⟩
          · have ⟨_, _, hDisjGF⟩ := List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hUfNd).1).1
            have hgAll := (hUfIff g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_map_of_mem hg))))
            exact metaSlot_disjoint_of_ne hwf hgAll (hFmAllOf fm hfm)
              (fun hEq => hDisjGF g.metaPtr (List.mem_map_of_mem hg) fm.ptr (List.mem_map_of_mem hfm) hEq)
              haMeta haFm
          · exact (allMetaSlot_disjoint_other hwf (hFmAllOf fm hfm)).2.2.2.2.2.2 g hg hMp a haMem haFm
    have hOwnIff : ∀ a : BitVec 64, OwnedRwByte st1 a ↔ (OwnedRwByte st a ∨ InRegion m 40 a) := by
      intro a; unfold OwnedRwByte
      have hCuEq : CarvedUserByte st1 a ↔ CarvedUserByte st a := Iff.rfl
      have hCm1 : CarvedMetaByte st1 a ↔ (CarvedMetaByte st a ∧ ¬ InRegion m 40 a) := hCarvedEr a
      change (((∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
          (∃ g ∈ st.groups, 0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) ∧
          ¬ CarvedUserByte st1 a ∧ ¬ CarvedMetaByte st1 a) ↔ _
      rw [hCuEq, hCm1]
      constructor
      · rintro ⟨hSrc, hNCu, hNCm⟩
        by_cases haM : InRegion m 40 a
        · exact Or.inr haM
        · exact Or.inl ⟨hSrc, hNCu, fun hCm => hNCm ⟨hCm, haM⟩⟩
      · rintro (⟨hSrc, hNCu, hNCm⟩ | haM)
        · exact ⟨hSrc, hNCu, fun ⟨hCm, _⟩ => hNCm hCm⟩
        · exact ⟨Or.inl ⟨maM, hmaM, hSubMa a haM⟩, (hNotRwCu a haM).2, fun ⟨_, hNM⟩ => hNM haM⟩
    have hByteAbs : ((m ↦ₛ fmNew.toBytes) ∗ ByteMap st.masterDom (OwnedRwByte st) bvHd) =
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
      have hExtRw : ByteMap st.masterDom (OwnedRwByte st) bvHd =
          ByteMap dom1 (OwnedRwByte st) bvHd :=
        (hSetSepExt _ fun a hRw => hwf.masterDom_wf.2.1 a (Or.inl hRw)).symm
      rw [hExtRw, ByteMap_absorb_slice hDomNd1 bvHd m fmNew.toBytes
        (by simp) (fun a ha => hMInDom1 a (by simpa using ha))
        (fun a ha => (hNotRwCu a (by simpa using ha)).1)]
      exact SetSep_congr (fun a _ => by simp only [FreeMetaDesc.toBytes_length]; exact (hOwnIff a).symm)
        (fun _ _ _ => rfl)
    have hProtEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
      have hExtPn : ProtNoneByteMap dom1 (OwnedProtNoneByte st) bv1 =
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) bv1 :=
        hSetSepExt _ fun a hPn => hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn))
      change ProtNoneByteMap dom1 (OwnedProtNoneByte st) bv1 = _
      rw [hExtPn]
      exact SetSep_congr (fun _ _ => Iff.rfl) fun a _ hPn => by
        rcases hPn with ⟨gp, hgp, ha⟩ | ⟨ap, hap, ha⟩
        · exact congrArg (a ↦₈ₙ ·) (hUnchangedOut.2.2.1 gp hgp a ha)
        · exact congrArg (a ↦₈ₙ ·) (hUnchangedOut.2.1 ap hap a ha)
    have hMapSetEq : MappedSet st1.masterDom (OwnedMappedByte st1) =
        MappedSet st.masterDom (OwnedMappedByte st) :=
      hSetSepExt _ fun a hMp => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp))
    have hGrpAct := groups_active_wf_congr hwf (st' := st1) rfl rfl rfl hUnchangedOut.2.2.2.2
    have hFmPtrMapEq : (st1.freeMetas.map (·.ptr)) = st.freeMetas.map (·.ptr) ++ [m] := by
      simp [st1, updateFreeMetasSnoc, fmNew, List.map_append, List.map_map, Function.comp_def]
    have ⟨hUfNd1, hUfMem1⟩ := nodup_move_erase_to_mid
      (a := st.groups.map (·.metaPtr)) (b := st.freeMetas.map (·.ptr))
      (c := st.bumpMetas) (d := st.reservedMetas) hUfNd hmRes
    have hNodesSnocEq :
        (st1.freeMetas.map fun fm => (fm.ptr, fm.prev, fm.next)) =
          (ns.map fun nd =>
            (nd.1,
             if nd.1 == hdFm.ptr then m else nd.2.1,
             if nd.1 == hdFm.prev then m else nd.2.2)) ++
          [(m, hdFm.prev, hdFm.ptr)] := by
      simp [st1, updateFreeMetasSnoc, fmNew, ns, fNode, hFms, hHdPtr, List.map_append, List.map_map,
        Function.comp_def]
    have hDll1 : CircularDllWf head (st1.freeMetas.map fun fm => (fm.ptr, fm.prev, fm.next)) := by
      rw [hNodesSnocEq, hHdPtr]
      exact hSnocDll
    have hFmBytes1 : ∀ fm' ∈ st1.freeMetas, readBytesFromMap bv1 fm'.ptr 40 = fm'.toBytes := by
      intro fm' hfm'
      rcases List.mem_append.mp hfm' with hUpd | hLastM
      · obtain ⟨fm0, hfm0, rfl⟩ := List.mem_map.mp hUpd
        have hOutM : ∀ a, InRegion fm0.ptr 40 a → bv1 a = bvHd a := fun a ha =>
          writeBytesToMap_out bvHd m fmNew.toBytes (by simpa using hDisjFmM fm0 hfm0 a ha)
        have hStepM : readBytesFromMap bv1 fm0.ptr 40 = readBytesFromMap bvHd fm0.ptr 40 :=
          readBytesFromMap_eq_of_inRegion (by decide) hOutM
        rw [hStepM]
        by_cases hIsHd : fm0.ptr = head
        · have hEqHd : fm0 = hdFm := hFmEqOfPtr fm0 hfm0 hdFm hhdMem (hIsHd.trans hHdPtr)
          subst hEqHd
          simp only [← hHdPtr, beq_self_eq_true, ↓reduceIte]
          exact readBytesFromMap_writeBytesToMap bvTl head hdUpd.toBytes (by simp)
        · have hBeqHd : (fm0.ptr == head) = false := beq_false_of_ne hIsHd
          have hStepHd : readBytesFromMap bvHd fm0.ptr 40 = readBytesFromMap bvTl fm0.ptr 40 :=
            readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
              writeBytesToMap_out bvTl head hdUpd.toBytes
                (by simpa [← hHdPtr] using hDisjOtherFm fm0 hfm0 hdFm hhdMem (hHdPtr ▸ hIsHd) a ha)
          rw [hStepHd]
          by_cases hIsTl : fm0.ptr = hdFm.prev
          · have hEqTl : fm0 = tlFm := hFmEqOfPtr fm0 hfm0 tlFm htlMem (hIsTl.trans hPrv0)
            have hBeqTlT : (fm0.ptr == hdFm.prev) = true := beq_iff_eq.mpr hIsTl
            simp only [hBeqHd, hBeqTlT, Bool.false_eq_true, ↓reduceIte]
            rw [hEqTl]
            conv => lhs; rw [← hPrv0]
            simpa only [FreeMetaDesc.toBytes_length] using
              readBytesFromMap_writeBytesToMap st.byteVal hdFm.prev tlUpd.toBytes (by simp)
          · have hBeqTl : (fm0.ptr == hdFm.prev) = false := beq_false_of_ne hIsTl
            simp only [hBeqHd, hBeqTl, Bool.false_eq_true, ↓reduceIte]
            refine (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => ?_).trans (hFmBytes fm0 hfm0)
            exact writeBytesToMap_out st.byteVal hdFm.prev tlUpd.toBytes
              (by simpa [← hPrv0] using hDisjOtherFm fm0 hfm0 tlFm htlMem (hPrv0 ▸ hIsTl) a ha)
      · simp only [List.mem_singleton] at hLastM; subst hLastM
        exact readBytesFromMap_writeBytesToMap bvHd m fmNew.toBytes (by simp)
    have hWf1 : MallocngWFInflight k base brkStart brk liveCost peakCost st1 :=
      { base_wf := trivial
        brk_bounds := hwf.brk_bounds
        ctx_lens := hwf.ctx_lens
        initDone_wf := hwf.initDone_wf
        initZero_wf := fun h0 => by simp [st1, hInit1] at h0
        bounces_wf := hwf.bounces_wf
        usage_wf := hwf.usage_wf
        brk_mode_wf := hwf.brk_mode_wf
        metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
          obtain ⟨h1, h2, h3, hHdr⟩ := hwf.metaAreas_wf.2.1 ma hma
          exact ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) (hUnchangedOut.1 ma hma)).trans hHdr⟩,
          hwf.metaAreas_wf.2.2⟩
        guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
          fun ap hap => by
            obtain ⟨h1, h2, h3, hZ⟩ := hwf.guard_avail_wf.2.2.2 ap hap
            exact ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) (hUnchangedOut.2.1 ap hap)).trans hZ⟩⟩
        inflight_wf := by
          have hInf := hwf.inflight_wf
          change (st.reservedMetas.erase m).length + totalClaimedSlots st ≤ k
          omega
        free_bump_metas_wf := ⟨hDll1, hFmBytes1, hBumpOr,
          fun bm hbm =>
            (readBytesFromMap_eq_of_inRegion (by decide) (hUnchangedOut.2.2.2.1 bm hbm)).trans
              (hwf.free_bump_metas_wf.2.2.2.1 bm hbm),
          by rw [show st1.groups = st.groups from rfl, hFmPtrMapEq]; exact hUfNd1,
          fun x => by
            rw [show st1.groups = st.groups from rfl, hFmPtrMapEq]
            change x ∈ st.groups.map (·.metaPtr) ++ (st.freeMetas.map (·.ptr) ++ [m]) ++
                st.bumpMetas ++ st.reservedMetas.erase m ↔ x ∈ allMetaSlots st
            exact (hUfMem1 x).trans (hUfIff x)⟩
        groups_nodup := hwf.groups_nodup
        groups_wf := hGrpAct.1
        regions_disjoint := hwf.regions_disjoint
        active_wf := hGrpAct.2.1
        liveMap_wf := hwf.liveMap_wf
        live_le_peak := hwf.live_le_peak
        effCost_le_live := hwf.effCost_le_live
        meta_pages_bound := hwf.meta_pages_bound
        empty_groups_bound := hwf.empty_groups_bound
        masterDom_wf := ⟨hDomNd1,
          fun a hOwn => by
            rcases hOwn with hRw1 | hPn1 | hMp1
            · rcases (hOwnIff a).mp hRw1 with hRw0 | haM
              · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inl hRw0))
              · exact hMInDom1 a haM
            · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn1)))
            · exact List.mem_append_left _ (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp1))),
          fun a ha => by
            rcases hDom1Split a ha with hIn0 | haM
            · exact hwf.masterDom_wf.2.2 a hIn0
            · exact ⟨(maM.base, 4096),
                List.mem_append_left _ (List.mem_append_left _
                  (List.mem_append_left _ (List.mem_map_of_mem hmaM))),
                hSubMa a haM⟩⟩ }
    exact ⟨hdFm, hhdMem, tlFm, htlMem, hHdPtr.symm, hPrv0.symm,
      by rw [show st.ctx.freeMetaHead = hdFm.ptr from hHdPtr]; exact hFmOwn hdFm hhdMem,
      by rw [hPrv0]; exact hFmOwn tlFm htlMem,
      by rw [show st.ctx.freeMetaHead = hdFm.ptr from hHdPtr]; exact hFmBytes hdFm hhdMem,
      by rw [hPrv0]; exact hFmBytes tlFm htlMem,
      hReadHdAfterTl, hByteAbs, hProtEq, hMapSetEq, hWf1, rfl, rfl, rfl⟩

end VerifiedLibraries.Mallocng.Proofs
