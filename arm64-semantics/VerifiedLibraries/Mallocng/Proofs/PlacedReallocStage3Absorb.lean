/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3Wf

/-!
# Stage 3 (`sc = 63` `mremap`) Heap Re-Absorption

Combines `reallocMremap_wf`, `reallocMremap_noOrphan`, and `SetSizeSlicePost` into the view-shift
entailment `reallocMremap_absorb` closing Stage 3 of `__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

set_option maxHeartbeats 400000 in
theorem reallocMremap_absorb (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sf : State) (st : MallocngSt)
    (hCount : MallocngCountIvsWF b ivs0 st)
    (hwf : MallocngWF A.base brkStart sf.brk b.liveCost b.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase newP : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32) (bsFinal : List (BitVec 8))
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hNewPNat : newP.toNat = newBase.toNat + 16 + (p.toNat - (g.slotStart 0).toNat))
    (hTp : sf.tpidrEl0 = tp) (hBrkStart : sf.brkStart = brkStart)
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sf.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        sf.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (hDisjMa : ∀ ma ∈ st.metaAreas, DisjointRegions ma.base 4096 newBase needed)
    (hDisjGp : ∀ gp ∈ st.guardPages, DisjointRegions gp 4096 newBase needed)
    (hDisjAp : ∀ ap ∈ st.availMetaPages, DisjointRegions ap 4096 newBase needed)
    (hDisjRg : ∀ rg ∈ st.groups, 0 < rg.maplen → rg.metaPtr ≠ g.metaPtr →
      DisjointRegions rg.mem (rg.maplen * 4096) newBase needed)
    (hSetSize :
      SetSizeSlicePost
        (ByteSlice.write8
          ((mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).take needed ++
            List.replicate (needed - g.maplen * 4096) 0#8)
          (needed - 4) 0#8)
        (13 + (p.toNat - (g.slotStart 0).toNat))
        (needed - 4)
        newSz
        (BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
        bsFinal) :
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz b
    let keptBs := origBs.take newSz
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ st.ctx.toBytes) ∗
    (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
    (newBase ↦ₛ bsFinal) ∗
    memMapped newBase needed ∗
    ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
    ReallocMremapFrame A tp st g ∗
    MallocngLiveAuth γ st.liveMap ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
    MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MallocngTightBlock γ p oldSz al ⊢
      |==> (MallocngPostEnv mallocngIface γ A tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf newP (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp newP (newSz, keptBs)) := by
  intro bf keptBs
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  obtain ⟨_, _, _, hMpG, _, _, _, _, _, _, hOldMemFit, _, hSt0Nat, _, hLoP,
      _, _, hOldSlotFit, hNewSlotFit0, _, _, hNeedLo0, hNeedDvd0, _, _, hNewEffBound0⟩ :=
    sc63_liveUser_bounds hCount hwf hg hIdx0 hSlot0 hSc63 hNewLo hNewHi
  have hNewSlotFit : 16 + (p.toNat - (g.slotStart 0).toNat) + newSz + 4 ≤ needed := by
    rw [hNeedEq]; exact hNewSlotFit0
  have hNeedLo : 4096 ≤ needed := by rw [hNeedEq]; exact hNeedLo0
  have hNeedDvd : 4096 ∣ needed := by rw [hNeedEq]; exact hNeedDvd0
  have hNewEffBound : needed ≤
      ((oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost) + 8195 := by
    rw [hNeedEq]; exact hNewEffBound0
  have hNeedResHi : (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) < 2 ^ 31 := by
    rw [hNeedEq]; omega
  obtain ⟨hDisjMetaOldG, hMetaOwn, _⟩ := sc63_metaPtr_and_mem_owned hwf hg hIdx0 hSlot0 hSc63
  let userBs := origBs ++ tailBs
  have hUserLen : userBs.length = oldSz := by simp [userBs, hTailLen]; omega
  let oldMapBs := mkSc63OldMapBs st.byteVal g p oldSz userBs
  have hOldMapLen : oldMapBs.length = g.maplen * 4096 :=
    mkSc63OldMapBs_length st.byteVal g p oldSz userBs hUserLen (by omega) (by omega)
  let bsRemap := oldMapBs.take needed ++ List.replicate (needed - g.maplen * 4096) 0#8
  have hRemapLen : bsRemap.length = needed := by
    simp only [bsRemap, List.length_append, List.length_take, List.length_replicate, hOldMapLen]
    omega
  let bsZero := ByteSlice.write8 bsRemap (needed - 4) 0#8
  change SetSizeSlicePost bsZero (13 + (p.toNat - (g.slotStart 0).toNat)) (needed - 4) newSz
    (BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
    bsFinal at hSetSize
  have hZeroLen : bsZero.length = needed :=
    (ByteSlice.write8_length bsRemap (needed - 4) 0#8 (by omega)).trans hRemapLen
  have hFinalLen : bsFinal.length = needed := hSetSize.1.trans hZeroLen
  have hFinalEndZero : bsFinal.getD (needed - 4) 0#8 = 0#8 := by
    rw [hSetSize.2.2.2.2.2 (needed - 4) (Nat.le_refl _)]
    dsimp only [bsZero]
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [↓reduceIte]
  have hEq16 : 13 + (p.toNat - (g.slotStart 0).toNat) + 3 + newSz =
      16 + (p.toNat - (g.slotStart 0).toNat) + newSz := by omega
  have hKeepRemap : ∀ i, i < 16 + (p.toNat - (g.slotStart 0).toNat) + min origBs.length newSz →
      i ≠ 13 + (p.toNat - (g.slotStart 0).toNat) →
      bsFinal.getD i 0#8 = oldMapBs.getD i 0#8 := by
    intro i hiLt hiNe
    rw [hSetSize.2.1 i (by omega) hiNe]
    dsimp only [bsZero]
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by omega)]
    simp only [show i ≠ needed - 4 by omega, ↓reduceIte]
    dsimp only [bsRemap]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [List.length_take, hOldMapLen]; omega),
      List.getElem?_eq_getElem (by rw [List.length_take, hOldMapLen]; omega),
      Option.getD_some, List.getElem_take]
    symm
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hOldMapLen]; omega),
      Option.getD_some]
  have hPreLenEq : p.toNat - g.mem.toNat = 16 + (p.toNat - (g.slotStart 0).toNat) := by omega
  have hFinalPre : ∀ i, i < 16 + (p.toNat - (g.slotStart 0).toNat) →
      i ≠ 13 + (p.toNat - (g.slotStart 0).toNat) →
      bsFinal.getD i 0#8 = st.byteVal (g.mem + BitVec.ofNat 64 i) := by
    intro i hiLt hiNe
    rw [hKeepRemap i (by omega) hiNe]
    dsimp only [oldMapBs, mkSc63OldMapBs]
    rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left (by rw [readBytesFromMap_length]; omega),
      List.getElem?_eq_getElem (by rw [readBytesFromMap_length]; omega),
      Option.getD_some, readBytesFromMap_getElem]
  have hFinalUser : ∀ k (hk : k < min origBs.length newSz),
      bsFinal.getD (16 + (p.toNat - (g.slotStart 0).toNat) + k) 0#8 = origBs[k]'(by omega) := by
    intro k hk
    rw [hKeepRemap (16 + (p.toNat - (g.slotStart 0).toNat) + k) (by omega) (by omega)]
    have hIdxSub : 16 + (p.toNat - (g.slotStart 0).toNat) + k -
        (readBytesFromMap st.byteVal g.mem (p.toNat - g.mem.toNat)).length = k := by
      rw [readBytesFromMap_length]; omega
    dsimp only [oldMapBs, mkSc63OldMapBs, userBs]
    rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_right (by rw [readBytesFromMap_length]; omega),
      hIdxSub, List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hFinalHdr := hSetSize.2.2.1
  have hFinalRes1 : 1 ≤ (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) →
      bsFinal.getD (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) 0#8 = 0#8 := by
    have h := hSetSize.2.2.2.1; rwa [hEq16] at h
  have hFinalRes5 : 5 ≤ (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) →
      bsFinal.getD ((needed - 4) - 5) 0#8 = 0#8 ∧
      ∀ j < 4, bsFinal.getD ((needed - 4) - 4 + j) 0#8 =
        (BitVec.ofNat 32 ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz))).extractLsb' (8 * j) 8 := by
    have h := hSetSize.2.2.2.2.1; rwa [hEq16] at h
  obtain ⟨hNewBWf, hFreshNewP, hCount', hwf', hRwOut, hRwNew, hUserReadK⟩ :=
    reallocMremap_wf hwf hCount hg hIdx0 origBs hOrigLe hSlot0 hSc63 bsFinal
      hNewHi hNewBaseGe hNewBaseAl hNeedLo hNeedDvd hNewBaseFit hNewPNat
      hNewSlotFit hNeedResHi hNewEffBound hDisjMa hDisjGp hDisjAp hDisjRg
      hFinalLen hFinalEndZero hFinalPre hFinalUser hFinalHdr hFinalRes1 hFinalRes5
  let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
  let g' := mkReallocMremapGroup g newBase newP needed newSz newEff
  let st' := mkReallocMremapSt st g p newBase newP needed newSz newEff bsFinal
  have hMetaBytesEq :
      ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes = g'.metaBytes := rfl
  have hMetaLen : g'.metaBytes.length = 40 := GroupDesc.metaBytes_length g'
  have hMapMul : (needed / 4096) * 4096 = needed := Nat.div_mul_cancel hNeedDvd
  have hMpG' : 0 < g'.maplen := by
    show 0 < needed / 4096
    rcases hNeedDvd with ⟨k, rfl⟩; rw [Nat.mul_div_cancel_left k (by decide)]; omega
  obtain ⟨hg'In, hGsCases, hGsKeep, _, _, _⟩ :=
    replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl
  have hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem :=
    reallocMremap_noOrphan hCount.2.2.1 hwf.groups_nodup.1 hg hMpG hMpG' rfl rfl hMapMul rfl
      hOldRw hPermRel
  let domRest := st.masterDom.filter (fun a => !decide (InRegion g.mem (g.maplen * 4096) a))
  have hDisjDom : ∀ a, a ∈ domRest → a ∈ rangeAddrs newBase needed → False :=
    fun a ha1 ha2 => (List.nodup_append.mp hwf'.masterDom_wf.1).2.2 a ha1 a ha2 rfl
  have hInDomRest : ∀ a, a ∈ st.masterDom → ¬ InRegion g.mem (g.maplen * 4096) a → a ∈ domRest :=
    fun a hD hN => List.mem_filter.mpr ⟨hD, by simp [hN]⟩
  have hInNewDom : ∀ a, InRegion newBase needed a → a ∈ st'.masterDom := fun a ha =>
    List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion newBase (by omega) a).mpr ha)
  have hMetaInDomRest : ∀ a, InRegion g.metaPtr 40 a → a ∈ domRest := fun a ha =>
    hInDomRest a (hMetaOwn a ha).2
      (fun hOG => not_both_inRegion_of_disjointRegions hDisjMetaOldG ha hOG)
  have hMetaInSt'Dom : ∀ a, InRegion g.metaPtr 40 a → a ∈ st'.masterDom :=
    fun a ha => List.mem_append_left _ (hMetaInDomRest a ha)
  let keepRw0 := fun a =>
    OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion g.mem (g.maplen * 4096) a
  have hRwShift : ByteMap st.masterDom keepRw0 st.byteVal =
      ByteMap st'.masterDom keepRw0 st.byteVal := by
    unfold ByteMap
    rw [← SetSep_filter_of_imp (p := fun a => !decide (InRegion g.mem (g.maplen * 4096) a))
          _ (fun a _ hk => by simp [hk.2.2])]
    exact (SetSep_append_right_empty (dom₁ := domRest) (dom₂ := rangeAddrs newBase needed) _
      (fun a haR hk => hDisjDom a (hInDomRest a (hwf.masterDom_wf.2.1 a (Or.inl hk.1)) hk.2.2) haR)).symm
  let val1 := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
  have hAbsMeta : ((g.metaPtr ↦ₛ g'.metaBytes) ∗ ByteMap st'.masterDom keepRw0 st.byteVal) =
      ByteMap st'.masterDom (fun a => keepRw0 a ∨ InRegion g.metaPtr g'.metaBytes.length a) val1 :=
    ByteMap_absorb_slice hwf'.masterDom_wf.1 st.byteVal g.metaPtr g'.metaBytes
      (by rw [hMetaLen]; decide)
      (fun a ha => hMetaInSt'Dom a (by rwa [hMetaLen] at ha))
      (fun a ha hk => hk.2.1 (by rwa [hMetaLen] at ha))
  have hAbsNew : ((newBase ↦ₛ bsFinal) ∗
      ByteMap st'.masterDom (fun a => keepRw0 a ∨ InRegion g.metaPtr g'.metaBytes.length a) val1) =
      ByteMap st'.masterDom
        (fun a => (keepRw0 a ∨ InRegion g.metaPtr g'.metaBytes.length a) ∨ InRegion newBase bsFinal.length a)
        st'.byteVal :=
    ByteMap_absorb_slice hwf'.masterDom_wf.1 val1 newBase bsFinal (by rw [hFinalLen]; omega)
      (fun a ha => hInNewDom a (by rwa [hFinalLen] at ha))
      (fun a ha hOr => by
        have haR : a ∈ rangeAddrs newBase needed :=
          (mem_rangeAddrs_iff_inRegion newBase (by omega) a).mpr (by rwa [hFinalLen] at ha)
        rcases hOr with hk | hM
        · exact hDisjDom a (hInDomRest a (hwf.masterDom_wf.2.1 a (Or.inl hk.1)) hk.2.2) haR
        · exact hDisjDom a (hMetaInDomRest a (by rwa [hMetaLen] at hM)) haR)
  have hSubNewP : ∀ a, InRegion newP newSz a → InRegion newBase needed a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hExtUser := ByteMap_extract_slice hwf'.masterDom_wf.1
    (keep := fun a => (keepRw0 a ∨ InRegion g.metaPtr g'.metaBytes.length a) ∨ InRegion newBase bsFinal.length a)
    st'.byteVal newP (n := newSz) (by omega)
    (fun a ha => hInNewDom a (hSubNewP a ha))
    (fun a ha => Or.inr (by rw [hFinalLen]; exact hSubNewP a ha))
  have hMetaRwSt' : ∀ a, InRegion g.metaPtr 40 a → OwnedRwByte st' a := fun a haM => by
    have hRwOld := (hMetaOwn a haM).1
    have hNotNB : ¬ InRegion newBase needed a := fun haNB =>
      hDisjDom a (hMetaInDomRest a haM)
        ((mem_rangeAddrs_iff_inRegion newBase (by omega) a).mpr haNB)
    have hSrc' : (∃ ma ∈ st'.metaAreas, InRegion ma.base 4096 a) ∨
        (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) := by
      rcases hRwOld.1 with ⟨ma, hma, haMa⟩ | ⟨x, hx, hMpX, haX⟩
      · exact Or.inl ⟨ma, hma, haMa⟩
      · by_cases hE : x.metaPtr = g.metaPtr
        · have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst r
          exact False.elim (not_both_inRegion_of_disjointRegions hDisjMetaOldG haM haX)
        · exact Or.inr ⟨x, hGsKeep x hx hE, hMpX, haX⟩
    have hNoCarvU' : ¬ CarvedUserByte st' a := by
      rintro ⟨x, hx, s, hs, hSub⟩
      rcases hGsCases x hx with rfl | ⟨_, hxO⟩
      · simp only [g', mkReallocMremapGroup, List.mem_singleton] at hs
        subst hs; exact hNotNB (hSubNewP a hSub)
      · exact hRwOld.2.1 ⟨x, hxO, s, hs, hSub⟩
    exact ⟨hSrc', hNoCarvU', hRwOld.2.2⟩
  have hByteEq : ByteMap st'.masterDom
      (fun a => ((keepRw0 a ∨ InRegion g.metaPtr g'.metaBytes.length a) ∨ InRegion newBase bsFinal.length a) ∧
        ¬ InRegion newP newSz a) st'.byteVal =
      ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal := by
    unfold ByteMap
    refine SetSep_congr (fun a haDom => ?_) (fun _ _ _ => rfl)
    rw [hMetaLen, hFinalLen]
    by_cases haNB : InRegion newBase needed a
    · exact ⟨fun h => (hRwNew a haNB).mpr h.2, fun h => ⟨Or.inr haNB, (hRwNew a haNB).mp h⟩⟩
    · have haNUser : ¬ InRegion newP newSz a := fun hU => haNB (hSubNewP a hU)
      have haDR : a ∈ domRest := by
        rcases List.mem_append.mp haDom with hL | hR
        · exact hL
        · exact False.elim (haNB ((mem_rangeAddrs_iff_inRegion newBase (by omega) a).mp hR))
      have haNOG : ¬ InRegion g.mem (g.maplen * 4096) a := by
        have hF := (List.mem_filter.mp haDR).2; simpa using hF
      by_cases haM : InRegion g.metaPtr 40 a
      · exact ⟨fun _ => hMetaRwSt' a haM, fun _ => ⟨Or.inl (Or.inr haM), haNUser⟩⟩
      · have hEq := (hRwOut a haM haNOG haNB).1
        refine ⟨fun h => ?_, fun h => ⟨Or.inl (Or.inl ⟨hEq.mp h, haM, haNOG⟩), haNUser⟩⟩
        rcases h.1 with (hk | hM) | hNB
        · exact hEq.mpr hk.1
        · exact False.elim (haM hM)
        · exact False.elim (haNB hNB)
  let keepMp0 := fun a => OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a
  have hMpShift : MappedSet st.masterDom keepMp0 = MappedSet st'.masterDom keepMp0 := by
    unfold MappedSet
    rw [← SetSep_filter_of_imp (p := fun a => !decide (InRegion g.mem (g.maplen * 4096) a))
          _ (fun a _ hk => by simp [hk.2])]
    exact (SetSep_append_right_empty (dom₁ := domRest) (dom₂ := rangeAddrs newBase needed) _
      (fun a haR hk => hDisjDom a (hInDomRest a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hk.1))) hk.2) haR)).symm
  have hAbsMp : (memMapped newBase needed ∗ MappedSet st'.masterDom keepMp0) =
      MappedSet st'.masterDom (fun a => keepMp0 a ∨ InRegion newBase needed a) :=
    MappedSet_absorb_slice hwf'.masterDom_wf.1 newBase (by omega) hInNewDom
      (fun a ha hk => hDisjDom a
        (hInDomRest a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hk.1))) hk.2)
        ((mem_rangeAddrs_iff_inRegion newBase (by omega) a).mpr ha))
  have hMpEq : MappedSet st'.masterDom (fun a => keepMp0 a ∨ InRegion newBase needed a) =
      MappedSet st'.masterDom (OwnedMappedByte st') := by
    unfold MappedSet
    refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    constructor
    · rintro (⟨hMp, hNOG⟩ | haNB)
      · rcases hMp with h1 | h2 | h3 | ⟨x, hx, hMpX, haX⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · have hNe : x.metaPtr ≠ g.metaPtr := fun hE => by
            have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst r; exact hNOG haX
          exact Or.inr (Or.inr (Or.inr ⟨x, hGsKeep x hx hNe, hMpX, haX⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨g', hg'In, hMpG', by simpa [g', mkReallocMremapGroup, hMapMul] using haNB⟩))
    · intro hMp'
      by_cases haNB : InRegion newBase needed a
      · exact Or.inr haNB
      · refine Or.inl ?_
        obtain ⟨hP123, hPRg, hCrossG⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
        have hGMemRg : (g.mem, g.maplen * 4096) ∈
            (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
          List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
        rcases hMp' with ⟨mb, hmb, haMb⟩ | ⟨mg, hmg, haMg⟩ | ⟨ap, hap, haAp⟩ | ⟨x, hx, hMpX, haX⟩
        · have hmb0 : mb ∈ st.mmapMetaAreas := hmb
          rw [hwf.brk_mode_wf.2.1] at hmb0
          obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hmb0).1
          exact ⟨Or.inl ⟨ma.base, hmb, haMb⟩, fun hOG =>
            not_both_inRegion_of_disjointRegions
              (hCrossG _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))) _ hGMemRg)
              haMb hOG⟩
        · have hmg0 : mg ∈ st.mmapGuardPages := hmg
          rw [hwf.brk_mode_wf.2.2.1] at hmg0
          exact ⟨Or.inr (Or.inl ⟨mg, hmg, haMg⟩), fun hOG =>
            not_both_inRegion_of_disjointRegions
              (hCrossG _ (List.mem_append_left _ (List.mem_append_right _
                (List.mem_map_of_mem (List.mem_filter.mp hmg0).1))) _ hGMemRg)
              haMg hOG⟩
        · exact ⟨Or.inr (Or.inr (Or.inl ⟨ap, hap, haAp⟩)), fun hOG =>
            not_both_inRegion_of_disjointRegions
              (hCrossG _ (List.mem_append_right _ (List.mem_map_of_mem hap)) _ hGMemRg) haAp hOG⟩
        · rcases hGsCases x hx with rfl | ⟨hNe, hxO⟩
          · exact False.elim (haNB (by simpa [g', mkReallocMremapGroup, hMapMul] using haX))
          · exact ⟨Or.inr (Or.inr (Or.inr ⟨x, hxO, hMpX, haX⟩)), fun hOG =>
              not_both_inRegion_of_disjointRegions
                (pairwiseDisjoint_map_ne (f := fun z : GroupDesc => (z.mem, z.maplen * 4096)) hPRg
                  (List.mem_filter.mpr ⟨hxO, decide_eq_true hMpX⟩)
                  (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
                  (fun hM => hNe (mem_groups_eq_of_mem hwf.groups_nodup.2 hxO hg hM ▸ rfl)))
                haX hOG⟩
  have hPnDisj : ∀ a, OwnedProtNoneByte st a →
      ¬ InRegion g.mem (g.maplen * 4096) a ∧ ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion newBase needed a := by
    intro a hPn
    obtain ⟨hP123, _, hCrossG⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
    obtain ⟨hP12, _, hCross12Ap⟩ := pairwiseDisjoint_append hP123
    obtain ⟨_, _, hCrossMaGp⟩ := pairwiseDisjoint_append hP12
    have hGMemRg : (g.mem, g.maplen * 4096) ∈
        (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
      List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
    have hmAllG : g.metaPtr ∈ allMetaSlots st :=
      (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
    obtain ⟨maG, hmaG, _, _, _, hmNatG, hmFitG, hMaG48⟩ := metaSlot_in_metaArea hwf hmAllG
    have hSubMaG : ∀ x, InRegion g.metaPtr 40 x → InRegion maG.base 4096 x := fun x hx => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) x).mp hx
      exact (inRegion_iff_toNat (by omega) x).mpr ⟨by omega, by omega⟩
    rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
    · exact ⟨fun hOG => not_both_inRegion_of_disjointRegions
          (hCrossG _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))) _ hGMemRg) haGp hOG,
        fun hM => not_both_inRegion_of_disjointRegions
          (hCrossMaGp _ (List.mem_map_of_mem hmaG) _ (List.mem_map_of_mem hgp)) (hSubMaG a hM) haGp,
        fun hNB => not_both_inRegion_of_disjointRegions (hDisjGp gp hgp) haGp hNB⟩
    · exact ⟨fun hOG => not_both_inRegion_of_disjointRegions
          (hCrossG _ (List.mem_append_right _ (List.mem_map_of_mem hap)) _ hGMemRg) haAp hOG,
        fun hM => not_both_inRegion_of_disjointRegions
          (hCross12Ap _ (List.mem_append_left _ (List.mem_map_of_mem hmaG)) _ (List.mem_map_of_mem hap))
          (hSubMaG a hM) haAp,
        fun hNB => not_both_inRegion_of_disjointRegions (hDisjAp ap hap) haAp hNB⟩
  have hPnEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal := by
    unfold ProtNoneByteMap
    rw [← SetSep_filter_of_imp (p := fun a => !decide (InRegion g.mem (g.maplen * 4096) a))
          _ (fun a _ hk => by simp [(hPnDisj a hk).1])]
    rw [← SetSep_append_right_empty (dom₁ := domRest) (dom₂ := rangeAddrs newBase needed) _
          (fun a haR hk => hDisjDom a
            (hInDomRest a (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hk))) (hPnDisj a hk).1) haR)]
    refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hk => ?_)
    obtain ⟨h1, h2, h3⟩ := hPnDisj a hk
    congr 1; exact (hRwOut a h2 h1 h3).2.symm
  have hKeptLen : keptBs.length = min origBs.length newSz := by simp [keptBs]; omega
  have hReadUser : (readBytesFromMap st'.byteVal newP newSz).take keptBs.length = keptBs := by
    apply List.ext_getElem
    · rw [List.length_take, readBytesFromMap_length, hKeptLen]; omega
    · intro k hk1 hk2
      rw [List.length_take, readBytesFromMap_length, hKeptLen] at hk1
      rw [List.getElem_take, readBytesFromMap_getElem, hUserReadK k (by omega)]
      simp [keptBs, List.getElem_take]
  have hUserInit : (newP ↦ₛ readBytesFromMap st'.byteVal newP newSz) ⊢
      (newP ↦ₛ keptBs) ∗ memRegion (newP + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) := by
    have hSplit : readBytesFromMap st'.byteVal newP newSz =
        keptBs ++ (readBytesFromMap st'.byteVal newP newSz).drop keptBs.length :=
      (List.take_append_drop keptBs.length (readBytesFromMap st'.byteVal newP newSz)).symm.trans
        (congrArg (· ++ _) hReadUser)
    rw [hSplit, pointsToBytes_append newP keptBs _]
    refine sepConj_mono_right ?_
    have hDropLen : ((readBytesFromMap st'.byteVal newP newSz).drop keptBs.length).length =
        newSz - keptBs.length := by rw [List.length_drop, readBytesFromMap_length]
    have hEnt := (IsBlock.pointsToBytes (newP + BitVec.ofNat 64 keptBs.length)
      ((readBytesFromMap st'.byteVal newP newSz).drop keptBs.length)).entails_memRegion
    rwa [hDropLen] at hEnt
  have hPureInit : (MallocngTightInitBlock γ al).pureWf newP (newSz, keptBs) :=
    ⟨hNewBWf.1, hNewBWf.2.1, Nat.lt_of_le_of_lt hNewBWf.2.2.1 (by decide), by omega⟩
  have hRepack := mallocngHeap_read_liveUser_repack γ A tp brkStart sf.brk bf (dynamicRootRegions st') st'
  unfold MallocngReadRest at hRepack
  have hReallocFrameEq : ReallocMremapFrame A tp st g =
      (ByteMap st.masterDom keepRw0 st.byteVal ∗
       MappedSet st.masterDom keepMp0 ∗
       ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) := rfl
  have hCtxEq : st.ctx = st'.ctx := rfl
  have hAuxvEq : st.auxvPtr = st'.auxvPtr := rfl
  have hSnapEq : st.auxvSnap = st'.auxvSnap := rfl
  have hLiveEq : (st.liveMap.erase p).insert newP newSz (st.liveMap.ov p) =
      st'.liveMap := rfl
  rw [hReallocFrameEq, hMetaBytesEq, hCtxEq, hAuxvEq, hSnapEq]
  have hErrno : ((tp - 0xa4#64) ↦₃₂ errnoVal) ⊢ ∃∗ ev : BitVec 32, (tp - 0xa4#64) ↦₃₂ ev :=
    Entails.sepExists_intro errnoVal
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (ByteMap st.masterDom keepRw0 st.byteVal) = PBy
    generalize (MappedSet st.masterDom keepMp0) = PMp
    generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
    generalize (MallocngAuxvState γ st'.auxvPtr st'.auxvSnap) = PAu
    generalize (MallocngLiveAuth γ st.liveMap) = PGh
    ac_rfl : _ =
      (MallocngLiveAuth γ st.liveMap ∗ MallocngTightBlock γ p oldSz al) ∗
      ((((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
       ((newBase ↦ₛ bsFinal) ∗
        ((g.metaPtr ↦ₛ g'.metaBytes) ∗ ByteMap st.masterDom keepRw0 st.byteVal)) ∗
       (memMapped newBase needed ∗ MappedSet st.masterDom keepMp0) ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st'.ctx.toBytes) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
       MallocngAuxvState γ st'.auxvPtr st'.auxvSnap))) ?_
  refine Entails.trans (sepConj_mono_left
      (mallocngTightBlock_replaceOv_bupd γ st.liveMap p oldSz newP newSz al hNewBWf hFreshNewP))
    (Entails.trans (bupd_frame_r _ _) (bupd_mono ?_))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left hErrno))) ?_
  change _ ∗ (MallocngRuntime A tp ∗ _) ⊢ _
  rw [hLiveEq, hRwShift, hAbsMeta, hAbsNew, hExtUser, hByteEq, hMpShift, hAbsMp, hMpEq, hPnEq]
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngRuntime A tp) = PRt
    generalize (ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal) = PBy
    generalize (MappedSet st'.masterDom (OwnedMappedByte st')) = PMp
    generalize (ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) = PPn
    generalize (MallocngAuxvState γ st'.auxvPtr st'.auxvSnap) = PAu
    generalize (MallocngLiveAuth γ st'.liveMap) = PGh
    ac_rfl : _ =
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st'.ctx.toBytes) ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       (MallocngLiveAuth γ st'.liveMap ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
        MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st') ∗
        MallocngRuntime A tp)) ∗
      (MallocngTightBlock γ newP newSz al ∗ (newP ↦ₛ readBytesFromMap st'.byteVal newP newSz)))) ?_
  refine Entails.trans (sepConj_mono
    (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨hCount', hwf'⟩ (Entails.refl _))))) hRepack)
    (sepConj_mono_right hUserInit)) ?_
  unfold MallocngPostEnv MallocngEnv
  refine Entails.trans ?_ (sepConj_mono_left (Entails.sepExists_intro (dynamicRootRegions st')))
  rw [pure_sepConj_of_true hNoOrph, pure_sepConj_of_true ⟨hTp, hBrkStart⟩, pure_sepConj_of_true hPureInit]
  show (mallocngIface.MallocngHeap γ A tp brkStart sf.brk bf (dynamicRootRegions st') ∗
    (MallocngTightBlock γ newP newSz al ∗
     ((newP ↦ₛ keptBs) ∗ memRegion (newP + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)))) ⊢
    mallocngIface.MallocngHeap γ A tp brkStart sf.brk bf (dynamicRootRegions st') ∗
    (MallocngTightBlock γ newP newSz al ∗ (newP ↦ₛ keptBs) ∗
     memRegion (newP + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length))
  exact Entails.of_eq (by ac_rfl)

end VerifiedLibraries.Mallocng.Proofs
