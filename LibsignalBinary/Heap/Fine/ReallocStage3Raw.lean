/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage3
public import LibsignalBinary.Heap.Fine.ReallocStage2Raw
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Raw-State Placed `__libc_realloc` Stage 3 (`sc = 63` `mremap`)

Verifies the post-`mremap` continuation (`+0x364 → ret`) of placed `__libc_realloc` (`blk14`),
exposing the concrete post-state `(st', g', newQ, newEff, live', peak')` and group/mapping equations
needed to preserve `MallocngFineInv`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Post-`mremap` Separation-Logic Absorption -/

private theorem cap0_sub_extra {needed extra : Nat} (h1 : 20 + extra ≤ needed) (h2 : needed < 2 ^ 64) :
    (BitVec.ofNat 64 needed - 20#64) - BitVec.ofNat 64 extra = BitVec.ofNat 64 ((needed - 4) - (16 + extra)) := by
  bv_omega

private theorem sepWP_bind_state_s3 {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sFin, sFin = s → SepWP prog ret sFin P post oom) : SepWP prog ret s P post oom :=
  h s rfl

set_option maxHeartbeats 400000 in
theorem reallocMremap_absorb_raw (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (st : MallocngSt)
    (hCount : MallocngCountIvsWF b ivs0 st)
    (hwf : MallocngWF A.base brkStart brk b.liveCost b.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (origBs tailBs : List (BitVec 8))
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
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    let st' := mkReallocMremapSt st g p newBase newP needed newSz newEff bsFinal
    (newP ≠ p → st.liveMap newP = none) ∧
    (MallocngRoTablesAt A ∗
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
     MallocngBlockToken γ p oldSz ⊢
       |==> (MallocngRoTablesA A ∗
             MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' ∗
             MallocngRuntime A tp ∗
             ⌜(MallocngInitBlock mallocngIface γ).pureWf newP (newSz, keptBs)⌝ ∗
             (MallocngInitBlock mallocngIface γ).interp newP (newSz, keptBs))) := by
  intro bf keptBs newEff st'
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
    simp only [bsRemap, List.length_append, List.length_take, List.length_replicate, hOldMapLen]; omega
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
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hOldMapLen]; omega), Option.getD_some]
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
  obtain ⟨hNewBWf, hFreshNewP, _hCount', hwf', hRwOut, hRwNew, hUserReadK⟩ :=
    reallocMremap_wf hwf hCount hg hIdx0 origBs hOrigLe hSlot0 hSc63 bsFinal
      hNewHi hNewBaseGe hNewBaseAl hNeedLo hNeedDvd hNewBaseFit hNewPNat
      hNewSlotFit hNeedResHi hNewEffBound hDisjMa hDisjGp hDisjAp hDisjRg
      hFinalLen hFinalEndZero hFinalPre hFinalUser hFinalHdr hFinalRes1 hFinalRes5
  refine ⟨fun hNe => hFreshNewP.resolve_left hNe, ?_⟩
  let g' := mkReallocMremapGroup g newBase newP needed newSz newEff
  have hMetaBytesEq :
      ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes = g'.metaBytes := rfl
  have hMetaLen : g'.metaBytes.length = 40 := GroupDesc.metaBytes_length g'
  have hMapMul : (needed / 4096) * 4096 = needed := Nat.div_mul_cancel hNeedDvd
  have hMpG' : 0 < g'.maplen := by
    show 0 < needed / 4096
    rcases hNeedDvd with ⟨k, rfl⟩; rw [Nat.mul_div_cancel_left k (by decide)]; omega
  obtain ⟨hg'In, hGsCases, hGsKeep, _, _, _⟩ :=
    VerifiedLibraries.Mallocng.Proofs.replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl
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
        obtain ⟨_, hPRg, hCrossG⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
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
    · intro k hk1 _
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
  have hPureInit : (MallocngInitBlock mallocngIface γ).pureWf newP (newSz, keptBs) :=
    ⟨hNewBWf.1, hNewBWf.2.1, Nat.lt_of_le_of_lt hNewBWf.2.2.1 (by decide), by omega⟩
  have hCoreEq : MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' =
      (MallocngLiveAuth γ st'.liveMap ∗ (A.ctx ↦ₛ st'.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
       MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
       ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
       ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
       MappedSet st'.masterDom (OwnedMappedByte st')) := by
    have hwfInf : MallocngWFInflight 0 A.base brkStart brk bf.liveCost bf.peakCost st' := hwf'
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
    rw [propext ⟨fun _ => trivial, fun _ => hwfInf⟩, pure_true, emp_sepConj]
  have hReallocFrameEq : ReallocMremapFrame A tp st g =
      (ByteMap st.masterDom keepRw0 st.byteVal ∗ MappedSet st.masterDom keepMp0 ∗
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
      (MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p oldSz) ∗
      ((((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
       ((newBase ↦ₛ bsFinal) ∗ ((g.metaPtr ↦ₛ g'.metaBytes) ∗ ByteMap st.masterDom keepRw0 st.byteVal)) ∗
       (memMapped newBase needed ∗ MappedSet st.masterDom keepMp0) ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MallocngRoTablesAt A ∗ (A.ctx ↦ₛ st'.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗
       ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗ MallocngAuxvState γ st'.auxvPtr st'.auxvSnap))) ?_
  refine Entails.trans (sepConj_mono_left
      (mallocngBlock_replaceOv_bupd γ st.liveMap p oldSz newP newSz hNewBWf hFreshNewP))
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
       (MallocngLiveAuth γ st'.liveMap ∗ (A.ctx ↦ₛ st'.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
        MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st')) ∗
       MallocngRuntime A tp) ∗
      (MallocngBlockToken γ newP newSz ∗ (newP ↦ₛ readBytesFromMap st'.byteVal newP newSz)))) ?_
  rw [← hCoreEq, show MallocngRoTablesAt A = MallocngRoTablesA A from rfl]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hUserInit)) ?_
  rw [pure_sepConj_of_true hPureInit]
  show (MallocngRoTablesA A ∗ MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' ∗
      MallocngRuntime A tp) ∗
    (MallocngBlockToken γ newP newSz ∗
     ((newP ↦ₛ keptBs) ∗ memRegion (newP + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length))) ⊢
    MallocngRoTablesA A ∗ MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st' ∗
    MallocngRuntime A tp ∗
    (MallocngBlockToken γ newP newSz ∗ (newP ↦ₛ keptBs) ∗
     memRegion (newP + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length))
  generalize (MallocngRoTablesA A) = PRo
  generalize (MallocngCoreStA γ A brkStart brk bf.liveCost bf.peakCost st') = PCore
  generalize (MallocngRuntime A tp) = PRt
  exact Entails.of_eq (by ac_rfl)

/-! ## Reconvergence Tail and Post-`mremap` Continuation -/

set_option maxHeartbeats 400000 in
theorem realloc_s3_finish_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hCount : MallocngCountIvsWF bgt ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32) {bsCur : List (BitVec 8)}
    {Frame : SepProp} {oom : State → SepProp}
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        s.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (hpc : s.pc = b + 0x3b8#64) (hrun : s.status = .Running)
    (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx20 : s.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat))
    (hw24 : s.readReg32 .x24 =
      BitVec.ofNat 32 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
    (hcs : ReallocUntouchedCS s0 s)
    (hCurLen : bsCur.length = needed)
    (hCurHdr : bsCur.getD (13 + (p.toNat - (g.slotStart 0).toNat)) 0#8 = st.byteVal (p - 3#64))
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
        (ByteSlice.write8 bsCur (13 + (p.toNat - (g.slotStart 0).toNat))
          (BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5)))) :
    let sp1 := s0.sp - 80#64
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((newBase ↦ₛ bsCur) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
        memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngBlockToken γ p oldSz ∗ Frame))
      (fun sf Pf =>
        ∃ (st' : MallocngSt) (g' : GroupDesc) (newQ : BitVec 64) (newEff live' peak' : Nat),
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf newQ (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp newQ (newSz, keptBs) ∗ Frame) ∧
          g'.metaPtr = g.metaPtr ∧ g'.sc = 63 ∧ g'.parentMeta = none ∧
          g'.nestedCap = 0 ∧ g'.lastIdx = 0 ∧
          0 < g'.maplen ∧ g'.maplen * 4096 = needed ∧
          g'.slots = [.liveUser newQ newSz newEff] ∧
          newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
          newEff - max newSz MallocngMinBlockCost = oldEff - max oldSz MallocngMinBlockCost ∧
          p.toNat - (g.slotStart 0).toNat ≤ oldEff - max oldSz MallocngMinBlockCost + 255 * 16 ∧
          (newQ ≠ p → st.liveMap newQ = none) ∧
          st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
          st'.metaAreas = st.metaAreas ∧
          (∀ k, st'.liveMap k = if k = newQ then some newSz else if k = p then none else st.liveMap k) ∧
          MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem)
      oom := by
  intro sp1 keptBs
  let newP := (newBase + 16#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat)
  let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
  let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
  have _ := hb
  obtain ⟨_, hLast0, _, hMpG, _, _, hParentNone, hNest0, _, _, _, _, _, _, _,
      _, _, _, hNewSlotFit0, _, _, hNeedLo0, hNeedDvd0, _, _, _⟩ :=
    sc63_liveUser_bounds hCount hwf hg hIdx0 hSlot0 hSc63 hNewLo hNewHi
  have hsw0 := (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx0
  rw [hSlot0] at hsw0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨hOffLe, _, _⟩, _, _, _, _, _, _⟩ := hsw0
  have hNewSlotFit : 16 + (p.toNat - (g.slotStart 0).toNat) + newSz + 4 ≤ needed := by
    rw [hNeedEq]; exact hNewSlotFit0
  have hNeedLo : 4096 ≤ needed := by rw [hNeedEq]; exact hNeedLo0
  have hNeedDvd : 4096 ∣ needed := by rw [hNeedEq]; exact hNeedDvd0
  have hNeedAl : needed % 4096 = 0 := Nat.mod_eq_zero_of_dvd hNeedDvd
  have hMapMul : (needed / 4096) * 4096 = needed := Nat.div_mul_cancel hNeedDvd
  let extra := p.toNat - (g.slotStart 0).toNat
  let hdrOff := 13 + extra
  let hdr8 := BitVec.ofNat 8 (min ((needed - 4) - (16 + extra + newSz)) 5 <<< 5)
  obtain ⟨_, hNewPNat, _, hAddrP3Neg, _, _⟩ := sc63_post_mremap_addrs hNewBaseFit hNewSlotFit
  have hHdrAnd31 := sc63_oldHdr_and31 hwf hg hIdx0 hSlot0
  let bsFinal := ByteSlice.write8 bsCur hdrOff hdr8
  have hFinalLen : bsFinal.length = needed :=
    (ByteSlice.write8_length bsCur hdrOff hdr8 (by rw [hCurLen]; dsimp only [hdrOff, extra]; omega)).trans hCurLen
  let g' := mkReallocMremapGroup g newBase newP needed newSz newEff
  let st' := mkReallocMremapSt st g p newBase newP needed newSz newEff bsFinal
  have hMpG' : 0 < g'.maplen := by
    show 0 < needed / 4096
    rcases hNeedDvd with ⟨k, rfl⟩; rw [Nat.mul_div_cancel_left k (by decide)]; omega
  have hTail : ∀ {m1 : Memory} {s2 : State},
      m1.perm = s.mem.perm →
      s2.pc = b + 0x294#64 → s2.status = .Running → s2.mem = m1 → s2.brk = s0.brk →
      MallocngProcPreserved s0 s2 → s2.sp = s0.sp - 80#64 → s2.spAligned = true →
      s2.readReg64 .x20 = newP →
      s2.readReg64 .x23 = s0.readReg64 .x23 → s2.readReg64 .x24 = s0.readReg64 .x24 →
      s2.readReg64 .x25 = s0.readReg64 .x25 → s2.readReg64 .x26 = s0.readReg64 .x26 →
      ReallocUntouchedCS s0 s2 →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s2
        ((newBase ↦ₛ bsFinal) ∗
         (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗
          (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
           (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
           memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
           ReallocMremapFrame maddrs tp st g ∗
           MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
           (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
           ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
           ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
           MallocngBlockToken γ p oldSz ∗ Frame)))
        (fun sf Pf =>
          ∃ (st' : MallocngSt) (g' : GroupDesc) (newQ : BitVec 64) (newEff live' peak' : Nat),
            sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
            (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
              MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
              MallocngRuntime maddrs tp ∗
              ⌜(MallocngInitBlock mallocngIface γ).pureWf newQ (newSz, keptBs)⌝ ∗
              (MallocngInitBlock mallocngIface γ).interp newQ (newSz, keptBs) ∗ Frame) ∧
            g'.metaPtr = g.metaPtr ∧ g'.sc = 63 ∧ g'.parentMeta = none ∧
            g'.nestedCap = 0 ∧ g'.lastIdx = 0 ∧
            0 < g'.maplen ∧ g'.maplen * 4096 = needed ∧
            g'.slots = [.liveUser newQ newSz newEff] ∧
            newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
            newEff - max newSz MallocngMinBlockCost = oldEff - max oldSz MallocngMinBlockCost ∧
            p.toNat - (g.slotStart 0).toNat ≤ oldEff - max oldSz MallocngMinBlockCost + 255 * 16 ∧
            (newQ ≠ p → st.liveMap newQ = none) ∧
            st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
            st'.metaAreas = st.metaAreas ∧
            (∀ k, st'.liveMap k = if k = newQ then some newSz else if k = p then none else st.liveMap k) ∧
            MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem)
        oom := by
    intro m1 s2 hm1Perm hpc2 hrun2 hmem2 hbrk2 hproc2 hsp2 hal2 hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
    apply sepWP_pure_of_sat (fun R hm =>
      reallocMremap_disjoint hwf hg hSc63 hFinalLen hNewBaseAl hNeedAl hNeedLo hNewBaseFit
        (Q := ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗ MallocngRoTablesAt maddrs ∗
          (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ MallocngLiveAuth γ st.liveMap ∗
          (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
          MallocngBlockToken γ p oldSz ∗ Frame ∗ R)
        (Satisfies.mono (Entails.of_eq (by
          generalize (MallocngRoTablesAt maddrs) = PRo
          generalize (ReallocMremapFrame maddrs tp st g) = PFr
          generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
          generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
          ac_rfl)) hm))
    rintro ⟨hDisjMa, hDisjGp, hDisjAp, hDisjRg⟩
    obtain ⟨hFreshImp, hAbs⟩ :=
      reallocMremap_absorb_raw (newP := newP) γ maddrs tp brkStart s0.brk bgt ivs0 st
        hCount hwf hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal bsFinal
        hNewLo hNewHi hNeedEq hNewBaseGe hNewBaseAl hNewBaseFit hNewPNat
        hDisjMa hDisjGp hDisjAp hDisjRg hSetSize
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
         (newBase ↦ₛ bsFinal) ∗ memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame maddrs tp st g ∗
         MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MallocngBlockToken γ p oldSz) ∗ Frame)
      (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (ReallocMremapFrame maddrs tp st g) = PFr
        generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
        generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
        ac_rfl)) ?_
    apply sepWP_bupd_pre (Q :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗
        (memRegion (s0.sp - 80#64 + 48#64) 8 ∗ memRegion (s0.sp - 80#64 + 56#64) 8 ∗
         memRegion (s0.sp - 80#64 + 64#64) 8 ∗ memRegion (s0.sp - 80#64 + 72#64) 8) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesA maddrs ∗
         MallocngCoreStA γ maddrs brkStart s0.brk bf.liveCost bf.peakCost st' ∗
         MallocngRuntime maddrs tp ∗
         ⌜(MallocngInitBlock mallocngIface γ).pureWf newP (newSz, keptBs)⌝ ∗
         (MallocngInitBlock mallocngIface γ).interp newP (newSz, keptBs) ∗ Frame))
    · refine Entails.trans (sepConj_mono_right (sepConj_mono (reallocSavedHi_entails_memRegions s0 _)
        (sepConj_mono_right (sepConj_mono_left hAbs)))) ?_
      refine Entails.trans bupd_frame_mid (bupd_mono ?_)
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize (MallocngCoreStA γ maddrs brkStart s0.brk bf.liveCost bf.peakCost st') = PCore
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize ((MallocngInitBlock mallocngIface γ).interp newP (newSz, keptBs)) = PInit
      exact Entails.of_eq (by ac_rfl)
    · refine SepWP.mono (realloc_epilogue_ok hb hpc2 hrun2 hsp2 hal2 hsp0
        hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2) ?_
      intro sf Pf _ _ ⟨hsfMem, hsfBrk, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
      have hPermSf : sf.mem.perm = s.mem.perm := by rw [hsfMem, hmem2, hm1Perm]
      have hBrk0 : sf.brk = s0.brk := hsfBrk.trans hbrk2
      have hProc0 : MallocngProcPreserved s0 sf := by
        obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hproc2
        obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hsfProc
        exact ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7⟩
      have hPermRelSf :
          (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sf.mem.perm = s0.mem.perm) ∨
          (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧
            sf.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
        rw [hPermSf]; exact hPermRel
      have hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem :=
        reallocMremap_noOrphan hCount.2.2.1 hwf.groups_nodup.1 hg hMpG hMpG' rfl rfl hMapMul rfl
          hOldRw hPermRelSf
      refine ⟨st', g', newP, newEff, bf.liveCost, bf.peakCost,
        hPermSf, hBrk0, hProc0, hsfSp, hsfCS, hsfX0, Entails.trans hPf ?_,
        rfl, hSc63, hParentNone, hNest0, hLast0, hMpG', hMapMul, rfl, rfl,
        Nat.add_sub_cancel _ _, hOffLe, hFreshImp, rfl, rfl,
        (fun k => by
          change ((st.liveMap.erase p).insert newP newSz (st.liveMap.ov p)).req k = _
          simp only [MallocngLiveMap.insert_req, MallocngLiveMap.erase_req]),
        hNoOrph⟩
      rw [hBrk0]
      generalize (MallocngRoTablesA maddrs) = PRo
      generalize (MallocngCoreStA γ maddrs brkStart s0.brk bf.liveCost bf.peakCost st') = PCore
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize ((MallocngInitBlock mallocngIface γ).interp newP (newSz, keptBs)) = PInit
      exact Entails.of_eq (by ac_rfl)
  conv => arg 4; dsimp only [sp1]
  generalize hRestEnv :
    (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
     memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
     ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngBlockToken γ p oldSz ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post' = post →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  have hFocusHdr : hdrOff < bsCur.length := by rw [hCurLen]; dsimp only [hdrOff, extra]; omega
  conv => arg 4; arg 1; rw [pointsToBytes_focus8 newBase bsCur hdrOff hFocusHdr]
  have hLdAddr : (newBase + 16#64) + BitVec.ofNat 64 extra + (-3#64) = newBase + BitVec.ofNat 64 hdrOff :=
    hAddrP3Neg
  wp_step; wp_step; wp_step
  conv => arg 4; arg 1; rw [← pointsToBytes_focus8 newBase bsCur hdrOff hFocusHdr]
  wp_str8_slice m1 hm1Perm hdrOff hdr8
    (by
      have hw24' := hw24
      try dsimp only [Reg.x24] at hw24'
      try simp only [wp_norm, arm64_norm] at hw24' ⊢
      try rw [hw24']
      try rw [hCurHdr]
      try rw [hHdrAnd31]
      try rw [BitVec.add_zero]
      dsimp only [hdr8, extra]
      bv_omega)
    (by
      rw [← hAddrP3Neg]
      try simp only [wp_norm, arm64_norm, hx20])
    (by rw [hCurLen]; dsimp only [hdrOff, extra]; omega)
  conv => arg 4; rw [reallocSavedHi_eq s0]
  wp_step; wp_step; wp_step
  conv => arg 4; rw [← reallocSavedHi_eq s0]
  subst hPostGoal; rw [← hRestEnv]
  exact hTail hm1Perm (by simp) (by simp [hrun]) (by simp) (by simp [hbrk])
    ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
     by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    (by simp [hsp]) (by simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
    (by simp [hx20, newP]) (by simp) (by simp) (by simp) (by simp)
    ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩

set_option maxHeartbeats 400000 in
/-- Complete raw-state Stage 3 post-`mremap` (`+0x364` → `ret`) directly over `(liveCost peakCost : Nat)`
    and `MallocngWF`, without any `MallocngBudget` or `MallocngCountIvsWF` input. -/
theorem realloc_s3_post_mremap_raw_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : MallocngBudget) (ivs_in : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hCount_in : MallocngCountIvsWF bgt ivs_in st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32)
    {Frame : SepProp} {oom : State → SepProp}
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        s.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (hpc : s.pc = b + 0x364#64) (hrun : s.status = .Running)
    (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = newBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat))
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx22 : s.readReg64 .x22 = g.metaPtr)
    (hx24 : s.readReg64 .x24 = 0#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 needed)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let keptBs := origBs.take newSz
    let bsRemap0 := (mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).take needed ++
      List.replicate (needed - g.maplen * 4096) 0#8
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ (newBase ↦ₛ bsRemap0) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngBlockToken γ p oldSz ∗ Frame))
      (fun sf Pf =>
        ∃ (st' : MallocngSt) (g' : GroupDesc) (newQ : BitVec 64) (newEff live' peak' : Nat),
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
            MallocngRuntime maddrs tp ∗
            ⌜(MallocngInitBlock mallocngIface γ).pureWf newQ (newSz, keptBs)⌝ ∗
            (MallocngInitBlock mallocngIface γ).interp newQ (newSz, keptBs) ∗ Frame) ∧
          g'.metaPtr = g.metaPtr ∧ g'.sc = 63 ∧ g'.parentMeta = none ∧
          g'.nestedCap = 0 ∧ g'.lastIdx = 0 ∧
          0 < g'.maplen ∧ g'.maplen * 4096 = needed ∧
          g'.slots = [.liveUser newQ newSz newEff] ∧
          newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
          newEff - max newSz MallocngMinBlockCost = oldEff - max oldSz MallocngMinBlockCost ∧
          p.toNat - (g.slotStart 0).toNat ≤ oldEff - max oldSz MallocngMinBlockCost + 255 * 16 ∧
          (newQ ≠ p → st.liveMap newQ = none) ∧
          st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
          st'.metaAreas = st.metaAreas ∧
          (∀ k, st'.liveMap k = if k = newQ then some newSz else if k = p then none else st.liveMap k) ∧
          MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem)
      oom := by
  intro sp1 keptBs bsRemap0
  let ivs0 := dynamicRootRegions st
  have hCount : MallocngCountIvsWF bgt ivs0 st := by
    dsimp only [ivs0]; rw [← hCount_in.2.2.1]; exact hCount_in
  have _ := hb
  dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26] at hx0 hx20 hx21 hx22 hx24 hx25 hx26
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let extra := p.toNat - (g.slotStart 0).toNat
  let hdrOff := 13 + extra
  let newRes := (needed - 4) - (16 + extra + newSz)
  let hdr8 := BitVec.ofNat 8 (min newRes 5 <<< 5)
  have ⟨hLast0, hOldMemFit, hSt0Nat, hLoP, hOldSlotFit, hNewSlotFit, hNeedLo, hNeedDvd⟩ :
      g.lastIdx = 0 ∧ g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 ∧
      (g.slotStart 0).toNat = g.mem.toNat + 16 ∧ (g.slotStart 0).toNat ≤ p.toNat ∧
      16 + extra + oldSz + 4 ≤ g.maplen * 4096 ∧ 16 + extra + newSz + 4 ≤ needed ∧
      4096 ≤ needed ∧ 4096 ∣ needed := by
    obtain ⟨_, h1, _, _, _, _, _, _, _, _, h2, _, h3, _, h4, _, _, h5, h6, _, _, h7, h8, _, _, _⟩ :=
      sc63_liveUser_bounds hCount hwf hg hIdx0 hSlot0 hSc63 hNewLo hNewHi
    rw [← hNeedEq] at h6 h7 h8; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hResBound : newRes ≤ 4095 := by dsimp only [newRes, extra] at hNeedEq ⊢; omega
  have hUserLen : (origBs ++ tailBs).length = oldSz := by simp [hTailLen]; omega
  have hOldMapLen : (mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).length = g.maplen * 4096 :=
    mkSc63OldMapBs_length st.byteVal g p oldSz (origBs ++ tailBs) hUserLen (by omega) (by omega)
  have hRemapLen0 : bsRemap0.length = needed := by
    simp only [bsRemap0, List.length_append, List.length_take, List.length_replicate, hOldMapLen]; omega
  have hRemapHdr0 : bsRemap0.getD hdrOff 0#8 = st.byteVal (p - 3#64) :=
    sc63_bsRemap_getD_hdr st.byteVal g (origBs ++ tailBs) hUserLen hOldMemFit hSt0Nat hLoP hOldSlotFit
      (by dsimp only [extra] at hNewSlotFit; omega)
  clear hSt0Nat
  have hAddrRes1 := (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).2.2.2.2.1
  have hAddrRes5 := (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).2.2.2.2.2
  have hDivEq : (newSz + extra + 4115) / 4096 = needed / 4096 := by
    rw [hNeedEq, Nat.mul_div_cancel _ (by decide)]
  have hNeedSymm := hNeedEq.symm; clear hNeedEq
  have hLsr25 : BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) >>> 12 =
      BitVec.ofNat 64 (needed / 4096) := by
    rw [lsr12_eq_pageDiv (by dsimp only [extra] at hNewSlotFit; omega)]
    exact congrArg (BitVec.ofNat 64) hDivEq
  generalize hv25 : BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) = v25 at hx25 hLsr25
  clear hv25
  have hBfiPw : g.packedWord &&& 4095#64 ||| ((BitVec.ofNat 64 (needed / 4096) &&& 4503599627370495#64) <<< 12) =
      ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).packedWord :=
    bfi_packedWord_maplen g (by omega) (by omega) (by omega)
  have hCap0Sub : (BitVec.ofNat 64 needed - 20#64) - BitVec.ofNat 64 extra =
      BitVec.ofNat 64 ((needed - 4) - (16 + extra)) := cap0_sub_extra (by omega) (by omega)
  have ⟨hSubsRes, hEqCap32⟩ := subs32_cap_newSz (cap := (needed - 4) - (16 + extra))
    (newSz := newSz) (by omega) (by omega) (by omega)
  have hHdr3Eq : hdrOff + 3 + newSz = 16 + extra + newSz := by dsimp only [hdrOff]; omega
  conv => arg 4; dsimp only [sp1]
  generalize hbsRemap : bsRemap0 = bsRemap
  have hRemapLen : bsRemap.length = needed := hbsRemap ▸ hRemapLen0
  have hRemapHdr : bsRemap.getD hdrOff 0#8 = st.byteVal (p - 3#64) := hbsRemap ▸ hRemapHdr0
  have hGoFin : ∀ {bsCur : List (BitVec 8)} {sFin : State},
      sFin.mem.perm = s.mem.perm → sFin.pc = b + 0x3b8#64 → sFin.status = .Running →
      sFin.brk = s0.brk → MallocngProcPreserved s0 sFin →
      sFin.sp = s0.sp - 80#64 → sFin.spAligned = true →
      sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra →
      sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) →
      ReallocUntouchedCS s0 sFin → bsCur.length = needed →
      bsCur.getD hdrOff 0#8 = st.byteVal (p - 3#64) →
      SetSizeSlicePost (ByteSlice.write8 bsRemap0 (needed - 4) 0#8) hdrOff (needed - 4)
        newSz hdr8 (ByteSlice.write8 bsCur hdrOff hdr8) →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) sFin
        ((newBase ↦ₛ bsCur) ∗
         ((g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
          (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
           stackFrameAt (s0.sp - 80#64) 720 ∗ MallocngRoTablesAt maddrs ∗
           (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
           ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
           MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
           (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
           ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
           ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
           MallocngBlockToken γ p oldSz ∗ Frame)))
        (fun sf Pf =>
          ∃ (st' : MallocngSt) (g' : GroupDesc) (newQ : BitVec 64) (newEff live' peak' : Nat),
            sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
            (Pf ⊢ stackFrame s0 800 ∗ MallocngRoTablesA maddrs ∗
              MallocngCoreStA γ maddrs brkStart sf.brk live' peak' st' ∗
              MallocngRuntime maddrs tp ∗
              ⌜(MallocngInitBlock mallocngIface γ).pureWf newQ (newSz, keptBs)⌝ ∗
              (MallocngInitBlock mallocngIface γ).interp newQ (newSz, keptBs) ∗ Frame) ∧
            g'.metaPtr = g.metaPtr ∧ g'.sc = 63 ∧ g'.parentMeta = none ∧
            g'.nestedCap = 0 ∧ g'.lastIdx = 0 ∧
            0 < g'.maplen ∧ g'.maplen * 4096 = needed ∧
            g'.slots = [.liveUser newQ newSz newEff] ∧
            newEff = (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost ∧
            newEff - max newSz MallocngMinBlockCost = oldEff - max oldSz MallocngMinBlockCost ∧
            p.toNat - (g.slotStart 0).toNat ≤ oldEff - max oldSz MallocngMinBlockCost + 255 * 16 ∧
            (newQ ≠ p → st.liveMap newQ = none) ∧
            st'.groups = st.groups.map (fun x => if x.metaPtr == g.metaPtr then g' else x) ∧
            st'.metaAreas = st.metaAreas ∧
            (∀ k, st'.liveMap k = if k = newQ then some newSz else if k = p then none else st.liveMap k) ∧
            MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem) oom := by
    intro bsCur sFin hPermEqF hpcF hrunF hbrkF hprocF hspF halF hx20F hw24F hcsF hCLen hCHdr hSet
    have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
        (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧
          sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
      rw [hPermEqF]; exact hPermRel
    refine SepWP.weaken_pre (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
      generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
      generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
      (SepWP.mono (realloc_s3_finish_raw_ok hb γ tp brkStart bgt ivs0 s0 sFin st hCount hwf hg hIdx0
        origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal hNewLo hNewHi hNeedSymm.symm
        hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF hpcF hrunF hbrkF hprocF
        hspF halF hsp0 hx20F hw24F hcsF hCLen hCHdr hSet)
        (fun _ _ _ _ ⟨st', g', newQ, newEff, l', pk', hpEq, rest⟩ =>
          ⟨st', g', newQ, newEff, l', pk', hpEq.trans hPermEqF, rest⟩))
  generalize hRestEnv :
    (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
     stackFrameAt (s0.sp - 80#64) 720 ∗ MallocngRoTablesAt maddrs ∗
     (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngBlockToken γ p oldSz ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post = post' →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  conv => arg 4; arg 1; rw [GroupDesc.metaBytes_pointsTo g.metaPtr g]
  wp_step
  conv => arg 4; arg 1; rw [← GroupDesc.metaBytes_pointsTo g.metaPtr g]
  wp_step; wp_step; wp_step
  wp_str64_slice m1 hm1Perm 16 newBase (by (try rw [hx0]); rfl) (by (try rw [hx22]); rfl)
    (by rw [GroupDesc.metaBytes_length]; decide)
  wp_step; wp_step
  wp_str64_slice m2 hm2Perm 32 (({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).packedWord)
    (by rw [hLast0, hSc63]) (by (try rw [hx22]); rfl)
    (by rw [ByteSlice.write64_length _ _ _ (by rw [GroupDesc.metaBytes_length]; decide),
            GroupDesc.metaBytes_length]; decide)
  conv => arg 4; arg 1; rw [metaBytes_write_mem_packedWord g newBase (needed / 4096) _ rfl]
  refine SepWP.weaken_pre (P' := (newBase ↦ₛ bsRemap) ∗
      ((g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗ RestEnv))
    (Entails.of_eq (by ac_rfl)) ?_
  wp_str8_slice m3 hm3Perm (needed - 4) 0#8 rfl
    (by
      try simp only [wp_norm, arm64_norm]
      try rw [hx0]
      try rw [hx26]
      exact (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).1)
    (by rw [hRemapLen]; omega)
  have hZeroLen : (ByteSlice.write8 bsRemap (needed - 4) 0#8).length = needed :=
    (ByteSlice.write8_length bsRemap (needed - 4) 0#8 (by rw [hRemapLen]; omega)).trans hRemapLen
  have hZeroHdr : (ByteSlice.write8 bsRemap (needed - 4) 0#8).getD hdrOff 0#8 = st.byteVal (p - 3#64) := by
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hRemapLen]; omega)]
    simp only [show hdrOff ≠ needed - 4 by dsimp only [hdrOff]; omega, ↓reduceIte, hRemapHdr]
  wp_step; wp_step; wp_step; wp_step
  wp_if hEq0
  · have hRes0 : newRes = 0 := by
      try rw [hx20] at hEq0
      try rw [hx21] at hEq0
      try rw [hx26] at hEq0
      dsimp only [extra] at hCap0Sub hEqCap32; rw [hCap0Sub] at hEq0
      have h0 := hEqCap32.mp hEq0; dsimp only [newRes, extra]; omega
    apply sepWP_bind_state_s3; intro sFin hsFin
    subst hPostGoal; rw [← hRestEnv]
    have hSet0 := setSize_case0 (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
      (by dsimp only [hdrOff, newRes] at hRes0 ⊢; omega) (by rw [hZeroLen]; omega)
    subst hbsRemap
    exact hGoFin
      (by rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm3Perm, hm2Perm, hm1Perm])
      (by rw [hsFin]; simp) (by rw [hsFin]; simp [hrun]) (by rw [hsFin]; simp [hbrk])
      (by rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
          by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩)
      (by rw [hsFin]; simp [hsp])
      (by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
      (by rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl)
      (by rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
          try rw [hx24]
          rw [hRes0]; decide)
      (by rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩)
      hZeroLen hZeroHdr hSet0
  · have hSubsRes' : (BitVec.ofNat 64 ((needed - 4) - (16 + extra))).truncate 32 -
        (BitVec.ofNat 64 newSz).truncate 32 = BitVec.ofNat 32 newRes := by
      rw [show (needed - 4) - (16 + extra) - newSz = newRes by dsimp only [newRes]; omega] at hSubsRes
      exact hSubsRes
    have hSubsResZ : BitVec.zeroExtend 32 (BitVec.ofNat 64 ((needed - 4) - (16 + extra))) -
        BitVec.zeroExtend 32 (BitVec.ofNat 64 newSz) = BitVec.ofNat 32 newRes := hSubsRes'
    have hResPos : 1 ≤ newRes := by
      have hNe0 : (needed - 4) - (16 + extra) - newSz ≠ 0 := fun h0 => by
        have hEqTrue := hEqCap32.mpr h0
        exfalso; revert hEq0
        try rw [hx20]
        try rw [hx21]
        try rw [hx26]
        dsimp only [extra] at hCap0Sub hEqTrue
        rw [hCap0Sub]; simp [hEqTrue]
      dsimp only [newRes]; omega
    have hAddr1 : (newBase + 16#64) + (BitVec.ofNat 64 needed - 20#64) +
        (0#32 - BitVec.ofNat 32 newRes).signExtend 64 =
        newBase + BitVec.ofNat 64 (hdrOff + 3 + newSz) := by
      rw [BitVec.zero_sub, hHdr3Eq]; exact hAddrRes1 hResPos (by omega)
    wp_step; wp_step; wp_step
    wp_str8_slice m4 hm4Perm (hdrOff + 3 + newSz) 0#8 rfl
      (by
        try simp only [wp_norm, arm64_norm]
        try rw [hx0]
        try rw [hx20]
        try rw [hx21]
        try rw [hx26]
        dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ ⊢
        try rw [hCap0Sub]
        try rw [hSubsRes']
        try rw [hSubsResZ]
        exact hAddr1)
      (by rw [hZeroLen]; dsimp only [hdrOff]; omega)
    try conv => arg 4; arg 1; rw [Nat.add_comm newSz (hdrOff + 3)]
    have hLen1 : (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8).length = needed :=
      (ByteSlice.write8_length _ _ _ (by rw [hZeroLen]; dsimp only [hdrOff]; omega)).trans hZeroLen
    have hHdr1 : (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8).getD hdrOff 0#8 =
        st.byteVal (p - 3#64) := by
      rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hZeroLen]; dsimp only [hdrOff]; omega)]
      simp only [show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte, hZeroHdr]
    wp_step
    wp_if hLe4
    · have hResLe4 : newRes ≤ 4 := by
        try rw [hx20] at hLe4
        try rw [hx21] at hLe4
        try rw [hx26] at hLe4
        dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
        try rw [hCap0Sub] at hLe4
        try rw [hSubsRes'] at hLe4
        try rw [hSubsResZ] at hLe4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            bv32_sle_iff_of_lt31 (by omega) (by decide), decide_eq_true_eq] at hLe4
        exact hLe4
      apply sepWP_bind_state_s3; intro sFin hsFin
      subst hPostGoal; rw [← hRestEnv]
      have hSet14 := setSize_case1to4 (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
        (by rw [hHdr3Eq]; exact hResPos) (by rw [hHdr3Eq]; exact hResLe4) (by rw [hZeroLen]; omega)
      subst hbsRemap
      exact hGoFin
        (by rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm4Perm, hm3Perm, hm2Perm, hm1Perm])
        (by rw [hsFin]; simp) (by rw [hsFin]; simp [hrun]) (by rw [hsFin]; simp [hbrk])
        (by rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
            by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩)
        (by rw [hsFin]; simp [hsp])
        (by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
        (by rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl)
        (by rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
            try rw [hx20]
            try rw [hx21]
            try rw [hx26]
            dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
            try rw [hCap0Sub]
            try rw [hSubsRes']
            try rw [hSubsResZ]
            rcases (by omega : newRes = 0 ∨ newRes = 1 ∨ newRes = 2 ∨ newRes = 3 ∨ newRes = 4) with hR | hR | hR | hR | hR <;>
              (rw [hR]; decide))
        (by rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩)
        hLen1 hHdr1 hSet14
    · have hResGe5 : 5 ≤ newRes := by
        have hNotLe : ¬ (newRes ≤ 4) := fun h4 => by
          have hSle : BitVec.sle (BitVec.ofNat 32 newRes) 4#32 = true := by
            rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
                bv32_sle_iff_of_lt31 (by omega) (by decide), decide_eq_true_eq]
            exact h4
          exfalso; revert hLe4
          try rw [hx20]
          try rw [hx21]
          try rw [hx26]
          dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
          try rw [hCap0Sub]
          try rw [hSubsRes']
          try rw [hSubsResZ]
          simp [hSle]
        omega
      wp_step
      wp_str8_slice m5 hm5Perm ((needed - 4) - 5) 0#8 rfl
        (by rw [← (hAddrRes5 hResGe5).1]; bv_lin)
        (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)
      have hLen2 : (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8)
          (hdrOff + 3 + newSz) 0#8) ((needed - 4) - 5) 0#8).length = needed :=
        (ByteSlice.write8_length _ _ _ (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)).trans hLen1
      wp_str32_slice m6 hm6Perm ((needed - 4) - 4) (BitVec.ofNat 32 newRes)
        (by
          try simp only [wp_norm, arm64_norm]
          try rw [hx20]
          try rw [hx21]
          try rw [hx26]
          dsimp only [extra] at hCap0Sub hSubsRes'
          rw [hCap0Sub, hSubsRes'])
        (by rw [← (hAddrRes5 hResGe5).2]; bv_lin)
        (by rw [hLen2]; dsimp only [newRes] at hResGe5; omega)
      have hLen3 : (ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8
          (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8)
          ((needed - 4) - 5) 0#8) ((needed - 4) - 4) (BitVec.ofNat 32 newRes)).length = needed :=
        (ByteSlice.write32_length _ _ _ (by rw [hLen2]; dsimp only [newRes] at hResGe5; omega)).trans hLen2
      have hHdr3 : (ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8
          (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8)
          ((needed - 4) - 5) 0#8) ((needed - 4) - 4) (BitVec.ofNat 32 newRes)).getD hdrOff 0#8 = st.byteVal (p - 3#64) := by
        rw [ByteSlice.getD_write32 _ _ _ _ _ (by rw [hLen2]; dsimp only [newRes] at hResGe5; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)]
        simp only [show ¬ ((needed - 4) - 4 ≤ hdrOff ∧ hdrOff < (needed - 4) - 4 + 4) by dsimp only [hdrOff, newRes] at hResGe5 ⊢; omega,
          show hdrOff ≠ (needed - 4) - 5 by dsimp only [hdrOff, newRes] at hResGe5 ⊢; omega, ↓reduceIte, hHdr1]
      apply sepWP_bind_state_s3; intro sFin hsFin
      subst hPostGoal; rw [← hRestEnv]
      have hSet5 := setSize_case5up (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
        (BitVec.ofNat 32 newRes) (by rw [hHdr3Eq]; exact hResGe5) (by rw [hHdr3Eq]) (by rw [hZeroLen]; omega)
      subst hbsRemap
      exact hGoFin
        (by rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm6Perm, hm5Perm, hm4Perm, hm3Perm, hm2Perm, hm1Perm])
        (by rw [hsFin]; simp) (by rw [hsFin]; simp [hrun]) (by rw [hsFin]; simp [hbrk])
        (by rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
            by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩)
        (by rw [hsFin]; simp [hsp])
        (by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
        (by rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl)
        (by rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
            exact mov_0xa0_res5up hResGe5)
        (by rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩)
        hLen3 hHdr3 hSet5

end LibsignalBinary.Heap.Fine
