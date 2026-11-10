/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedFreeHelpers2

/-!
# In-Place Slot Transition Helpers for `__libc_free`

Provides pure invariant-transition and spatial framing lemmas for `__libc_free` and
`nontrivial_free`: single-slot `MallocngWFInflight` preservation (`wf_of_inPlaceSlotMod`), entry
`.liveUser -> .claimed` slot release (`free_release_userSlot_wf`), and `ByteMap` preservation across
40-byte `struct meta` updates (`metaBytes_update_spatial`).
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Sum Lifting and In-Place Slot Modification Combinator -/

theorem replaceGroupByMeta_map_sum {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g g1 : GroupDesc} (hg : g ∈ gs) (f : GroupDesc → Nat) :
    ((replaceGroupByMeta gs g.metaPtr g1).map f).sum + f g = (gs.map f).sum + f g1 := by
  obtain ⟨pre, post, hGsEq, _, _, hRep, _⟩ := split_groups_at_mem hNd hg
  rw [hRep g1, hGsEq]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

set_option maxHeartbeats 400000 in
/-- Preserves `MallocngWFInflight` across any in-place single-slot transition `g -> g1`
    (`g1.slots = g.slots.set idx s1`) with writes confined to `SlotWriteMod g idx` and unchanged
    `ctx`, `activeLists`, and `reservedMetas`. -/
theorem wf_of_inPlaceSlotMod {inflight inflight' : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost liveCost' : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g g1 : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hNotNested : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm)
    {s1 : SlotState} {bv1 : BitVec 64 → BitVec 8} {lm1 : MallocngLiveMap}
    (hMeta : g1.metaPtr = g.metaPtr) (hPrev : g1.prev = g.prev) (hNext : g1.next = g.next)
    (hMem : g1.mem = g.mem) (hLast : g1.lastIdx = g.lastIdx) (hSc : g1.sc = g.sc)
    (hMaplen : g1.maplen = g.maplen) (hActByte : g1.activeByte = g.activeByte)
    (hPar : g1.parentMeta = g.parentMeta) (hCap : g1.nestedCap = g.nestedCap)
    (hSlots : g1.slots = g.slots.set idx s1)
    (hMaskOther : ∀ j : Nat, j < g.slots.length → j ≠ idx →
      g1.availMask.getLsbD j = g.availMask.getLsbD j ∧
      g1.freedMask.getLsbD j = g.freedMask.getLsbD j)
    (hMaskDisj : g1.availMask &&& g1.freedMask = 0#32)
    (hMaskLt : (g1.availMask ||| g1.freedMask).toNat < 2 ^ g.cnt)
    (hBvOut : ∀ a : BitVec 64, ¬ SlotWriteMod g idx a → bv1 a = st.byteVal a)
    (hMetaBytes : readBytesFromMap bv1 g1.metaPtr 40 = g1.metaBytes)
    (hSlot1Wf : SlotWf
      { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1, liveMap := lm1 }
      g1 idx s1)
    (hActNotMem : ∀ (hScLt : g.sc < st.activeLists.length),
      g.metaPtr ∉ st.activeLists[g.sc]'hScLt → g1.availMask = 0#32 ∧ g1.freedMask = 0#32)
    (hActTail : ∀ (hScLt : g.sc < st.activeLists.length) (i : Nat)
      (hi : i < (st.activeLists[g.sc]'hScLt).length), 0 < i →
      g.metaPtr = (st.activeLists[g.sc]'hScLt)[i]'hi → g1.availMask = 0#32 ∧ g1.freedMask ≠ 0#32)
    (hEmpty1 : g1.isEmpty = true →
      0 < g1.maplen ∧ 7 ≤ g1.sc ∧ g1.sc ≤ 38 ∧ g1.maplen * 4096 ≤ 1048576 ∧
      (∀ h : g1.sc < st.activeLists.length, st.activeLists[g1.sc]'h = [g1.metaPtr]) ∧
      (g1.lastIdx = 0 → slotStride g1.sc + 16 ≤ g1.maplen * 4096))
    (hInflight' : st.reservedMetas.length +
      totalClaimedSlots { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1, liveMap := lm1 } ≤ inflight')
    (hLivePeak : liveCost' ≤ peakCost)
    (hEffLe : totalLiveEffCost
      { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1, liveMap := lm1 } ≤ liveCost')
    (hLiveMap1 : ∀ (q : BitVec 64) (r : Nat),
      lm1 q = some r ↔
        ∃ h ∈ replaceGroupByMeta st.groups g.metaPtr g1, ∃ j : Nat, ∃ hj : j < h.slots.length, ∃ c : Nat,
          h.slots[j]'hj = .liveUser q r c)
    (hOwnDom : ∀ a : BitVec 64,
      OwnedRwByte { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1, liveMap := lm1 } a →
      a ∈ st.masterDom)
    (hLiveOv : ∀ u r, st.liveMap u = some r → lm1.ov u = st.liveMap.ov u := by intros; rfl) :
    MallocngWFInflight inflight' base brkStart brk liveCost' peakCost
      { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1, liveMap := lm1 } := by
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let st1 : MallocngSt :=
    { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1, liveMap := lm1 }
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg hMeta hMem hMaplen hSc hLast
  have hDisj := slotWriteMod_disjoint hwf hg hIdx hNotNested
  have hCnt : g1.cnt = g.cnt := by simp [GroupDesc.cnt, hLast]
  have hStr : g1.stride = g.stride := by simp [GroupDesc.stride, hLast, hMaplen, hSc]
  have hTot : g1.totalBytes = g.totalBytes := by simp [GroupDesc.totalBytes, hMaplen, hCap]
  have hStor : g1.storage = g.storage := by simp [GroupDesc.storage, hMem]
  have hSt : ∀ j, g1.slotStart j = g.slotStart j := fun j => by simp [GroupDesc.slotStart, hStor, hStr]
  have hEn : ∀ j, g1.slotEnd j = g.slotEnd j := fun j => by simp [GroupDesc.slotEnd, hSt, hStr]
  have hActI : g1.activeIdx = g.activeIdx := by simp [GroupDesc.activeIdx, hActByte]
  have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
    unfold dynamicRootRegions; simp only [st1, hRep.2.2.1]
  have hNestedMap : ∀ cg ∈ st.groups, cg.maplen = 0 →
      ∃ cg' ∈ st1.groups, cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
        cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap := fun cg hcg _ => by
    by_cases hEq : cg.metaPtr = g.metaPtr
    · have hCgEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hEq; subst hCgEq
      exact ⟨g1, hRep.2.2.2.2.1, hMeta, hPar, hMem, hCap⟩
    · exact ⟨cg, hRep.2.2.2.2.2.2.1 cg hcg hEq, rfl, rfl, rfl, rfl⟩
  have hParentLift : ∀ h0 ∈ st.groups, h0.maplen = 0 →
      1 ≤ h0.lastIdx ∧ ∃ pg' ∈ st1.groups, ∃ pIdx : Nat, ∃ hp' : pIdx < pg'.slots.length,
        h0.parentMeta = some pg'.metaPtr ∧ pg'.sc < 48 ∧ h0.sc < pg'.sc ∧ pg'.sc ≤ 24 ∧
        pg'.slots[pIdx]'hp' = .liveNested h0.metaPtr ∧
        (pg'.slotStart pIdx).toNat ≤ h0.mem.toNat ∧
        h0.mem.toNat + h0.nestedCap ≤ (pg'.slotEnd pIdx).toNat ∧
        h0.nestedCap = slotStride pg'.sc - 4 := fun h0 hh0 hM0 => by
    obtain ⟨hL1, pg, hpg, pIdx, hp, hPM, hPSc, hLtSc, hLe24, hPSlot, hPLo, hPHi, hPCap⟩ :=
      (hwf.groups_wf h0 hh0).2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
    refine ⟨hL1, ?_⟩
    by_cases hEq : pg.metaPtr = g.metaPtr
    · have hPgEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hEq; subst hPgEq
      have hpNe : pIdx ≠ idx := fun hJ => by subst hJ; exact hNotNested h0.metaPtr hPSlot
      have hp1 : pIdx < g1.slots.length := by simp [hSlots, hp]
      refine ⟨g1, hRep.2.2.2.2.1, pIdx, hp1, hMeta ▸ hPM, hSc ▸ hPSc, hSc ▸ hLtSc, hSc ▸ hLe24,
        ?_, (hSt pIdx).symm ▸ hPLo, (hEn pIdx).symm ▸ hPHi, hSc ▸ hPCap⟩
      simp only [hSlots, List.getElem_set, Ne.symm hpNe, ↓reduceIte, hPSlot]
    · exact ⟨pg, hRep.2.2.2.2.2.2.1 pg hpg hEq, pIdx, hp, hPM, hPSc, hLtSc, hLe24, hPSlot, hPLo, hPHi, hPCap⟩
  exact
    { base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := hwf.ctx_lens
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun h0 => by
        have hEmptyGs := (hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1
        rw [hEmptyGs] at hg; cases hg
      bounces_wf := hwf.bounces_wf
      usage_wf := fun sc hsc => by rw [hwf.usage_wf sc hsc]; exact (hRep.2.2.2.1 sc).symm
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
        have hMa := hwf.metaAreas_wf.2.1 ma hma
        refine ⟨hMa.1, hMa.2.1, hMa.2.2.1, ?_⟩
        rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.1 ma hma a ha)]
        exact hMa.2.2.2, hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
        fun ap hap => by
          have hAp := hwf.guard_avail_wf.2.2.2 ap hap
          refine ⟨hAp.1, hAp.2.1, hAp.2.2.1, ?_⟩
          have hmAll : g.metaPtr ∈ allMetaSlots st :=
            (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
          obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf hmAll
          obtain ⟨rgG, hrgG, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
          have ⟨_, hStorG, hStG, hSub4G, hEnG, hEnLeG, hG48, _, _⟩ :=
            group_slot_bounds (hwf.groups_wf g hg) hIdx
          have ⟨hStrG, _⟩ := group_stride_pos_and_align (hwf.groups_wf g hg)
          have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
          have hRgTot : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
          have hRg48 : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
          have ⟨hABC, _, hCrossCD⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
          have ⟨_, _, hCrossABC⟩ := pairwiseDisjoint_append hABC
          have hDisjMaAp := hCrossABC (maG.base, 4096)
            (List.mem_append_left _ (List.mem_map_of_mem hmaG)) (ap, 4096) (List.mem_map_of_mem hap)
          have hDisjApRg := hCrossCD (ap, 4096)
            (List.mem_append_right _ (List.mem_map_of_mem hap)) (rgG.mem, rgG.maplen * 4096)
            (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgG, decide_eq_true hRgMp⟩))
          rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a fun hMod => by
            rcases hMod with hM | ⟨hS, _⟩
            · exact not_both_inRegion_of_disjointRegions hDisjMaAp (hInMaG a hM) ha
            · have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hS
              have hInRg : InRegion rgG.mem (rgG.maplen * 4096) a :=
                (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
              exact not_both_inRegion_of_disjointRegions hDisjApRg ha hInRg]
          exact hAp.2.2.2⟩
      inflight_wf := hInflight'
      free_bump_metas_wf := by
        have ⟨hDll, hFmBytes, hBump, hBmBytes, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
        have ⟨hNd123, _, _⟩ := List.nodup_append.mp hUfNd
        have ⟨hNd12, _, hDisjBm⟩ := List.nodup_append.mp hNd123
        have ⟨_, _, hDisjFm⟩ := List.nodup_append.mp hNd12
        refine ⟨hDll, fun fm hfm => ?_, hBump, fun bm hbm => ?_, ?_, ?_⟩
        · have hNe : fm.ptr ≠ g.metaPtr := fun hEq =>
            hDisjFm g.metaPtr (List.mem_map_of_mem hg) fm.ptr (List.mem_map_of_mem hfm) hEq.symm
          have hAll : fm.ptr ∈ allMetaSlots st := (hUfIff fm.ptr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
          rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 fm.ptr hAll hNe a ha)]
          exact hFmBytes fm hfm
        · have hNe : bm ≠ g.metaPtr := fun hEq =>
            hDisjBm g.metaPtr (List.mem_append_left _ (List.mem_map_of_mem hg)) bm hbm hEq.symm
          have hAll : bm ∈ allMetaSlots st := (hUfIff bm).mp
            (List.mem_append_left _ (List.mem_append_right _ hbm))
          rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvOut a (hDisj.2.1 bm hAll hNe a ha)]
          exact hBmBytes bm hbm
        · simpa only [st1, hRep.1] using hUfNd
        · intro m; simpa only [st1, hRep.1, allMetaSlots] using hUfIff m
      groups_nodup := ⟨hRep.1 ▸ hwf.groups_nodup.1, hRep.2.1 ▸ hwf.groups_nodup.2⟩
      groups_wf := fun h' hh' => by
        rcases hRep.2.2.2.2.2.1 h' hh' with hEqG1 | ⟨hh0, hNeM⟩
        · subst h'
          have hGWf := hwf.groups_wf g hg
          have hHdrDisj := hDisj.2.2.1 g hg
          have hGMem48 : g.mem.toNat + 9 ≤ 2 ^ 64 := by
            have := hGWf.2.2.2.2.2.2.1; have := hGWf.2.2.2.2.2.2.2.1; omega
          refine ⟨hSc ▸ hGWf.1, hLast ▸ hGWf.2.1, by simp [hSlots, hCnt, hGWf.2.2.1],
            by rw [hSc, hLast, hMaplen, hPrev, hNext]; exact hGWf.2.2.2.1,
            hMem ▸ hGWf.2.2.2.2.1, hMem ▸ hGWf.2.2.2.2.2.1,
            by rw [hMem, hTot]; exact hGWf.2.2.2.2.2.2.1,
            by rw [hCnt, hStr, hTot]; exact hGWf.2.2.2.2.2.2.2.1,
            by rw [hMaplen, hCnt, hStr, hTot]; exact hGWf.2.2.2.2.2.2.2.2.1,
            by rw [hLast, hEn]; exact (hBvOut _ hHdrDisj.2).trans hGWf.2.2.2.2.2.2.2.2.2.1,
            by rw [hMaplen, hPar]; exact hGWf.2.2.2.2.2.2.2.2.2.2.1,
            by rw [hMaplen, hMem, hCap, hSc, hLast, hStr]; exact hGWf.2.2.2.2.2.2.2.2.2.2.2.1,
            fun hM0 => by
              have hRes := hParentLift g hg (hMaplen ▸ hM0)
              exact ⟨hLast ▸ hRes.1, by simpa only [hPar, hSc, hMeta, hMem, hCap] using hRes.2⟩,
            hMaskDisj, hCnt ▸ hMaskLt, by rw [hActI, hLast]; exact hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hMetaBytes,
            by rw [hMem, hMeta, readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
                 hBvOut a (hHdrDisj.1 a ((inRegion_iff_toNat (by omega) a).mpr
                   (by have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha; omega)))]
               exact hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            by rw [hMem, hActByte]
               exact (hBvOut (g.mem + 8#64) (hHdrDisj.1 (g.mem + 8#64)
                 ((inRegion_iff_toNat (by omega) (g.mem + 8#64)).mpr
                   ⟨by rw [bv64_add_toNat (by omega)]; omega,
                    by rw [bv64_add_toNat (by omega)]; omega⟩))).trans
                 hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun j hj1 => by
              have hj : j < g.slots.length := by simpa [hSlots] using hj1
              by_cases hjEq : j = idx
              · subst hjEq
                have hGet1 : (g1.slots)[j]'hj1 = s1 := by simp [hSlots]
                rw [hGet1]; exact hSlot1Wf
              · have hGet1 : (g1.slots)[j]'hj1 = g.slots[j]'hj := by
                  simp only [hSlots, List.getElem_set, Ne.symm hjEq, ↓reduceIte]
                rw [hGet1]
                exact slotWf_other_of_slotWriteMod hwf hg hIdx hNotNested hBvOut hNestedMap
                  hg hj (Or.inr hjEq) hMeta hMem hSc hLast hMaplen hActByte
                  (hMaskOther j hj hjEq).1 (hMaskOther j hj hjEq).2 rfl
                  (fun u r e hS => hLiveOv u r ((hwf.liveMap_wf u r).mpr ⟨g, hg, j, hj, e, hS⟩))⟩
        · have hHWf := hwf.groups_wf h' hh0
          have hHdrDisj := hDisj.2.2.1 h' hh0
          have hHMem48 : h'.mem.toNat + 9 ≤ 2 ^ 64 := by
            have := hHWf.2.2.2.2.2.2.1; have := hHWf.2.2.2.2.2.2.2.1; omega
          have hAllH : h'.metaPtr ∈ allMetaSlots st :=
            (hwf.free_bump_metas_wf.2.2.2.2.2 h'.metaPtr).mp
              (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hh0))))
          refine ⟨hHWf.1, hHWf.2.1, hHWf.2.2.1, hHWf.2.2.2.1, hHWf.2.2.2.2.1, hHWf.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.1,
            (hBvOut _ hHdrDisj.2).trans hHWf.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.2.1,
            hParentLift h' hh0, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            by rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
                 hBvOut a (hDisj.2.1 h'.metaPtr hAllH hNeM a ha)]
               exact hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            by rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
                 hBvOut a (hHdrDisj.1 a ((inRegion_iff_toNat (by omega) a).mpr
                   (by have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha; omega)))]
               exact hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (hBvOut (h'.mem + 8#64) (hHdrDisj.1 (h'.mem + 8#64)
              ((inRegion_iff_toNat (by omega) (h'.mem + 8#64)).mpr
                ⟨by rw [bv64_add_toNat (by omega)]; omega,
                 by rw [bv64_add_toNat (by omega)]; omega⟩))).trans
              hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun j hj => slotWf_other_of_slotWriteMod hwf hg hIdx hNotNested hBvOut hNestedMap
              hh0 hj (Or.inl hNeM) rfl rfl rfl rfl rfl rfl rfl rfl rfl
              (fun u r e hS => hLiveOv u r ((hwf.liveMap_wf u r).mpr ⟨h', hh0, j, hj, e, hS⟩))⟩
      regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
      active_wf := fun sc h1 h2 => by
        have hAct := hwf.active_wf sc h1 h2
        obtain ⟨pre, post, hGsSplit, hPreNe, _, _, _⟩ := split_groups_at_mem hwf.groups_nodup.1 hg
        have hFindG : st.groups.find? (·.metaPtr == g.metaPtr) = some g := by
          rw [hGsSplit, List.find?_append, List.find?_cons]
          have hPreNone : pre.find? (·.metaPtr == g.metaPtr) = none :=
            List.find?_eq_none.mpr fun h hh => by simp [hPreNe h hh]
          simp [hPreNone]
        have hFindMap : ∀ m : BitVec 64,
            (findGroupByMeta st1 m).map (fun h => (h.metaPtr, h.prev, h.next)) =
            (findGroupByMeta st m).map (fun h => (h.metaPtr, h.prev, h.next)) := fun m => by
          unfold findGroupByMeta
          simp only [st1, hRep.2.2.2.2.2.2.2 m]
          by_cases hm : m == g.metaPtr
          · have hmEq : m = g.metaPtr := beq_iff_eq.mp hm; subst hmEq
            simp [hFindG, hMeta, hPrev, hNext]
          · simp [hm]
        have hFMapEq :
            ((st.activeLists[sc]'h2).filterMap fun m =>
              (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
            ((st.activeLists[sc]'h2).filterMap fun m =>
              (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
          congr 1; funext m; exact hFindMap m
        refine ⟨fun m hm => ?_, hFMapEq ▸ hAct.2.1, hFMapEq ▸ hAct.2.2.1,
          fun h' hh' hSc' => ?_, fun i hi hPos h' hh' hEqM => ?_,
          fun h₁ hh₁ h₂ hh₂ hSc₁ hSc₂ hLt₁ hLt₂ => ?_, fun h' hh' hSc' hLt => ?_⟩
        · obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct.1 m hm
          by_cases hEq : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq; subst hE
            exact ⟨g1, hRep.2.2.2.2.1, hMeta.trans hM0, hSc.trans hSc0⟩
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, hM0, hSc0⟩
        · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · have hSub := hAct.2.2.2.1 g hg (hSc.symm.trans hSc')
            refine ⟨by rw [hMeta, hPrev, hNext]; exact hSub.1, fun hNot => ?_⟩
            have hNotG : g.metaPtr ∉ st.activeLists[sc]'h2 := hMeta ▸ hNot
            have hScEq : g.sc = sc := hSc.symm.trans hSc'
            subst hScEq
            exact ⟨(hActNotMem h2 hNotG).1, (hActNotMem h2 hNotG).2,
              by rw [hActI, hLast]; exact (hSub.2 hNotG).2.2⟩
          · exact hAct.2.2.2.1 h' hh0 hSc'
        · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · have hSub := hAct.1 ((st.activeLists[sc]'h2)[i]'hi) (List.getElem_mem hi)
            obtain ⟨h0, hh0, hM0, hSc0⟩ := hSub
            have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg
              (hM0.trans (hEqM.symm.trans hMeta)); subst hE; subst hSc0
            exact hActTail h2 i hi hPos (hMeta.symm.trans hEqM)
          · exact hAct.2.2.2.2.1 i hi hPos h' hh0 hEqM
        · have ⟨h₁0, hh₁0, hM₁, hSc₁0, hLt₁0⟩ :
              ∃ h₁0 ∈ st.groups, h₁.metaPtr = h₁0.metaPtr ∧ h₁0.sc = sc ∧ h₁0.activeIdx < h₁0.lastIdx := by
            rcases hRep.2.2.2.2.2.1 h₁ hh₁ with rfl | ⟨hh0, _⟩
            · exact ⟨g, hg, hMeta, hSc.symm.trans hSc₁, by rwa [hActI, hLast] at hLt₁⟩
            · exact ⟨h₁, hh0, rfl, hSc₁, hLt₁⟩
          have ⟨h₂0, hh₂0, hM₂, hSc₂0, hLt₂0⟩ :
              ∃ h₂0 ∈ st.groups, h₂.metaPtr = h₂0.metaPtr ∧ h₂0.sc = sc ∧ h₂0.activeIdx < h₂0.lastIdx := by
            rcases hRep.2.2.2.2.2.1 h₂ hh₂ with rfl | ⟨hh0, _⟩
            · exact ⟨g, hg, hMeta, hSc.symm.trans hSc₂, by rwa [hActI, hLast] at hLt₂⟩
            · exact ⟨h₂, hh0, rfl, hSc₂, hLt₂⟩
          exact hM₁.trans ((hAct.2.2.2.2.2.1 h₁0 hh₁0 h₂0 hh₂0 hSc₁0 hSc₂0 hLt₁0 hLt₂0).trans hM₂.symm)
        · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · rw [hMeta]; exact hAct.2.2.2.2.2.2 g hg (hSc.symm.trans hSc') (by rwa [hActI, hLast] at hLt)
          · exact hAct.2.2.2.2.2.2 h' hh0 hSc' hLt
      liveMap_wf := hLiveMap1
      live_le_peak := hLivePeak
      effCost_le_live := hEffLe
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun h' hh' hEmp => by
        rcases hRep.2.2.2.2.2.1 h' hh' with hEqH | ⟨hh0, _⟩
        · subst h'
          obtain ⟨e1, e2, e3, e4, e5, e7⟩ := hEmpty1 hEmp
          refine ⟨e1, e2, e3, e4, fun hLt => ?_, fun g' hg' hEmp' hSc' => ?_, e7⟩
          · rw [e5 hLt]; exact List.mem_singleton_self _
          · rcases hRep.2.2.2.2.2.1 g' hg' with hEqG | ⟨hg0, _⟩
            · subst g'; rfl
            · have hLtSc : g1.sc < st.activeLists.length := by
                have := hwf.ctx_lens.2.2.2.2.2; omega
              have hLtSc' : g'.sc < st.activeLists.length := by omega
              have hIn := (hwf.empty_groups_bound g' hg0 hEmp').2.2.2.2.1 hLtSc'
              have hOpt : st.activeLists[g'.sc]? = some [g1.metaPtr] := by
                rw [hSc', List.getElem?_eq_getElem hLtSc, e5 hLtSc]
              have hEqL : st.activeLists[g'.sc]'hLtSc' = [g1.metaPtr] :=
                Option.some.inj ((List.getElem?_eq_getElem hLtSc').symm.trans hOpt)
              rw [hEqL] at hIn
              exact List.mem_singleton.mp hIn
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound h' hh0 hEmp
          refine ⟨e1, e2, e3, e4, e5, fun g' hg' hEmp' hSc' => ?_, e7⟩
          rcases hRep.2.2.2.2.2.1 g' hg' with hEqG | ⟨hg0, _⟩
          · subst g'
            obtain ⟨_, _, _, _, e5_1, _⟩ := hEmpty1 hEmp'
            have hLtSc : h'.sc < st.activeLists.length := by
              have := hwf.ctx_lens.2.2.2.2.2; omega
            have hLtSc1 : g1.sc < st.activeLists.length := by omega
            have hIn := e5 hLtSc
            have hOpt : st.activeLists[h'.sc]? = some [g1.metaPtr] := by
              rw [← hSc', List.getElem?_eq_getElem hLtSc1, e5_1 hLtSc1]
            have hEqL : st.activeLists[h'.sc]'hLtSc = [g1.metaPtr] :=
              Option.some.inj ((List.getElem?_eq_getElem hLtSc).symm.trans hOpt)
            rw [hEqL] at hIn
            exact (List.mem_singleton.mp hIn).symm
          · exact e6 g' hg0 hEmp' hSc'
      masterDom_wf := ⟨hwf.masterDom_wf.1, fun a hAny => by
        rcases hAny with hRw | hProt | hMap
        · exact hOwnDom a hRw
        · exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hProt))
        · refine hwf.masterDom_wf.2.1 a (Or.inr (Or.inr ?_))
          unfold OwnedMappedByte at hMap ⊢
          rcases hMap with h1 | h2 | h3 | ⟨h', hh', hMp', hIn'⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h3))
          · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
            · exact Or.inr (Or.inr (Or.inr ⟨g, hg, hMaplen ▸ hMp', hMem ▸ hMaplen ▸ hIn'⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨h', hh0, hMp', hIn'⟩)),
        fun a ha => hDynEq.symm ▸ hwf.masterDom_wf.2.2 a ha⟩ }

/-! ## `__libc_free` Entry `.liveUser` Slot Release -/

set_option maxHeartbeats 400000 in
/-- Pure invariant transition for `__libc_free` entry release (`mkReleasedSt st g idx p bs`):
    transitions `MallocngWF` (`inflight = 0`) at budget `b` to `MallocngWFInflight 1` at
    `bf = mallocngFreeBudget false n b` with `g1.slots[idx] = .claimed`. -/
theorem free_release_userSlot_wf {base brkStart brk : BitVec 64}
    {b : MallocngBudget} {ivs : List (BitVec 64 × Nat)} {st : MallocngSt}
    (γ : GhostName)
    (hwf : MallocngWF base brkStart brk b.liveCost b.peakCost st)
    (hCntIvs : MallocngCountIvsWF b ivs st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {n effCost : Nat} (hSlot : g.slots[idx]'hIdx = .liveUser p n effCost)
    {bs : List (BitVec 8)} (hBsLen : bs.length = n) :
    let g1 := mkReleasedGroup g idx
    let st1 := mkReleasedSt st g idx p bs
    let bf := mallocngFreeBudget false n b
    g1 ∈ st1.groups ∧
    g1.slots.length = g.slots.length ∧
    (∀ hIdx1 : idx < g1.slots.length, g1.slots[idx]'hIdx1 = .claimed) ∧
    MallocngCountIvsWF bf ivs st1 ∧
    MallocngWFInflight 1 base brkStart brk bf.liveCost bf.peakCost st1 ∧
    (EmptyGroupKeepWf st → EmptyGroupKeepWf st1) := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let g1 := mkReleasedGroup g idx
  let st1 := mkReleasedSt st g idx p bs
  let bf := mallocngFreeBudget false n b
  have hSpat := free_release_userSlot_spatial γ hwf hg hIdx hSlot hBsLen
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g1)
  have hGWf := hwf.groups_wf g hg
  have ⟨_, _, hStNat, hSub4Nat, hEnNat, _, hEn48, _, hEnMod12⟩ := group_slot_bounds hGWf hIdx
  have ⟨hStrGe16, _⟩ := group_stride_pos_and_align hGWf
  have hSMG : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hSWf := hGWf.slot_wf idx hIdx
  rw [hSlot] at hSWf
  have hBlkWf : MallocngBlockWf p n := hSWf.2.2.2.2.1
  have hPLo : (g.slotStart idx).toNat ≤ p.toNat := hSWf.2.2.2.2.2.1
  have hPHi : p.toNat + n ≤ (g.slotEnd idx).toNat := hSWf.2.2.2.2.2.2.1
  have hEffGe : max n MallocngMinBlockCost ≤ effCost := hSWf.2.2.2.2.2.2.2.1
  have hPSub3 := bv64_sub_toNat (a := p) (n := 3) (by omega)
  have hBvOut : ∀ a : BitVec 64, ¬ SlotWriteMod g idx a → st1.byteVal a = st.byteVal a := by
    intro a hNotMod
    have hNotP : ¬ InRegion p bs.length a := fun hInP => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp (hBsLen ▸ hInP)
      exact hNotMod (Or.inr ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
        fun hEq => by have := congrArg BitVec.toNat hEq; omega⟩)
    have hNotH3 : ¬ InRegion (p - 3#64) 3 a := fun hInH3 => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hInH3
      exact hNotMod (Or.inr ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩,
        fun hEq => by have := congrArg BitVec.toNat hEq; omega⟩)
    simp only [st1, mkReleasedSt]
    rw [writeBytesToMap_out _ _ _ hNotP, writeBytesToMap_out _ _ _ hNotH3]
  have hDisj := slotWriteMod_disjoint hwf hg hIdx (by simp [hSlot])
  have hAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf hAllG
  obtain ⟨rgG, hrgG, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
  have hRgTot : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
  have hRg48 : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
  have hMetaDisj : ∀ a : BitVec 64, InRegion g.metaPtr 40 a → st1.byteVal a = st.byteVal a := by
    intro a ha
    have hDisjMaRg := metaArea_disjoint_root_group hwf hmaG hrgG hRgMp
    have hNotRg : ¬ InRegion rgG.mem (rgG.maplen * 4096) a := fun hInRg =>
      not_both_inRegion_of_disjointRegions hDisjMaRg (hInMaG a ha) hInRg
    have hNotP : ¬ InRegion p bs.length a := fun hInP => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp (hBsLen ▸ hInP)
      exact hNotRg ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    have hNotH3 : ¬ InRegion (p - 3#64) 3 a := fun hInH3 => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hInH3
      exact hNotRg ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    simp only [st1, mkReleasedSt]
    rw [writeBytesToMap_out _ _ _ hNotP, writeBytesToMap_out _ _ _ hNotH3]
  have hCountSum : totalLiveCount st1 + 1 = totalLiveCount st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotLiveCount).sum) (g1 := g1)
    have hS := list_set_map_sum g.slots hIdx .claimed slotLiveCount
    rw [hSlot] at hS
    unfold totalLiveCount
    simp only [st1, mkReleasedSt, g1, mkReleasedGroup, slotLiveCount] at hG hS ⊢
    omega
  have hEffSum : totalLiveEffCost st1 + effCost = totalLiveEffCost st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotEffCost).sum) (g1 := g1)
    have hS := list_set_map_sum g.slots hIdx .claimed slotEffCost
    rw [hSlot] at hS
    unfold totalLiveEffCost
    simp only [st1, mkReleasedSt, g1, mkReleasedGroup, slotEffCost] at hG hS ⊢
    omega
  have hClaimSum : totalClaimedSlots st1 = totalClaimedSlots st + 1 := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := g1)
    have hS := list_set_filter_len g.slots hIdx .claimed SlotState.isClaimed
    rw [hSlot] at hS
    unfold totalClaimedSlots
    simp only [st1, mkReleasedSt, g1, mkReleasedGroup, SlotState.isClaimed,
      Bool.false_eq_true, ↓reduceIte] at hG hS ⊢
    omega
  have hCntIvs1 : MallocngCountIvsWF bf ivs st1 := by
    obtain ⟨hLP, hTotL, hIvsEq, hIvsLen, hMaLen⟩ := hCntIvs
    have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
      unfold dynamicRootRegions; dsimp only [st1, mkReleasedSt, g1] at hRep ⊢; rw [hRep.2.2.1]
    refine ⟨by simp [bf, mallocngFreeBudget]; omega,
      by simp [bf, mallocngFreeBudget]; omega,
      hIvsEq.trans hDynEq.symm,
      by simpa [bf, mallocngFreeBudget] using hIvsLen,
      by simpa [st1, mkReleasedSt, bf, mallocngFreeBudget] using hMaLen.1,
      by
        simp only [st1, mkReleasedSt, bf, mallocngFreeBudget, replaceGroupByMeta]
        exact hMaLen.2.map_ite g.metaPtr fun hm hs => hMaLen.2 g hg hm hs⟩
  have hLiveMap1 : ∀ (q : BitVec 64) (r : Nat),
      st1.liveMap q = some r ↔
        ∃ h' ∈ st1.groups, ∃ j : Nat, ∃ hj : j < h'.slots.length, ∃ c : Nat,
          h'.slots[j]'hj = .liveUser q r c := by
    intro q r
    simp only [st1, mkReleasedSt, MallocngLiveMap.erase_req]
    by_cases hqp : q = p
    · subst hqp
      simp only [↓reduceIte, reduceCtorEq, false_iff]
      rintro ⟨h', hh', j, hj', c, hSlot'⟩
      have ⟨h0, hh0, hj0, hDiff, hSlot0⟩ :
          ∃ h0 ∈ st.groups, ∃ hj0 : j < h0.slots.length,
            (g ≠ h0 ∨ idx ≠ j) ∧ h0.slots[j]'hj0 = .liveUser q r c := by
        rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, hNeM⟩
        · have hj0 : j < g.slots.length := by simpa [g1, mkReleasedGroup] using hj'
          by_cases hjEq : j = idx
          · subst hjEq; simp [g1, mkReleasedGroup] at hSlot'
          · simp only [g1, mkReleasedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
            exact ⟨g, hg, hj0, Or.inr (Ne.symm hjEq), hSlot'⟩
        · exact ⟨h', hh0, hj', Or.inl (fun hE => hNeM (congrArg GroupDesc.metaPtr hE.symm)), hSlot'⟩
      have hSWf0 := (hwf.groups_wf h0 hh0).slot_wf j hj0
      rw [hSlot0] at hSWf0
      have ⟨_, _, hSt0, hSub4_0, hEn0, _, h48_0, _, hEnMod0⟩ := group_slot_bounds (hwf.groups_wf h0 hh0) hj0
      have ⟨hStr0, _⟩ := group_stride_pos_and_align (hwf.groups_wf h0 hh0)
      have hSM0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
      have hPLo0 : (h0.slotStart j).toNat ≤ q.toNat := hSWf0.2.2.2.2.2.1
      have hPHi0 : q.toNat + r ≤ (h0.slotEnd j).toNat := hSWf0.2.2.2.2.2.2.1
      have hPMod16 : q.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hBlkWf.2.1
      have hPLtG : q.toNat < (g.slotEnd idx).toNat := by omega
      have hPLt0 : q.toNat < (h0.slotEnd j).toNat := by omega
      exact nonNested_slotSlice_disjoint hwf hg hIdx (by simp [hSlot]) hh0 hj0 (by simp [hSlot0]) hDiff
        ((inRegion_iff_toNat (by omega) q).mpr ⟨by omega, by omega⟩)
        ((inRegion_iff_toNat (by omega) q).mpr ⟨by omega, by omega⟩)
    · simp only [hqp, ↓reduceIte, hwf.liveMap_wf q r]
      constructor
      · rintro ⟨h0, hh0, j, hj0, c, hSlot0⟩
        by_cases hEq : h0.metaPtr = g.metaPtr
        · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq; subst hE
          have hjNe : j ≠ idx := fun hJ => by
            subst hJ; rw [hSlot] at hSlot0; injection hSlot0 with hQP; exact hqp hQP.symm
          refine ⟨g1, hRep.2.2.2.2.1, j, by simp [g1, mkReleasedGroup, hj0], c, ?_⟩
          simp only [g1, mkReleasedGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hSlot0]
        · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, j, hj0, c, hSlot0⟩
      · rintro ⟨h', hh', j, hj', c, hSlot'⟩
        rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
        · have hj0 : j < g.slots.length := by simpa [g1, mkReleasedGroup] using hj'
          by_cases hjEq : j = idx
          · subst hjEq; simp [g1, mkReleasedGroup] at hSlot'
          · simp only [g1, mkReleasedGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
            exact ⟨g, hg, j, hj0, c, hSlot'⟩
        · exact ⟨h', hh0, j, hj', c, hSlot'⟩
  have hNotEmp1 : g1.isEmpty = false := by
    cases hE : g1.isEmpty with
    | false => rfl
    | true =>
      have hIdx1 : idx < g1.slots.length := by simp [g1, mkReleasedGroup, hIdx]
      have hMemC : SlotState.claimed ∈ g1.slots := by
        have hGet : g1.slots[idx]'hIdx1 = .claimed := by simp [g1, mkReleasedGroup]
        exact hGet ▸ List.getElem_mem hIdx1
      have hAll := List.all_eq_true.mp hE .claimed hMemC
      simp [SlotState.isFree] at hAll
  refine ⟨hRep.2.2.2.2.1, by simp [mkReleasedGroup], fun _ => by simp [mkReleasedGroup],
    hCntIvs1, ?_, fun hKeep h' hh' hMp h7 h38 => ?_⟩
  · refine wf_of_inPlaceSlotMod hwf hg hIdx (by simp [hSlot])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ _ => ⟨rfl, rfl⟩)
      hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hBvOut
      (by have hMPtr : (mkReleasedGroup g idx).metaPtr = g.metaPtr := rfl
          have hMB : (mkReleasedGroup g idx).metaBytes = g.metaBytes := rfl
          rw [hMPtr, hMB]
          exact (readBytesFromMap_eq_of_inRegion (by decide) hMetaDisj).trans
            hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (by dsimp only [SlotWf]
          have hStartEq : (mkReleasedGroup g idx).slotStart idx = g.slotStart idx := rfl
          have hActEq : (mkReleasedGroup g idx).activeIdx = g.activeIdx := rfl
          rw [hStartEq, hActEq]
          refine ⟨(hBvOut _ fun hM => ?_).trans hSWf.1,
            ⟨fun hAv => False.elim (by have := hSWf.2.1.mp hAv; cases this), fun hC => by cases hC⟩,
            ⟨fun hFr => False.elim (by have := hSWf.2.2.1.mp hFr; cases this), fun hC => by cases hC⟩,
            fun hLt => False.elim (by have := hSWf.2.2.2.1 hLt; cases this), trivial⟩
          rcases hM with hInM | ⟨_, hNe⟩
          · exact not_both_inRegion_of_disjointRegions
              (metaArea_disjoint_root_group hwf hmaG hrgG hRgMp) (hInMaG _ hInM)
              ((inRegion_iff_toNat (by omega) (g.slotStart idx - 4#64)).mpr ⟨by omega, by omega⟩)
          · exact hNe rfl)
      (fun hScLt hNot => by
        have hSc48 : g.sc < 48 := by
          rcases hGWf.1 with h48 | h63; exact h48; rw [hwf.ctx_lens.2.2.2.2.2] at hScLt; omega
        have hAct := hwf.active_wf g.sc (by rw [hwf.ctx_lens.1]; exact hSc48) hScLt
        exact ⟨((hAct.2.2.2.1 g hg rfl).2 hNot).1, ((hAct.2.2.2.1 g hg rfl).2 hNot).2.1⟩)
      (fun hScLt i hi hPos hEqM => by
        have hSc48 : g.sc < 48 := by
          rcases hGWf.1 with h48 | h63; exact h48; rw [hwf.ctx_lens.2.2.2.2.2] at hScLt; omega
        have hAct := hwf.active_wf g.sc (by rw [hwf.ctx_lens.1]; exact hSc48) hScLt
        exact hAct.2.2.2.2.1 i hi hPos g hg hEqM)
      (fun hEmp => by rw [hNotEmp1] at hEmp; cases hEmp)
      (by have := hwf.inflight_wf; dsimp only [st1, mkReleasedSt, g1] at hClaimSum ⊢; omega)
      (by have := hwf.live_le_peak; simp [ mallocngFreeBudget]; omega)
      (by have := hwf.effCost_le_live
          simp only [st1, mkReleasedSt, mallocngFreeBudget, Bool.false_eq_true, ↓reduceIte] at hEffSum ⊢
          omega)
      hLiveMap1
      (fun a hRw => by
        rcases (hSpat.2.1 a).mp hRw with hOld | hInP
        · exact hwf.masterDom_wf.2.1 a (Or.inl hOld)
        · exact hwf.masterDom_wf.2.1 a (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr ⟨rgG, hrgG, hRgMp, by
              have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp hInP
              exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩⟩))))))
  · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
    · exact hKeep g hg hMp h7 h38
    · exact hKeep h' hh0 hMp h7 h38

/-! ## Spatial Framing for In-Place `struct meta` Updates -/

/-- When `g -> g1` only changes a `.claimed` slot `idx` to `.freeAvail` or `.freeInactive` and
    writes `g1.metaBytes` (`40` B) at `g.metaPtr`, `OwnedRwByte`, `ProtNoneByteMap`, and
    `MappedSet` are invariant and `(g.metaPtr ↦ₛ g1.metaBytes)` absorbs back into `ByteMap`. -/
theorem metaBytes_update_spatial {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g g1 : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hSlot : g.slots[idx]'hIdx = .claimed)
    {s1 : SlotState} (hS1NotUser : ∀ u r c, s1 ≠ .liveUser u r c)
    (hMeta : g1.metaPtr = g.metaPtr) (hMem : g1.mem = g.mem)
    (hMaplen : g1.maplen = g.maplen) (hSc : g1.sc = g.sc) (hLast : g1.lastIdx = g.lastIdx)
    (hSlots : g1.slots = g.slots.set idx s1) :
    let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
    let st1 := { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1 }
    (∀ a : BitVec 64, InRegion g.metaPtr 40 a → OwnedRwByte st a ∧ a ∈ st.masterDom) ∧
    (∀ a : BitVec 64, OwnedRwByte st1 a ↔ OwnedRwByte st a) ∧
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) ∧
    (((g.metaPtr ↦ₛ g1.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) := by
  dsimp only []
  let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
  let st1 : MallocngSt := { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1 }
  have hMetaOwn := (meta_ownedRw_of_mem_groups hwf hg).2.2.2.2
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg hMeta hMem hMaplen hSc hLast
  have hRootEq : ∀ a : BitVec 64,
      (∃ h ∈ st1.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) ↔
      (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a) := by
    intro a; constructor
    · rintro ⟨h, hh, hMp, hIn⟩
      rcases hRep.2.2.2.2.2.1 h hh with rfl | ⟨hh0, _⟩
      · exact ⟨g, hg, hMaplen ▸ hMp, hMem ▸ hMaplen ▸ hIn⟩
      · exact ⟨h, hh0, hMp, hIn⟩
    · rintro ⟨h, hh, hMp, hIn⟩
      by_cases hEq : h.metaPtr = g.metaPtr
      · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hEq; subst hE
        exact ⟨g1, hRep.2.2.2.2.1, hMaplen.symm ▸ hMp, hMem.symm ▸ hMaplen.symm ▸ hIn⟩
      · exact ⟨h, hRep.2.2.2.2.2.2.1 h hh hEq, hMp, hIn⟩
  have hCarvedEq : ∀ a : BitVec 64, CarvedUserByte st1 a ↔ CarvedUserByte st a := by
    intro a; constructor
    · rintro ⟨h', hh', s, hs, hSub⟩
      obtain ⟨j, hj', hEqS⟩ := List.getElem_of_mem hs
      rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
      · have hj : j < g.slots.length := by simpa [hSlots] using hj'
        by_cases hjEq : j = idx
        · subst hjEq; simp only [hSlots, List.getElem_set_self] at hEqS; subst hEqS
          cases s1 with
          | liveUser u r c => exact False.elim (hS1NotUser u r c rfl)
          | _ => simp at hSub
        · simp only [hSlots, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hEqS
          exact ⟨g, hg, s, hEqS ▸ List.getElem_mem hj, hSub⟩
      · exact ⟨h', hh0, s, hs, hSub⟩
    · rintro ⟨h0, hh0, s, hs, hSub⟩
      obtain ⟨j, hj0, hEqS⟩ := List.getElem_of_mem hs
      by_cases hEq : h0.metaPtr = g.metaPtr
      · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq; subst hE
        by_cases hjEq : j = idx
        · subst hjEq; rw [← hEqS, hSlot] at hSub; simp at hSub
        · have hj1 : j < g1.slots.length := by simp [hSlots, hj0]
          have hGet1 : g1.slots[j]'hj1 = s := by
            simp only [hSlots, List.getElem_set, Ne.symm hjEq, ↓reduceIte, hEqS]
          exact ⟨g1, hRep.2.2.2.2.1, s, hGet1 ▸ List.getElem_mem hj1, hSub⟩
      · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, s, hs, hSub⟩
  have hOwnEq : ∀ a : BitVec 64, OwnedRwByte st1 a ↔ OwnedRwByte st a := by
    intro a; unfold OwnedRwByte
    have hMaEq : st1.metaAreas = st.metaAreas := rfl
    have hCmEq : CarvedMetaByte st1 a ↔ CarvedMetaByte st a := Iff.rfl
    rw [hMaEq, hRootEq a, hCarvedEq a, hCmEq]
  have hMapEq : ∀ a : BitVec 64, OwnedMappedByte st1 a ↔ OwnedMappedByte st a := by
    intro a; unfold OwnedMappedByte
    change (_ ∨ _ ∨ _ ∨ (∃ h ∈ st1.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ↔ _
    rw [hRootEq a]
  have hAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf hAllG
  have hProtEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun _ _ => Iff.rfl) fun a _ hProt => ?_
    have ⟨hABC, _, _⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
    have ⟨hAB, _, hCrossAC⟩ := pairwiseDisjoint_append hABC
    have ⟨_, _, hCrossAB⟩ := pairwiseDisjoint_append hAB
    have hNotM : ¬ InRegion g.metaPtr g1.metaBytes.length a := fun hInM => by
      simp only [GroupDesc.metaBytes_length] at hInM
      rcases hProt with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
      · exact not_both_inRegion_of_disjointRegions
          (hCrossAB (maG.base, 4096) (List.mem_map_of_mem hmaG) (gp, 4096) (List.mem_map_of_mem hgp))
          (hInMaG a hInM) haGp
      · exact not_both_inRegion_of_disjointRegions
          (hCrossAC (maG.base, 4096) (List.mem_append_left _ (List.mem_map_of_mem hmaG))
            (ap, 4096) (List.mem_map_of_mem hap))
          (hInMaG a hInM) haAp
    simp only [st1, bv1]
    rw [writeBytesToMap_out _ _ _ hNotM]
  refine ⟨hMetaOwn, hOwnEq, hProtEq, SetSep_congr (fun a _ => hMapEq a) (fun _ _ _ => rfl), ?_⟩
  rw [ByteMap_absorb_slice hwf.masterDom_wf.1 st.byteVal g.metaPtr g1.metaBytes
    (by rw [GroupDesc.metaBytes_length]; decide)
    (fun a ha => (hMetaOwn a (by simpa using ha)).2)
    (fun _ hIn ⟨_, hN⟩ => hN (by simpa using hIn))]
  exact SetSep_congr (fun a _ => by
    rw [GroupDesc.metaBytes_length]
    exact ⟨fun h => (hOwnEq a).mpr (h.elim And.left (fun ha => (hMetaOwn a ha).1)),
      fun h => by
        by_cases ha : InRegion g.metaPtr 40 a
        · exact Or.inr ha
        · exact Or.inl ⟨(hOwnEq a).mp h, ha⟩⟩)
    (fun _ _ _ => rfl)

end VerifiedLibraries.Mallocng.Proofs

