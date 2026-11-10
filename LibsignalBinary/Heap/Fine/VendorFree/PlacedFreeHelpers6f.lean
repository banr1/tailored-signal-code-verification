/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-
Invariant-transition helpers for nested-group retirement in multi-block `nontrivial_free`:
bitfield extractions (`packedWord_low8_low16`, `nestedHdr_extract`) for parent validation at
`+0x308..+0x3f8`, and `free_retire_nestedGroup` for retiring an all-free nested group (`g.maplen = 0`)
and clearing `[g.mem, +8)` at `+0x3fc`.
-/
public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers6e
public import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

@[expose] public section

/-! ## Bitfield and Sub-Word Unpack Lemmas (`+0x308..+0x3f8`) -/

theorem packedWord_low8_low16 (h : GroupDesc) (hLast : h.lastIdx ≤ 31) (hSc : h.sc < 48) :
    ((h.packedWord.truncate 8).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 h.lastIdx ∧
    (((h.packedWord.truncate 16).zeroExtend 64) >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 h.sc := by
  unfold GroupDesc.packedWord
  have h1 :
      ∀ a b c : BitVec 64,
        (((((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)).truncate 8).zeroExtend 32) &&&
          0x1f#32) = (a &&& 0x1f#64).truncate 32 := by
    intro a b c; bv_robdd
  have h2 :
      ∀ a b c : BitVec 64,
        ((((((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)).truncate 16).zeroExtend 64) >>> 6) &&&
          0x3f#64) = b &&& 0x3f#64 := by
    intro a b c; bv_robdd
  rw [h1, h2]
  have hL : (BitVec.ofNat 64 h.lastIdx).ult 32#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change h.lastIdx % 2 ^ 64 < 32; omega
  have hS : (BitVec.ofNat 64 h.sc).ult 64#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change h.sc % 2 ^ 64 < 64; omega
  rw [show BitVec.ofNat 32 h.lastIdx = (BitVec.ofNat 64 h.lastIdx).truncate 32 by bv_omega]
  exact ⟨by revert hL; bv_robdd, by revert hS; bv_robdd⟩

theorem nestedHdr_extract (pIdx : Nat) (hIdx : pIdx ≤ 31) :
    ((BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 pIdx := by
  have h1 : BitVec.ofNat 8 ((6 <<< 5) ||| pIdx) = (6#8 <<< 5) ||| BitVec.ofNat 8 pIdx := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    have hShLt : (6 : Nat) <<< 5 < 256 := by decide
    have hIdxMod : pIdx % 256 = pIdx := Nat.mod_eq_of_lt (by omega)
    have hOrLt : (6 <<< 5 ||| pIdx) < 256 := Nat.or_lt_two_pow (n := 8) hShLt (by omega)
    change (6 <<< 5 ||| pIdx) % 256 = ((6 <<< 5) % 256) ||| (pIdx % 256)
    rw [hIdxMod, Nat.mod_eq_of_lt hShLt, Nat.mod_eq_of_lt hOrLt]
  have hI : (BitVec.ofNat 8 pIdx).ult 32#8 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change pIdx % 256 < 32; omega
  rw [h1, show BitVec.ofNat 32 pIdx = (BitVec.ofNat 8 pIdx).zeroExtend 32 by bv_omega]
  revert hI; bv_robdd

private theorem sizeClass_pos_of_lt48 {sc : Nat} (hSc : sc < 48) :
    1 ≤ sizeClass sc ∧ 16 ≤ slotStride sc := by
  have hFin : ∀ s : Fin 48, 1 ≤ sizeClass s.1 := by decide
  have h1 : 1 ≤ sizeClass sc := hFin ⟨sc, hSc⟩
  exact ⟨h1, by unfold slotStride; omega⟩

private theorem pointsTo64_split_low8 (a w : BitVec 64) :
    ∃ R : SepProp, (a ↦₆₄ w) = ((a ↦₈ w.truncate 8) ∗ R) := by
  have hB0 : w.extractLsb' 0 8 = w.truncate 8 := by bv_robdd
  let tl := [w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8, w.extractLsb' 32 8,
    w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8]
  have hUnp : unpack64 w = [w.truncate 8] ++ tl := by unfold unpack64 tl; simp [hB0]
  refine ⟨(a + 1#64) ↦ₛ tl, ?_⟩
  rw [pointsTo64_eq_pointsToBytes, hUnp, pointsToBytes_append, pointsToBytes_singleton,
    List.length_singleton]

private theorem pointsTo64_split_low16 (a w : BitVec 64) :
    ∃ R : SepProp, (a ↦₆₄ w) = ((a ↦₁₆ w.truncate 16) ∗ R) := by
  have hB0 : w.extractLsb' 0 8 = (w.truncate 16).extractLsb' 0 8 := by bv_robdd
  have hB1 : w.extractLsb' 8 8 = (w.truncate 16).extractLsb' 8 8 := by bv_robdd
  let tl := [w.extractLsb' 16 8, w.extractLsb' 24 8, w.extractLsb' 32 8, w.extractLsb' 40 8,
    w.extractLsb' 48 8, w.extractLsb' 56 8]
  have hUnp : unpack64 w = unpack16 (w.truncate 16) ++ tl := by
    unfold unpack64 unpack16 tl; simp [hB0, hB1]
  refine ⟨(a + 2#64) ↦ₛ tl, ?_⟩
  rw [pointsTo64_eq_pointsToBytes, hUnp, pointsToBytes_append, ← pointsTo16_eq_pointsToBytes,
    unpack16_length]

/-! ## Parent Offset and Size-Class Bounds for Nested Groups -/

private theorem nested_parent_tot_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g pg0 : GroupDesc} (hg : g ∈ st.groups) (hpg0 : pg0 ∈ st.groups)
    {pIdx : Nat} (hp0 : pIdx < pg0.slots.length)
    (hScLe24 : pg0.sc ≤ 24)
    (hStartLe : (pg0.slotStart pIdx).toNat ≤ g.mem.toNat)
    (hEndLe : g.mem.toNat + g.nestedCap ≤ (pg0.slotEnd pIdx).toNat)
    (hCapEq : g.nestedCap = slotStride pg0.sc - 4) :
    let tot := (g.mem.toNat - pg0.storage.toNat) / 16
    g.mem &&& 0xf#64 = 0#64 ∧
    g.mem.toNat = pg0.mem.toNat + 16 + 16 * tot ∧
    pIdx * sizeClass pg0.sc ≤ tot ∧
    tot < (pIdx + 1) * sizeClass pg0.sc ∧
    (0 < pg0.maplen →
      BitVec.ofNat 64 (pg0.maplen * 4096) ≠ 0#64 ∧
      pg0.maplen * 4096 ≤ 65536 ∧
      1 ≤ pg0.maplen * 256 ∧
      tot ≤ pg0.maplen * 256 - 1) := by
  dsimp only []
  have hGWf := hwf.groups_wf g hg
  have hPgWf := hwf.groups_wf pg0 hpg0
  have hGMod16 : g.mem.toNat % 16 = 0 := hGWf.2.2.2.2.2.1
  have hPgMod16 : pg0.mem.toNat % 16 = 0 := hPgWf.2.2.2.2.2.1
  have hMemMask : g.mem &&& 0xf#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change g.mem.toNat &&& 15 = 0
    rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact hGMod16
  have ⟨hPgStrGe, _, hPgStor, hPgEndLast, _, hPgSlotCalc⟩ := group_slot_toNat hPgWf
  have hpCnt : pIdx < pg0.cnt := hPgWf.2.2.1 ▸ hp0
  have ⟨hPgSt, hPgEn, _⟩ := hPgSlotCalc pIdx hpCnt
  have ⟨hScPos, hSlotStrGe16⟩ := sizeClass_pos_of_lt48 (by omega : pg0.sc < 48)
  have hGMemEq : g.mem.toNat = pg0.mem.toNat + 16 + 16 * ((g.mem.toNat - pg0.storage.toNat) / 16) := by
    omega
  have hTotBounds :
      pIdx * sizeClass pg0.sc ≤ (g.mem.toNat - pg0.storage.toNat) / 16 ∧
      (g.mem.toNat - pg0.storage.toNat) / 16 < (pIdx + 1) * sizeClass pg0.sc := by
    by_cases hSingleRoot : pg0.lastIdx = 0 ∧ 0 < pg0.maplen
    · obtain ⟨hL0, hMpPos⟩ := hSingleRoot
      have hpZero : pIdx = 0 := by unfold GroupDesc.cnt at hpCnt; omega
      subst hpZero
      refine ⟨by simp, ?_⟩
      simp only [Nat.zero_add, Nat.one_mul]
      have hRootProps := hPgWf.2.2.2.2.2.2.2.2.2.2.2.1 hMpPos
      rcases (hRootProps.2.2.2 (by omega)).2 hL0 with hStrLe | ⟨hGe24, hAlign⟩
      · have : g.mem.toNat ≤ pg0.storage.toNat := by
          unfold slotStride at hCapEq hStrLe; omega
        omega
      · have hSc24 : pg0.sc = 24 := by omega
        rw [hSc24] at hAlign hCapEq ⊢
        have hSz24 : sizeClass 24 = 146 := by decide
        have hSt24 : slotStride 24 = 2336 := by decide
        have hPa24 : pageAlignUp (2336 + 16) = 4096 := by decide
        rw [hSt24, hPa24] at hAlign
        have hStr4080 : pg0.stride = 4080 := by
          simp [GroupDesc.stride, hL0, hMpPos]; omega
        rw [hSz24]; omega
    · have hCondF : (pg0.lastIdx == 0 && decide (0 < pg0.maplen)) = false := by
        cases hB1 : (pg0.lastIdx == 0)
        · simp
        · simp only [Bool.true_and, decide_eq_false_iff_not]
          exact fun hMp => hSingleRoot ⟨beq_iff_eq.mp hB1, hMp⟩
      have hStrEq : pg0.stride = 16 * sizeClass pg0.sc := by
        unfold GroupDesc.stride slotStride
        simp [hCondF]
      have hMul16 : pIdx * pg0.stride = 16 * (pIdx * sizeClass pg0.sc) := by
        rw [hStrEq, ← Nat.mul_assoc, Nat.mul_comm pIdx 16, Nat.mul_assoc]
      have hCap16 : g.nestedCap = 16 * sizeClass pg0.sc - 4 := by
        rw [hCapEq]; rfl
      have hAdd1 : (pIdx + 1) * sizeClass pg0.sc = pIdx * sizeClass pg0.sc + sizeClass pg0.sc :=
        Nat.succ_mul pIdx (sizeClass pg0.sc)
      have hMul16Succ : (pIdx + 1) * pg0.stride =
          16 * (pIdx * sizeClass pg0.sc) + 16 * sizeClass pg0.sc := by
        rw [Nat.succ_mul, hMul16, hStrEq]
      rw [hMul16] at hPgSt
      rw [hMul16Succ] at hPgEn
      rw [hAdd1]
      generalize pIdx * sizeClass pg0.sc = q at hPgSt hPgEn ⊢
      generalize sizeClass pg0.sc = s at hScPos hCap16 hPgSt hPgEn ⊢
      omega
  refine ⟨hMemMask, hGMemEq, hTotBounds.1, hTotBounds.2, fun hMpPos => ?_⟩
  have hRootProps := hPgWf.2.2.2.2.2.2.2.2.2.2.2.1 hMpPos
  have hLe64k : pg0.maplen * 4096 ≤ 65536 := hRootProps.2.2.1 (by omega)
  have hBvNe0 : BitVec.ofNat 64 (pg0.maplen * 4096) ≠ 0#64 := by
    intro hEq
    have hT := congrArg BitVec.toNat hEq
    simp only [BitVec.toNat_ofNat] at hT
    change (pg0.maplen * 4096) % 2 ^ 64 = 0 at hT
    have : 0 < pg0.maplen * 4096 ∧ pg0.maplen * 4096 < 2 ^ 64 := ⟨by omega, by omega⟩
    omega
  have hStrict := hPgWf.2.2.2.2.2.2.2.2.1 hMpPos
  have hTotPg : pg0.totalBytes = pg0.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
  have hMulLe : (pIdx + 1) * pg0.stride ≤ pg0.cnt * pg0.stride := Nat.mul_le_mul_right _ hpCnt
  have hSucc : (pIdx + 1) * pg0.stride = pIdx * pg0.stride + pg0.stride := Nat.succ_mul pIdx pg0.stride
  have hCapGe12 : 12 ≤ g.nestedCap := by omega
  exact ⟨hBvNe0, hLe64k, by omega, by omega⟩

/-! ## Intermediate Dequeue State (`stMid`) -/

set_option maxHeartbeats 400000 in
private theorem nested_stMid_wf {k : Nat} {base brkStart brk : BitVec 64}
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
    dynamicRootRegions stMid = dynamicRootRegions st := by
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
      obtain ⟨pg', hpg', hPgM', _, hPgMem', hPgCap', hPgSc'⟩ := hLiftNonG pg hpg hPgNeG
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
  exact ⟨hpgDeq, hRep.2.2.2.2.1, hWfMid, hOwnRwIff, hOwnMapIff, hLiveCntEq, hDynEq⟩

/-! ## Nested Group Validation and Retirement -/

set_option maxHeartbeats 800000 in
/-- Retires an all-free nested group `g` (`g.maplen = 0`) at `+0x304..+0x404`: carves
    `(g.metaPtr ↦ₛ gZero.metaBytes)`, extracts parent read-focuses and bounds, and updates
    `[g.mem, +8) ↦₆₄ 0#64` (`+0x3fc`) into `st1` with `pg1.slots[pIdx] = .claimed`. -/
theorem free_retire_nestedGroup {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    (_hKeep : EmptyGroupKeepWf st) (_hFull : FullQueueKeepWf st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hSlot : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMap0 : g.maplen = 0)
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq) :
    let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
    let keepAfterMeta : BitVec 64 → Prop := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a
    ∃ (pg0 : GroupDesc) (pIdx tot : Nat) (maPg : MetaAreaDesc),
      let pg1 : GroupDesc := { pg0 with slots := pg0.slots.set pIdx .claimed }
      let gs1 := replaceGroupByMeta gsDeq pg0.metaPtr pg1
      let bv1 := writeBytesToMap bvDeq g.mem (unpack64 0#64)
      let st1 : MallocngSt :=
        { st with
          ctx := { st.ctx with active := active1, usageByClass := usage1 }
          reservedMetas := g.metaPtr :: st.reservedMetas
          groups := gs1
          activeLists := actLists1
          byteVal := bv1 }
      ByteMap st.masterDom (OwnedRwByte st) bvDeq =
        ((g.metaPtr ↦ₛ gZero.metaBytes) ∗ ByteMap st.masterDom keepAfterMeta bvDeq) ∧
      g.mem &&& 0xf#64 = 0#64 ∧ pIdx ≤ pg0.lastIdx ∧ pg0.lastIdx ≤ 31 ∧ pg0.sc ≤ 24 ∧ tot ≤ 0xffff ∧
      ((BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 pIdx ∧
      g.mem + (-16#64 - ((BitVec.ofNat 32 tot <<< 4).signExtend 64)) = pg0.mem ∧
      ((pg0.packedWord.truncate 8).zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 pg0.lastIdx ∧
      ((pg0.availMask >>> BitVec.ofNat 32 pIdx).getLsbD 0 = false ∧
       (pg0.availMask >>> (BitVec.ofNat 32 pIdx &&& 31#32)).getLsbD 0 = false) ∧
      ((pg0.freedMask >>> BitVec.ofNat 32 pIdx).getLsbD 0 = false ∧
       (pg0.freedMask >>> (BitVec.ofNat 32 pIdx &&& 31#32)).getLsbD 0 = false) ∧
      pg0.metaPtr &&& 0xfffffffffffff000#64 = maPg.base ∧
      (((pg0.packedWord.truncate 16).zeroExtend 64) >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 pg0.sc ∧
      pIdx * sizeClass pg0.sc ≤ tot ∧ tot < (pIdx + 1) * sizeClass pg0.sc ∧
      pg0.packedWord &&& 0xfffffffffffff000#64 = BitVec.ofNat 64 (pg0.maplen * 4096) ∧
      (0 < pg0.maplen → BitVec.ofNat 64 (pg0.maplen * 4096) ≠ 0#64 ∧ pg0.maplen * 4096 ≤ 65536 ∧
        1 ≤ pg0.maplen * 256 ∧ tot ≤ pg0.maplen * 256 - 1) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
        (((g.mem - 4#64) ↦₈ 0#8) ∗ ((g.mem - 3#64) ↦₈ BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)) ∗
         ((g.mem - 2#64) ↦₁₆ BitVec.ofNat 16 tot) ∗ R)) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq = ((pg0.mem ↦₆₄ pg0.metaPtr) ∗ R)) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
        (((pg0.metaPtr ↦₆₄ pg0.prev) ∗ ((pg0.metaPtr + 8#64) ↦₆₄ pg0.next) ∗
          ((pg0.metaPtr + 16#64) ↦₆₄ pg0.mem) ∗ ((pg0.metaPtr + 24#64) ↦₃₂ pg0.availMask) ∗
          ((pg0.metaPtr + 28#64) ↦₃₂ pg0.freedMask) ∗ ((pg0.metaPtr + 32#64) ↦₆₄ pg0.packedWord)) ∗ R)) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq = (((pg0.metaPtr + 32#64) ↦₈ pg0.packedWord.truncate 8) ∗ R)) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq = (((pg0.metaPtr + 32#64) ↦₁₆ pg0.packedWord.truncate 16) ∗ R)) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq = ((maPg.base ↦₆₄ st.ctx.secret) ∗ R)) ∧
      (∃ R, ByteMap st.masterDom keepAfterMeta bvDeq = ((g.mem ↦₆₄ g.metaPtr) ∗ R) ∧
        ((g.mem ↦₆₄ 0#64) ∗ R) = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) ∧
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
      MappedSet st1.masterDom (OwnedMappedByte st1) = MappedSet st.masterDom (OwnedMappedByte st) ∧
      MallocngWFInflight (k + 2) base brkStart brk liveCost peakCost st1 ∧
      EmptyGroupKeepWf st1 ∧ FullQueueKeepWf st1 ∧ pg1 ∈ st1.groups ∧
      (∃ hp1 : pIdx < pg1.slots.length, pg1.slots[pIdx]'hp1 = .claimed) ∧
      pg1.metaPtr = pg0.metaPtr ∧ groupNestBound pg1 < groupNestBound g ∧
      g.metaPtr ∈ st1.reservedMetas ∧ st1.reservedMetas.erase g.metaPtr = st.reservedMetas ∧
      totalLiveCount st1 = totalLiveCount st ∧ dynamicRootRegions st1 = dynamicRootRegions st ∧
      pg0 ∈ gsDeq := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hGWf := hwf.groups_wf g hg
  obtain ⟨_, pg0, hpg0, pIdx, hp0, hParG, hPgSc48, hGScLt, hPgSc24, hSlotPg,
    hStartLe, hEndLe, hCapEq⟩ := hGWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
  have hPgWf0 := hwf.groups_wf pg0 hpg0
  have hPgSWf := hPgWf0.slot_wf pIdx hp0; rw [hSlotPg] at hPgSWf
  obtain ⟨_, hAvIff, hFrIff, _, _, cg, hcg, hCgM, _, _, _, _, _, hTot16, hHdrM4, hHdrM3, hHdrM2⟩ := hPgSWf
  have hCgEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hCgM; subst hCgEqG
  let tot := (cg.mem.toNat - pg0.storage.toNat) / 16
  have hpPgAll : pg0.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 pg0.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hpg0))))
  have hmGAll : cg.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 cg.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  obtain ⟨maPg, hmaPg, kPg, hkPg, _, hPgMetaNat, _, hMaPg48⟩ := metaSlot_in_metaArea hwf hpPgAll
  refine ⟨pg0, pIdx, tot, maPg, ?_⟩
  let gZero : GroupDesc := { cg with prev := 0#64, next := 0#64 }
  let keepAfterMeta : BitVec 64 → Prop := fun a => OwnedRwByte st a ∧ ¬ InRegion cg.metaPtr 40 a
  let pg1 : GroupDesc := { pg0 with slots := pg0.slots.set pIdx .claimed }
  let gs1 := replaceGroupByMeta gsDeq pg0.metaPtr pg1
  let bv1 := writeBytesToMap bvDeq cg.mem (unpack64 0#64)
  let stMid : MallocngSt :=
    { st with
      ctx := { st.ctx with active := active1, usageByClass := usage1 }
      reservedMetas := cg.metaPtr :: st.reservedMetas
      groups := gs1
      activeLists := actLists1
      byteVal := bvDeq }
  let st1 : MallocngSt :=
    { st with
      ctx := { st.ctx with active := active1, usageByClass := usage1 }
      reservedMetas := cg.metaPtr :: st.reservedMetas
      groups := gs1
      activeLists := actLists1
      byteVal := bv1 }
  have ⟨hpgDeq, hpg1Mid, hWfMid, hOwnMidIff, hOwnMapMidIff, hLiveMid, hDynMid⟩ :=
    nested_stMid_wf hwf hg hpg0 hIdx hp0 hSlot hAllFree hMap0 hParG hGScLt hSlotPg hDeq
  have hDomNd := hwf.masterDom_wf.1
  have ⟨_, _, _, _, hGMetaOwn⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hCarveGMeta : ByteMap st.masterDom (OwnedRwByte st) bvDeq =
      ((cg.metaPtr ↦ₛ gZero.metaBytes) ∗ ByteMap st.masterDom keepAfterMeta bvDeq) := by
    rw [ByteMap_extract_slice hDomNd bvDeq cg.metaPtr (by decide)
      (fun a ha => (hGMetaOwn a ha).2) (fun a ha => (hGMetaOwn a ha).1), hDeq.g_zero_bytes]
  have hLast31 : pg0.lastIdx ≤ 31 := hPgWf0.2.1
  have hpLeLast : pIdx ≤ pg0.lastIdx := by have := hPgWf0.2.2.1; unfold GroupDesc.cnt at this; omega
  have ⟨hMemMask, hGMemEq, hTotLo, hTotHi, hRootPgProps⟩ :=
    nested_parent_tot_bounds hwf hg hpg0 hp0 hPgSc24 hStartLe hEndLe hCapEq
  have hHdrExt := nestedHdr_extract pIdx (by omega)
  have hPgMem48 : pg0.mem.toNat + 16 + 16 * tot ≤ 2 ^ 48 := by
    have : cg.totalBytes = cg.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
    have := hGWf.2.2.2.2.2.2.1; omega
  have hPgMemAddr := group_mem_addr_of_totalOff (p := cg.mem) (mem := pg0.mem) (tot := tot)
    (by omega) hPgMem48 hGMemEq
  have ⟨hLow8, hLow16⟩ := packedWord_low8_low16 pg0 hLast31 hPgSc48
  have hAvF : pg0.availMask.getLsbD pIdx = false := by
    cases hB : pg0.availMask.getLsbD pIdx
    · rfl
    · cases hAvIff.mp hB
  have hFrF : pg0.freedMask.getLsbD pIdx = false := by
    cases hB : pg0.freedMask.getLsbD pIdx
    · rfl
    · cases hFrIff.mp hB
  have hAvShift := mask_ushiftRight_bit0_false pg0.availMask (by omega) hAvF
  have hFrShift := mask_ushiftRight_bit0_false pg0.freedMask (by omega) hFrF
  have ⟨_, hMaMod, hMaHi, hMaHdr8, hMaOwn⟩ := metaArea_header_ownedRw hwf hmaPg
  have hPgPageMask : pg0.metaPtr &&& 0xfffffffffffff000#64 = maPg.base :=
    bv64_page_mask_eq (off := 24 + kPg * 40) hMaMod (by omega) (by omega)
  have hPgPackMask := packedWord_and_pageMask pg0
  have hp1 : pIdx < pg1.slots.length := by simp [pg1, hp0]
  have hSlotPg1 : pg1.slots[pIdx]'hp1 = .claimed := by simp [pg1]
  have hPg1WfMid := hWfMid.groups_wf pg1 hpg1Mid
  obtain ⟨rg, hrgMid, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hWfMid hpg1Mid
  change rg.mem.toNat ≤ pg0.mem.toNat at hRgLo
  change pg0.mem.toNat + pg0.totalBytes ≤ rg.mem.toNat + rg.maplen * 4096 at hRgHi
  have hRg48 : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
    have hRTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
    have := (hWfMid.groups_wf rg hrgMid).2.2.2.2.2.2.1; omega
  have ⟨_, _, hSt0Nat, hSub4_0Nat, hEn0Nat, hEnLeTot0, hTot0_48, _, _⟩ :=
    group_slot_bounds hPgWf0 hp0
  have ⟨hStr0Ge16, _⟩ := group_stride_pos_and_align hPgWf0
  have hSM0 : (pIdx + 1) * pg0.stride = pIdx * pg0.stride + pg0.stride :=
    Nat.succ_mul pIdx pg0.stride
  have hPgInRg : ∀ a, InRegion pg0.mem pg0.totalBytes a → InRegion rg.mem (rg.maplen * 4096) a := by
    intro a ha
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hSliceKeep : ∀ a : BitVec 64,
      InRegion (pg0.slotStart pIdx - 4#64) pg0.stride a → keepAfterMeta a ∧ a ∈ st.masterDom := by
    intro a ha0
    have ha1 : InRegion (pg1.slotStart pIdx - 4#64) pg1.stride a := ha0
    have ⟨hLoA, hHiA⟩ := (inRegion_iff_toNat (by omega) a).mp ha0
    have haInPg0 : InRegion pg0.mem pg0.totalBytes a :=
      (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    have haInRg : InRegion rg.mem (rg.maplen * 4096) a := hPgInRg a haInPg0
    have hNotCu : ¬ CarvedUserByte stMid a := by
      rintro ⟨h', hh', s', hs', hSub⟩
      obtain ⟨j', hj', hEqS'⟩ := List.getElem_of_mem hs'
      cases hS' : s' with
      | freeAvail | freeInactive | claimed | liveNested _ => simp [hS'] at hSub
      | liveUser u r c =>
        simp only [hS'] at hSub
        have hDiff : pg1 ≠ h' ∨ pIdx ≠ j' := by
          by_cases hE : pg1 = h'
          · subst hE
            exact Or.inr fun hJ => by
              subst hJ; rw [hSlotPg1] at hEqS'; rw [← hEqS'] at hS'; cases hS'
          · exact Or.inl hE
        have hHWf' := hWfMid.groups_wf h' hh'
        have hSW' := hHWf'.slot_wf j' hj'
        rw [hEqS'.trans hS'] at hSW'
        have ⟨_, _, hSt', hSub4', hEn', _, h48', _, _⟩ := group_slot_bounds hHWf' hj'
        have hSM' : (j' + 1) * h'.stride = j' * h'.stride + h'.stride := Nat.succ_mul j' h'.stride
        have hULo : (h'.slotStart j').toNat ≤ u.toNat := hSW'.2.2.2.2.2.1
        have hUHi : u.toNat + r ≤ (h'.slotEnd j').toNat := hSW'.2.2.2.2.2.2.1
        have ⟨hu1, hu2⟩ := (inRegion_iff_toNat (by omega) a).mp hSub
        exact nonNested_slotSlice_disjoint hWfMid hpg1Mid hp1 (by simp [pg1])
          hh' hj' (by simp [hEqS'.trans hS']) hDiff ha1
          ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
    have hNotCm : ¬ CarvedMetaByte stMid a := by
      rintro ⟨m, hmRes, haM⟩
      have hmAll : m ∈ allMetaSlots stMid :=
        (hWfMid.free_bump_metas_wf.2.2.2.2.2 m).mp (List.mem_append_right _ hmRes)
      obtain ⟨maM', hmaM', kM, hkM, _, hMNat, _, hMa48⟩ := metaSlot_in_metaArea hWfMid hmAll
      have ⟨hMLo, hMHi⟩ := (inRegion_iff_toNat (by omega) a).mp haM
      exact not_both_inRegion_of_disjointRegions
        (metaArea_disjoint_root_group hWfMid hmaM' hrgMid hRgMp)
        ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) haInRg
    have hOwnMid : OwnedRwByte stMid a := ⟨Or.inr ⟨rg, hrgMid, hRgMp, haInRg⟩, hNotCu, hNotCm⟩
    exact ⟨(hOwnMidIff a).mp hOwnMid, hWfMid.masterDom_wf.2.1 a (Or.inl hOwnMid)⟩
  have hDisjDeq := groupMetaMod_disjoint hwf hDeq.only_group_metas
  have ⟨hBvDataPg, _⟩ := hDisjDeq.2.2.2.2.2 pg0 hpg0
  have hCapGe12 : 12 ≤ cg.nestedCap := by
    have := (sizeClass_pos_of_lt48 hPgSc48).2; omega
  have hGGe : 4096 ≤ cg.mem.toNat := hGWf.2.2.2.2.1
  have hFocusHdr : ∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
      (((cg.mem - 4#64) ↦₈ 0#8) ∗
       ((cg.mem - 3#64) ↦₈ BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)) ∗
       ((cg.mem - 2#64) ↦₁₆ BitVec.ofNat 16 tot) ∗ R) := by
    have hSub4 := bv64_sub_toNat (a := cg.mem) (n := 4) (by omega)
    have hSub3 := bv64_sub_toNat (a := cg.mem) (n := 3) (by omega)
    have hSub2 := bv64_sub_toNat (a := cg.mem) (n := 2) (by omega)
    have hInSl : ∀ a, InRegion (cg.mem - 4#64) 4 a → InRegion (pg0.slotStart pIdx - 4#64) pg0.stride a := by
      intro a ha; have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    have hInData : ∀ a, InRegion (cg.mem - 4#64) 4 a → InRegion pg0.mem pg0.totalBytes a := by
      intro a ha; have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp (hInSl a ha)
      exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    have hRead4 : readBytesFromMap bvDeq (cg.mem - 4#64) 4 =
        [0#8, BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)] ++ unpack16 (BitVec.ofNat 16 tot) := by
      rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha => hBvDataPg a (hInData a ha)]
      unfold readBytesFromMap rangeAddrs; unfold readBytesFromMap rangeAddrs at hHdrM2
      have h0 : cg.mem - 4#64 + BitVec.ofNat 64 0 = cg.mem - 4#64 := by bv_arith
      have h1 : cg.mem - 4#64 + BitVec.ofNat 64 1 = cg.mem - 3#64 := by bv_arith
      have h2 : cg.mem - 4#64 + BitVec.ofNat 64 2 = cg.mem - 2#64 + BitVec.ofNat 64 0 := by bv_arith
      have h3 : cg.mem - 4#64 + BitVec.ofNat 64 3 = cg.mem - 2#64 + BitVec.ofNat 64 1 := by bv_arith
      simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil] at hHdrM2 ⊢
      rw [h0, h1, h2, h3, hHdrM4, hHdrM3, hHdrM2]
    refine ⟨ByteMap st.masterDom (fun a => keepAfterMeta a ∧ ¬ InRegion (cg.mem - 4#64) 4 a) bvDeq, ?_⟩
    rw [ByteMap_extract_slice hDomNd bvDeq (cg.mem - 4#64) (by decide)
      (fun a ha => (hSliceKeep a (hInSl a ha)).2) (fun a ha => (hSliceKeep a (hInSl a ha)).1), hRead4]
    have hSplit : ((cg.mem - 4#64) ↦ₛ ([0#8] ++ ([BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)] ++ unpack16 (BitVec.ofNat 16 tot)))) =
        (((cg.mem - 4#64) ↦₈ 0#8) ∗ ((cg.mem - 3#64) ↦₈ BitVec.ofNat 8 ((6 <<< 5) ||| pIdx)) ∗
         ((cg.mem - 2#64) ↦₁₆ BitVec.ofNat 16 tot)) := by
      rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_singleton, pointsToBytes_singleton, ← pointsTo16_eq_pointsToBytes]
      simp only [List.length_singleton,
        show cg.mem - 4#64 + BitVec.ofNat 64 1 = cg.mem - 3#64 by bv_arith,
        show cg.mem - 3#64 + BitVec.ofNat 64 1 = cg.mem - 2#64 by bv_arith]
    simpa only [List.cons_append, List.nil_append, sepConj_assoc] using congrArg (· ∗ _) hSplit
  have ⟨hPgMemRead0, _, hPgMemOwn⟩ := group_header_ownedRw hwf hpg0
  have hFocusPgMem : ∃ R, ByteMap st.masterDom keepAfterMeta bvDeq = ((pg0.mem ↦₆₄ pg0.metaPtr) ∗ R) := by
    have hTotPgGe16 : 16 ≤ pg0.totalBytes := by
      have := hPgWf0.2.2.2.2.2.2.2.1; have ⟨hSG, _⟩ := group_slot_toNat hPgWf0
      have h1 : 1 ≤ pg0.cnt := by unfold GroupDesc.cnt; omega
      have := Nat.le_trans hSG (Nat.le_mul_of_pos_left _ h1); omega
    have hInKeep : ∀ a, InRegion pg0.mem 8 a → keepAfterMeta a ∧ a ∈ st.masterDom := by
      intro a ha8; have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha8
      have ha16 : InRegion pg0.mem 16 a := (inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩
      have haTot : InRegion pg0.mem pg0.totalBytes a := (inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩
      have hNotGM : ¬ InRegion cg.metaPtr 40 a := fun haGM => by
        obtain ⟨maG, hmaG, kG, hkG, _, hGMNat, _, hMaG48⟩ := metaSlot_in_metaArea hwf hmGAll
        have ⟨g1, g2⟩ := (inRegion_iff_toNat (by omega) a).mp haGM
        exact not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hWfMid hmaG hrgMid hRgMp)
          ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩) (hPgInRg a haTot)
      exact ⟨⟨(hPgMemOwn a ha16).1, hNotGM⟩, (hPgMemOwn a ha16).2⟩
    refine ⟨ByteMap st.masterDom (fun a => keepAfterMeta a ∧ ¬ InRegion pg0.mem 8 a) bvDeq, ?_⟩
    rw [ByteMap_extract_slice hDomNd bvDeq pg0.mem (by decide) (fun a ha => (hInKeep a ha).2) (fun a ha => (hInKeep a ha).1),
      readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
        exact hBvDataPg a ((inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩),
      hPgMemRead0, ← pointsTo64_eq_pointsToBytes]
  have ⟨_, _, _, _, hPgMetaOwn⟩ := meta_ownedRw_of_mem_groups hwf hpg0
  have hPgNeG : pg0.metaPtr ≠ cg.metaPtr := fun hE => by
    have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg0 hg hE; subst hEq; omega
  have hFocusPgMeta : ∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
      (((pg0.metaPtr ↦₆₄ pg0.prev) ∗ ((pg0.metaPtr + 8#64) ↦₆₄ pg0.next) ∗
        ((pg0.metaPtr + 16#64) ↦₆₄ pg0.mem) ∗ ((pg0.metaPtr + 24#64) ↦₃₂ pg0.availMask) ∗
        ((pg0.metaPtr + 28#64) ↦₃₂ pg0.freedMask) ∗ ((pg0.metaPtr + 32#64) ↦₆₄ pg0.packedWord)) ∗ R) := by
    refine ⟨ByteMap st.masterDom (fun a => keepAfterMeta a ∧ ¬ InRegion pg0.metaPtr 40 a) bvDeq, ?_⟩
    rw [ByteMap_extract_slice hDomNd bvDeq pg0.metaPtr (by decide) (fun a ha => (hPgMetaOwn a ha).2)
      (fun a ha => ⟨(hPgMetaOwn a ha).1, fun haG => metaSlots_disjoint hwf hpPgAll hmGAll hPgNeG ha haG⟩),
      hDeq.each_meta_bytes pg0 hpgDeq, GroupDesc.metaBytes_pointsTo]
  have hFocusPacked8 : ∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
      (((pg0.metaPtr + 32#64) ↦₈ pg0.packedWord.truncate 8) ∗ R) := by
    obtain ⟨Rm, hFm⟩ := hFocusPgMeta
    obtain ⟨R8, hS8⟩ := pointsTo64_split_low8 (pg0.metaPtr + 32#64) pg0.packedWord
    refine ⟨R8 ∗ ((pg0.metaPtr ↦₆₄ pg0.prev) ∗ ((pg0.metaPtr + 8#64) ↦₆₄ pg0.next) ∗
      ((pg0.metaPtr + 16#64) ↦₆₄ pg0.mem) ∗ ((pg0.metaPtr + 24#64) ↦₃₂ pg0.availMask) ∗
      ((pg0.metaPtr + 28#64) ↦₃₂ pg0.freedMask)) ∗ Rm, ?_⟩; rw [hFm, hS8]; ac_rfl
  have hFocusPacked16 : ∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
      (((pg0.metaPtr + 32#64) ↦₁₆ pg0.packedWord.truncate 16) ∗ R) := by
    obtain ⟨Rm, hFm⟩ := hFocusPgMeta
    obtain ⟨R16, hS16⟩ := pointsTo64_split_low16 (pg0.metaPtr + 32#64) pg0.packedWord
    refine ⟨R16 ∗ ((pg0.metaPtr ↦₆₄ pg0.prev) ∗ ((pg0.metaPtr + 8#64) ↦₆₄ pg0.next) ∗
      ((pg0.metaPtr + 16#64) ↦₆₄ pg0.mem) ∗ ((pg0.metaPtr + 24#64) ↦₃₂ pg0.availMask) ∗
      ((pg0.metaPtr + 28#64) ↦₃₂ pg0.freedMask)) ∗ Rm, ?_⟩
    rw [hFm, hS16]; ac_rfl
  have hFocusSecret : ∃ R, ByteMap st.masterDom keepAfterMeta bvDeq =
      ((maPg.base ↦₆₄ st.ctx.secret) ∗ R) := by
    obtain ⟨maG, hmaG, kG, hkG, _, hGMNat, _, hMaG48⟩ := metaSlot_in_metaArea hwf hmGAll
    have hInKeep : ∀ a, InRegion maPg.base 8 a → keepAfterMeta a ∧ a ∈ st.masterDom := by
      intro a ha8
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha8
      have ha24 : InRegion maPg.base 24 a := (inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩
      have hNotGM : ¬ InRegion cg.metaPtr 40 a := fun haGM => by
        have ⟨g1, g2⟩ := (inRegion_iff_toNat (by omega) a).mp haGM
        by_cases hSameMa : maPg = maG
        · subst hSameMa; omega
        · obtain ⟨i1, hi1, hE1⟩ := List.getElem_of_mem hmaPg
          obtain ⟨i2, hi2, hE2⟩ := List.getElem_of_mem hmaG
          have hIdxNe : i1 ≠ i2 := fun hI => by subst hI; rw [hE1] at hE2; exact hSameMa hE2
          have hpdMa := (PairwiseDisjointRegions.append_iff.mp
            (PairwiseDisjointRegions.append_iff.mp
              (PairwiseDisjointRegions.append_iff.mp hwf.regions_disjoint.1).1).1).1
          have hDisjMa := PairwiseDisjointRegions.getElem_disjoint hpdMa
            (by simp [hi1]) (by simp [hi2]) hIdxNe
          simp only [List.getElem_map, hE1, hE2] at hDisjMa
          exact DisjointRegions.not_both hDisjMa
            ((inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩)
            ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
      exact ⟨⟨(hMaOwn a ha24).1, hNotGM⟩, (hMaOwn a ha24).2⟩
    refine ⟨ByteMap st.masterDom (fun a => keepAfterMeta a ∧ ¬ InRegion maPg.base 8 a) bvDeq, ?_⟩
    rw [ByteMap_extract_slice hDomNd bvDeq maPg.base (by decide)
      (fun a ha => (hInKeep a ha).2) (fun a ha => (hInKeep a ha).1),
      readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
        exact hDisjDeq.1 maPg hmaPg a ((inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩),
      hMaHdr8, ← pointsTo64_eq_pointsToBytes]
  have hG48 : cg.mem.toNat + cg.nestedCap ≤ 2 ^ 48 := by
    have : cg.totalBytes = cg.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
    have := hGWf.2.2.2.2.2.2.1; omega
  have hGMemInSlice : ∀ a, InRegion cg.mem 8 a → InRegion (pg0.slotStart pIdx - 4#64) pg0.stride a := by
    intro a ha; have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hGMemInSlotMod : ∀ a, InRegion cg.mem 8 a → SlotWriteMod pg1 pIdx a := by
    intro a ha; have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    refine Or.inr ⟨hGMemInSlice a ha, fun hEq => ?_⟩
    rw [hEq] at h1; change cg.mem.toNat ≤ (pg0.slotStart pIdx - 4#64).toNat at h1; omega
  have hRepSelf : replaceGroupByMeta stMid.groups pg1.metaPtr pg1 = stMid.groups := by
    obtain ⟨pre, post, hEq, _, _, hR, _⟩ := split_groups_at_mem hWfMid.groups_nodup.1 hpg1Mid
    rw [hR pg1, ← hEq]
  have hSt1EqRep : st1 =
      { stMid with
        groups := replaceGroupByMeta stMid.groups pg1.metaPtr pg1
        byteVal := bv1
        liveMap := stMid.liveMap } := by simp [st1, stMid, hRepSelf]
  have hWf1 : MallocngWFInflight (k + 2) base brkStart brk liveCost peakCost st1 := by
    rw [hSt1EqRep]
    refine wf_of_inPlaceSlotMod hWfMid hpg1Mid hp1 (by simp [pg1])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (show pg1.slots = pg1.slots.set pIdx .claimed by simp [pg1])
      (fun _ _ _ => ⟨rfl, rfl⟩)
      hPg1WfMid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hPg1WfMid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (fun a hNotMod => writeBytesToMap_out bvDeq cg.mem (unpack64 0#64)
        (by rw [unpack64_length]; exact fun ha => hNotMod (hGMemInSlotMod a ha)))
      (by
        rw [readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          writeBytesToMap_out bvDeq cg.mem (unpack64 0#64) (by
            rw [unpack64_length]; intro haG
            have ha0 : InRegion pg0.metaPtr 40 a := ha
            have ⟨m1, m2⟩ := (inRegion_iff_toNat (by omega) a).mp ha0
            exact not_both_inRegion_of_disjointRegions
              (metaArea_disjoint_root_group hWfMid hmaPg hrgMid hRgMp)
              ((inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
              (hPgInRg a (by
                have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp (hGMemInSlice a haG)
                exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)))]
        exact hPg1WfMid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (by
        rw [hRepSelf]
        have hNot8 : ¬ InRegion cg.mem 8 (pg1.slotStart pIdx - 4#64) := fun ha => by
          have ⟨h1, _⟩ := (inRegion_iff_toNat (by omega) (pg0.slotStart pIdx - 4#64)).mp ha; omega
        have hS0 := hPg1WfMid.slot_wf pIdx hp1
        rw [hSlotPg1] at hS0
        exact ⟨(writeBytesToMap_out bvDeq cg.mem (unpack64 0#64)
          (by rw [unpack64_length]; exact hNot8)).trans hS0.1,
          hS0.2.1, hS0.2.2.1, hS0.2.2.2.1, trivial⟩)
      (fun hScLt hNotIn =>
        (((hWfMid.active_wf pg1.sc (by rw [hWfMid.ctx_lens.1]; rw [hWfMid.ctx_lens.2.2.2.2.2] at hScLt; exact hScLt)
          hScLt).2.2.2.1 pg1 hpg1Mid rfl).2 hNotIn).imp id And.left)
      (fun hScLt i hi hiPos hEqM =>
        (hWfMid.active_wf pg1.sc (by rw [hWfMid.ctx_lens.1]; rw [hWfMid.ctx_lens.2.2.2.2.2] at hScLt; exact hScLt)
          hScLt).2.2.2.2.1 i hi hiPos pg1 hpg1Mid hEqM)
      (fun hEmp => False.elim (by
        have := List.all_eq_true.mp hEmp (pg1.slots[pIdx]'hp1) (List.getElem_mem hp1)
        rw [hSlotPg1] at this; cases this))
      (by rw [hRepSelf]; exact hWfMid.inflight_wf)
      hWfMid.live_le_peak
      (by rw [hRepSelf]; exact hWfMid.effCost_le_live)
      (fun q r => by rw [hRepSelf]; exact hWfMid.liveMap_wf q r)
      (fun a hOwn => by rw [hRepSelf] at hOwn; exact hWfMid.masterDom_wf.2.1 a (Or.inl hOwn))
  have ⟨hGMemRead0, _, _⟩ := group_header_ownedRw hwf hg
  have ⟨hBvDataG, _⟩ := hDisjDeq.2.2.2.2.2 cg hg
  have hStoreGMem : ∃ R,
      ByteMap st.masterDom keepAfterMeta bvDeq = ((cg.mem ↦₆₄ cg.metaPtr) ∗ R) ∧
      ((cg.mem ↦₆₄ 0#64) ∗ R) = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
    let R := ByteMap st.masterDom (fun a => keepAfterMeta a ∧ ¬ InRegion cg.mem 8 a) bvDeq
    refine ⟨R, ?_, ?_⟩
    · rw [ByteMap_extract_slice hDomNd bvDeq cg.mem (by decide)
        (fun a ha => (hSliceKeep a (hGMemInSlice a ha)).2)
        (fun a ha => (hSliceKeep a (hGMemInSlice a ha)).1),
        readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          have : cg.totalBytes = cg.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
          exact hBvDataG a ((inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩),
        hGMemRead0, ← pointsTo64_eq_pointsToBytes]
    · dsimp only [R]; rw [pointsTo64_eq_pointsToBytes]
      have hAbs := ByteMap_absorb_slice hDomNd
        (keep := fun a => keepAfterMeta a ∧ ¬ InRegion cg.mem 8 a) bvDeq cg.mem (unpack64 0#64)
        (by rw [unpack64_length]; decide)
        (fun a ha => (hSliceKeep a (hGMemInSlice a (by simpa [unpack64_length] using ha))).2)
        (fun _ hIn ⟨_, hN⟩ => hN (by simpa [unpack64_length] using hIn))
      rw [hAbs]
      have hOwn1Iff : ∀ a, OwnedRwByte st1 a ↔ keepAfterMeta a := hOwnMidIff
      unfold ByteMap
      exact SetSep_congr (fun a _ => by
        rw [unpack64_length, hOwn1Iff a]
        exact ⟨fun h => h.elim And.left (fun ha => (hSliceKeep a (hGMemInSlice a ha)).1),
          fun h => by by_cases ha : InRegion cg.mem 8 a; exact Or.inr ha; exact Or.inl ⟨h, ha⟩⟩)
        (fun _ _ _ => rfl)
  have hProtEq : ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := by
    unfold ProtNoneByteMap
    refine SetSep_congr (fun _ _ => Iff.rfl) fun a _ hPn => congrArg (a ↦₈ₙ ·) ?_
    have hNotGMem : ¬ InRegion cg.mem 8 a := fun haG => by
      have haRg : InRegion rg.mem (rg.maplen * 4096) a :=
        hPgInRg a (by
          have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp (hGMemInSlice a haG)
          exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩)
      have ⟨_, _, hCross⟩ := pairwiseDisjoint_append hWfMid.regions_disjoint.1
      rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
      · exact not_both_inRegion_of_disjointRegions
          (hCross (gp, 4096)
            (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp)))
            (rg.mem, rg.maplen * 4096)
            (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgMid, decide_eq_true hRgMp⟩)))
          haGp haRg
      · exact not_both_inRegion_of_disjointRegions
          (hCross (ap, 4096)
            (List.mem_append_right _ (List.mem_map_of_mem hap))
            (rg.mem, rg.maplen * 4096)
            (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgMid, decide_eq_true hRgMp⟩)))
          haAp haRg
    exact (writeBytesToMap_out bvDeq cg.mem (unpack64 0#64)
      (by rw [unpack64_length]; exact hNotGMem)).trans
      (by
        rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
        · exact hDisjDeq.2.2.1 gp hgp a haGp
        · exact hDisjDeq.2.1 ap hap a haAp)
  have hMapSetEq : MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) :=
    SetSep_congr (fun a _ => hOwnMapMidIff a) (fun _ _ _ => rfl)
  have hKeep1 : EmptyGroupKeepWf st1 := emptyGroupKeepWf_of_wf hWf1
  have hFull1 : FullQueueKeepWf st1 := trivial
  have hNestLt : groupNestBound pg1 < groupNestBound cg := by
    have hEqB : groupNestBound pg1 = groupNestBound pg0 := rfl
    rw [hEqB]
    exact groupNestBound_parent_lt hwf hg hMap0 hpg0 hParG
  exact ⟨hCarveGMeta, hMemMask, hpLeLast, hLast31, hPgSc24, hTot16, hHdrExt, hPgMemAddr,
    hLow8, ⟨hAvShift.2, hAvShift.1⟩, ⟨hFrShift.2, hFrShift.1⟩, hPgPageMask, hLow16,
    hTotLo, hTotHi, hPgPackMask, hRootPgProps,
    hFocusHdr, hFocusPgMem, hFocusPgMeta, hFocusPacked8, hFocusPacked16, hFocusSecret,
    hStoreGMem, hProtEq, hMapSetEq, hWf1, hKeep1, hFull1,
    hpg1Mid, ⟨hp1, hSlotPg1⟩, rfl, hNestLt,
    List.mem_cons_self .., List.erase_cons_head .., hLiveMid, hDynMid,
    hDeq.other_sc_mem pg0 hpg0 (by omega)⟩

end

end LibsignalBinary.Heap.Fine.VendorFree
