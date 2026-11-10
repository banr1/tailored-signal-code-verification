/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.FreeSubHelpers

/-!
# Fine-Grained Placed `nontrivial_free` Stage 3

Strengthens `VendorFree.free_retire_nestedGroup` (`blk05`, `+0x304..+0x404`) with
`SameLiveUserSub st1 st` across nested-group (`g.maplen = 0`) validation and `[g.mem] := 0#64`
retirement.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace LibsignalBinary.Heap.Fine

open Arm64 ProofLib ProofLib.SepLogic
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open LibsignalBinary.Heap.Fine.VendorFree

/-! ## Sub-Word Unpack and Parent Offset Bounds -/

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

/-! ## Nested-Group Validation and Retirement -/

set_option maxHeartbeats 800000 in
/-- Strengthened pure + spatial helper for retiring an all-free nested group `g` (`g.maplen = 0`) at
    `+0x304..+0x404`, additionally exporting `SameLiveUserSub st1 st`. -/
theorem free_retire_nestedGroup_fine {k : Nat} {base brkStart brk : BitVec 64}
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
      SameLiveUserSub st1 st := by
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
  have ⟨hpgDeq, hpg1Mid, hWfMid, hOwnMidIff, hOwnMapMidIff, hLiveMid, hDynMid, hSubMid⟩ :=
    nested_stMid_wf_fine hwf hg hpg0 hIdx hp0 hSlot hAllFree hMap0 hParG hGScLt hSlotPg hDeq
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
  have hSub1 : SameLiveUserSub st1 st :=
    SameLiveUserSub.trans (sameLiveUserSub_of_groups_eq hWfMid.groups_nodup.1 rfl rfl rfl) hSubMid
  exact ⟨hCarveGMeta, hMemMask, hpLeLast, hLast31, hPgSc24, hTot16, hHdrExt, hPgMemAddr,
    hLow8, ⟨hAvShift.2, hAvShift.1⟩, ⟨hFrShift.2, hFrShift.1⟩, hPgPageMask, hLow16,
    hTotLo, hTotHi, hPgPackMask, hRootPgProps,
    hFocusHdr, hFocusPgMem, hFocusPgMeta, hFocusPacked8, hFocusPacked16, hFocusSecret,
    hStoreGMem, hProtEq, hMapSetEq, hWf1, hKeep1, hFull1,
    hpg1Mid, ⟨hp1, hSlotPg1⟩, rfl, hNestLt,
    List.mem_cons_self .., List.erase_cons_head .., hLiveMid, hDynMid, hSub1⟩

end LibsignalBinary.Heap.Fine
