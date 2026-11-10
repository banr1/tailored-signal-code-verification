/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.LiveUserBandHelpers

/-!
# Slot Metadata and Layout Invariant Helpers

Extracts spatial `ByteMap` focus slices and bitfield/arithmetic invariants for active `.liveUser`
slots from `MallocngWFInflight`, together with the opaque read-only frame `MallocngReadRest`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## `LiveUserBlockFacts` Bundle and Extraction -/

structure LiveUserBlockFacts (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (p : BitVec 64) (n effCost : Nat) : Prop where
  dom_nodup        : st.masterDom.Nodup
  ctx_lens         :
    st.ctx.active.length = 48 ∧ st.ctx.usageByClass.length = 48 ∧
    st.ctx.unmapSeq.length = 32 ∧ st.ctx.bounces.length = 32
  p_ne_zero        : p ≠ 0#64
  p_mod_16         : p.toNat % 16 = 0
  p_and_15         : p &&& 0xf#64 = 0#64
  p_ge_4096        : 4096 + 16 ≤ p.toNat
  p_add_n_48       : p.toNat + n ≤ 2 ^ 48
  n_le_max         : n ≤ MallocngMaxAllocSize
  idx_le_last      : idx ≤ g.lastIdx
  last_le_31       : g.lastIdx ≤ 31
  sc_cases         : g.sc < 48 ∨ g.sc = 63
  sc_63_props      : g.sc = 63 → g.lastIdx = 0 ∧ 0 < g.maplen ∧ g.prev = 0#64 ∧ g.next = 0#64
  maplen_zero_sc   : g.maplen = 0 → g.sc < 48 ∧ 1 ≤ g.lastIdx
  maplen_lt_52     : g.maplen < 2 ^ 52
  maplen_bytes_48  : g.maplen * 4096 ≤ 2 ^ 48
  mem_bounds       : 4096 ≤ g.mem.toNat ∧ g.mem.toNat % 16 = 0 ∧ g.mem.toNat + 16 ≤ p.toNat
  stride_bounds    :
    16 ≤ g.stride ∧ g.stride % 16 = 0 ∧
    g.storage.toNat = g.mem.toNat + 16 ∧
    (g.slotStart idx).toNat = g.mem.toNat + 16 + idx * g.stride ∧
    (g.slotEnd idx).toNat = g.mem.toNat + 12 + (idx + 1) * g.stride ∧
    (g.slotEnd idx).toNat ≤ 2 ^ 48
  start_le_p       : (g.slotStart idx).toNat ≤ p.toNat
  p_add_n_le_end   : p.toNat + n ≤ (g.slotEnd idx).toNat
  effCost_bounds   :
    max n MallocngMinBlockCost ≤ effCost ∧
    (p.toNat - (g.slotStart idx).toNat ≤ (effCost - max n MallocngMinBlockCost) + 255 * 16 ∧
      effCost - max n MallocngMinBlockCost ≤ MaxAlignedAllocAlign - 16) ∧
    (2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < effCost) ∧
    (g.sc = 63 → g.maplen * 4096 ≤ effCost + 8195)
  totalOff_lt_27   : (p.toNat - g.storage.toNat) / 16 < 2 ^ 27
  p_eq_storage_off : p.toNat = g.mem.toNat + 16 + 16 * ((p.toNat - g.storage.toNat) / 16)
  long_off_props   :
    0xffff < (p.toNat - g.storage.toNat) / 16 → g.sc = 63 ∧ idx = 0
  sc_lt_48_off     :
    g.sc < 48 →
      idx * sizeClass g.sc ≤ (p.toNat - g.storage.toNat) / 16 ∧
      (p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc
  maplen_pos_off   :
    0 < g.maplen → (p.toNat - g.storage.toNat) / 16 + 2 ≤ g.maplen * 256
  reserved_lt_31   : (g.slotEnd idx).toNat - (p.toNat + n) < 2 ^ 31
  avail_bit_false  : g.availMask.getLsbD idx = false
  freed_bit_false  : g.freedMask.getLsbD idx = false
  meta_page_base   :
    ∃ ma ∈ st.metaAreas,
      g.metaPtr &&& 0xfffffffffffff000#64 = ma.base ∧
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ((ma.base ↦₆₄ st.ctx.secret) ∗
          ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion ma.base 8 a) st.byteVal)
  focus_hdr_short  :
    (p.toNat - g.storage.toNat) / 16 ≤ 0xffff →
      let r5 := min ((g.slotEnd idx).toNat - (p.toNat + n)) 5
      let tot := (p.toNat - g.storage.toNat) / 16
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        (((p - 4#64) ↦₈ 0#8) ∗
         ((p - 3#64) ↦₈ BitVec.ofNat 8 ((r5 <<< 5) ||| idx)) ∗
         ((p - 2#64) ↦₁₆ BitVec.ofNat 16 tot) ∗
         ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 4#64) 4 a) st.byteVal)
  focus_hdr_long   :
    0xffff < (p.toNat - g.storage.toNat) / 16 →
      let r5 := min ((g.slotEnd idx).toNat - (p.toNat + n)) 5
      let tot := (p.toNat - g.storage.toNat) / 16
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        (((p - 8#64) ↦₃₂ BitVec.ofNat 32 tot) ∗
         ((p - 4#64) ↦₈ 1#8) ∗
         ((p - 3#64) ↦₈ BitVec.ofNat 8 ((r5 <<< 5) ||| idx)) ∗
         ((p - 2#64) ↦₁₆ 0#16) ∗
         ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (p - 8#64) 8 a) st.byteVal)
  focus_group_mem  :
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      ((g.mem ↦₆₄ g.metaPtr) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.mem 8 a) st.byteVal)
  focus_meta       :
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((g.metaPtr ↦₆₄ g.prev) ∗
        ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
        ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗
        ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
        ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗
        ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal)
  focus_trailer5   :
    5 ≤ (g.slotEnd idx).toNat - (p.toNat + n) →
      let res := (g.slotEnd idx).toNat - (p.toNat + n)
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        (((g.slotEnd idx - 5#64) ↦₈ 0#8) ∗
         ((g.slotEnd idx - 4#64) ↦₃₂ BitVec.ofNat 32 res) ∗
         ByteMap st.masterDom
           (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotEnd idx - 5#64) 5 a) st.byteVal)
  focus_end_req    :
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((p + BitVec.ofNat 64 n) ↦₈ 0#8) ∗
        ByteMap st.masterDom
          (fun a => OwnedRwByte st a ∧ ¬ InRegion (p + BitVec.ofNat 64 n) 1 a) st.byteVal)
  focus_slot_end   :
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((g.slotEnd idx) ↦₈ 0#8) ∗
        ByteMap st.masterDom
          (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotEnd idx) 1 a) st.byteVal)

theorem liveUserBlockFacts_of {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {n effCost : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p n effCost) :
    LiveUserBlockFacts st g idx p n effCost := by
  have hgWf := hwf.groups_wf g hg
  have hSWf := GroupWf.slot_wf hgWf idx hIdx
  rw [hSlot] at hSWf
  obtain ⟨_, hAvailIff, hFreedIff, _, hBody⟩ := hSWf
  dsimp only at hBody
  obtain ⟨⟨hpNe0, hpDvd16, hpN48, hnMax⟩, hStartLeP, hPNLeEnd, hEffGe, hOffB,
    hResLt31, ⟨hSc2Eff, hSc48OffLt⟩, hSc63Map, hHdrM3, hOffEnc, _, hRes5⟩ := hBody
  have ⟨hIdxCnt, hStor, hStart, hStartSub4, hEnd, hEndLeTot, hTot48, _, _⟩ :=
    group_slot_bounds hgWf hIdx
  have ⟨hStrideGe16, hStrideMod16⟩ := group_stride_pos_and_align hgWf
  have hLast31 : g.lastIdx ≤ 31 := hgWf.2.1
  have hIdxLeLast : idx ≤ g.lastIdx := by unfold GroupDesc.cnt at hIdxCnt; omega
  have hMemGe : 4096 ≤ g.mem.toNat := hgWf.2.2.2.2.1
  have hMemMod : g.mem.toNat % 16 = 0 := hgWf.2.2.2.2.2.1
  have hpMod16 : p.toNat % 16 = 0 := Nat.mod_eq_zero_of_dvd hpDvd16
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48 := by omega
  have hPEq : p.toNat = g.mem.toNat + 16 + 16 * ((p.toNat - g.storage.toNat) / 16) := by omega
  have hTotLt27 : (p.toNat - g.storage.toNat) / 16 < 2 ^ 27 := by
    by_cases hLe : (p.toNat - g.storage.toNat) / 16 ≤ 0xffff
    · omega
    · simp only [hLe, ↓reduceIte] at hOffEnc
      exact hOffEnc.2.2.1
  have hLongProps : 0xffff < (p.toNat - g.storage.toNat) / 16 → g.sc = 63 ∧ idx = 0 := by
    intro hGt
    have hNle : ¬ ((p.toNat - g.storage.toNat) / 16 ≤ 0xffff) := by omega
    simp only [hNle, ↓reduceIte] at hOffEnc
    exact ⟨hOffEnc.1, hOffEnc.2.1⟩
  have hMapBytes48 : g.maplen * 4096 ≤ 2 ^ 48 := by
    by_cases hMp : 0 < g.maplen
    · have : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
      omega
    · have : g.maplen = 0 := by omega
      omega
  have hMap0Sc : g.maplen = 0 → g.sc < 48 ∧ 1 ≤ g.lastIdx := by
    intro hM0
    have h1 := (hgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hM0).1
    rcases hgWf.1 with hSc48 | hSc63
    · exact ⟨hSc48, h1⟩
    · have := (hgWf.2.2.2.1 hSc63).2.1; omega
  have hSc48Bounds : g.sc < 48 →
      idx * sizeClass g.sc ≤ (p.toNat - g.storage.toNat) / 16 ∧
      (p.toNat - g.storage.toNat) / 16 < (idx + 1) * sizeClass g.sc := by
    intro hSc48
    refine ⟨?_, hSc48OffLt hSc48⟩
    by_cases hIdx0 : idx = 0
    · subst hIdx0; simp
    · have hLastNe0 : (g.lastIdx == 0) = false := beq_false_of_ne (by omega)
      have hStrideEq : g.stride = 16 * sizeClass g.sc := by
        unfold GroupDesc.stride slotStride
        simp [hLastNe0]
      have hMul16 : idx * g.stride = 16 * (idx * sizeClass g.sc) := by
        rw [hStrideEq, ← Nat.mul_assoc, Nat.mul_comm idx 16, Nat.mul_assoc]
      generalize idx * sizeClass g.sc = q at hMul16 ⊢
      omega
  have hMapPosOff : 0 < g.maplen → (p.toNat - g.storage.toNat) / 16 + 2 ≤ g.maplen * 256 := by
    intro hMp
    have hStrict := hgWf.2.2.2.2.2.2.2.2.1 hMp
    have hTotEq : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
    have hMulLe : (idx + 1) * g.stride ≤ g.cnt * g.stride :=
      Nat.mul_le_mul_right _ hIdxCnt
    omega
  have hAvailF : g.availMask.getLsbD idx = false := by
    cases h : g.availMask.getLsbD idx
    · rfl
    · cases hAvailIff.mp h
  have hFreedF : g.freedMask.getLsbD idx = false := by
    cases h : g.freedMask.getLsbD idx
    · rfl
    · cases hFreedIff.mp h
  have hNodup := hwf.masterDom_wf.1
  have hmAll : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hg))))
  obtain ⟨ma, hma, k, hk, _, hMetaNat, _, _⟩ := metaSlot_in_metaArea hwf hmAll
  have ⟨_, hMaMod, hMaHi, hMaHdr8, hMaOwn⟩ := metaArea_header_ownedRw hwf hma
  have hMetaMask : g.metaPtr &&& 0xfffffffffffff000#64 = ma.base :=
    bv64_page_mask_eq (off := 24 + k * 40) hMaMod (by omega) (by omega)
  have h8Le : (8 : Nat) ≤ 2 ^ 64 := by omega
  have h40Le : (40 : Nat) ≤ 2 ^ 64 := by omega
  have h1Le : (1 : Nat) ≤ 2 ^ 64 := by omega
  have hFocusMa : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      ((ma.base ↦₆₄ st.ctx.secret) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion ma.base 8 a) st.byteVal) := by
    have hSub8 : ∀ a, InRegion ma.base 8 a → InRegion ma.base 24 a := fun a ha => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      exact (inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩
    rw [ByteMap_extract_slice hNodup st.byteVal ma.base h8Le
      (fun a ha => (hMaOwn a (hSub8 a ha)).2) (fun a ha => (hMaOwn a (hSub8 a ha)).1),
      hMaHdr8, ← pointsTo64_eq_pointsToBytes]
  have ⟨hGMemRead, _, hGMemOwn⟩ := group_header_ownedRw hwf hg
  have hFocusGMem : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      ((g.mem ↦₆₄ g.metaPtr) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.mem 8 a) st.byteVal) := by
    have hSub8 : ∀ a, InRegion g.mem 8 a → InRegion g.mem 16 a := fun a ha => by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      exact (inRegion_iff_toNat (by omega) a).mpr ⟨h1, by omega⟩
    rw [ByteMap_extract_slice hNodup st.byteVal g.mem h8Le
      (fun a ha => (hGMemOwn a (hSub8 a ha)).2) (fun a ha => (hGMemOwn a (hSub8 a ha)).1),
      hGMemRead, ← pointsTo64_eq_pointsToBytes]
  have ⟨_, _, _, hMetaRead, hMetaOwn⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hFocusMeta : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((g.metaPtr ↦₆₄ g.prev) ∗
        ((g.metaPtr + 8#64) ↦₆₄ g.next) ∗
        ((g.metaPtr + 16#64) ↦₆₄ g.mem) ∗
        ((g.metaPtr + 24#64) ↦₃₂ g.availMask) ∗
        ((g.metaPtr + 28#64) ↦₃₂ g.freedMask) ∗
        ((g.metaPtr + 32#64) ↦₆₄ g.packedWord)) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) := by
    rw [ByteMap_extract_slice hNodup st.byteVal g.metaPtr h40Le
      (fun a ha => (hMetaOwn a ha).2) (fun a ha => (hMetaOwn a ha).1),
      hMetaRead, GroupDesc.metaBytes_pointsTo]
  have ⟨_, hZEnd, hZReqEnd, hBandOwn⟩ := liveUser_band_ownedRw hwf hg hIdx hSlot
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hFocusEndReq : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((p + BitVec.ofNat 64 n) ↦₈ 0#8) ∗
        ByteMap st.masterDom
          (fun a => OwnedRwByte st a ∧ ¬ InRegion (p + BitVec.ofNat 64 n) 1 a) st.byteVal) := by
    have hPNat : (p + BitVec.ofNat 64 n).toNat = p.toNat + n := bv64_add_toNat (by omega)
    have hInBand : ∀ a, InRegion (p + BitVec.ofNat 64 n) 1 a →
        InRegion (g.slotStart idx - 4#64) (g.stride + 1) a ∧ ¬ InRegion p n a := by
      intro a ha
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      refine ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩, fun hPN => ?_⟩
      have := (inRegion_iff_toNat (by omega) a).mp hPN; omega
    rw [ByteMap_extract_slice hNodup st.byteVal (p + BitVec.ofNat 64 n) h1Le
      (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).2)
      (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).1),
      readBytesFromMap_one, hZReqEnd, pointsToBytes_singleton]
  have hFocusSlotEnd : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      (((g.slotEnd idx) ↦₈ 0#8) ∗
        ByteMap st.masterDom
          (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.slotEnd idx) 1 a) st.byteVal) := by
    have hInBand : ∀ a, InRegion (g.slotEnd idx) 1 a →
        InRegion (g.slotStart idx - 4#64) (g.stride + 1) a ∧ ¬ InRegion p n a := by
      intro a ha
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      refine ⟨(inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩, fun hPN => ?_⟩
      have := (inRegion_iff_toNat (by omega) a).mp hPN; omega
    rw [ByteMap_extract_slice hNodup st.byteVal (g.slotEnd idx) h1Le
      (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).2)
      (fun a ha => (hBandOwn a (hInBand a ha).1 (hInBand a ha).2).1),
      readBytesFromMap_one, hZEnd, pointsToBytes_singleton]
  exact
    { dom_nodup := hNodup
      ctx_lens := ⟨hwf.ctx_lens.1, hwf.ctx_lens.2.1, hwf.ctx_lens.2.2.1, hwf.ctx_lens.2.2.2.1⟩
      p_ne_zero := hpNe0
      p_mod_16 := hpMod16
      p_and_15 := bv64_and_15_of_mod hpMod16
      p_ge_4096 := by omega
      p_add_n_48 := hpN48
      n_le_max := hnMax
      idx_le_last := hIdxLeLast
      last_le_31 := hLast31
      sc_cases := hgWf.1
      sc_63_props := hgWf.2.2.2.1
      maplen_zero_sc := hMap0Sc
      maplen_lt_52 := by omega
      maplen_bytes_48 := hMapBytes48
      mem_bounds := ⟨hMemGe, hMemMod, by omega⟩
      stride_bounds := ⟨hStrideGe16, hStrideMod16, hStor, hStart, hEnd, hEnd48⟩
      start_le_p := hStartLeP
      p_add_n_le_end := hPNLeEnd
      effCost_bounds := ⟨hEffGe, ⟨hOffB.1, hOffB.2.1⟩, hSc2Eff, hSc63Map⟩
      totalOff_lt_27 := hTotLt27
      p_eq_storage_off := hPEq
      long_off_props := hLongProps
      sc_lt_48_off := hSc48Bounds
      maplen_pos_off := hMapPosOff
      reserved_lt_31 := hResLt31
      avail_bit_false := hAvailF
      freed_bit_false := hFreedF
      meta_page_base := ⟨ma, hma, hMetaMask, hFocusMa⟩
      focus_hdr_short := fun hLe => by
        simp only [hLe, ↓reduceIte] at hOffEnc
        exact focus_hdr_short_of hNodup hStartSub4 hEnd hEnd48 hStartLeP hStart hMemGe hpN48
          hPNLeEnd hBandOwn hOffEnc.1 hHdrM3 hOffEnc.2
      focus_hdr_long := fun hGt => by
        have hNle : ¬ ((p.toNat - g.storage.toNat) / 16 ≤ 0xffff) := by omega
        simp only [hNle, ↓reduceIte] at hOffEnc
        obtain ⟨_, hIdx0, _, hM4_1, hM2_0, hM8_32⟩ := hOffEnc
        exact focus_hdr_long_of hNodup hStartSub4 hEnd hEnd48 (by subst hIdx0; omega) hStart
          hMemGe hpN48 hPNLeEnd hBandOwn hM8_32 hM4_1 hHdrM3 hM2_0
      focus_group_mem := hFocusGMem
      focus_meta := hFocusMeta
      focus_trailer5 := fun hGe5 =>
        focus_trailer5_of hNodup hStartSub4 hEnd hEnd48 hStartLeP hStart hMemGe hpN48 hGe5
          hBandOwn (hRes5 hGe5).1 (hRes5 hGe5).2
      focus_end_req := hFocusEndReq
      focus_slot_end := hFocusSlotEnd }

/-! ## Opaque Read-Only Heap Bundle (`MallocngReadRest`) and Unpack/Repack Bridges -/

@[irreducible] def MallocngReadRest
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (st : MallocngSt) : SepProp :=
  ⌜MallocngCountIvsWF b ivs st ∧ MallocngWF A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
  MallocngLiveAuth γ st.liveMap ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
  MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st) ∗
  MallocngRuntime A tp

theorem mallocngHeap_read_liveUser_unpackΦ {T : SepProp} {Φ : MallocngLiveMap → Prop} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (p : BitVec 64) (n : Nat)
    (hLook : ∀ L : MallocngLiveMap, MallocngLiveAuth γ L ∗ T ⊢
      ⌜L p = some n ∧ Φ L⌝ ∗ MallocngLiveAuth γ L ∗ T) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs ∗ T ⊢
      ∃∗ st : MallocngSt, ∃∗ g : GroupDesc, ∃∗ idx : Nat, ∃∗ effCost : Nat,
        ⌜g ∈ st.groups ∧
          (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p n effCost) ∧
          LiveUserBlockFacts st g idx p n effCost ∧ Φ st.liveMap⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        T := by
  show MallocngHeapImpl γ A tp brkStart brk b ivs ∗ T ⊢ _
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq]
  unfold MallocngRoTablesA
  rw [sepConj_assoc, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun st => ?_
  unfold MallocngCoreStA MallocngCoreStInflightA
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜MallocngCountIvsWF b ivs st⌝ ∗
      ⌜MallocngWF A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
      ((MallocngLiveAuth γ st.liveMap ∗ T) ∗
       (MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime A tp)) by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl)) ?_
  refine Entails.pure_left fun hCount => Entails.pure_left fun hWf => ?_
  refine Entails.trans (sepConj_mono_left (hLook st.liveMap)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hLive, hΦ⟩ => ?_
  obtain ⟨g, hg, idx, hIdx, effCost, hSlot⟩ := (hWf.liveMap_wf p n).mp hLive
  have hFacts := liveUserBlockFacts_of hWf hg hIdx hSlot
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun g' => ∃∗ idx' : Nat, ∃∗ effCost' : Nat,
        ⌜g' ∈ st.groups ∧
          (∃ hIdx' : idx' < g'.slots.length, g'.slots[idx']'hIdx' = .liveUser p n effCost') ∧
          LiveUserBlockFacts st g' idx' p n effCost' ∧ Φ st.liveMap⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        T) g)
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun idx' => ∃∗ effCost' : Nat,
        ⌜g ∈ st.groups ∧
          (∃ hIdx' : idx' < g.slots.length, g.slots[idx']'hIdx' = .liveUser p n effCost') ∧
          LiveUserBlockFacts st g idx' p n effCost' ∧ Φ st.liveMap⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        T) idx)
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun effCost' =>
        ⌜g ∈ st.groups ∧
          (∃ hIdx' : idx < g.slots.length, g.slots[idx]'hIdx' = .liveUser p n effCost') ∧
          LiveUserBlockFacts st g idx p n effCost' ∧ Φ st.liveMap⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        T) effCost)
  refine Entails.pure_right ⟨hg, ⟨hIdx, hSlot⟩, hFacts, hΦ⟩ ?_
  unfold MallocngReadRest
  rw [pure_sepConj_of_true ⟨hCount, hWf⟩]
  exact Entails.of_eq (by generalize (MallocngRoTablesAt A) = PRo; ac_rfl)

theorem mallocngHeap_read_liveUser_unpackT {T : SepProp} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (p : BitVec 64) (n : Nat)
    (hLook : ∀ L : MallocngLiveMap, MallocngLiveAuth γ L ∗ T ⊢
      ⌜L p = some n⌝ ∗ MallocngLiveAuth γ L ∗ T) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs ∗ T ⊢
      ∃∗ st : MallocngSt, ∃∗ g : GroupDesc, ∃∗ idx : Nat, ∃∗ effCost : Nat,
        ⌜g ∈ st.groups ∧
          (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p n effCost) ∧
          LiveUserBlockFacts st g idx p n effCost⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        T := by
  refine Entails.trans (mallocngHeap_read_liveUser_unpackΦ (Φ := fun _ => True)
    γ A tp brkStart brk b ivs p n fun L => Entails.trans (hLook L)
      (Entails.pure_left fun h => Entails.pure_right ⟨h, trivial⟩ (Entails.refl _))) ?_
  refine Entails.sepExists_mono fun st => Entails.sepExists_mono fun g =>
    Entails.sepExists_mono fun idx => Entails.sepExists_mono fun effCost => ?_
  exact Entails.pure_left fun h => Entails.pure_right ⟨h.1, h.2.1, h.2.2.1⟩ (Entails.refl _)

theorem mallocngHeap_read_liveUser_unpack (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (p : BitVec 64) (n : Nat) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs ∗ MallocngBlockToken γ p n ⊢
      ∃∗ st : MallocngSt, ∃∗ g : GroupDesc, ∃∗ idx : Nat, ∃∗ effCost : Nat,
        ⌜g ∈ st.groups ∧
          (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p n effCost) ∧
          LiveUserBlockFacts st g idx p n effCost⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        MallocngBlockToken γ p n :=
  mallocngHeap_read_liveUser_unpackT γ A tp brkStart brk b ivs p n fun L =>
    Entails.trans (mallocngBlock_lookup γ L p n) (Entails.pure_left fun h =>
      Entails.pure_right h.2 (Entails.refl _))

theorem mallocngHeap_read_liveUser_unpackTight (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (p : BitVec 64) (n a : Nat) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs ∗ MallocngTightBlock γ p n a ⊢
      ∃∗ st : MallocngSt, ∃∗ g : GroupDesc, ∃∗ idx : Nat, ∃∗ effCost : Nat,
        ⌜g ∈ st.groups ∧
          (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p n effCost) ∧
          LiveUserBlockFacts st g idx p n effCost ∧ st.liveMap.ov p ≤ a - 16⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRest γ A tp brkStart brk b ivs st ∗
        MallocngTightBlock γ p n a :=
  mallocngHeap_read_liveUser_unpackΦ (Φ := fun L => L.ov p ≤ a - 16)
    γ A tp brkStart brk b ivs p n fun L =>
      Entails.trans (mallocngTightBlock_lookup γ L p n a) (Entails.pure_left fun h =>
        Entails.pure_right h.2 (Entails.refl _))

theorem mallocngHeap_read_liveUser_repack (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (st : MallocngSt) :
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
    MallocngReadRest γ A tp brkStart brk b ivs st ⊢
      mallocngIface.MallocngHeap γ A tp brkStart brk b ivs := by
  show _ ⊢ MallocngHeapImpl γ A tp brkStart brk b ivs
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq]
  unfold MallocngReadRest MallocngRoTablesA MallocngCoreStA MallocngCoreStInflightA
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜MallocngCountIvsWF b ivs st ∧ MallocngWF A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
      ((MallocngRoTablesAt A ∗
        (MallocngLiveAuth γ st.liveMap ∗
         (A.ctx ↦ₛ st.ctx.toBytes) ∗
         (A.lock ↦₃₂ 0#32) ∗
         (A.replaced ↦₃₂ 0#32) ∗
         (A.aaReplaced ↦₃₂ 0#32) ∗
         ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
         MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
         ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st))) ∗
       MallocngRuntime A tp) by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl)) ?_
  refine Entails.pure_left fun ⟨hCount, hWf⟩ => ?_
  refine sepConj_mono_left (sepConj_mono_right ?_)
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun st' =>
        ⌜MallocngCountIvsWF b ivs st'⌝ ∗
        ⌜MallocngWF A.base brkStart brk b.liveCost b.peakCost st'⌝ ∗
        MallocngLiveAuth γ st'.liveMap ∗
        (A.ctx ↦ₛ st'.ctx.toBytes) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        ((A.libc + 8#64) ↦₆₄ st'.auxvPtr) ∗
        MallocngAuxvState γ st'.auxvPtr st'.auxvSnap ∗
        ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
        ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
        MappedSet st'.masterDom (OwnedMappedByte st'))
      st)
  rw [pure_sepConj_of_true hCount, pure_sepConj_of_true hWf]
  exact Entails.refl _

/-! ## Pure Bitfield and Address Lemmas for `get_meta`, `get_stride`, and `get_nominal_size` -/

theorem hdrByte_extract (r5 idx : Nat) (hr5 : r5 ≤ 5) (hIdx : idx ≤ 31) :
    let b : BitVec 8 := BitVec.ofNat 8 ((r5 <<< 5) ||| idx)
    (b.zeroExtend 32) &&& 0x1f#32 = BitVec.ofNat 32 idx ∧
    (b.zeroExtend 32) >>> 5 = BitVec.ofNat 32 r5 ∧
    (((b.zeroExtend 32).zeroExtend 64) >>> 5) &&& 7#64 = BitVec.ofNat 64 r5 ∧
    ((b.zeroExtend 32).ule 0x9f#32 ↔ r5 < 5) := by
  have h1 : (BitVec.ofNat 8 ((r5 <<< 5) ||| idx)) =
      ((BitVec.ofNat 8 r5) <<< 5) ||| BitVec.ofNat 8 idx := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    have hR5Lt : r5 <<< 5 < 256 := by rw [Nat.shiftLeft_eq]; omega
    have hR5Mod : r5 % 256 = r5 := Nat.mod_eq_of_lt (by omega)
    have hIdxMod : idx % 256 = idx := Nat.mod_eq_of_lt (by omega)
    have hShMod : (r5 <<< 5) % 256 = r5 <<< 5 := Nat.mod_eq_of_lt hR5Lt
    have hOrLt : (r5 <<< 5 ||| idx) < 256 :=
      Nat.or_lt_two_pow (n := 8) hR5Lt (by omega)
    rw [hR5Mod, hIdxMod, hShMod, Nat.mod_eq_of_lt hOrLt]
  have hR : (BitVec.ofNat 8 r5).ult 6#8 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change r5 % 256 < 6; omega
  have hI : (BitVec.ofNat 8 idx).ult 32#8 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 256 < 32; omega
  dsimp only
  rw [h1,
    show BitVec.ofNat 32 idx = (BitVec.ofNat 8 idx).zeroExtend 32 by bv_omega,
    show BitVec.ofNat 32 r5 = (BitVec.ofNat 8 r5).zeroExtend 32 by bv_omega,
    show BitVec.ofNat 64 r5 = (BitVec.ofNat 8 r5).zeroExtend 64 by bv_omega,
    show (r5 < 5) ↔ ((BitVec.ofNat 8 r5).ult 5#8 = true) by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change r5 < 5 ↔ r5 % 256 < 5; omega]
  revert hR hI
  bv_robdd

theorem mask_ushiftRight_bit0_false (m : BitVec 32) {idx : Nat}
    (hIdx : idx ≤ 31) (hBit : m.getLsbD idx = false) :
    (m >>> (BitVec.ofNat 32 idx &&& 31#32)).getLsbD 0 = false ∧
    (m >>> BitVec.ofNat 32 idx).getLsbD 0 = false := by
  have hMod : (BitVec.ofNat 32 idx &&& 31#32) = BitVec.ofNat 32 idx := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (idx % 4294967296) &&& 31 = idx % 4294967296
    rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h0 : (m >>> BitVec.ofNat 32 idx).getLsbD 0 = false := by
    rw [BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.add_zero]
    exact hBit
  exact ⟨by rw [hMod]; exact h0, h0⟩

theorem group_mem_addr_of_totalOff {p mem : BitVec 64} {tot : Nat}
    (hTot : tot < 2 ^ 27) (_hMem48 : mem.toNat + 16 + 16 * tot ≤ 2 ^ 48)
    (hpEq : p.toNat = mem.toNat + 16 + 16 * tot) :
    p + (-16#64 - ((BitVec.ofNat 32 tot <<< 4).signExtend 64)) = mem := by
  have hShift : ((BitVec.ofNat 32 tot <<< 4).signExtend 64) = BitVec.ofNat 64 (16 * tot) := by
    have hLt : (BitVec.ofNat 32 tot).ult (1#32 <<< 27) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change tot % 4294967296 < 134217728
      omega
    rw [show BitVec.ofNat 64 (16 * tot) = ((BitVec.ofNat 32 tot).zeroExtend 64) <<< 4 by bv_omega]
    revert hLt; bv_robdd
  rw [hShift]
  bv_omega

end VerifiedLibraries.Mallocng.Proofs
