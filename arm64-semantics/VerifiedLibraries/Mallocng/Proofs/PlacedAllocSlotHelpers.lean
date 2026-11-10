/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupHelpers2
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers3

/-!
# Invariant Helpers for Placed `alloc_slot`

Proves `MallocngWFInflight`, `ByteMap`, and `CtxFields` transition and absorption lemmas for
`alloc_slot` (`try_avail` dequeue and head rotation, `pageSpanSteps` `activeIdx` bump,
`activate_group` `freedMask` to `availMask` transfer, `bounces` decrement, and
`claimFreeAvailInflight_absorb`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Stride Bound and Fast Bit-Pop (`claimFreeAvailInflight_absorb`) -/

theorem req_add_four_le_stride_of_avail {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {sc req : Nat}
    (hScEq : g.sc = sc) (hSc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hAvailNe : g.availMask ≠ 0#32) :
    req + 4 ≤ g.stride := by
  have ⟨hSlo, _⟩ := slotStride_bounds_48 hSc
  have hReqLe : req + 4 ≤ slotStride sc := by
    unfold slotStride at hSlo; unfold nominalSlotCap at hReq; unfold slotStride; omega
  unfold GroupDesc.stride
  cases hCond : g.lastIdx == 0 && decide (0 < g.maplen)
  · simp [hScEq, hReqLe]
  · simp only [↓reduceIte]
    have hLast0 : g.lastIdx = 0 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hCond).1
    have hgw := hwf.groups_wf g hg
    let idx := ctz32DeBruijn g.availMask
    obtain ⟨_, hIdx32, _, hIso, _, hSet, _, _⟩ := ctz32DeBruijn_spec hAvailNe
    obtain ⟨hBitTrue, _, _, _, _⟩ := bit32_sub_pow2_props idx hIdx32 g.availMask hIso hSet
    have hIdxCnt : idx < g.cnt := Classical.byContradiction fun hGe => by
      have hPowLe : 2 ^ g.cnt ≤ 2 ^ idx := Nat.pow_le_pow_right (n := 2) (by omega) (Nat.le_of_not_lt hGe)
      have hShiftNat : (1#32 <<< idx).toNat = 2 ^ idx := by
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
          Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by omega) hIdx32)]
      have hAndLe : (g.availMask &&& (1#32 <<< idx)).toNat ≤ g.availMask.toNat := by
        rw [BitVec.toNat_and]; exact Nat.and_le_left
      have hOrGe : g.availMask.toNat ≤ (g.availMask ||| g.freedMask).toNat :=
        BitVec.le_def.mp (by bv_bits : g.availMask ≤ g.availMask ||| g.freedMask)
      rw [hSet, hShiftNat] at hAndLe
      have hOrLt := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hIdx0 : idx = 0 := by unfold GroupDesc.cnt at hIdxCnt; omega
    have hLen1 : g.slots.length = 1 := by have hL := hgw.2.2.1; unfold GroupDesc.cnt at hL; omega
    have hIdx : idx < g.slots.length := by omega
    have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
    have hFreeAvail : g.slots[idx]'hIdx = .freeAvail := hsw.2.1.mp hBitTrue
    have hSlotsEq : g.slots = [.freeAvail] := by
      rcases hs : g.slots with _ | ⟨x, _ | _⟩
      · simp [hs] at hLen1
      · simp [hs, hIdx0] at hFreeAvail; simp [hFreeAvail]
      · simp [hs] at hLen1
    have hEmpty : g.isEmpty = true := by simp [GroupDesc.isEmpty, hSlotsEq, SlotState.isFree]
    have hGe := (hwf.empty_groups_bound g hg hEmpty).2.2.2.2.2.2 hLast0
    rw [hScEq] at hGe; omega

theorem claimFreeAvailInflight_absorb {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hAvailNe : g.availMask ≠ 0#32) :
    let idx := ctz32DeBruijn g.availMask
    let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
    let g' := mkReplaceSlotGroup g idx newAvail .claimed
    let val' := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
    let st1 := mkReplaceSlotSt st g idx newAvail .claimed val' st.liveMap
    idx < g.slots.length ∧
    idx < 32 ∧
    g'.isMmapped = false ∧
    st1.metaAreas.length = st.metaAreas.length ∧
    totalLiveCount st1 = totalLiveCount st ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st1 ∧
    g' ∈ st1.groups ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      ((g.metaPtr ↦ₛ g.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) ∧
    ((g.metaPtr ↦ₛ g'.metaBytes) ∗
      ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) := by
  intro idx newAvail g' val' st1
  have hgw := hwf.groups_wf g hg
  obtain ⟨_, hIdx32, _, hIso, _, hSet, _, _⟩ := ctz32DeBruijn_spec hAvailNe
  obtain ⟨hBitTrue, _, hRemBit, hRemAnd, hRemOr⟩ := bit32_sub_pow2_props idx hIdx32 g.availMask hIso hSet
  have hIdxCnt : idx < g.cnt := Classical.byContradiction fun hGe => by
    have hPowLe : 2 ^ g.cnt ≤ 2 ^ idx := Nat.pow_le_pow_right (n := 2) (by omega) (Nat.le_of_not_lt hGe)
    have hShiftNat : (1#32 <<< idx).toNat = 2 ^ idx := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
        Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by omega) hIdx32)]
    have hAndLe : (g.availMask &&& (1#32 <<< idx)).toNat ≤ g.availMask.toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_left
    have hOrGe : g.availMask.toNat ≤ (g.availMask ||| g.freedMask).toNat :=
      BitVec.le_def.mp (by bv_bits : g.availMask ≤ g.availMask ||| g.freedMask)
    rw [hSet, hShiftNat] at hAndLe
    have hOrLt := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hIdx : idx < g.slots.length := by rw [hgw.2.2.1]; exact hIdxCnt
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  have hFreeAvail : g.slots[idx]'hIdx = .freeAvail := hsw.2.1.mp hBitTrue
  have hNotMmap : g'.isMmapped = false := by
    change g.isMmapped = false
    cases hMm : g.isMmapped with
    | false => rfl
    | true =>
      have hNF := not_isFree_of_isMmapped hwf hg hMm (hFreeAvail ▸ List.getElem_mem hIdx)
      simp [SlotState.isFree] at hNF
  have hMetaOwn := (meta_ownedRw_of_mem_groups hwf hg).2.2.2.2
  have hNotN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by rw [hFreeAvail]; intro _ h; cases h
  have hNotU : ∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c := by rw [hFreeAvail]; intro _ _ _ h; cases h
  have hStartOutMeta : ¬ InRegion g.metaPtr 40 (g.slotStart idx - 4#64) := by
    have hgAll : g.metaPtr ∈ allMetaSlots st :=
      (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
    obtain ⟨_, _, _, ⟨ma, hma, hInMa⟩, _⟩ := allMetaSlots_info hwf hgAll
    obtain ⟨rg, hrg, hrgPos, hRgLo, _, hRgStrict⟩ := group_root_containment hwf hg
    have hGs := group_slot_toNat hgw
    obtain ⟨hStCalc, hEndCalc⟩ := hGs.2.2.2.2.2 idx hIdxCnt
    have hLastEnd := hGs.2.2.2.1
    have hMulS : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
    have hEndMono : (g.slotEnd idx).toNat ≤ (g.slotEnd g.lastIdx).toNat := by
      have : (idx + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt
      omega
    have hRgBound := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
    have hRgTot : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hrgPos]
    have hSub4Nat : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 := by
      have := hGs.1; bv_omega
    have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hInRg : InRegion rg.mem (rg.maplen * 4096) (g.slotStart idx - 4#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by have := hGs.1; omega⟩
    exact fun hIn => DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hrg hrgPos) (hInMa _ hIn) hInRg
  have hMetaLen : g'.metaBytes.length = 40 := GroupDesc.metaBytes_length g'
  have hTargetSw : SlotWf st1 g' idx .claimed := by
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · change writeBytesToMap st.byteVal g.metaPtr g'.metaBytes (g.slotStart idx - 4#64) = 0#8
      rw [writeBytesToMap_out _ _ _ (by rwa [hMetaLen])]; exact hsw.1
    · have hBF : newAvail.getLsbD idx = false := by simpa using hRemBit idx
      simp [g', mkReplaceSlotGroup, hBF]
    · simp only [g', mkReplaceSlotGroup, reduceCtorEq, iff_false, Bool.not_eq_true]
      cases hF : g.freedMask.getLsbD idx with
      | false => rfl
      | true => have hFI := hsw.2.2.1.mp hF; rw [hFreeAvail] at hFI; cases hFI
    · intro hLt; exfalso; have hFI := hsw.2.2.2.1 hLt; rw [hFreeAvail] at hFI; cases hFI
  obtain ⟨hwf1, hg'Mem, _, hCntEq, hDynEq, hMpIff, hCarvIff⟩ := replaceSlot_wf_core (inflight' := inflight + 1)
    hwf hg hIdx hNotN hNotU (fun _ h => by cases h) rfl
    (hRemAnd g.freedMask hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (Nat.lt_of_le_of_lt (hRemOr g.freedMask) hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun j hj => by rw [hRemBit j]; simp [hj])
    (Or.inr hAvailNe)
    (fun a hNotMod => writeBytesToMap_out _ _ _ (fun hIn => hNotMod (Or.inl (by rwa [hMetaLen] at hIn))))
    (readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr g'.metaBytes (by rw [hMetaLen]; decide))
    hTargetSw
    (by have := hwf.inflight_wf; simp [SlotState.isClaimed]; omega)
    (fun p n => ⟨fun h => Or.inr h, fun h => h.elim (fun ⟨_, hE⟩ => by cases hE) id⟩)
    (fun _ _ _ => rfl)
    hwf.live_le_peak (by simp [slotEffCost, hwf.effCost_le_live]) (Nat.le_refl _)
  have hExt := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st)
    st.byteVal g.metaPtr (n := 40) (by decide)
    (fun a ha => (hMetaOwn a ha).2) (fun a ha => (hMetaOwn a ha).1)
  have hReadMeta : readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes :=
    hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hReadMeta] at hExt
  have hAbs := ByteMap_absorb_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a)
    st.byteVal g.metaPtr g'.metaBytes (by rw [hMetaLen]; decide)
    (fun a ha => (hMetaOwn a (by rwa [hMetaLen] at ha)).2)
    (fun _ ha hK => hK.2 (by rwa [hMetaLen] at ha))
  have hRwEq : ByteMap st.masterDom
      (fun a => (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∨ InRegion g.metaPtr g'.metaBytes.length a) val' =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
    unfold ByteMap; refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    rw [hMetaLen]
    have hOwnEq : OwnedRwByte st1 a ↔ OwnedRwByte st a := by
      obtain ⟨_, hGsCases, hGsKeep, _, _, _, _, _, _⟩ :=
        replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl rfl rfl rfl rfl rfl rfl
      unfold OwnedRwByte
      refine ⟨fun ⟨hD, hNC, hNM⟩ => ⟨?_, fun hc => hNC ((hCarvIff a).mpr (Or.inr hc)), hNM⟩,
        fun ⟨hD, hNC, hNM⟩ => ⟨?_, fun hc => hNC (((hCarvIff a).mp hc).elim (fun ⟨_, _, _, hE, _⟩ => by cases hE) id), hNM⟩⟩
      · exact hD.elim Or.inl (fun ⟨x, hx, hp, hi⟩ => (hGsCases x hx).elim
          (fun ⟨_, hE⟩ => by subst hE; exact Or.inr ⟨g, hg, hp, hi⟩) (fun ⟨_, hxO⟩ => Or.inr ⟨x, hxO, hp, hi⟩))
      · exact hD.elim Or.inl (fun ⟨x, hx, hp, hi⟩ =>
          if hE : x.metaPtr = g.metaPtr then
            by have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX; exact Or.inr ⟨g', hg'Mem, hp, hi⟩
          else Or.inr ⟨x, hGsKeep x hx hE, hp, hi⟩)
    rw [hOwnEq]
    exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => (hMetaOwn a h2).1),
      fun h => if hM : InRegion g.metaPtr 40 a then Or.inr hM else Or.inl ⟨h, hM⟩⟩
  have hPnEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := by
    unfold ProtNoneByteMap; refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => ?_)
    obtain ⟨hDisjAp, hDisjGp⟩ := protNone_disjoint_slotWriteMod hwf hg hIdx
    have hOut : ¬ InRegion g.metaPtr 40 a := fun hM =>
      hPn.elim (fun ⟨gp, hgp, ha⟩ => hDisjGp gp hgp a ha (Or.inl hM))
        (fun ⟨ap, hap, ha⟩ => hDisjAp ap hap a ha (Or.inl hM))
    congr 1; exact (writeBytesToMap_out st.byteVal g.metaPtr g'.metaBytes (by rwa [hMetaLen])).symm
  have hMpEq : MappedSet st.masterDom (OwnedMappedByte st) = MappedSet st1.masterDom (OwnedMappedByte st1) := by
    unfold MappedSet; exact SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl)
  exact ⟨hIdx, hIdx32, hNotMmap, rfl, by simpa [slotLiveCount] using hCntEq, hDynEq,
    hwf1, hg'Mem, hExt, hAbs.trans hRwEq, hPnEq, hMpEq⟩

/-! ## `CtxFields` and `ByteMap` Focus Helpers, Head Rotation, and `bounces` Decrement -/

private theorem flatMap_unpack64_len (xs : List (BitVec 64)) :
    (xs.flatMap unpack64).length = 8 * xs.length :=
  unpackL_length xs

private theorem flatMap_unpack64_split (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    xs.flatMap unpack64 =
      (xs.take i).flatMap unpack64 ++ unpack64 (xs[i]'hi) ++ (xs.drop (i + 1)).flatMap unpack64 := by
  have hxs : xs = xs.take i ++ [xs[i]'hi] ++ xs.drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have h1 := congrArg (fun l => l.flatMap unpack64) hxs
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at h1 ⊢
  exact h1

private theorem flatMap_unpack64_set (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) (v : BitVec 64) :
    (xs.set i v).flatMap unpack64 =
      (xs.take i).flatMap unpack64 ++ unpack64 v ++ (xs.drop (i + 1)).flatMap unpack64 := by
  have hxs : xs.set i v = xs.take i ++ [v] ++ xs.drop (i + 1) := by
    simp [List.set_eq_take_append_cons_drop, hi, List.append_assoc]
  have h1 := congrArg (fun l => l.flatMap unpack64) hxs
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at h1 ⊢
  exact h1

theorem ctx_focus_active (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) {sc : Nat} (hsc : sc < 48) (v : BitVec 64) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) =
        (((ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (c.active[sc]'(hAct ▸ hsc))) ∗ Rest) ∧
      (((ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ v) ∗ Rest) =
        (ctx ↦ₛ { c with active := c.active.set sc v }.toBytes) := by
  have hsc' : sc < c.active.length := hAct ▸ hsc
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ (c.active.take sc).flatMap unpack64
  let suf := (c.active.drop (sc + 1)).flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 80 + 8 * sc := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len, List.length_take, hAct]; omega
  have hAddr1 : ctx + BitVec.ofNat 64 (80 + 8 * sc) = ctx + 80#64 + BitVec.ofNat 64 (8 * sc) := by bv_omega
  have hAddr2 : ctx + 80#64 + BitVec.ofNat 64 (8 * sc) + 8#64 = ctx + BitVec.ofNat 64 (88 + 8 * sc) := by bv_omega
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + BitVec.ofNat 64 (88 + 8 * sc)) ↦ₛ suf), ?_, ?_⟩
  · have hEq : c.toBytes = pre ++ (unpack64 (c.active[sc]'hsc') ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, flatMap_unpack64_split c.active hsc', List.append_assoc]
    rw [hEq, pointsToBytes_append ctx pre, pointsToBytes_append _ (unpack64 _), hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, hAddr1, hAddr2]; ac_rfl
  · have hEq : { c with active := c.active.set sc v }.toBytes = pre ++ (unpack64 v ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, flatMap_unpack64_set c.active hsc' v, List.append_assoc]
    rw [hEq, pointsToBytes_append ctx pre, pointsToBytes_append _ (unpack64 v), hPreLen, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, hAddr1, hAddr2]; ac_rfl

theorem ctx_focus_bounces (ctx : BitVec 64) (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32)
    {k : Nat} (hk : k < 32) (v : BitVec 8) :
    ∃ Rest : SepProp,
      (ctx ↦ₛ c.toBytes) =
        (((ctx + 880#64 + BitVec.ofNat 64 k) ↦₈ (c.bounces[k]'(hBnc ▸ hk))) ∗ Rest) ∧
      (((ctx + 880#64 + BitVec.ofNat 64 k) ↦₈ v) ∗ Rest) =
        (ctx ↦ₛ { c with bounces := c.bounces.set k v }.toBytes) := by
  have hk' : k < c.bounces.length := hBnc ▸ hk
  let pre := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
    unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
    unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
    unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++ c.active.flatMap unpack64 ++
    c.usageByClass.flatMap unpack64 ++ c.unmapSeq ++ c.bounces.take k
  let suf := c.bounces.drop (k + 1) ++ [c.seq] ++ c.seqPad ++ unpack64 c.brk
  have hPreLen : pre.length = 880 + k := by
    simp only [pre, List.length_append, unpack64_length, unpack32_length,
      flatMap_unpack64_len, List.length_take, hAct, hUse, hUnm, hBnc]; omega
  have hAddr1 : ctx + BitVec.ofNat 64 (880 + k) = ctx + 880#64 + BitVec.ofNat 64 k := by bv_omega
  refine ⟨(ctx ↦ₛ pre) ∗ ((ctx + 880#64 + BitVec.ofNat 64 k + 1#64) ↦ₛ suf), ?_, ?_⟩
  · have hB1 : c.bounces = c.bounces.take k ++ [c.bounces[k]'hk'] ++ c.bounces.drop (k + 1) := by
      rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hk', List.take_append_drop]
    have hEq : c.toBytes = pre ++ ([c.bounces[k]'hk'] ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
      rw (occs := .pos [1]) [hB1]; simp only [List.append_assoc]
    rw [hEq, pointsToBytes_append ctx pre, pointsToBytes_append _ [_], hPreLen, List.length_singleton,
      pointsToBytes_singleton, hAddr1]; ac_rfl
  · have hB2 : c.bounces.set k v = c.bounces.take k ++ [v] ++ c.bounces.drop (k + 1) := by
      simp [List.set_eq_take_append_cons_drop, hk', List.append_assoc]
    have hEq : { c with bounces := c.bounces.set k v }.toBytes = pre ++ ([v] ++ suf) := by
      simp only [CtxFields.toBytes, pre, suf, List.append_assoc]
      rw [hB2]; simp only [List.append_assoc]
    rw [hEq, pointsToBytes_append ctx pre, pointsToBytes_append _ [v], hPreLen, List.length_singleton,
      pointsToBytes_singleton, hAddr1]; ac_rfl

theorem slot_byteMap_update40 {dom : List (BitVec 64)} (hNd : dom.Nodup)
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
    (fun a ha => (hSub a (hLen ▸ ha)).2) (fun _ hIn ⟨_, hN⟩ => hN (hLen ▸ hIn))]
  exact SetSep_congr (fun a _ => by
    rw [hLen]
    exact ⟨fun h => h.elim And.left (fun ha => (hSub a ha).1),
      fun h => if ha : InRegion m 40 a then Or.inr ha else Or.inl ⟨h, ha⟩⟩)
    (fun _ _ _ => rfl)

theorem slot_findGroupByMeta_eq_of_mem {st : MallocngSt}
    (hNd : (st.groups.map (·.metaPtr)).Nodup) {g : GroupDesc} (hg : g ∈ st.groups) :
    findGroupByMeta st g.metaPtr = some g := by
  unfold findGroupByMeta
  cases hF : st.groups.find? (·.metaPtr == g.metaPtr) with
  | none => exact False.elim (List.find?_eq_none.mp hF g hg (beq_self_eq_true _))
  | some g' =>
    have hEqP := List.find?_some hF
    exact congrArg some (mem_groups_eq_of_metaPtr hNd (List.mem_of_find?_eq_some hF) hg
      (beq_iff_eq.mp hEqP))

theorem activeList_nodes_map_fst {st : MallocngSt} {ms : List (BitVec 64)}
    (hNd : (st.groups.map (·.metaPtr)).Nodup)
    (hMem : ∀ m ∈ ms, ∃ g ∈ st.groups, g.metaPtr = m) :
    (ms.filterMap (fun m => (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next))).map Prod.fst =
      ms := by
  induction ms with
  | nil => rfl
  | cons m tl ih =>
    obtain ⟨g, hg, rfl⟩ := hMem m (List.mem_cons_self ..)
    simp [slot_findGroupByMeta_eq_of_mem hNd hg, ih (fun x hx => hMem x (List.mem_cons_of_mem _ hx))]

theorem tryAvail_rotate_wf {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < 48)
    {g : GroupDesc} (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : st.ctx.active[sc]'(by rw [hwf.ctx_lens.1]; exact hsc) = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hFrNe : g.freedMask ≠ 0#32) :
    let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
    let ms := st.activeLists[sc]'h2
    let ms1 := ms.tail ++ [g.metaPtr]
    let st1 : MallocngSt :=
      { st with
        ctx := { st.ctx with active := st.ctx.active.set sc g.next }
        activeLists := st.activeLists.set sc ms1 }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 ∧
    (∃ g1 ∈ st1.groups,
      g1.metaPtr = g.next ∧ g1.sc = sc ∧ g1.availMask = 0#32 ∧ g1.freedMask ≠ 0#32 ∧
      (g.activeIdx < g.lastIdx → g.next ≠ g.metaPtr → g1.activeIdx = g1.lastIdx)) := by
  intro h2 ms ms1 st1
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have hmLo := (meta_ownedRw_of_mem_groups hwf hg).1
  have hmNe0 : g.metaPtr ≠ 0#64 := fun h0 => by rw [h0] at hmLo; simp at hmLo
  have hAct : ActiveClassWf st sc (st.ctx.active[sc]'h1) ms := hwf.active_wf sc h1 h2
  let f : BitVec 64 → Option (BitVec 64 × BitVec 64 × BitVec 64) :=
    fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)
  cases hMs : ms with
  | nil =>
    have h0 : st.ctx.active[sc]'h1 = 0#64 := by simpa [hMs, CircularDllWf] using hAct.2.1
    exact False.elim (hmNe0 (hHead.symm.trans h0))
  | cons m0 tl =>
    obtain ⟨g0, hg0, rfl, _⟩ := hAct.1 m0 (hMs ▸ List.mem_cons_self ..)
    have hF0 := slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg0
    have hDll0 : CircularDllWf g.metaPtr ((g0.metaPtr, g0.prev, g0.next) :: tl.filterMap f) := by
      simpa [hMs, hHead, f, hF0] using hAct.2.1
    have rflG0 := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg0 hg hDll0.1.symm
    subst g0
    have hMs1Eq : ms1 = tl ++ [g.metaPtr] := by simp [ms1, hMs]
    have hFmEq : ms1.filterMap f = tl.filterMap f ++ [(g.metaPtr, g.prev, g.next)] := by
      simp [hMs1Eq, List.filterMap_append, f, hF0]
    have hDll1 : CircularDllWf g.next (ms1.filterMap f) := hFmEq ▸ CircularDllWf.rotate_head hDll0
    have hMemIff : ∀ m, m ∈ ms1 ↔ m ∈ ms := fun m => by
      simp [hMs1Eq, hMs, Or.comm]
    have hAct1 : ActiveClassWf st1 sc g.next ms1 := by
      refine ⟨fun m hm => hAct.1 m ((hMemIff m).mp hm), hDll1, ?_,
        fun h hh hScH => ?_, fun i hi hiPos h hh hMH => ?_,
        hAct.2.2.2.2.2.1, fun h hh hScH hLtH => ?_⟩
      · change (ms1.filterMap f).length = ms1.length
        rw [hFmEq, List.length_append, List.length_singleton, hMs1Eq, List.length_append, List.length_singleton]
        have hL : (ms.filterMap f).length = ms.length := hAct.2.2.1
        simp only [hMs, List.filterMap_cons, f, hF0, Option.map_some, List.length_cons] at hL; omega
      · have h4 := hAct.2.2.2.1 h hh hScH
        simpa [hMemIff h.metaPtr] using h4
      · simp only [hMs1Eq] at hi hMH
        by_cases hiTl : i < tl.length
        · rw [List.getElem_append_left hiTl] at hMH
          have hiMs : i + 1 < ms.length := by simp [hMs]; omega
          have hEqElem : tl[i]'hiTl = ms[i + 1]'hiMs := by simp [hMs]
          exact hAct.2.2.2.2.1 (i + 1) hiMs (by omega) h hh (hMH.trans hEqElem)
        · have hiEq : i = tl.length := by simp [List.length_append] at hi; omega
          subst hiEq; simp at hMH
          have rflH := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh hg hMH
          subst h; exact ⟨hAv0, hFrNe⟩
      · obtain ⟨hmIn, hPos⟩ := hAct.2.2.2.2.2.2 h hh hScH hLtH
        exact ⟨(hMemIff h.metaPtr).mpr hmIn, hPos⟩
    have hWf1 : MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 := {
      base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := by
        obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hwf.ctx_lens
        exact ⟨by simp [st1, l1], l2, l3, l4, l5, by simp [st1, l6]⟩
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun hZ => by
        have hGsNil := (hwf.initZero_wf hZ).2.2.2.2.2.2.2.2.2.1
        rw [hGsNil] at hg; cases hg
      bounces_wf := hwf.bounces_wf
      usage_wf := hwf.usage_wf
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := hwf.metaAreas_wf
      guard_avail_wf := hwf.guard_avail_wf
      inflight_wf := hwf.inflight_wf
      free_bump_metas_wf := hwf.free_bump_metas_wf
      groups_nodup := hwf.groups_nodup
      groups_wf := hwf.groups_wf
      regions_disjoint := hwf.regions_disjoint
      active_wf := fun k hk1 hk2 => by
        by_cases hk : k = sc
        · subst hk; simpa [st1] using hAct1
        · simp only [st1, List.getElem_set_ne (Ne.symm hk)]
          exact hwf.active_wf k (by simpa [st1] using hk1) (by simpa [st1] using hk2)
      liveMap_wf := hwf.liveMap_wf
      live_le_peak := hwf.live_le_peak
      effCost_le_live := hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun u hu hEmpty => by
        obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hwf.empty_groups_bound u hu hEmpty
        refine ⟨p1, p2, p3, p4, fun hL => ?_, p6, p7⟩
        by_cases hUSc : u.sc = sc
        · subst hUSc
          dsimp only [st1]; rw [List.getElem_set_self]
          exact (hMemIff u.metaPtr).mpr (p5 h2)
        · simpa [st1, List.getElem_set_ne (Ne.symm hUSc)] using p5 (by simpa [st1] using hL)
      masterDom_wf := hwf.masterDom_wf
    }
    refine ⟨hWf1, ?_⟩
    cases hTl : tl with
    | nil =>
      have hNxEq : g.next = g.metaPtr := by
        have hDllS : CircularDllWf g.metaPtr [(g.metaPtr, g.prev, g.next)] := by simpa [hTl] using hDll0
        exact ((CircularDllWf.singleton_iff_next_eq hDllS).2 rfl).2
      exact ⟨g, hg, hNxEq.symm, hScEq, hAv0, hFrNe, fun _ hNe => False.elim (hNe hNxEq)⟩
    | cons m1 tl' =>
      obtain ⟨g1, hg1, hM1, hSc1⟩ := hAct.1 m1 (hMs ▸ hTl ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hF1 := slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg1
      have hDllC : CircularDllWf g.metaPtr
          ((g.metaPtr, g.prev, g.next) :: (g1.metaPtr, g1.prev, g1.next) :: tl'.filterMap f) := by
        simpa [hTl, f, hF1, ← hM1] using hDll0
      have hNxM1 : g.next = g1.metaPtr := (CircularDllWf.dequeue_head hDllC).1
      have h1Lt : 1 < ms.length := by simp [hMs, hTl]
      have ⟨hAv1, hFr1⟩ := hAct.2.2.2.2.1 1 h1Lt (by omega) g1 hg1 (by simp [hMs, hTl, hM1])
      refine ⟨g1, hg1, hNxM1.symm, hSc1, hAv1, hFr1, fun hLtG hNxNe => ?_⟩
      have hLe1 := (hwf.groups_wf g1 hg1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      by_cases hLt1 : g1.activeIdx < g1.lastIdx
      · exact False.elim (hNxNe (hNxM1.trans (hAct.2.2.2.2.2.1 g hg g1 hg1 hScEq hSc1 hLtG hLt1).symm))
      · omega

private theorem mask32_bits_check :
    ((List.range 32).all fun k =>
      ((List.range 32).all fun j =>
        ((((2#32 <<< k) - 1#32).getLsbD j) == decide (j ≤ k)) &&
        (((-(2#32 <<< k)).getLsbD j) == decide (k < j)))) = true := by decide +kernel

theorem activateMask_props {actIdx lastIdx : Nat} {m : BitVec 32}
    (hActLe : actIdx ≤ lastIdx) (hLast : lastIdx ≤ 31)
    (hBound : m.toNat < 2 ^ (lastIdx + 1)) :
    let cntMask := (2#32 <<< actIdx) - 1#32
    let hiMask := -(2#32 <<< actIdx)
    (∀ j, j < 32 → cntMask.getLsbD j = decide (j ≤ actIdx) ∧ hiMask.getLsbD j = decide (actIdx < j)) ∧
    (cntMask &&& m) &&& (m &&& hiMask) = 0#32 ∧
    (cntMask &&& m) ||| (m &&& hiMask) = m ∧
    ((cntMask &&& m) ||| (m &&& hiMask)).toNat < 2 ^ (lastIdx + 1) := by
  intro cntMask hiMask
  have hk := List.all_eq_true.mp mask32_bits_check actIdx (List.mem_range.mpr (by omega))
  have hBits : ∀ j, j < 32 → cntMask.getLsbD j = decide (j ≤ actIdx) ∧ hiMask.getLsbD j = decide (actIdx < j) := by
    intro j hj
    have hjB := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true, beq_iff_eq] at hjB
    exact hjB
  have hAnd : (cntMask &&& m) &&& (m &&& hiMask) = 0#32 := by
    ext j hj
    obtain ⟨hc, hh⟩ := hBits j hj
    change ((cntMask &&& m) &&& (m &&& hiMask)).getLsbD j = (0#32).getLsbD j
    simp only [BitVec.getLsbD_and, hc, hh, BitVec.getLsbD_zero]
    by_cases hle : j ≤ actIdx
    · have hlt : ¬ (actIdx < j) := by omega
      simp [hle, hlt]
    · simp [hle]
  have hOr : (cntMask &&& m) ||| (m &&& hiMask) = m := by
    ext j hj
    obtain ⟨hc, hh⟩ := hBits j hj
    change ((cntMask &&& m) ||| (m &&& hiMask)).getLsbD j = m.getLsbD j
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, hc, hh]
    by_cases hle : j ≤ actIdx
    · have hlt : ¬ (actIdx < j) := by omega
      simp [hle, hlt]
    · have hlt : actIdx < j := by omega
      simp [hle, hlt]
  refine ⟨hBits, hAnd, hOr, ?_⟩
  rw [hOr]; exact hBound

theorem activeMask_and_freed_of_eq_lastIdx {g : GroupDesc}
    (hLast : g.lastIdx ≤ 31) (hBound : (g.availMask ||| g.freedMask).toNat < 2 ^ g.cnt)
    (hEq : g.activeIdx = g.lastIdx) :
    ((2#32 <<< g.activeIdx) - 1#32) &&& g.freedMask = g.freedMask := by
  have hFrLt : g.freedMask.toNat < 2 ^ (g.lastIdx + 1) := by
    have hOrGe : g.freedMask.toNat ≤ (g.availMask ||| g.freedMask).toNat :=
      BitVec.le_def.mp (by bv_bits : g.freedMask ≤ g.availMask ||| g.freedMask)
    unfold GroupDesc.cnt at hBound; omega
  rw [hEq]
  obtain ⟨hBits, _, _, _⟩ := activateMask_props (Nat.le_refl g.lastIdx) hLast hFrLt
  ext j hj
  obtain ⟨hc, _⟩ := hBits j hj
  change (((2#32 <<< g.lastIdx) - 1#32) &&& g.freedMask).getLsbD j = g.freedMask.getLsbD j
  simp only [BitVec.getLsbD_and, hc]
  by_cases hle : j ≤ g.lastIdx
  · simp [hle]
  · have hZ : g.freedMask.getLsbD j = false := by
      rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hFrLt
        (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hle, hZ]

theorem tryAvail_dec_bounces_wf {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {k : Nat} (hk : k < 32)
    (hNe0 : (st.ctx.bounces[k]'(hwf.ctx_lens.2.2.2.1 ▸ hk)) ≠ 0#8) :
    let hkB : k < st.ctx.bounces.length := hwf.ctx_lens.2.2.2.1 ▸ hk
    let b := st.ctx.bounces[k]'hkB
    let st1 : MallocngSt := { st with ctx := { st.ctx with bounces := st.ctx.bounces.set k (b - 1#8) } }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 := by
  intro hkB b st1
  have hbLe : b.toNat ≤ 150 := hwf.bounces_wf b (List.getElem_mem hkB)
  have hbPos : 0 < b.toNat := by
    cases Nat.eq_zero_or_pos b.toNat with
    | inl h0 => exact False.elim (hNe0 (BitVec.eq_of_toNat_eq (by simpa using h0)))
    | inr hp => exact hp
  have hbSubLe : (b - 1#8).toNat ≤ 150 := by
    have : (b - 1#8).toNat = b.toNat - 1 := by bv_omega
    omega
  exact {
    base_wf := trivial
    brk_bounds := hwf.brk_bounds
    ctx_lens := by
      obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hwf.ctx_lens
      exact ⟨l1, l2, l3, by simp [st1, l4], l5, l6⟩
    initDone_wf := hwf.initDone_wf
    initZero_wf := fun hZ => by
      have hGsNil := (hwf.initZero_wf hZ).2.2.2.2.2.2.2.2.2.1
      rw [hGsNil] at hg; cases hg
    bounces_wf := fun x hx => by
      rcases List.mem_or_eq_of_mem_set hx with hxOld | rfl
      · exact hwf.bounces_wf x hxOld
      · exact hbSubLe
    usage_wf := hwf.usage_wf
    brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := hwf.metaAreas_wf
    guard_avail_wf := hwf.guard_avail_wf
    inflight_wf := hwf.inflight_wf
    free_bump_metas_wf := hwf.free_bump_metas_wf
    groups_nodup := hwf.groups_nodup
    groups_wf := hwf.groups_wf
    regions_disjoint := hwf.regions_disjoint
    active_wf := hwf.active_wf
    liveMap_wf := hwf.liveMap_wf
    live_le_peak := hwf.live_le_peak
    effCost_le_live := hwf.effCost_le_live
    meta_pages_bound := hwf.meta_pages_bound
    empty_groups_bound := hwf.empty_groups_bound
    masterDom_wf := hwf.masterDom_wf
  }

end VerifiedLibraries.Mallocng.Proofs
