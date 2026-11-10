/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupHelpers2

/-!
# Pure Invariant Helpers 3 for Placed `alloc_group`

Proves `wf_alloc_nested`: nested-slot group creation inside placed `alloc_slot` (`blk08`) preserves
`MallocngWFInflight`, `totalLiveEffCost`, and `totalLiveCount`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

private theorem list_set_claimed_cost_count : ∀ (xs : List SlotState) (i : Nat) (hi : i < xs.length),
    xs[i]'hi = .claimed → ∀ (m : BitVec 64),
    ((xs.set i (.liveNested m)).filter SlotState.isClaimed).length + 1 =
      (xs.filter SlotState.isClaimed).length ∧
    ((xs.set i (.liveNested m)).map slotEffCost).sum = (xs.map slotEffCost).sum ∧
    ((xs.set i (.liveNested m)).map slotLiveCount).sum = (xs.map slotLiveCount).sum
  | x :: rest, 0, _, h0, m => by
    have hx : x = .claimed := h0; subst hx
    rw [List.set_cons_zero, List.filter_cons_of_neg Bool.false_ne_true, List.filter_cons_of_pos rfl]
    simp [slotEffCost, slotLiveCount]
  | x :: rest, i + 1, hi, h, m => by
    have ⟨ih1, ih2, ih3⟩ := list_set_claimed_cost_count rest i (Nat.lt_of_succ_lt_succ hi) h m
    simp only [List.set_cons_succ, List.map_cons, List.sum_cons, ih2, ih3, and_self, and_true]
    by_cases hx : SlotState.isClaimed x = true
    · rw [List.filter_cons_of_pos hx, List.filter_cons_of_pos hx]; simp [← ih1]
    · rw [List.filter_cons_of_neg hx, List.filter_cons_of_neg hx]; exact ih1

private theorem groups_set_claimed_sum : ∀ (gs : List GroupDesc), (gs.map (·.metaPtr)).Nodup →
    ∀ {pg : GroupDesc}, pg ∈ gs → ∀ {i : Nat} (hi : i < pg.slots.length),
    pg.slots[i]'hi = .claimed → ∀ (m : BitVec 64),
    let f := fun g : GroupDesc => if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set i (.liveNested m) } else g
    ((gs.map f).map (fun g => (g.slots.filter SlotState.isClaimed).length)).sum + 1 =
      (gs.map (fun g => (g.slots.filter SlotState.isClaimed).length)).sum ∧
    ((gs.map f).map (fun g => (g.slots.map slotEffCost).sum)).sum =
      (gs.map (fun g => (g.slots.map slotEffCost).sum)).sum ∧
    ((gs.map f).map (fun g => (g.slots.map slotLiveCount).sum)).sum =
      (gs.map (fun g => (g.slots.map slotLiveCount).sum)).sum
  | [], _, _, hpg, _, _, _, _ => by cases hpg
  | g :: rest, hnd, pg, hpg, i, hi, hcl, m => by
    obtain ⟨hNotIn, hndR⟩ := List.nodup_cons.mp hnd
    have ⟨hc1, hc2, hc3⟩ := list_set_claimed_cost_count pg.slots i hi hcl m
    rcases List.mem_cons.mp hpg with hEqPg | hpgR
    · subst hEqPg
      have hId : ∀ ls : List GroupDesc, pg.metaPtr ∉ ls.map (·.metaPtr) →
          ls.map (fun x => if x.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set i (.liveNested m) } else x) = ls := by
        intro ls; induction ls with
        | nil => intro _; rfl
        | cons x xs ih =>
          intro hn
          have hne : (x.metaPtr == pg.metaPtr) = false := beq_false_of_ne fun h => hn (by rw [← h]; exact List.Mem.head _)
          simp only [List.map_cons, hne, Bool.false_eq_true, ↓reduceIte, ih fun h => hn (List.Mem.tail _ h)]
      simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, hId rest hNotIn, List.sum_cons, hc2, hc3, and_self, and_true]; omega
    · have hNe : (g.metaPtr == pg.metaPtr) = false :=
        beq_false_of_ne fun h => by dsimp only at hNotIn; rw [h] at hNotIn; exact hNotIn (List.mem_map_of_mem hpgR)
      obtain ⟨ih1, ih2, ih3⟩ := groups_set_claimed_sum rest hndR hpgR hi hcl m
      simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte, List.sum_cons, ih2, ih3, and_self, and_true]; omega

set_option maxHeartbeats 400000 in
theorem wf_alloc_nested {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (inflight + 1) base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc48 : sc < 48) (hscA : sc < st.ctx.active.length)
    (hscL : sc < st.activeLists.length) (hscU : sc < st.ctx.usageByClass.length)
    (hActZero : st.ctx.active[sc]'hscA = 0#64)
    {m : BitVec 64} {resTail : List (BitVec 64)} (hRes : st.reservedMetas = m :: resTail)
    {pg : GroupDesc} (hpg : pg ∈ st.groups) {pIdx : Nat} (hpIdx : pIdx < pg.slots.length)
    (hClaimed : pg.slots[pIdx]'hpIdx = .claimed) (hpSc24 : pg.sc ≤ 24) (hscLtPg : sc < pg.sc)
    {mb : BitVec 64} {lastIdx : Nat} {actB : BitVec 8}
    (hLastGe1 : 1 ≤ lastIdx) (hLast31 : lastIdx ≤ 31)
    (hActLe : (actB &&& 0x1f#8).toNat ≤ lastIdx) (hActPos : (actB &&& 0x1f#8).toNat < lastIdx → 0 < sc)
    (hMbLoStart : (pg.slotStart pIdx).toNat ≤ mb.toNat)
    (hMbAlign : (mb.toNat - (pg.slotStart pIdx).toNat) % 16 = 0)
    (hMbEnd : mb.toNat + (slotStride pg.sc - 4) ≤ (pg.slotEnd pIdx).toNat)
    (hOffUnits : (mb.toNat - pg.storage.toNat) / 16 ≤ 65535)
    (hCapLe : 12 + (lastIdx + 1) * slotStride sc ≤ slotStride pg.sc - 4)
    {slotBs' : List (BitVec 8)} (hSlotBsLen : slotBs'.length = pg.stride + 1)
    (hVStart : writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs' (pg.slotStart pIdx - 4#64) = 0#8)
    (hVEnd : writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs' (pg.slotEnd pIdx) = 0#8)
    (hVMb4 : writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs' (mb - 4#64) = 0#8)
    (hVMb3 : writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs' (mb - 3#64) =
      BitVec.ofNat 8 ((6 <<< 5) ||| pIdx))
    (hVMb2 : readBytesFromMap (writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs') (mb - 2#64) 2 =
      unpack16 (BitVec.ofNat 16 ((mb.toNat - pg.storage.toNat) / 16)))
    (hVMb0 : readBytesFromMap (writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs') mb 8 = unpack64 m)
    (hVMb8 : writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs' (mb + 8#64) = actB)
    (hVCgEnd : writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs'
      (mb + BitVec.ofNat 64 (12 + (lastIdx + 1) * slotStride sc)) = 0#8)
    (hVCgHdr : ∀ idx : Nat, idx < lastIdx + 1 →
      writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs'
        (mb + BitVec.ofNat 64 (12 + idx * slotStride sc)) = 0#8) :
    let activeIdx := (actB &&& 0x1f#8).toNat
    let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32
    let cg : GroupDesc := {
      metaPtr := m, prev := m, next := m, mem := mb,
      availMask := initAvail - 1#32,
      freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail,
      lastIdx := lastIdx, sc := sc, maplen := 0, activeByte := actB,
      parentMeta := some pg.metaPtr, nestedCap := slotStride pg.sc - 4,
      slots := newGroupSlots lastIdx activeIdx, freshZero := false }
    let pg' : GroupDesc := { pg with slots := pg.slots.set pIdx (.liveNested m) }
    let f : GroupDesc → GroupDesc := fun g => if g.metaPtr == pg.metaPtr then pg' else g
    let val₁ := writeBytesToMap st.byteVal (pg.slotStart pIdx - 4#64) slotBs'
    let val' := writeBytesToMap val₁ m cg.metaBytes
    let ctx' : CtxFields := { st.ctx with
      active := st.ctx.active.set sc m,
      usageByClass := st.ctx.usageByClass.set sc (st.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 cg.cnt) }
    let st' : MallocngSt := { st with
      ctx := ctx', reservedMetas := resTail, groups := cg :: st.groups.map f,
      activeLists := st.activeLists.set sc [m],
      masterDom := extendDom st.masterDom m 40, byteVal := val' }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st' ∧
    totalLiveEffCost st' = totalLiveEffCost st ∧
    totalLiveCount st' = totalLiveCount st ∧
    cg.isMmapped = false ∧
    ((m ↦ₛ cg.metaBytes) ∗ ((pg.slotStart pIdx - 4#64) ↦ₛ slotBs') ∗
      ByteMap st.masterDom (fun a => OwnedRwByte st a ∧
        ¬ InRegion (pg.slotStart pIdx - 4#64) (pg.stride + 1) a) st.byteVal) =
      ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) = MappedSet st'.masterDom (OwnedMappedByte st') := by
  intro activeIdx initAvail cg pg' f val₁ val' ctx' st'
  have hmMem : m ∈ st.reservedMetas := hRes ▸ List.Mem.head _
  obtain ⟨hmLo, _, hmHi, hmNotGrp, ⟨maM, hmaM, hInMaM⟩, hmNoCu, hmNoRw, hmDisjRes, hmDisjGrp⟩ :=
    reservedMeta_info hwf hmMem
  have hmNe0 : m ≠ 0#64 := fun h => by rw [h] at hmLo; simp at hmLo
  have hpgWf := hwf.groups_wf pg hpg; have hpCnt : pIdx < pg.cnt := hpgWf.2.2.1 ▸ hpIdx
  have hpgGs := group_slot_toNat hpgWf; obtain ⟨hpgStEq, hpgEnEq, hpgSub4⟩ := hpgGs.2.2.2.2.2 pIdx hpCnt
  have hpgMemLo := hpgWf.2.2.2.2.1; have hpgStorEq := hpgGs.2.2.1
  have hpgEnLe : (pg.slotEnd pIdx).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
    have : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt
    have := hpgGs.2.2.2.1; omega
  obtain ⟨grPg, hgrPg, hgrPgPos, hGrPgLo, _, hGrPgStrict⟩ := group_root_containment hwf hpg
  have hGrPgHi := (hwf.groups_wf grPg hgrPg).2.2.2.2.2.2.1
  have hGrPgTot : grPg.totalBytes = grPg.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPgPos]
  have hPgCapGe : 28 ≤ slotStride pg.sc - 4 := by
    have := (sizeClass_bounds hsc48).1
    have : 2 * slotStride sc ≤ (lastIdx + 1) * slotStride sc := Nat.mul_le_mul_right _ (by omega)
    unfold slotStride at this hCapLe ⊢; omega
  obtain ⟨hZSt0, hZEn0, hClaimOwn⟩ := claimed_slot_ownedRw hwf hpg hpIdx hClaimed
  have hNoMInSlot : ∀ a : BitVec 64, (pg.slotStart pIdx - 4#64).toNat ≤ a.toNat →
      a.toNat ≤ (pg.slotEnd pIdx).toNat → val' a = val₁ a := fun a h1 h2 => by
    dsimp only [val']; refine writeBytesToMap_out _ _ _ ?_
    simp only [GroupDesc.metaBytes_length]; intro haM
    exact (hmDisjGrp grPg hgrPg).2 a haM (by rw [hGrPgTot]; exact (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩)
  have hSpanEq : (pg.slotStart pIdx - 4#64).toNat + (pg.stride + 1) = (pg.slotEnd pIdx).toNat + 1 := by
    have : pIdx * pg.stride + pg.stride = (pIdx + 1) * pg.stride := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hValOut : ∀ a : BitVec 64, ¬ InRegion m 40 a →
      ¬ ((pg.slotStart pIdx - 4#64).toNat < a.toNat ∧ a.toNat < (pg.slotEnd pIdx).toNat) →
      val' a = st.byteVal a := fun a haM hOut => by
    dsimp only [val']; rw [writeBytesToMap_out _ _ _ (by simpa using haM)]
    by_cases haSl : InRegion (pg.slotStart pIdx - 4#64) (pg.stride + 1) a
    · have haB := (inRegion_bounds (by omega)).mp haSl
      by_cases hL : a.toNat = (pg.slotStart pIdx - 4#64).toNat
      · have hEq : a = pg.slotStart pIdx - 4#64 := BitVec.eq_of_toNat_eq hL
        rw [hEq, hZSt0]; exact hVStart
      · have hEq : a = pg.slotEnd pIdx := BitVec.eq_of_toNat_eq (by omega)
        rw [hEq, hZEn0]; exact hVEnd
    · exact writeBytesToMap_out _ _ _ (hSlotBsLen ▸ haSl)
  obtain ⟨hUnMa, hUnAp, hUnFm, hUnBm, hUnGrp⟩ :=
    unchanged_outside_claimed_slot hwf hmMem hpg hpIdx hClaimed hValOut
  obtain ⟨hSlLen, hSlNotEmp, hSlCl, hSlCost, hSlIdx⟩ := newGroupSlots_info hActLe
  obtain ⟨hBmDisj, hBmOr, hBmBits⟩ := newGroupBitmaps_spec hLast31 hActLe
  have hfEq : ∀ g ∈ st.groups, f g =
      { g with slots := if g.metaPtr == pg.metaPtr then pg.slots.set pIdx (.liveNested m) else g.slots } := by
    intro g hg; dsimp only [f]; by_cases h : (g.metaPtr == pg.metaPtr) = true
    · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp h); simp [pg']
    · simp [h]
  have hfPg : f pg = pg' := by dsimp only [f]; simp
  have hCgWf : GroupWf st' cg := by
    have hPgStr16 : pg.stride % 16 = 0 := by
      unfold GroupDesc.stride; split
      · have := hpgGs.1; omega
      · unfold slotStride; omega
    have hMul16 : (pIdx * pg.stride) % 16 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans (Nat.dvd_iff_mod_eq_zero.mpr hPgStr16) (Nat.dvd_mul_left _ _))
    have hPgMem16 := hpgWf.2.2.2.2.2.1
    have hCgStr : cg.stride = slotStride sc := by simp [GroupDesc.stride, cg]
    have hCgTot : cg.totalBytes = slotStride pg.sc - 4 := by simp [GroupDesc.totalBytes, cg]
    have hCgCnt : cg.cnt = lastIdx + 1 := rfl
    have hScStr16 : 16 ≤ slotStride sc := by have := (sizeClass_bounds hsc48).1; unfold slotStride; omega
    have hEndAddr : cg.slotEnd cg.lastIdx = mb + BitVec.ofNat 64 (12 + (lastIdx + 1) * slotStride sc) := by
      have : (lastIdx + 1) * slotStride sc = lastIdx * slotStride sc + slotStride sc := by rw [Nat.add_mul, Nat.one_mul]
      apply BitVec.eq_of_toNat_eq; unfold GroupDesc.slotEnd GroupDesc.slotStart GroupDesc.storage
      rw [show cg.lastIdx = lastIdx from rfl, show cg.mem = mb from rfl, hCgStr]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨Or.inl hsc48, hLast31, hSlLen, fun h63 => absurd h63 (by change sc ≠ 63; omega),
      by change 4096 ≤ mb.toNat; omega, by change mb.toNat % 16 = 0; omega,
      by rw [hCgTot]; change mb.toNat + (slotStride pg.sc - 4) ≤ 2 ^ 48; omega,
      by rw [hCgCnt, hCgStr, hCgTot]; exact hCapLe,
      fun h0 => absurd h0 (by change ¬ (0 < 0); omega),
      by dsimp only [st']; rw [hEndAddr, hNoMInSlot _
           (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
           (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hVCgEnd,
      ⟨fun h0 => absurd h0 (by change ¬ (0 < 0); omega), fun hn => by cases hn⟩,
      fun h0 => absurd h0 (by change ¬ (0 < 0); omega),
      fun _ => ⟨hLastGe1, pg', hfPg ▸ List.Mem.tail _ (List.mem_map_of_mem (f := f) hpg), pIdx,
        by dsimp only [pg']; simp [hpIdx], rfl, by change pg.sc < 48; omega, hscLtPg, hpSc24,
        by dsimp only [pg', cg]; simp, hMbLoStart, hMbEnd, rfl⟩,
      hBmDisj, hBmOr, hActLe,
      by simpa [st', val', cg] using readBytesFromMap_writeBytesToMap val₁ m cg.metaBytes (by simp),
      (readBytesFromMap_congr (by decide) fun a ha => by
        have := (inRegion_bounds (b := mb) (n := 8) (by omega)).mp ha
        exact hNoMInSlot a (by omega) (by omega)).trans hVMb0,
      by have := add_ofNat_toNat (x := mb) (k := 8) (by omega)
         exact (hNoMInSlot (mb + 8#64) (by omega) (by omega)).trans hVMb8,
      fun idx hIdx => ?_⟩
    have hIdxLt : idx < lastIdx + 1 := hSlLen ▸ hIdx
    have hHdrAddr : cg.slotStart idx - 4#64 = mb + BitVec.ofNat 64 (12 + idx * slotStride sc) := by
      have : idx * slotStride sc ≤ (lastIdx + 1) * slotStride sc := Nat.mul_le_mul_right _ (by omega)
      apply BitVec.eq_of_toNat_eq; unfold GroupDesc.slotStart GroupDesc.storage
      rw [show cg.mem = mb from rfl, hCgStr]
      have hSub := sub_ofNat_toNat (x := mb + 16#64 + BitVec.ofNat 64 (idx * slotStride sc)) (k := 4)
        (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      rw [hSub]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hZIdx : st'.byteVal (cg.slotStart idx - 4#64) = 0#8 := by
      have : idx * slotStride sc ≤ (lastIdx + 1) * slotStride sc := Nat.mul_le_mul_right _ (by omega)
      dsimp only [st']; rw [hHdrAddr, hNoMInSlot _
        (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
      exact hVCgHdr idx hIdxLt
    obtain ⟨hS0, hSAv, hSFr⟩ := hSlIdx idx hIdx; obtain ⟨hBAv, hBFr⟩ := hBmBits idx hIdxLt
    refine ⟨hZIdx, hBAv.trans hSAv, hBFr.trans hSFr, fun hGt => hSFr.mp (by change activeIdx < idx at hGt; exact hGt), ?_⟩
    cases idx with
    | zero => rw [hS0 rfl]; trivial
    | succ j =>
      by_cases hj : j + 1 ≤ activeIdx
      · rw [hSAv.mp ⟨by omega, hj⟩]; trivial
      · rw [hSFr.mp (by omega)]; trivial
  have hOldGrpWf : ∀ g ∈ st.groups, GroupWf st' (f g) := fun g hg => by
    have hgWf := hwf.groups_wf g hg
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩ := hwf.groups_wf g hg
    obtain ⟨hG40, hGM8, hGM8b, hGEnd, hGSl⟩ := hUnGrp g hg
    have hc3' : (if g.metaPtr == pg.metaPtr then pg.slots.set pIdx (.liveNested m) else g.slots).length = g.cnt := by
      by_cases hB : (g.metaPtr == pg.metaPtr) = true
      · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB); simp [c3]
      · simp [hB, c3]
    rw [hfEq g hg]
    refine ⟨c1, c2, hc3',
      c4, c5, c6, c7, c8, c9, hGEnd.trans c10, c11, c12, ?_,
      c14, c15, c16, hG40.trans c17, hGM8.trans c18, hGM8b.trans c19, fun idx hIdx => ?_⟩
    · intro hz
      obtain ⟨hl, p₀, hp₀, k, hk, hpM, hpSc, hgLt, hp24, hpSl, hpLo, hpHi, hpCap⟩ := c13 hz
      by_cases hB : (p₀.metaPtr == pg.metaPtr) = true
      · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hp₀ hpg (beq_iff_eq.mp hB)
        have hNe : pIdx ≠ k := fun hEq => by subst hEq; rw [hClaimed] at hpSl; cases hpSl
        exact ⟨hl, pg', hfPg ▸ List.Mem.tail _ (List.mem_map_of_mem (f := f) hp₀), k,
          by dsimp only [pg']; simp [hk], hpM, hpSc, hgLt, hp24,
          by dsimp only [pg']; simpa [List.getElem_set_ne hNe] using hpSl, hpLo, hpHi, hpCap⟩
      · have hfP0 : f p₀ = p₀ := by dsimp only [f]; simp [hB]
        exact ⟨hl, p₀, hfP0 ▸ List.Mem.tail _ (List.mem_map_of_mem (f := f) hp₀), k, hk,
          hpM, hpSc, hgLt, hp24, hpSl, hpLo, hpHi, hpCap⟩
    · have hIdx0 : idx < g.slots.length := by
        split at hIdx
        · next hB =>
          cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
          simpa using hIdx
        · exact hIdx
      by_cases hHit : (g.metaPtr == pg.metaPtr) = true ∧ idx = pIdx
      · obtain ⟨hB, hIdxEq⟩ := hHit; cases hIdxEq.symm
        cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
        simp only [beq_self_eq_true, ↓reduceIte, List.getElem_set_self]
        obtain ⟨_, hAv0, hFr0, hAct0, _⟩ := c20 pIdx hIdx0
        rw [hClaimed] at hAv0 hFr0 hAct0
        have hSub4 := sub_ofNat_toNat (x := mb) (k := 4) (by omega)
        have hSub3 := sub_ofNat_toNat (x := mb) (k := 3) (by omega)
        have hSub2 := sub_ofNat_toNat (x := mb) (k := 2) (by omega)
        have hStDef : ({ pg with slots := pg.slots.set pIdx (.liveNested m) } : GroupDesc).slotStart pIdx = pg.slotStart pIdx := rfl
        have hEnDef : ({ pg with slots := pg.slots.set pIdx (.liveNested m) } : GroupDesc).slotEnd pIdx = pg.slotEnd pIdx := rfl
        unfold SlotWf; dsimp only; rw [hStDef, hEnDef]
        refine ⟨(hNoMInSlot _ (by omega) (by omega)).trans hVStart,
          ⟨fun h => absurd (hAv0.mp h) (by decide), fun h => by cases h⟩,
          ⟨fun h => absurd (hFr0.mp h) (by decide), fun h => by cases h⟩,
          fun hGt => absurd (hAct0 hGt) (by decide),
          by change pg.sc < 48; omega, cg, List.Mem.head _, rfl, rfl, hMbLoStart, hMbAlign, hMbEnd, rfl, hOffUnits,
          (hNoMInSlot (mb - 4#64) (by omega) (by omega)).trans hVMb4,
          (hNoMInSlot (mb - 3#64) (by omega) (by omega)).trans hVMb3,
          (readBytesFromMap_congr (by decide) fun a ha => by
            have := (inRegion_bounds (b := mb - 2#64) (n := 2) (by omega)).mp ha
            exact hNoMInSlot a (by omega) (by omega)).trans hVMb2⟩
      · have hSlEq : (if g.metaPtr == pg.metaPtr then pg.slots.set pIdx (.liveNested m) else g.slots)[idx]'hIdx =
            g.slots[idx]'hIdx0 := by
          by_cases hB : (g.metaPtr == pg.metaPtr) = true
          · have hNe : pIdx ≠ idx := fun h => hHit ⟨hB, h.symm⟩
            cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
            simp [List.getElem_set_ne hNe]
          · simp [hB]
        rw [hSlEq]
        exact slotWf_congr hgWf hIdx0 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (c20 idx hIdx0)
          (hGSl idx hIdx0).1
          (fun cm hs cg₀ hcg₀ hcm hpM => ⟨(hGSl idx hIdx0).2.1 cm hs cg₀ hcg₀ hcm hpM,
            f cg₀, List.Mem.tail _ (List.mem_map_of_mem hcg₀),
            by rw [hfEq cg₀ hcg₀], by rw [hfEq cg₀ hcg₀], by rw [hfEq cg₀ hcg₀], by rw [hfEq cg₀ hcg₀]⟩)
          (hGSl idx hIdx0).2.2
  have hMapMeta : (st.groups.map f).map (·.metaPtr) = st.groups.map (·.metaPtr) := by
    rw [List.map_map]; exact List.map_congr_left fun g hg => by simp only [Function.comp_apply]; rw [hfEq g hg]
  have hMapMem : (st.groups.map f).map (·.mem) = st.groups.map (·.mem) := by
    rw [List.map_map]; exact List.map_congr_left fun g hg => by simp only [Function.comp_apply]; rw [hfEq g hg]
  have hRootAux : ∀ (gs : List GroupDesc), (∀ g ∈ gs, (f g).mem = g.mem ∧ (f g).maplen = g.maplen) →
      ((gs.map f).filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096)) =
      (gs.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096)) := by
    intro gs hfg; induction gs with
    | nil => rfl
    | cons g rest ih =>
      obtain ⟨hm0, hml0⟩ := hfg g (List.Mem.head _)
      have ihR := ih fun x hx => hfg x (List.Mem.tail _ hx)
      simp only [List.map_cons, List.filter_cons, hml0]
      cases decide (0 < g.maplen) <;> simp [hm0, hml0, ihR]
  have hDynEq : dynamicRootRegions st' = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st', cg]
    simp only [Nat.lt_irrefl, decide_false, List.filter_cons, Bool.false_eq_true, ↓reduceIte]
    rw [hRootAux st.groups fun g hg => ⟨by rw [hfEq g hg], by rw [hfEq g hg]⟩]
  have hEmptyAct : st.activeLists[sc]'hscL = [] := by
    have hAct := hwf.active_wf sc hscA hscL
    exact List.eq_nil_of_length_eq_zero (hAct.2.2.1.symm.trans
      (by simp [(CircularDllWf.head_eq_zero_iff hAct.2.1).mp hActZero]))
  obtain ⟨_, _, _, _, hUsedNd, hUsedAll⟩ := hwf.free_bump_metas_wf
  obtain ⟨hDomNd, hDomMem, hBmRwExt, hBmPnExt, hMpExt⟩ :=
    extendDom_spec (st := { st with byteVal := val₁ }) hwf.masterDom_wf.1 hwf.masterDom_wf.2.1 m (n := 40) (by omega)
  have hCuIff : ∀ a : BitVec 64, CarvedUserByte st' a ↔ CarvedUserByte st a := fun a => by
    unfold CarvedUserByte; simp only [st', List.mem_cons, List.mem_map]
    constructor
    · rintro ⟨g', rfl | ⟨g, hg, rfl⟩, s, hs, h⟩
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
        cases i with
        | zero => rw [(hSlIdx 0 hi).1 rfl] at h; cases h
        | succ j =>
          by_cases hj : j + 1 ≤ activeIdx
          · rw [(hSlIdx (j + 1) hi).2.1.mp ⟨by omega, hj⟩] at h; cases h
          · rw [(hSlIdx (j + 1) hi).2.2.mp (by omega)] at h; cases h
      · rw [hfEq g hg] at hs; dsimp only at hs; split at hs
        · next hB =>
          cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
          rcases List.mem_or_eq_of_mem_set hs with hs0 | rfl
          · exact ⟨pg, hg, s, hs0, h⟩
          · cases h
        · exact ⟨g, hg, s, hs, h⟩
    · rintro ⟨g, hg, s, hs, h⟩; refine ⟨f g, Or.inr ⟨g, hg, rfl⟩, s, ?_, h⟩; rw [hfEq g hg]; dsimp only; split
      · next hB =>
        cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
        have hNe : pIdx ≠ i := fun hEq => by subst hEq; rw [hClaimed] at h; cases h
        have hi' : i < (pg.slots.set pIdx (.liveNested m)).length := by simp; exact hi
        have := List.getElem_mem hi'; rwa [List.getElem_set_ne hNe] at this
      · exact hs
  have hRwIff : ∀ a : BitVec 64, OwnedRwByte st' a ↔ OwnedRwByte st a ∨ InRegion m 40 a := fun a => by
    unfold OwnedRwByte CarvedMetaByte; simp only [st', cg, hRes, List.mem_cons, List.mem_map, hCuIff a]; constructor
    · rintro ⟨h1, hNoCu, hNoRes⟩
      by_cases haM : InRegion m 40 a
      · exact Or.inr haM
      · refine Or.inl ⟨?_, hNoCu, fun ⟨mr, hmr, hin⟩ => ?_⟩
        · rcases h1 with hMa | ⟨g', rfl | ⟨g, hg, rfl⟩, hp, hin⟩
          · exact Or.inl hMa
          · exact absurd hp (Nat.lt_irrefl 0)
          · rw [hfEq g hg] at hp hin; exact Or.inr ⟨g, hg, hp, hin⟩
        · exact hmr.elim (fun hEq => haM (hEq ▸ hin)) fun hmrT => hNoRes ⟨mr, hmrT, hin⟩
    · rintro (⟨h1, hNoCu, hNoRes⟩ | haM)
      · refine ⟨?_, hNoCu, fun ⟨mr, hmr, hin⟩ => hNoRes ⟨mr, Or.inr hmr, hin⟩⟩
        exact h1.imp id fun ⟨g, hg, hp, hin⟩ => ⟨f g, Or.inr ⟨g, hg, rfl⟩, by rw [hfEq g hg]; exact hp, by rw [hfEq g hg]; exact hin⟩
      · exact ⟨Or.inl ⟨maM, hmaM, hInMaM a haM⟩, hmNoCu a haM, fun ⟨mr, hmr, hin⟩ => by
          rw [hRes, List.nodup_append, List.nodup_cons] at hUsedNd
          exact DisjointRegions.not_both (hmDisjRes mr (hRes ▸ List.Mem.tail _ hmr) fun hEq => hUsedNd.2.1.1 (hEq ▸ hmr)) haM hin⟩
  have hMpIff : ∀ a : BitVec 64, OwnedMappedByte st' a ↔ OwnedMappedByte st a := fun a => by
    unfold OwnedMappedByte; simp only [st', cg, List.mem_cons, List.mem_map]
    exact ⟨fun h => by rcases h with h1 | h2 | h3 | ⟨g', rfl | ⟨g, hg, rfl⟩, hp, hin⟩
                       · exact Or.inl h1
                       · exact Or.inr (Or.inl h2)
                       · exact Or.inr (Or.inr (Or.inl h3))
                       · exact absurd hp (Nat.lt_irrefl 0)
                       · rw [hfEq g hg] at hp hin; exact Or.inr (Or.inr (Or.inr ⟨g, hg, hp, hin⟩)),
      fun h => by rcases h with h1 | h2 | h3 | ⟨g, hg, hp, hin⟩
                  · exact Or.inl h1
                  · exact Or.inr (Or.inl h2)
                  · exact Or.inr (Or.inr (Or.inl h3))
                  · exact Or.inr (Or.inr (Or.inr ⟨f g, Or.inr ⟨g, hg, rfl⟩, by rw [hfEq g hg]; exact hp, by rw [hfEq g hg]; exact hin⟩))⟩
  obtain ⟨_, _, _, hBmPnExt0, hMpExt0⟩ := extendDom_spec hwf.masterDom_wf.1 hwf.masterDom_wf.2.1 m (n := 40) (by omega)
  obtain ⟨hClSum, hCostSum, hCountSum⟩ := groups_set_claimed_sum st.groups hwf.groups_nodup.1 hpg hpIdx hClaimed m
  have hPermUsed : (st'.groups.map (·.metaPtr) ++ st'.freeMetas.map (·.ptr) ++ st'.bumpMetas ++ st'.reservedMetas).Perm
      (st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas) := by
    dsimp only [st', cg]; rw [List.map_cons, hMapMeta, hRes, List.cons_append]; exact List.perm_middle.symm
  have hCostEq : totalLiveEffCost st' = totalLiveEffCost st := by
    unfold totalLiveEffCost; dsimp only [st', cg]; rw [List.map_cons, List.sum_cons, hSlCost, Nat.zero_add]; exact hCostSum
  have hSlCount : ((newGroupSlots lastIdx activeIdx).map slotLiveCount).sum = 0 := by
    simp [newGroupSlots, slotLiveCount]
  have hCountEq : totalLiveCount st' = totalLiveCount st := by
    unfold totalLiveCount; dsimp only [st', cg]; rw [List.map_cons, List.sum_cons, hSlCount, Nat.zero_add]; exact hCountSum
  have hIsMmap : cg.isMmapped = false := by
    unfold GroupDesc.isMmapped; dsimp only [cg]; simp [show (sc == 63) = false from beq_false_of_ne (by omega)]
  refine ⟨?_, hCostEq, hCountEq, hIsMmap, ?_, ?_, ?_⟩
  · refine {
      base_wf := trivial, brk_bounds := hwf.brk_bounds
      ctx_lens := ⟨by dsimp only [st', ctx']; simp [hwf.ctx_lens.1], by dsimp only [st', ctx']; simp [hwf.ctx_lens.2.1],
        hwf.ctx_lens.2.2.1, hwf.ctx_lens.2.2.2.1, hwf.ctx_lens.2.2.2.2.1, by dsimp only [st']; simp [hwf.ctx_lens.2.2.2.2.2]⟩
      initDone_wf := hwf.initDone_wf, bounces_wf := hwf.bounces_wf, brk_mode_wf := hwf.brk_mode_wf
      initZero_wf := fun hz => by have := (hwf.initZero_wf hz).2.2.2.2.2.2.2.2.1; rw [hRes] at this; cases this
      usage_wf := usageWf_after_allocGroup hwf hscU rfl hLast31
        (by rw [List.map_map]; exact List.map_congr_left fun g hg => by simp only [Function.comp_apply]; rw [hfEq g hg])
      metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => ⟨(hwf.metaAreas_wf.2.1 ma hma).1, (hwf.metaAreas_wf.2.1 ma hma).2.1,
        (hwf.metaAreas_wf.2.1 ma hma).2.2.1, (hUnMa ma hma).trans (hwf.metaAreas_wf.2.1 ma hma).2.2.2⟩, hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
        fun ap hap => ⟨(hwf.guard_avail_wf.2.2.2 ap hap).1, (hwf.guard_avail_wf.2.2.2 ap hap).2.1,
          (hwf.guard_avail_wf.2.2.2 ap hap).2.2.1, (hUnAp ap hap).trans (hwf.guard_avail_wf.2.2.2 ap hap).2.2.2⟩⟩
      inflight_wf := by
        have hInf := hwf.inflight_wf; unfold totalClaimedSlots at hInf ⊢
        dsimp only [st', cg, activeIdx, f, pg'] at hClSum ⊢
        simp only [hRes, List.length_cons, List.map_cons, List.sum_cons, hSlCl] at hInf ⊢; omega
      free_bump_metas_wf := ⟨hwf.free_bump_metas_wf.1, fun fm hfm => (hUnFm fm hfm).trans (hwf.free_bump_metas_wf.2.1 fm hfm),
        hwf.free_bump_metas_wf.2.2.1, fun bm hbm => (hUnBm bm hbm).trans (hwf.free_bump_metas_wf.2.2.2.1 bm hbm),
        hPermUsed.nodup_iff.mpr hUsedNd, fun x => hPermUsed.mem_iff.trans (hUsedAll x)⟩
      groups_nodup := ⟨by dsimp only [st', cg]; rw [List.map_cons, hMapMeta]; exact List.nodup_cons.mpr ⟨hmNotGrp, hwf.groups_nodup.1⟩,
        by dsimp only [st', cg]; rw [List.map_cons, hMapMem]; refine List.nodup_cons.mpr ⟨fun hMem => ?_, hwf.groups_nodup.2⟩
           obtain ⟨g, hg, hEq⟩ := List.mem_map.mp hMem; dsimp only at hEq
           have hgGs := group_slot_toNat (hwf.groups_wf g hg); have hEqNat : g.mem.toNat = mb.toNat := congrArg BitVec.toNat hEq
           have : 1 * 16 ≤ g.cnt * g.stride := Nat.mul_le_mul hgGs.2.1 hgGs.1
           have hgEnd := hgGs.2.2.2.1; have := hpgGs.1; have := hpgGs.2.2.2.1
           have : pIdx * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ (Nat.le_of_lt hpCnt)
           rcases comparable_of_groupContains (x := mb.toNat) hwf hpg hg ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with rfl | hAncPgG | hAncGPg
           · omega
           · obtain ⟨_, _, k, hk, hsK, hLoK, _, _, hHiK⟩ := strictAncestor_slot_bounds hwf hAncPgG hpg
             have hkC := hpgGs.2.2.2.2.2 k (hpgWf.2.2.1 ▸ hk)
             have hkEq : k = pIdx := by
               by_cases hlt : k < pIdx
               · have : (k + 1) * pg.stride ≤ pIdx * pg.stride := Nat.mul_le_mul_right _ hlt; omega
               · by_cases hgt : pIdx < k
                 · have : (pIdx + 1) * pg.stride ≤ k * pg.stride := Nat.mul_le_mul_right _ hgt; omega
                 · omega
             subst hkEq; rw [hClaimed] at hsK; cases hsK
           · obtain ⟨_, _, k, hk, _, hLoK, hMemLe, _, _⟩ := strictAncestor_slot_bounds hwf hAncGPg hg
             have := (hgGs.2.2.2.2.2 k ((hwf.groups_wf g hg).2.2.1 ▸ hk)).1; omega⟩
      groups_wf := fun g' hg' => by
        rcases List.mem_cons.mp hg' with rfl | hgMap
        · exact hCgWf
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgMap; exact hOldGrpWf g hg
      regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
      active_wf := activeWf_after_allocGroup (cg := cg) hwf hscA hscL hEmptyAct hmNe0 hmNotGrp rfl rfl rfl rfl hActPos
        (f := f) (fun g hg => by rw [hfEq g hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl rfl rfl
      liveMap_wf := fun p n => by
        rw [hwf.liveMap_wf p n]; simp only [st', List.mem_cons, List.mem_map]; constructor
        · rintro ⟨g, hg, idx, hIdx, e, hs⟩
          by_cases hB : (g.metaPtr == pg.metaPtr) = true
          · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
            have hNe : pIdx ≠ idx := fun hEq => by subst hEq; rw [hClaimed] at hs; cases hs
            exact ⟨pg', Or.inr ⟨pg, hg, hfPg⟩, idx, by dsimp only [pg']; simp [hIdx], e,
              by dsimp only [pg']; simpa [List.getElem_set_ne hNe] using hs⟩
          · exact ⟨g, Or.inr ⟨g, hg, by dsimp only [f]; simp [hB]⟩, idx, hIdx, e, hs⟩
        · rintro ⟨g', rfl | ⟨g, hg, rfl⟩, idx, hIdx, e, hs⟩
          · cases idx with
            | zero => rw [(hSlIdx 0 hIdx).1 rfl] at hs; cases hs
            | succ j =>
              by_cases hj : j + 1 ≤ activeIdx
              · rw [(hSlIdx (j + 1) hIdx).2.1.mp ⟨by omega, hj⟩] at hs; cases hs
              · rw [(hSlIdx (j + 1) hIdx).2.2.mp (by omega)] at hs; cases hs
          · by_cases hB : (g.metaPtr == pg.metaPtr) = true
            · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
              dsimp only [f, pg'] at hIdx hs; simp only [beq_self_eq_true, ↓reduceIte] at hIdx hs
              have hNe : pIdx ≠ idx := fun hEq => by subst hEq; simp at hs
              rw [List.getElem_set_ne hNe] at hs; exact ⟨pg, hg, idx, by simpa using hIdx, e, hs⟩
            · dsimp only [f] at hIdx hs; simp only [hB, Bool.false_eq_true, ↓reduceIte] at hIdx hs
              exact ⟨g, hg, idx, hIdx, e, hs⟩
      live_le_peak := hwf.live_le_peak, effCost_le_live := hCostEq ▸ hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun g' hg' hEmp => by
        rcases List.mem_cons.mp hg' with rfl | hgMap
        · unfold GroupDesc.isEmpty at hEmp; dsimp only [cg] at hEmp; rw [hSlNotEmp] at hEmp; cases hEmp
        · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgMap; rw [hfEq g hg] at hEmp ⊢
          by_cases hB : (g.metaPtr == pg.metaPtr) = true
          · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg hpg (beq_iff_eq.mp hB)
            unfold GroupDesc.isEmpty at hEmp; simp only [hB, ↓reduceIte, List.all_eq_true] at hEmp
            have hp' : pIdx < (pg.slots.set pIdx (.liveNested m)).length := by simp; exact hpIdx
            cases hEmp _ (by simpa using List.getElem_mem hp')
          · simp only [Bool.not_eq_true] at hB; simp only [hB, Bool.false_eq_true, ↓reduceIte] at hEmp
            obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound g hg hEmp
            refine ⟨e1, e2, e3, e4, fun h1 => ?_, fun g2' hg2' hEmp2 hSc2 => ?_, e7⟩
            · have h2 : g.sc < st.activeLists.length := by dsimp only [st'] at h1; simpa using h1
              have hNeSc : sc ≠ g.sc := fun hEq => by subst hEq; have := e5 h2; rw [hEmptyAct] at this; cases this
              dsimp only [st']; simpa [List.getElem_set_ne hNeSc] using e5 h2
            · rcases List.mem_cons.mp hg2' with rfl | hgMap2
              · unfold GroupDesc.isEmpty at hEmp2; dsimp only [cg] at hEmp2; rw [hSlNotEmp] at hEmp2; cases hEmp2
              · obtain ⟨g2, hg2, rfl⟩ := List.mem_map.mp hgMap2; rw [hfEq g2 hg2] at hEmp2 hSc2 ⊢
                by_cases hB2 : (g2.metaPtr == pg.metaPtr) = true
                · cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg2 hpg (beq_iff_eq.mp hB2)
                  unfold GroupDesc.isEmpty at hEmp2; simp only [hB2, ↓reduceIte, List.all_eq_true] at hEmp2
                  have hp' : pIdx < (pg.slots.set pIdx (.liveNested m)).length := by simp; exact hpIdx
                  cases hEmp2 _ (by simpa using List.getElem_mem hp')
                · simp only [Bool.not_eq_true] at hB2; simp only [hB2, Bool.false_eq_true, ↓reduceIte] at hEmp2
                  exact e6 g2 hg2 hEmp2 hSc2
      masterDom_wf := ⟨hDomNd, fun a h => (hDomMem a).mpr (by
          rcases h with hRw | hPn | hMp
          · exact ((hRwIff a).mp hRw).elim (fun h0 => Or.inl (hwf.masterDom_wf.2.1 a (Or.inl h0))) Or.inr
          · exact Or.inl (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn)))
          · exact Or.inl (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr ((hMpIff a).mp hMp))))),
        fun a ha => by
          rw [hDynEq]; exact ((hDomMem a).mp ha).elim (hwf.masterDom_wf.2.2 a) fun haM =>
            ⟨(maM.base, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmaM))), hInMaM a haM⟩⟩ }
  · have hPgFit : pg.stride + 1 ≤ 2 ^ 64 := by
      have : 1 * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul hpgGs.2.1 (Nat.le_refl _)
      have := hpgGs.2.2.2.2.1; have := hpgWf.2.2.2.2.2.2.1; omega
    have hVal1Slice : ByteMap st.masterDom (OwnedRwByte st) val₁ = ((pg.slotStart pIdx - 4#64) ↦ₛ slotBs') ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (pg.slotStart pIdx - 4#64) (pg.stride + 1) a) st.byteVal := by
      rw [ByteMap_extract_slice (n := pg.stride + 1) hwf.masterDom_wf.1 val₁ (pg.slotStart pIdx - 4#64)
            hPgFit (fun a ha => (hClaimOwn a ha).2) (fun a ha => (hClaimOwn a ha).1)]
      rw [show readBytesFromMap val₁ (pg.slotStart pIdx - 4#64) (pg.stride + 1) = slotBs' from by
        dsimp only [val₁]; rw [← hSlotBsLen]; exact readBytesFromMap_writeBytesToMap st.byteVal _ slotBs' (by omega)]
      exact congrArg (_ ∗ ·) (SetSep_congr (fun _ _ => Iff.rfl) fun a _ ⟨_, hNot⟩ =>
        congrArg (a ↦₈ ·) (writeBytesToMap_out _ _ _ (hSlotBsLen ▸ hNot)))
    have hBmRwExt' : ByteMap st.masterDom (OwnedRwByte st) val₁ =
        ByteMap (extendDom st.masterDom m 40) (OwnedRwByte st) val₁ := hBmRwExt
    rw [← hVal1Slice, hBmRwExt',
        ByteMap_absorb_slice hDomNd val₁ m cg.metaBytes (by simp)
          (fun a ha => (hDomMem a).mpr (Or.inr (by simpa using ha))) (fun a ha => hmNoRw a (by simpa using ha))]
    exact SetSep_congr (fun a _ => by rw [show cg.metaBytes.length = 40 by simp]; exact (hRwIff a).symm) (fun _ _ _ => rfl)
  · refine hBmPnExt0.trans (SetSep_congr (fun _ _ => Iff.rfl) fun a _ hk => congrArg (a ↦₈ₙ ·) (Eq.symm ?_))
    have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
    rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
    have hpd23 := (PairwiseDisjointRegions.append_iff.mp hpd.2.1).2.2
    have hpd3 := PairwiseDisjointRegions.append_iff.mp (PairwiseDisjointRegions.append_iff.mp hpd.2.1).2.1
    have hGrF : grPg ∈ st.groups.filter (fun g => decide (0 < g.maplen)) := List.mem_filter.mpr ⟨hgrPg, decide_eq_true hgrPgPos⟩
    have hInGr : (pg.slotStart pIdx - 4#64).toNat < a.toNat ∧ a.toNat < (pg.slotEnd pIdx).toNat →
        InRegion grPg.mem (grPg.maplen * 4096) a := fun ⟨_, _⟩ =>
      (inRegion_bounds (b := grPg.mem) (n := grPg.maplen * 4096) (by omega)).mpr ⟨by omega, by omega⟩
    rcases hk with ⟨gp, hgp, hin⟩ | ⟨ap, hap, hin⟩
    · exact hValOut a (fun haM => DisjointRegions.not_both (hpd.2.2 (maM.base, 4096) (List.mem_map_of_mem hmaM) (gp, 4096)
          (List.mem_append_left _ (List.mem_map_of_mem hgp))) (hInMaM a haM) hin)
        (fun hInt => DisjointRegions.not_both (hpd23 (gp, 4096) (List.mem_map_of_mem hgp) (grPg.mem, grPg.maplen * 4096)
          (List.mem_append_right _ (List.mem_map_of_mem hGrF))) hin (hInGr hInt))
    · exact hValOut a (fun haM => DisjointRegions.not_both (hpd.2.2 (maM.base, 4096) (List.mem_map_of_mem hmaM) (ap, 4096)
          (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hap)))) (hInMaM a haM) hin)
        (fun hInt => DisjointRegions.not_both (hpd3.2.2 (ap, 4096) (List.mem_map_of_mem hap) (grPg.mem, grPg.maplen * 4096)
          (List.mem_map_of_mem hGrF)) hin (hInGr hInt))
  · exact hMpExt0.trans (SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl))

end VerifiedLibraries.Mallocng.Proofs
