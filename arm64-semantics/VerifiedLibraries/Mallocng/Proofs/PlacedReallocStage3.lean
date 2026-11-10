/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocStage2

/-!
# Placed `__libc_realloc` Stage 3

Proves the post-`mremap` metadata update, three-way `set_size` slack write, and reconvergence
epilogue (`realloc_s3_post_mremap_ok` and `realloc_s3_finish_ok`) for individual-`mmap` (`sc = 63`)
resizing in `__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Bitvector and Address Helpers -/

theorem and_neg4096_eq_pageMul {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& -4096#64 = BitVec.ofNat 64 ((n / 4096) * 4096) := by
  rw [show ∀ v : BitVec 64, v &&& -4096#64 = (v >>> 12) <<< 12 by intro v; bv_robdd]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]

theorem lsr12_eq_pageDiv {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 12 = BitVec.ofNat 64 (n / 4096) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem bfi_packedWord_maplen (g : GroupDesc) {newBase : BitVec 64} {newMaplen : Nat}
    (hLast : g.lastIdx ≤ 31) (hSc : g.sc < 64) (hNewMap : newMaplen < 2 ^ 52) :
    g.packedWord &&& 4095#64 ||| ((BitVec.ofNat 64 newMaplen &&& 4503599627370495#64) <<< 12) =
      ({ g with mem := newBase, maplen := newMaplen } : GroupDesc).packedWord := by
  have hL := bv64_ult_of_lt (by omega) (Nat.lt_succ_of_le hLast)
  have hS := bv64_ult_of_lt (by omega) hSc
  have hM := bv64_ult_of_lt (k := 2 ^ 52) (by omega) hNewMap
  dsimp only [GroupDesc.packedWord]; revert hL hS hM; bv_robdd

theorem mov_0xa0_res5up {res : Nat} (hRes5 : 5 ≤ res) :
    (160#32 : BitVec 32) = BitVec.ofNat 32 ((min res 5) <<< 5) := by rw [Nat.min_eq_right hRes5]; rfl

theorem cmn_x0_neg1_iff (x0 : BitVec 64) :
    ConditionHolds .EQ (addsPState64 x0 1#64) = true ↔ x0 = -1#64 := by
  have hEq : ConditionHolds .EQ (addsPState64 x0 1#64) = (x0 == -1#64) := by
    unfold addsPState64; dsimp only [ConditionHolds]; bv_robdd
  rw [hEq, beq_iff_eq]

theorem ccmp_sc_newSz_ls_iff {sc newSz : Nat} (hSc : sc < 48 ∨ sc = 63) (hNewHi : newSz < 2 ^ 64) :
    ConditionHolds .LS (if ConditionHolds .HI (subsPState32 (BitVec.ofNat 32 sc) 47#32) then
      subsPState64 (BitVec.ofNat 64 newSz) 131051#64 else PState.ofBits4 0#4) = true ↔
      (sc < 48 ∨ newSz ≤ 131051) := by
  rcases hSc with hLt | rfl
  · have hHi : ConditionHolds .HI (subsPState32 (BitVec.ofNat 32 sc) 47#32) = false := by
      have hUlt : (BitVec.ofNat 32 sc).ult 48#32 = true := by
        rw [BitVec.ult, decide_eq_true_eq]; simp only [BitVec.toNat_ofNat]; omega
      generalize BitVec.ofNat 32 sc = v at hUlt; unfold subsPState32; dsimp only [ConditionHolds]; revert hUlt; bv_robdd
    rw [hHi]; simp only [Bool.false_eq_true, ↓reduceIte, hLt, true_or, iff_true]; decide
  · have hHi63 : ConditionHolds .HI (subsPState32 (BitVec.ofNat 32 63) 47#32) = true := by
      unfold subsPState32; dsimp only [ConditionHolds]; bv_robdd
    rw [hHi63]; simp only [↓reduceIte, show ¬ (63 < 48) by decide, false_or]
    have hLs : ∀ v : BitVec 64, ConditionHolds .LS (subsPState64 v 131051#64) = v.ule 131051#64 := by
      intro v; unfold subsPState64; dsimp only [ConditionHolds]; bv_robdd
    rw [hLs, BitVec.ule, decide_eq_true_eq]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNewHi]

theorem sc63_oldHdr_and31 {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat}
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff) :
    (st.byteVal (p - 3#64)).zeroExtend 32 &&& 0x1f#32 = 0#32 := by
  have hgw := hwf.groups_wf g hg
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx0
  rw [hSlot0] at hsw
  have hHdrP3 := hsw.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hHdrP3]
  exact (hdrByte_extract _ 0 (Nat.min_le_right _ _) (by decide)).1

theorem sc63_bsRemap_getD_hdr (val : BitVec 64 → BitVec 8) (g : GroupDesc)
    {p : BitVec 64} {oldSz needed : Nat} (userBs : List (BitVec 8))
    (hUserLen : userBs.length = oldSz)
    (hMemFit : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48)
    (hSt0 : (g.slotStart 0).toNat = g.mem.toNat + 16)
    (hLo : (g.slotStart 0).toNat ≤ p.toNat)
    (hOldFit : 16 + (p.toNat - (g.slotStart 0).toNat) + oldSz + 4 ≤ g.maplen * 4096)
    (hNewFit : 16 + (p.toNat - (g.slotStart 0).toNat) + 4 ≤ needed) :
    let extra := p.toNat - (g.slotStart 0).toNat
    let oldMapBs := mkSc63OldMapBs val g p oldSz userBs
    let bsRemap := oldMapBs.take needed ++ List.replicate (needed - g.maplen * 4096) 0#8
    bsRemap.getD (13 + extra) 0#8 = val (p - 3#64) := by
  intro extra oldMapBs bsRemap
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hOldLen : oldMapBs.length = g.maplen * 4096 :=
    mkSc63OldMapBs_length val g p oldSz userBs hUserLen (by omega) (by omega)
  dsimp only [bsRemap]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [List.length_take, hOldLen]; dsimp only [extra]; omega),
    List.getElem?_take_of_lt (by dsimp only [extra]; omega)]
  dsimp only [oldMapBs, mkSc63OldMapBs]
  rw [List.append_assoc,
    List.getElem?_append_left (by rw [readBytesFromMap_length]; dsimp only [extra]; omega),
    List.getElem?_eq_getElem (by rw [readBytesFromMap_length]; dsimp only [extra]; omega),
    Option.getD_some, readBytesFromMap_getElem]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [bv64_add_toNat (by dsimp only [extra]; omega), bv64_sub_toNat (by omega)]
  dsimp only [extra]; omega

theorem sc63_post_mremap_addrs {newBase : BitVec 64} {needed extra newSz : Nat}
    (hFit48 : newBase.toNat + needed ≤ 2 ^ 48)
    (hSlotFit : 16 + extra + newSz + 4 ≤ needed) :
    let newSlot1 := newBase + 16#64
    let cap0 := BitVec.ofNat 64 needed - 20#64
    let newP := newSlot1 + BitVec.ofNat 64 extra
    let newEnd := newSlot1 + cap0
    let newRes := (needed - 4) - (16 + extra + newSz)
    newSlot1 + cap0 = newBase + BitVec.ofNat 64 (needed - 4) ∧
    newP.toNat = newBase.toNat + 16 + extra ∧
    newP - 3#64 = newBase + BitVec.ofNat 64 (13 + extra) ∧
    newP + (-3#64) = newBase + BitVec.ofNat 64 (13 + extra) ∧
    (1 ≤ newRes → newRes < 2 ^ 31 →
      newEnd + (-BitVec.ofNat 32 newRes).signExtend 64 =
        newBase + BitVec.ofNat 64 (16 + extra + newSz)) ∧
    (5 ≤ newRes →
      newEnd + (-5#64) = newBase + BitVec.ofNat 64 ((needed - 4) - 5) ∧
      newEnd + (-4#64) = newBase + BitVec.ofNat 64 ((needed - 4) - 4)) := by
  intro newSlot1 cap0 newP newEnd newRes
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hEndEq : newSlot1 + cap0 = newBase + BitVec.ofNat 64 (needed - 4) := by
    dsimp only [newSlot1, cap0]; bv_omega
  have hNewPNat : newP.toNat = newBase.toNat + 16 + extra := by
    dsimp only [newP, newSlot1]
    rw [bv64_add_toNat (by rw [bv64_add_toNat (by omega)]; omega), bv64_add_toNat (by omega)]
  have hP3 : newP - 3#64 = newBase + BitVec.ofNat 64 (13 + extra) := by
    dsimp only [newP, newSlot1]; bv_omega
  refine ⟨hEndEq, hNewPNat, hP3, (by bv_lin : newP + (-3#64) = newP - 3#64).trans hP3,
    fun hR1 hR31 => ?_, fun hR5 => ⟨?_, ?_⟩⟩
  · dsimp only [newEnd]
    rw [hEndEq, neg32_sxtw_of_pos_lt31 hR1 hR31,
        show newBase + BitVec.ofNat 64 (needed - 4) + (-BitVec.ofNat 64 newRes) =
          newBase + BitVec.ofNat 64 (needed - 4) - BitVec.ofNat 64 newRes by bv_lin]
    dsimp only [newRes] at hR1 ⊢; bv_omega
  · dsimp only [newEnd]
    rw [hEndEq, show newBase + BitVec.ofNat 64 (needed - 4) + (-5#64) =
      newBase + BitVec.ofNat 64 (needed - 4) - 5#64 by bv_lin]
    dsimp only [newRes] at hR5; bv_omega
  · dsimp only [newEnd]
    rw [hEndEq, show newBase + BitVec.ofNat 64 (needed - 4) + (-4#64) =
      newBase + BitVec.ofNat 64 (needed - 4) - 4#64 by bv_lin]
    dsimp only [newRes] at hR5; bv_omega

/-! ## Reconvergence Tail -/

set_option maxHeartbeats 400000 in
theorem realloc_s3_finish_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hCount : MallocngCountIvsWF bgt ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
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
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
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
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((newBase ↦ₛ bsCur) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗
        (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
        memMapped newBase needed ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth γ st.liveMap ∗
        (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗
        (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
        MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ Frame))
      (fun sf Pf =>
        (∃ newQ : BitVec 64,
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf newQ (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp newQ (newSz, keptBs) ∗
            Frame))) oom := by
  intro sp1 bf keptBs
  let newP := (newBase + 16#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat)
  have _ := hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hNewSlotFit0, _, _, hNeedLo0, hNeedDvd0, _, _, _⟩ :=
    sc63_liveUser_bounds hCount hwf hg hIdx0 hSlot0 hSc63 hNewLo hNewHi
  have hNewSlotFit : 16 + (p.toNat - (g.slotStart 0).toNat) + newSz + 4 ≤ needed := by
    rw [hNeedEq]; exact hNewSlotFit0
  have hNeedLo : 4096 ≤ needed := by rw [hNeedEq]; exact hNeedLo0
  have hNeedDvd : 4096 ∣ needed := by rw [hNeedEq]; exact hNeedDvd0
  have hNeedAl : needed % 4096 = 0 := Nat.mod_eq_zero_of_dvd hNeedDvd
  let extra := p.toNat - (g.slotStart 0).toNat
  let hdrOff := 13 + extra
  let hdr8 := BitVec.ofNat 8 (min ((needed - 4) - (16 + extra + newSz)) 5 <<< 5)
  obtain ⟨_, hNewPNat, hAddrP3Sub, hAddrP3Neg, _, _⟩ := sc63_post_mremap_addrs hNewBaseFit hNewSlotFit
  have hHdrAnd31 := sc63_oldHdr_and31 hwf hg hIdx0 hSlot0
  have hspAlign1 : (s0.sp - 80#64) &&& 15#64 = 0#64 := sp_sub80_align16 hsp0
  let bsFinal := ByteSlice.write8 bsCur hdrOff hdr8
  have hFinalLen : bsFinal.length = needed :=
    (ByteSlice.write8_length bsCur hdrOff hdr8 (by rw [hCurLen]; dsimp only [hdrOff, extra]; omega)).trans hCurLen
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
          (MallocngRoTablesAt maddrs ∗
           (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
           (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
           memMapped newBase needed ∗
           ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
           ReallocMremapFrame maddrs tp st g ∗
           MallocngLiveAuth γ st.liveMap ∗
           (maddrs.lock ↦₃₂ 0#32) ∗
           (maddrs.replaced ↦₃₂ 0#32) ∗
           (maddrs.aaReplaced ↦₃₂ 0#32) ∗
           ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
           MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
           ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
           MallocngTightBlock γ p oldSz al ∗ Frame)))
        (fun sf Pf =>
          (∃ newQ : BitVec 64,
            sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
            (Pf ⊢ stackFrame s0 800 ∗
              MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
              ⌜(MallocngTightInitBlock γ al).pureWf newQ (newSz, keptBs)⌝ ∗
              (MallocngTightInitBlock γ al).interp newQ (newSz, keptBs) ∗
              Frame))) oom := by
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
          MallocngTightBlock γ p oldSz al ∗ Frame ∗ R)
        (Satisfies.mono (Entails.of_eq (by
          generalize (MallocngRoTablesAt maddrs) = PRo
          generalize (ReallocMremapFrame maddrs tp st g) = PFr
          generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
          generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu
          ac_rfl)) hm))
    rintro ⟨hDisjMa, hDisjGp, hDisjAp, hDisjRg⟩
    have hPermRel2 :
        (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s2.mem.perm = s0.mem.perm) ∨
        (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧
          s2.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
      rw [hmem2, hm1Perm]
      exact hPermRel
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesAt maddrs ∗
         (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
         (newBase ↦ₛ bsFinal) ∗
         memMapped newBase needed ∗
         ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame maddrs tp st g ∗
         MallocngLiveAuth γ st.liveMap ∗
         (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗
         (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
         MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MallocngTightBlock γ p oldSz al) ∗ Frame)
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
        (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 s2 ∗
         ⌜(MallocngTightInitBlock γ al).pureWf newP (newSz, keptBs)⌝ ∗
         (MallocngTightInitBlock γ al).interp newP (newSz, keptBs) ∗ Frame))
    · have hwf2 : MallocngWF maddrs.base brkStart s2.brk bgt.liveCost bgt.peakCost st := by
        rwa [hbrk2]
      have hAbs := reallocMremap_absorb (newP := newP) (al := al) γ maddrs tp brkStart bgt ivs0 s0 s2 st
        hCount hwf2 hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal bsFinal
        hNewLo hNewHi hNeedEq hNewBaseGe hNewBaseAl hNewBaseFit hNewPNat
        (hproc2.2.2.1.trans htp0) (hproc2.2.2.2.1.trans hbrks0)
        hOldRw hPermRel2 hDisjMa hDisjGp hDisjAp hDisjRg hSetSize
      refine Entails.trans (sepConj_mono_right (sepConj_mono (reallocSavedHi_entails_memRegions s0 _)
        (sepConj_mono_right (sepConj_mono_left hAbs)))) ?_
      exact Entails.trans bupd_frame_mid (bupd_mono (Entails.of_eq (by ac_rfl)))
    · refine SepWP.mono (realloc_epilogue_ok hb hpc2 hrun2 hsp2 hal2 hsp0
        hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2) ?_
      intro sf Pf _ _ ⟨hsfMem, hsfBrk, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
      have hBrk0 : sf.brk = s0.brk := hsfBrk.trans hbrk2
      have hProc0 : MallocngProcPreserved s0 sf := by
        obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hproc2
        obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hsfProc
        exact ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7⟩
      refine ⟨newP, by rw [hsfMem, hmem2, hm1Perm], hBrk0, hProc0, hsfSp, hsfCS, hsfX0, Entails.trans hPf ?_⟩
      rw [mallocngPostEnv_congr_state (s2 := sf) hsfMem hsfBrk hsfProc.2.2.1 hsfProc.2.2.2.1]
      exact Entails.of_eq (by ac_rfl)
  conv => arg 4; dsimp only [sp1]
  generalize hRestEnv :
    (MallocngRoTablesAt maddrs ∗
     (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
     memMapped newBase needed ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
     ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗
     (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗
     (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
     MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngTightBlock γ p oldSz al ∗ Frame) = RestEnv
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
    (by have hw24' := hw24
        try dsimp only [Reg.x24] at hw24'
        try simp only [wp_norm, arm64_norm] at hw24' ⊢
        try rw [hw24']
        try rw [hCurHdr]
        try rw [hHdrAnd31]
        try rw [BitVec.add_zero]
        dsimp only [hdr8, extra]
        bv_omega)
    (by rw [← hAddrP3Neg]; try simp only [wp_norm, arm64_norm, hx20]; bv_lin)
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

/-! ## Post-`mremap` Metadata and `set_size` -/

private theorem cap0_sub_extra {needed extra : Nat} (h1 : 20 + extra ≤ needed) (h2 : needed < 2 ^ 64) :
    (BitVec.ofNat 64 needed - 20#64) - BitVec.ofNat 64 extra = BitVec.ofNat 64 ((needed - 4) - (16 + extra)) := by bv_omega

private theorem sepWP_bind_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ sFin, sFin = s → SepWP prog ret sFin P post oom) : SepWP prog ret s P post oom := h s rfl

set_option maxHeartbeats 400000 in
theorem realloc_s3_post_mremap_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hCount : MallocngCountIvsWF bgt ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bgt.liveCost bgt.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
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
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
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
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
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
        MallocngTightBlock γ p oldSz al ∗ Frame))
      (fun sf Pf =>
        (∃ newQ : BitVec 64,
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf newQ (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp newQ (newSz, keptBs) ∗ Frame))) oom := by
  intro sp1 bf keptBs bsRemap0
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
  generalize hRestEnv :
    (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
     stackFrameAt (s0.sp - 80#64) 720 ∗ MallocngRoTablesAt maddrs ∗
     (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngTightBlock γ p oldSz al ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post = post' →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  conv => arg 4; arg 1; rw [GroupDesc.metaBytes_pointsTo g.metaPtr g]
  wp_step
  conv => arg 4; arg 1; rw [← GroupDesc.metaBytes_pointsTo g.metaPtr g]
  wp_step; wp_step; wp_step
  wp_str64_slice m1 hm1Perm 16 newBase (by first | rfl | rw [hx0]) (by first | rfl | rw [hx22])
    (by rw [GroupDesc.metaBytes_length]; decide)
  wp_step; wp_step
  wp_str64_slice m2 hm2Perm 32 (({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).packedWord)
    (by rw [hLast0, hSc63])
    (by first | rfl | rw [hx22])
    (by rw [ByteSlice.write64_length _ _ _ (by rw [GroupDesc.metaBytes_length]; decide),
            GroupDesc.metaBytes_length]; decide)
  conv => arg 4; arg 1; rw [metaBytes_write_mem_packedWord g newBase (needed / 4096) _ rfl]
  refine SepWP.weaken_pre (P' := (newBase ↦ₛ bsRemap) ∗
      ((g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗ RestEnv))
    (Entails.of_eq (by ac_rfl)) ?_
  wp_str8_slice m3 hm3Perm (needed - 4) 0#8 rfl
    (by try simp only [wp_norm, arm64_norm]; try rw [hx0]; try rw [hx26]
        exact (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).1)
    (by rw [hRemapLen]; omega)
  have hZeroLen : (ByteSlice.write8 bsRemap (needed - 4) 0#8).length = needed :=
    (ByteSlice.write8_length bsRemap (needed - 4) 0#8 (by rw [hRemapLen]; omega)).trans hRemapLen
  have hZeroHdr : (ByteSlice.write8 bsRemap (needed - 4) 0#8).getD hdrOff 0#8 = st.byteVal (p - 3#64) := by
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hRemapLen]; omega)]
    simp only [show hdrOff ≠ needed - 4 by dsimp only [hdrOff]; omega, ↓reduceIte, hRemapHdr]
  wp_step; wp_step; wp_step; wp_step
  wp_if hEq0
  ·
    have hRes0 : newRes = 0 := by
      try rw [hx20] at hEq0; try rw [hx21] at hEq0; try rw [hx26] at hEq0
      dsimp only [extra] at hCap0Sub hEqCap32; rw [hCap0Sub] at hEq0
      have h0 := hEqCap32.mp hEq0; dsimp only [newRes, extra]; omega
    apply sepWP_bind_state; intro sFin hsFin
    have hPermEqF : sFin.mem.perm = s.mem.perm := by
      rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm3Perm, hm2Perm, hm1Perm]
    have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
        (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧ sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
      rw [hPermEqF]; exact hPermRel
    have hpcF : sFin.pc = b + 0x3b8#64 := by rw [hsFin]; simp
    have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun]
    have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; simp [hbrk]
    have hprocF : MallocngProcPreserved s0 sFin := by
      rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
        by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp]
    have halF : sFin.spAligned = true := by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal
    have hx20F : sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra := by
      rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl
    have hw24F : sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) := by
      rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]; try rw [hx24]; rw [hRes0]; decide
    have hcsF : ReallocUntouchedCS s0 sFin := by
      rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
    clear hsFin; subst hPostGoal; rw [← hRestEnv]
    have hSet0 := setSize_case0 (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
      (by dsimp only [hdrOff, newRes] at hRes0 ⊢; omega) (by rw [hZeroLen]; omega)
    subst hbsRemap
    refine SepWP.weaken_pre (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
      generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
      generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
      (SepWP.mono (realloc_s3_finish_ok hb γ tp brkStart bgt ivs0 s0 sFin st hCount hwf hg hIdx0
        origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal hNewLo hNewHi hNeedSymm.symm
        hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF hpcF hrunF hbrkF hprocF htp0 hbrks0
        hspF halF hsp0 hx20F hw24F hcsF hZeroLen hZeroHdr hSet0)
        (fun _ _ _ _ ⟨newQ, hpEq, rest⟩ => ⟨newQ, hpEq.trans hPermEqF, rest⟩))
  ·
    have hSubsRes' : (BitVec.ofNat 64 ((needed - 4) - (16 + extra))).truncate 32 -
        (BitVec.ofNat 64 newSz).truncate 32 = BitVec.ofNat 32 newRes := by
      rw [show (needed - 4) - (16 + extra) - newSz = newRes by dsimp only [newRes]; omega] at hSubsRes
      exact hSubsRes
    have hSubsResZ : BitVec.zeroExtend 32 (BitVec.ofNat 64 ((needed - 4) - (16 + extra))) -
        BitVec.zeroExtend 32 (BitVec.ofNat 64 newSz) = BitVec.ofNat 32 newRes := hSubsRes'
    have hResPos : 1 ≤ newRes := by
      have hNe0 : (needed - 4) - (16 + extra) - newSz ≠ 0 := fun h0 => by
        have hEqTrue := hEqCap32.mpr h0
        exfalso; revert hEq0
        try rw [hx20]; try rw [hx21]; try rw [hx26]
        dsimp only [extra] at hCap0Sub hEqTrue
        rw [hCap0Sub]; simp [hEqTrue]
      dsimp only [newRes]; omega
    have hAddr1 : (newBase + 16#64) + (BitVec.ofNat 64 needed - 20#64) +
        (0#32 - BitVec.ofNat 32 newRes).signExtend 64 =
        newBase + BitVec.ofNat 64 (hdrOff + 3 + newSz) := by
      rw [BitVec.zero_sub, hHdr3Eq]; exact hAddrRes1 hResPos (by omega)
    wp_step; wp_step; wp_step
    wp_str8_slice m4 hm4Perm (hdrOff + 3 + newSz) 0#8 rfl
      (by rw [← hAddr1]; try simp only [wp_norm, arm64_norm]
          try rw [hx0]; try rw [hx20]; try rw [hx21]; try rw [hx26]
          dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ ⊢
          try rw [hCap0Sub]; try rw [hSubsRes']; try rw [hSubsResZ]; bv_lin)
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
    ·
      have hResLe4 : newRes ≤ 4 := by
        try rw [hx20] at hLe4; try rw [hx21] at hLe4; try rw [hx26] at hLe4
        dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
        try rw [hCap0Sub] at hLe4; try rw [hSubsRes'] at hLe4; try rw [hSubsResZ] at hLe4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            bv32_sle_iff_of_lt31 (by omega) (by decide), decide_eq_true_eq] at hLe4
        exact hLe4
      apply sepWP_bind_state; intro sFin hsFin
      have hPermEqF : sFin.mem.perm = s.mem.perm := by
        rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm4Perm, hm3Perm, hm2Perm, hm1Perm]
      have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
          (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧ sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
        rw [hPermEqF]; exact hPermRel
      have hpcF : sFin.pc = b + 0x3b8#64 := by rw [hsFin]; simp
      have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun]
      have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; simp [hbrk]
      have hprocF : MallocngProcPreserved s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
          by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp]
      have halF : sFin.spAligned = true := by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal
      have hx20F : sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra := by
        rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl
      have hw24F : sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) := by
        rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
        try rw [hx20]; try rw [hx21]; try rw [hx26]
        dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
        try rw [hCap0Sub]; try rw [hSubsRes']; try rw [hSubsResZ]
        rcases (by omega : newRes = 0 ∨ newRes = 1 ∨ newRes = 2 ∨ newRes = 3 ∨ newRes = 4) with hR | hR | hR | hR | hR <;>
          (rw [hR]; decide)
      have hcsF : ReallocUntouchedCS s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin; subst hPostGoal; rw [← hRestEnv]
      have hSet14 := setSize_case1to4 (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
        (by rw [hHdr3Eq]; exact hResPos) (by rw [hHdr3Eq]; exact hResLe4) (by rw [hZeroLen]; omega)
      subst hbsRemap
      refine SepWP.weaken_pre (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
        generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
        generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
        (SepWP.mono (realloc_s3_finish_ok hb γ tp brkStart bgt ivs0 s0 sFin st hCount hwf hg hIdx0
          origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal hNewLo hNewHi hNeedSymm.symm
          hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF hpcF hrunF hbrkF hprocF htp0 hbrks0
          hspF halF hsp0 hx20F hw24F hcsF hLen1 hHdr1 hSet14)
          (fun _ _ _ _ ⟨newQ, hpEq, rest⟩ => ⟨newQ, hpEq.trans hPermEqF, rest⟩))
    ·
      have hResGe5 : 5 ≤ newRes := by
        have hNotLe : ¬ (newRes ≤ 4) := fun h4 => by
          have hSle : BitVec.sle (BitVec.ofNat 32 newRes) 4#32 = true := by
            rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
                bv32_sle_iff_of_lt31 (by omega) (by decide), decide_eq_true_eq]
            exact h4
          exfalso; revert hLe4
          try rw [hx20]; try rw [hx21]; try rw [hx26]
          dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
          try rw [hCap0Sub]; try rw [hSubsRes']; try rw [hSubsResZ]
          simp [hSle]
        omega
      wp_step
      wp_str8_slice m5 hm5Perm ((needed - 4) - 5) 0#8 rfl
        (by rw [← (hAddrRes5 hResGe5).1]; try simp only [wp_norm, arm64_norm]; try rw [hx0]; try rw [hx26]; bv_lin)
        (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)
      have hLen2 : (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8)
          (hdrOff + 3 + newSz) 0#8) ((needed - 4) - 5) 0#8).length = needed :=
        (ByteSlice.write8_length _ _ _ (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)).trans hLen1
      wp_str32_slice m6 hm6Perm ((needed - 4) - 4) (BitVec.ofNat 32 newRes)
        (by try simp only [wp_norm, arm64_norm]; try rw [hx20]; try rw [hx21]; try rw [hx26]
            dsimp only [extra] at hCap0Sub hSubsRes'; rw [hCap0Sub, hSubsRes'])
        (by rw [← (hAddrRes5 hResGe5).2]; try simp only [wp_norm, arm64_norm]; try rw [hx0]; try rw [hx26]; bv_lin)
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
      apply sepWP_bind_state; intro sFin hsFin
      have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
          (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧ sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
        rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm6Perm, hm5Perm, hm4Perm, hm3Perm, hm2Perm, hm1Perm]; exact hPermRel
      have hPermEqF : sFin.mem.perm = s.mem.perm := by
        rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm6Perm, hm5Perm, hm4Perm, hm3Perm, hm2Perm, hm1Perm]
      have hpcF : sFin.pc = b + 0x3b8#64 := by rw [hsFin]; simp
      have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun]
      have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; simp [hbrk]
      have hprocF : MallocngProcPreserved s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
          by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp]
      have halF : sFin.spAligned = true := by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal
      have hx20F : sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra := by
        rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl
      have hw24F : sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) := by
        rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
        exact mov_0xa0_res5up hResGe5
      have hcsF : ReallocUntouchedCS s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin; subst hPostGoal; rw [← hRestEnv]
      have hSet5 := setSize_case5up (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
        (BitVec.ofNat 32 newRes) (by rw [hHdr3Eq]; exact hResGe5) (by rw [hHdr3Eq]) (by rw [hZeroLen]; omega)
      subst hbsRemap
      refine SepWP.weaken_pre (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
        generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
        generalize (MallocngAuxvState γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
        (SepWP.mono (realloc_s3_finish_ok hb γ tp brkStart bgt ivs0 s0 sFin st hCount hwf hg hIdx0
          origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal hNewLo hNewHi hNeedSymm.symm
          hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF hpcF hrunF hbrkF hprocF htp0 hbrks0
          hspF halF hsp0 hx20F hw24F hcsF hLen3 hHdr3 hSet5)
          (fun _ _ _ _ ⟨newQ, hpEq, rest⟩ => ⟨newQ, hpEq.trans hPermEqF, rest⟩))

end VerifiedLibraries.Mallocng.Proofs
