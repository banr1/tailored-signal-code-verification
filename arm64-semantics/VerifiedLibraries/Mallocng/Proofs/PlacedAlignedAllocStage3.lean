/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocStage2
public import VerifiedLibraries.Mallocng.Proofs.Cost.TokSpecs
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `aligned_alloc` Stage 3

Proves `alignedAlloc_reframe_ok`, the unified `+0x1b4` to `ret` stage in `aligned_alloc` (`blk12`)
combining the `delta = 0` and `delta > 0` reframing paths with `alignedAlloc_reframe_finish`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Reframe `delta > 0` Sub-Stages -/

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_fwd_ok [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 12 b)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p len : BitVec 64} {eff : Nat}
    (hStPlus16 : (g.slotStart idx).toNat + 16 ≤ new_p.toNat)
    (hNewFitEnd : new_p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    {bv : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a →
      alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a)
    (hHdrOff :
      let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then
        bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else
        bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
          readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    (hTrl1 : 1 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) → bv (new_p + len) = 0#8)
    (hTrl5 : 5 ≤ (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) →
      bv (g.slotEnd idx - 5#64) = 0#8 ∧
        readBytesFromMap bv (g.slotEnd idx - 4#64) 4 =
          unpack32 (BitVec.ofNat 32 ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat))))
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x234#64) (hrun : s.status = .Running)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk)
    (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = new_p)
    (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 g.stride)
    (hx5 : (s.readReg64 .x5).truncate 8 =
      BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx))
    (hx6 : s.readReg64 .x6 = g.mem + 16#64)
    (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
  have hprog : blkPC_b12.rebase b (fun _ => none) = mallocngBlockProg mmpl 12 msvc := by
    rw [mallocngBlockProg_eq_b12, hb]
  have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1; have hGWf := hwf.groups_wf g hg
  have ⟨hEn48, hIdx31, hBand48, _hBandLo, _hBandHi, _hSub3Hi, _hSub2Lo, _hSub2Hi,
        _hM8Lo, _hM8Hi, _hM4Lo, _hM4Hi, _hM3Lo, _hM3Hi, _hM2Lo, _hM2Hi⟩ :
      (g.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 ∧
      (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ (g.slotStart idx).toNat ∧
      (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (g.slotStart idx).toNat ≤ (g.slotStart idx - 3#64).toNat + 3 ∧
      (g.slotStart idx - 2#64).toNat + 2 ≤ (g.slotStart idx).toNat ∧
      (g.slotStart idx).toNat ≤ (g.slotStart idx - 2#64).toNat + 2 ∧
      (new_p - 8#64).toNat + 8 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 8#64).toNat + 8 ∧
      (new_p - 4#64).toNat + 4 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 4#64).toNat + 4 ∧
      (new_p - 3#64).toNat + 3 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 3#64).toNat + 3 ∧
      (new_p - 2#64).toNat + 2 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 2#64).toNat + 2 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf
    have ⟨_hIdxCnt, _, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hLast31 : g.lastIdx ≤ 31 := hGWf.2.1; have _hCntEq : g.cnt = g.lastIdx + 1 := rfl
    have _hMul1 : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.add_one_mul idx g.stride
    have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
    have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 2) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 8) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 4) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 3) (by omega); have _ := bv64_sub_toNat (a := new_p) (n := 2) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hNewM3Band := subRegion_of_bounds hBand48 (ea := new_p - 3#64) (subLen := 1) (by omega) (by omega)
  have hStM3Band := subRegion_of_bounds hBand48 (ea := g.slotStart idx - 3#64) (subLen := 1) (by omega) (by omega)
  have hStM2Band := subRegion_of_bounds hBand48 (ea := g.slotStart idx - 2#64) (subLen := 2) (by omega) (by omega)
  have hMaddSt := bv_madd_slotStart (g := g) hIdx31
  have _ := hStPlus16; have _ := hNewFitEnd; have _ := hEn48
  wp_step
  refine step_bm8 (pc := b + 0x238#64) (next_pc := b + 0x23c#64) (ea := new_p - 3#64)
    (val := BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx))
    hNodup (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp only [evalAddrMode, arm64_norm, hx0])
    (by simpa [arm64_norm] using hx5)
    (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1) ?_
  intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1
  wp_step; wp_step; wp_step; wp_step
  refine step_bm8 (pc := b + 0x24c#64) (next_pc := b + 0x250#64) (ea := g.slotStart idx - 3#64) (val := 0xe0#8) hNodup
    (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp only [evalAddrMode, arm64_norm])
    (by simp [arm64_norm]) (fun a ha => (hInBand a (hStM3Band a ha)).2) (fun a ha => (hInBand a (hStM3Band a ha)).1) ?_
  intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
  let fwdW16 : BitVec 16 := (((new_p - g.slotStart idx) >>> 4).truncate 16)
  refine step_bm16 (pc := b + 0x250#64) (next_pc := b + 0x254#64) (ea := g.slotStart idx - 2#64) (val := fwdW16) hNodup
    (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
    (by simp [arm64_norm]) (by simp only [evalAddrMode, arm64_norm])
    (by simp [arm64_norm, fwdW16])
    (fun a ha => (hInBand a (hStM2Band a ha)).2) (fun a ha => (hInBand a (hStM2Band a ha)).1) ?_
  intro m3 hm3 hkf3; have hcl3 := hcl2.of_keepsFrozen hkf3
  refine ldp19_20_to_epilogue (offLdp := 0x254) hb hprog (by wp_close_fetch_cl) (by wp_close_fetch_cl)
    (by bv_arith) rfl (by simp [arm64_norm, hrun]) hcl3
    (hm3.trans (hm2.trans (hm1.trans hperm))) (by simp [arm64_norm, hbrk])
    (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0])
    ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
     by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
     by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
     by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩ ?_
  have hGeM8 : ∀ a : BitVec 64, (new_p - 8#64).toNat ≤ a.toNat → a ≠ new_p - 3#64 →
      writeBytesToMap (writeBytesToMap (writeBytesToMap bv (new_p - 3#64)
        [BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (new_p.toNat + len.toNat)) 5 <<< 5) ||| idx)])
        (g.slotStart idx - 3#64) [0xe0#8]) (g.slotStart idx - 2#64) (unpack16 fwdW16) a = bv a := by
    intro a _haLo haNe
    rw [writeBytesToMap_out _ _ _ (fun hIn => by
          have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp hIn; omega),
        writeBytesToMap_out _ _ _ (fun hIn => by
          have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
        writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) haNe)]
  have hNe3 : ∀ a : BitVec 64, a.toNat ≠ (new_p - 3#64).toNat → a ≠ new_p - 3#64 :=
    fun _ hn he => hn (congrArg BitVec.toNat he)
  refine ⟨outBand_write hStM2Band (outBand_write hStM3Band (outBand_write hNewM3Band hOut)), ?_, ?_, ?_, ?_⟩
  · rw [writeBytesToMap_out _ _ _ (fun hIn => by
          have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) _).mp hIn; omega),
        writeBytesToMap_out _ _ _ (fun hIn => by
          have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
    exact writeBytesToMap_self_one _ _ _
  · dsimp only [] at hHdrOff ⊢
    by_cases hTotLe : (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff
    · simp only [hTotLe, ↓reduceIte] at hHdrOff ⊢
      exact ⟨(hGeM8 _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha
          exact hGeM8 a (by omega) (hNe3 a (by omega))).trans hHdrOff.2⟩
    · simp only [hTotLe, ↓reduceIte] at hHdrOff ⊢
      exact ⟨(hGeM8 _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha
          exact hGeM8 a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha
          exact hGeM8 a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.2⟩
  · intro h1
    have _hNewLenNat : (new_p + len).toNat = new_p.toNat + len.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact (hGeM8 _ (by omega) (hNe3 _ (by omega))).trans (hTrl1 h1)
  · intro h5
    have _hEnM5 := bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega)
    have _hEnM4 := bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
    exact ⟨(hGeM8 _ (by omega) (hNe3 _ (by omega))).trans (hTrl5 h5).1,
      (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
        have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha
        exact hGeM8 a (by omega) (hNe3 a (by omega))).trans (hTrl5 h5).2⟩

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_deltaPos_tail_ok [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 12 b)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p new_p len : BitVec 64} {eff : Nat}
    (hStPlus16 : (g.slotStart idx).toNat + 16 ≤ new_p.toNat)
    (hNewFitEnd : new_p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    (hRes31 : (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31)
    {bvHdr : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a →
      alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bvHdr a = st.byteVal a)
    (hHdrOff :
      let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then
        bvHdr (new_p - 4#64) = 0#8 ∧ readBytesFromMap bvHdr (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else
        bvHdr (new_p - 4#64) = 1#8 ∧ readBytesFromMap bvHdr (new_p - 2#64) 2 = [0#8, 0#8] ∧
          readBytesFromMap bvHdr (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot'))
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1f8#64) (hrun : s.status = .Running)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk)
    (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = new_p)
    (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx3 : s.readReg64 .x3 = g.slotEnd idx)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 g.stride)
    (hx6 : s.readReg64 .x6 = g.mem + 16#64)
    (hx20 : s.readReg64 .x20 = len)
    (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bvHdr ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
  have _ := hb
  have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1
  have hGWf := hwf.groups_wf g hg
  have ⟨hEn48, hIdx31, hBand48, _hBandLo, _hBandHi,
        _hNewM8Lo, _hNewM8Hi, _hNewM4Lo, _hNewM4Hi,
        _hNewM3Lo, _hNewM3Hi, _hNewM2Lo, _hNewM2Hi⟩ :
      (g.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 ∧
      (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ (g.slotStart idx).toNat ∧
      (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (new_p - 8#64).toNat + 8 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 8#64).toNat + 8 ∧
      (new_p - 4#64).toNat + 4 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 4#64).toNat + 4 ∧
      (new_p - 3#64).toNat + 3 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 3#64).toNat + 3 ∧
      (new_p - 2#64).toNat + 2 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 2#64).toNat + 2 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf
    have ⟨_hIdxCnt, _, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hLast31 : g.lastIdx ≤ 31 := hGWf.2.1
    have _hCntEq : g.cnt = g.lastIdx + 1 := rfl
    have _hMul1 : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.add_one_mul idx g.stride
    have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 8) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 4) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 3) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 2) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩
  have hNewM3Band := subRegion_of_bounds hBand48 (ea := new_p - 3#64) (subLen := 1) (by omega) (by omega)
  have hHdrOffLift : ∀ bv : BitVec 64 → BitVec 8,
      (∀ a : BitVec 64, a.toNat < new_p.toNat → a ≠ new_p - 3#64 → bv a = bvHdr a) →
      let tot' := (new_p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
        readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot') := fun bv hAg => by
    have hNe3 : ∀ a : BitVec 64, a.toNat ≠ (new_p - 3#64).toNat → a ≠ new_p - 3#64 :=
      fun _ hn he => hn (congrArg BitVec.toNat he)
    dsimp only [] at hHdrOff ⊢
    by_cases hTotLe : (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff
    · simp only [hTotLe, ↓reduceIte] at hHdrOff ⊢
      exact ⟨(hAg _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha
          exact hAg a (by omega) (hNe3 a (by omega))).trans hHdrOff.2⟩
    · simp only [hTotLe, ↓reduceIte] at hHdrOff ⊢
      exact ⟨(hAg _ (by omega) (hNe3 _ (by omega))).trans hHdrOff.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp ha
          exact hAg a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha
          exact hAg a (by omega) (hNe3 a (by omega))).trans hHdrOff.2.2⟩
  let res' := (g.slotEnd idx).toNat - (new_p.toNat + len.toNat)
  have hSubs : (g.slotEnd idx - new_p).truncate 32 - len.truncate 32 = BitVec.ofNat 32 res' :=
    res_subs32_eq hNewFitEnd hEn48
  have hIdxTr8 : ((BitVec.ofNat 32 idx).zeroExtend 64).truncate 8 = BitVec.ofNat 8 idx := by bv_omega
  refine step_bm8 (pc := b + 0x1f8#64) (next_pc := b + 0x1fc#64)
    (ea := new_p - 3#64) (val := BitVec.ofNat 8 idx) hNodup
    hpc (by bv_arith) hrun (by wp_close_fetch_cl)
    (by simp [arm64_norm])
    (by simp only [evalAddrMode, arm64_norm, hx0])
    (by simp only [arm64_norm, hx2]; exact hIdxTr8)
    (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1) ?_
  intro m1 hm1 hkf1
  have hcl1 := hcl.of_keepsFrozen hkf1
  let bv1 := writeBytesToMap bvHdr (new_p - 3#64) [BitVec.ofNat 8 idx]
  have hLowIdx : (BitVec.ofNat 8 idx).zeroExtend 32 &&& 0x1f#32 = BitVec.ofNat 32 idx := by
    have h0 := (hdrByte_extract 0 idx (by omega) hIdx31).1
    simpa using h0
  wp_step; wp_step; wp_step; wp_step
  wp_if hResEq0
  · have hRes0 : res' = 0 := by
      have hEq : (g.slotEnd idx - new_p).truncate 32 - len.truncate 32 = 0#32 := by
        rw [hResEq0, BitVec.sub_self]
      rw [hSubs] at hEq
      have ht := congrArg BitVec.toNat hEq
      simp only [BitVec.toNat_ofNat] at ht
      omega
    dsimp only [res'] at hRes0
    refine alignedAlloc_reframe_fwd_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hInBand
      (outBand_write hNewM3Band hOut)
      (hHdrOffLift _ (fun a _ hNe =>
        writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)))
      (fun _ => by omega) (fun _ => by omega)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl1 (hm1.trans hperm) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx4])
      (by simp only [arm64_norm]
          rw [hRes0, show (min 0 5 <<< 5) ||| idx = idx by simp]; bv_omega)
      (by simp [arm64_norm, hx6])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
       by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
       by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
  · have hResPos : 1 ≤ res' := by
      refine Classical.byContradiction fun hNot => hResEq0 ?_
      have h0 : res' = 0 := by omega
      exact eq_of_sub32_eq_zero (by rw [hSubs, h0])
    have ⟨_hNewLenLo, _hNewLenHi⟩ :
        (new_p + len).toNat ≤ new_p.toNat + len.toNat ∧ new_p.toNat + len.toNat ≤ (new_p + len).toNat := by
      have h := BitVec.toNat_add new_p len
      rw [Nat.mod_eq_of_lt (by omega)] at h; exact ⟨by omega, by omega⟩
    have hNewLenBand := subRegion_of_bounds hBand48 (ea := new_p + len) (subLen := 1) (by omega) (by omega)
    have hEaEnd : g.slotEnd idx + (0#32 - BitVec.ofNat 32 res').signExtend 64 = new_p + len :=
      slotEnd_add_sxtw_neg_res hNewFitEnd hEn48 hResPos hRes31
    wp_step; wp_step
    refine step_bm8 (pc := b + 0x214#64) (next_pc := b + 0x218#64)
      (ea := new_p + len) (val := 0#8) hNodup
      (by simp [arm64_norm]) (by bv_arith)
      (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm, hx3, Prod.mk.injEq, and_true]; exact hEaEnd)
      (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewLenBand a ha)).2) (fun a ha => (hInBand a (hNewLenBand a ha)).1) ?_
    intro m2 hm2 hkf2
    have hcl2 := hcl1.of_keepsFrozen hkf2
    let bv2 := writeBytesToMap bv1 (new_p + len) [0#8]
    wp_step
    wp_if hLe4
    · have hResLe4 : res' ≤ 4 := by
        rwa [bv32_sle4_iff hRes31, decide_eq_true_eq] at hLe4
      conv => arg 4; rw [byteMap_focus8 hNodup bv2 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; rw [← byteMap_focus8 hNodup bv2 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      have hBv2M3 : bv2 (new_p - 3#64) = BitVec.ofNat 8 idx := by
        dsimp only [bv2, bv1]
        rw [writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
        exact writeBytesToMap_self_one _ _ _
      have hPack := hdr3_pack_le4 (hBv2M3.symm ▸ hLowIdx) hIdx31 hResPos hResLe4
      refine alignedAlloc_reframe_fwd_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hInBand
        (outBand_write hNewLenBand (outBand_write hNewM3Band hOut))
        (hHdrOffLift _ (fun a _haLt hNe => by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)]))
        (fun _ => writeBytesToMap_self_one _ _ _) (fun _ => by omega)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl2
        (hm2.trans (hm1.trans hperm)) (by simp [arm64_norm, hbrk])
        (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx4])
        (by simp only [arm64_norm]; exact hPack)
        (by simp [arm64_norm, hx6])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
         by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
         by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
    · have hResGe5 : 5 ≤ res' := by
        rw [bv32_sle4_iff hRes31, decide_eq_true_eq] at hLe4; omega
      have ⟨_hEnM5Lo, _hEnM5Hi, _hEnM4Lo, _hEnM4Hi⟩ :
          (g.slotEnd idx - 5#64).toNat + 5 ≤ (g.slotEnd idx).toNat ∧
          (g.slotEnd idx).toNat ≤ (g.slotEnd idx - 5#64).toNat + 5 ∧
          (g.slotEnd idx - 4#64).toNat + 4 ≤ (g.slotEnd idx).toNat ∧
          (g.slotEnd idx).toNat ≤ (g.slotEnd idx - 4#64).toNat + 4 := by
        have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega)
        have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
        exact ⟨by omega, by omega, by omega, by omega⟩
      have hEnM5Band := subRegion_of_bounds hBand48 (ea := g.slotEnd idx - 5#64) (subLen := 1) (by omega) (by omega)
      have hEnM4Band := subRegion_of_bounds hBand48 (ea := g.slotEnd idx - 4#64) (subLen := 4) (by omega) (by omega)
      refine step_bm8 (pc := b + 0x21c#64) (next_pc := b + 0x220#64)
        (ea := g.slotEnd idx - 5#64) (val := 0#8) hNodup
        (by simp [arm64_norm]) (by bv_arith)
        (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm])
        (by simp only [evalAddrMode, arm64_norm, hx3])
        (by simp [arm64_norm])
        (fun a ha => (hInBand a (hEnM5Band a ha)).2) (fun a ha => (hInBand a (hEnM5Band a ha)).1) ?_
      intro m3 hm3 hkf3
      have hcl3 := hcl2.of_keepsFrozen hkf3
      refine step_bm32 (pc := b + 0x220#64) (next_pc := b + 0x224#64)
        (ea := g.slotEnd idx - 4#64) (val := BitVec.ofNat 32 res') hNodup
        (by simp [arm64_norm]) (by bv_arith)
        (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm])
        (by simp only [evalAddrMode, arm64_norm, hx3])
        (by simp [arm64_norm])
        (fun a ha => (hInBand a (hEnM4Band a ha)).2) (fun a ha => (hInBand a (hEnM4Band a ha)).1) ?_
      intro m4 hm4 hkf4
      have hcl4 := hcl3.of_keepsFrozen hkf4
      let bv4 := writeBytesToMap (writeBytesToMap bv2 (g.slotEnd idx - 5#64) [0#8])
        (g.slotEnd idx - 4#64) (unpack32 (BitVec.ofNat 32 res'))
      conv => arg 4; rw [byteMap_focus8 hNodup bv4 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      wp_step; wp_step; wp_step; wp_step
      conv => arg 4; rw [← byteMap_focus8 hNodup bv4 (new_p - 3#64)
        (fun a ha => (hInBand a (hNewM3Band a ha)).2) (fun a ha => (hInBand a (hNewM3Band a ha)).1)]
      have hBv4M3 : bv4 (new_p - 3#64) = BitVec.ofNat 8 idx := by
        dsimp only [bv4, bv2, bv1]
        rw [writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
        exact writeBytesToMap_self_one _ _ _
      have hPack5 := hdr3_pack_ge5 (hBv4M3.symm ▸ hLowIdx) hIdx31 hResGe5
      refine alignedAlloc_reframe_fwd_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hInBand
        (outBand_write hEnM4Band (outBand_write hEnM5Band (outBand_write hNewLenBand (outBand_write hNewM3Band hOut))))
        (hHdrOffLift _ (fun a _haLt hNe => by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
              writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)]))
        (fun _ => by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega)]
          by_cases hEq5 : new_p + len = g.slotEnd idx - 5#64
          · rw [hEq5]; exact writeBytesToMap_self_one _ _ _
          · rw [writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hEq5)]
            exact writeBytesToMap_self_one _ _ _)
        (fun _ => ⟨by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega)]
          exact writeBytesToMap_self_one _ _ _,
          readBytesFromMap_writeBytesToMap _ _ (unpack32 (BitVec.ofNat 32 res')) (by simp)⟩)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl4
        (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))) (by simp [arm64_norm, hbrk])
        (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx4])
        (by simp only [arm64_norm]; exact hPack5) (by simp [arm64_norm, hx6])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
         by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
         by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩

set_option maxHeartbeats 400000 in
private theorem alignedAlloc_reframe_deltaPos_ok [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 12 b)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p delta new_p len : BitVec 64} {eff : Nat}
    (hNewEq : new_p = p + delta)
    (hStPlus16 : (g.slotStart idx).toNat + 16 ≤ new_p.toNat)
    (hNewFitEnd : new_p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    (hRes31 : (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31)
    (hLargeProps : ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff →
      g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27)
    {bv0 : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a →
      alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut0 : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv0 a = st.byteVal a)
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x1d8#64) (hrun : s.status = .Running)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk)
    (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = p) (hx1 : s.readReg64 .x1 = delta)
    (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx3 : s.readReg64 .x3 = g.slotEnd idx)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 g.stride)
    (hx6 : s.readReg64 .x6 = g.mem + 16#64)
    (hx20 : s.readReg64 .x20 = len)
    (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
  have _ := hb; have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1; have hGWf := hwf.groups_wf g hg
  have ⟨hBand48, _hStorLo, _hNew48, _hBandLo, _hBandHi,
        _hM8Lo, _hM8Hi, _hM4Lo, _hM4Hi, _hM2Lo, _hM2Hi⟩ :
      (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧
      g.storage.toNat ≤ new_p.toNat ∧ new_p.toNat ≤ 2 ^ 48 ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ (g.slotStart idx).toNat ∧
      (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (new_p - 8#64).toNat + 8 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 8#64).toNat + 8 ∧
      (new_p - 4#64).toNat + 4 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 4#64).toNat + 4 ∧
      (new_p - 2#64).toNat + 2 ≤ new_p.toNat ∧ new_p.toNat ≤ (new_p - 2#64).toNat + 2 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf
    have ⟨_, _hStorNat, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hMul1 : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.add_one_mul idx g.stride
    have _ := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 8) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 4) (by omega)
    have _ := bv64_sub_toNat (a := new_p) (n := 2) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hNewM8Band := subRegion_of_bounds hBand48 (ea := new_p - 8#64) (subLen := 4) (by omega) (by omega)
  have hNewM4Band := subRegion_of_bounds hBand48 (ea := new_p - 4#64) (subLen := 1) (by omega) (by omega)
  have hNewM2Band := subRegion_of_bounds hBand48 (ea := new_p - 2#64) (subLen := 2) (by omega) (by omega)
  let tot' := (new_p.toNat - g.storage.toNat) / 16
  have hTot27 : tot' < 2 ^ 27 := by
    by_cases hLe : tot' ≤ 0xffff
    · omega
    · exact (hLargeProps hLe).2.2
  have hNewSymm : p + delta = new_p := hNewEq.symm
  clear hNewEq
  have hStorEq : g.mem + 16#64 = g.storage := rfl
  have hLsr : (new_p - g.storage) >>> 4 = BitVec.ofNat 64 tot' := tot_lsr4_eq (by omega) (by omega)
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  have hHiIff : (0xffff#32).ult ((BitVec.ofNat 64 tot').truncate 32) = decide (¬ tot' ≤ 0xffff) :=
    (conditionHolds_hi_subsPState32 ((BitVec.ofNat 64 tot').truncate 32) 0xffff#32).symm.trans
      (tot_cmp_hi_iff hTot27)
  wp_if hHi
  · have hNotLe : ¬ tot' ≤ 0xffff := by
      have hC := hHi
      try rw [tot_cmp_hi_iff hTot27] at hC
      try rw [hHiIff] at hC
      simpa [decide_eq_true_eq] using hC
    wp_step
    refine step_bm32 (pc := b + 0x2c4#64) (next_pc := b + 0x2c8#64)
      (ea := new_p - 8#64) (val := BitVec.ofNat 32 tot') hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm])
      (by simp only [arm64_norm]; bv_omega)
      (fun a ha => (hInBand a (hNewM8Band a ha)).2) (fun a ha => (hInBand a (hNewM8Band a ha)).1) ?_
    intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1
    refine step_bm8 (pc := b + 0x2c8#64) (next_pc := b + 0x2cc#64)
      (ea := new_p - 4#64) (val := 1#8) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm])
      (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewM4Band a ha)).2) (fun a ha => (hInBand a (hNewM4Band a ha)).1) ?_
    intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
    refine step_bm16 (pc := b + 0x2cc#64) (next_pc := b + 0x2d0#64)
      (ea := new_p - 2#64) (val := 0#16) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm])
      (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewM2Band a ha)).2) (fun a ha => (hInBand a (hNewM2Band a ha)).1) ?_
    intro m3 hm3 hkf3; have hcl3 := hcl2.of_keepsFrozen hkf3
    wp_step
    refine alignedAlloc_reframe_deltaPos_tail_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hRes31 hInBand
      (outBand_write hNewM2Band (outBand_write hNewM4Band (outBand_write hNewM8Band hOut0)))
      (by
        simp only [show ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff from hNotLe, ↓reduceIte]
        refine ⟨by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) _).mp hIn; omega)]
          exact writeBytesToMap_self_one _ _ _,
          readBytesFromMap_writeBytesToMap _ _ (unpack16 0#16) (by simp),
          (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha
            rw [writeBytesToMap_out _ _ _ (fun hIn => by
                  have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) a).mp hIn; omega),
                writeBytesToMap_out _ _ _ (fun hIn => by
                  have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega)]).trans
            (readBytesFromMap_writeBytesToMap _ _ (unpack32 (BitVec.ofNat 32 tot')) (by simp))⟩)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl3
      (hm3.trans (hm2.trans (hm1.trans hperm))) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0
      (by simp [arm64_norm]) (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx3]) (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hx6])
      (by simp [arm64_norm, hx20])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
       by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
       by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
  · have hLe : tot' ≤ 0xffff := by
      refine Classical.byContradiction fun hNot => hHi ?_
      try rw [tot_cmp_hi_iff hTot27]
      try rw [hHiIff]
      simpa [decide_eq_true_eq] using hNot
    refine step_bm8 (pc := b + 0x1f0#64) (next_pc := b + 0x1f4#64)
      (ea := new_p - 4#64) (val := 0#8) hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm])
      (by simp [arm64_norm])
      (fun a ha => (hInBand a (hNewM4Band a ha)).2) (fun a ha => (hInBand a (hNewM4Band a ha)).1) ?_
    intro m1 hm1 hkf1; have hcl1 := hcl.of_keepsFrozen hkf1
    refine step_bm16 (pc := b + 0x1f4#64) (next_pc := b + 0x1f8#64)
      (ea := new_p - 2#64) (val := BitVec.ofNat 16 tot') hNodup
      (by simp [arm64_norm]) (by bv_arith) (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm])
      (by simp only [arm64_norm]; bv_omega)
      (fun a ha => (hInBand a (hNewM2Band a ha)).2) (fun a ha => (hInBand a (hNewM2Band a ha)).1) ?_
    intro m2 hm2 hkf2; have hcl2 := hcl1.of_keepsFrozen hkf2
    refine alignedAlloc_reframe_deltaPos_tail_ok hb hwf hg hIdx hStPlus16 hNewFitEnd hRes31 hInBand
      (outBand_write hNewM2Band (outBand_write hNewM4Band hOut0))
      (by
        simp only [show (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff from hLe, ↓reduceIte]
        exact ⟨by
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 2) (by omega) _).mp hIn; omega)]
          exact writeBytesToMap_self_one _ _ _,
          readBytesFromMap_writeBytesToMap _ _ (unpack16 (BitVec.ofNat 16 tot')) (by simp)⟩)
      rfl (by simp [arm64_norm, hrun]) hcl2
      (hm2.trans (hm1.trans hperm)) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0
      (by simp [arm64_norm]) (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx3]) (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hx6])
      (by simp [arm64_norm, hx20])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
       by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
       by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩

/-! ## Unified Reframe Stage -/

private theorem sbfm_idx_add1 {idx : Nat} (hIdx31 : idx ≤ 31) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 idx + 1#32) &&& 0xffffffff#64 |||
      (if (BitVec.ofNat 32 idx + 1#32)[31] = true then 0xffffffffffffffff#64 else 0#64) &&&
        0xffffffff00000000#64) =
    (((BitVec.ofNat 32 idx).zeroExtend 64 + 1#64).truncate 32).signExtend 64 := by
  have hb31 : (BitVec.ofNat 32 idx + 1#32)[31] = false := by
    rw [BitVec.getElem_eq_testBit_toNat]; apply Nat.testBit_lt_two_pow
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; change (idx % 4294967296 + 1) % 4294967296 < 2147483648; omega
  have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
  rw [hb31]; revert hlt; bv_robdd

set_option maxHeartbeats 400000 in
theorem alignedAlloc_reframe_ok [MallocngMultiPlacement] {prog : Program}
    {b : BitVec 64} (hb : BlkBase 12 b) (hprog : prog = mallocngBlockProg mmpl 12 msvc)
    {B : GhostName → BitVec 64 → Nat → Nat → SepProp} (hB : ∀ γ p n a, MallocngTightBlock γ p n a ⊢ B γ p n a)
    (γ : GhostName) {tp brkStart align len : BitVec 64} {bud : MallocngBudget}
    {st : MallocngSt} {s0 s4 : State}
    (hwf : MallocngWF maddrs.base brkStart s4.brk
      (mallocngAllocBudget true (mallocngAlignedEffSize align.toNat len.toNat) bud).liveCost
      (mallocngAllocBudget true (mallocngAlignedEffSize align.toNat len.toNat) bud).peakCost st)
    (hCnt : MallocngCountIvsWF
      (mallocngAllocBudget true (mallocngAlignedEffSize align.toNat len.toNat) bud)
      (dynamicRootRegions st) st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {bs : List (BitVec 8)}
    (hBsLen : bs.length = mallocngAlignedEffSize align.toNat len.toNat)
    (hSlot : g.slots[idx]'hIdx = .liveUser p (mallocngAlignedEffSize align.toNat len.toNat)
      (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost))
    (hOff255 : p.toNat - (g.slotStart idx).toNat ≤ 255 * 16)
    (hSc24_26 : 24 ≤ g.sc ∧ g.sc ≤ 26 → nominalSlotCap 23 < mallocngAlignedEffSize align.toNat len.toNat)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ mallocngAlignedEffSize align.toNat len.toNat + 4115)
    (hAlignOk : alignedAllocAlignOk align = true) (hAlignMax : align.toNat ≤ MaxAlignedAllocAlign)
    (hNoOvf : len.toNat + align.toNat < 2 ^ 64)
    {sp0 : BitVec 64} {oom : State → SepProp}
    (hpc : s4.pc = b + 0x1b4#64) (hrun : s4.status = .Running)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem)
    (hsp : s4.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s4.readReg64 .x0 = p) (hx2 : s4.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx4 : s4.readReg64 .x4 = BitVec.ofNat 64 g.stride) (hx6 : s4.readReg64 .x6 = g.mem)
    (hx19 : s4.readReg64 .x19 = if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64)
    (hx20 : s4.readReg64 .x20 = len) (hcs21_28 : CalleeSaved21_28 s0 s4) :
    let eff := mallocngAlignedEffSize align.toNat len.toNat
    let b1 := mallocngAllocBudget true eff bud
    let b2 := mallocngAlignedBudget true align.toNat len.toNat bud
    SepWP prog (s0.readReg64 .lr) s4
      (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s4.brk b1.liveCost b1.peakCost st ∗
       MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
       stackFrameAt (sp0 - 32#64) 704 ∗ AlignedSpillSlots sp0 s0)
      (fun sf Pf =>
        (∃ new_p : BitVec 64, sf.readReg64 .x0 = new_p ∧
          (MallocngTokBlock (B γ)).pureWf new_p (len.toNat, max align.toNat 16) ∧
          (Pf ⊢ stackFrameAt sp0 736 ∗
            MallocngCoreImpl γ maddrs brkStart sf.brk b2 (dynamicRootRegions st) ∗
            MallocngRuntime maddrs tp ∗
            (MallocngTokBlock (B γ)).interp new_p (len.toNat, max align.toNat 16))) ∧
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem ∧ sf.mem.perm = s4.mem.perm ∧
        sf.brk = s4.brk ∧ MallocngProcPreserved s4 sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  intro eff b1 b2
  have hProgEq : prog = blkPC_b12.rebase b (fun _ => none) := by rw [hprog, mallocngBlockProg_eq_b12, hb]
  subst hProgEq
  have hGWf := hwf.groups_wf g hg; have ⟨hStr16, _⟩ := group_stride_pos_and_align hGWf
  have ⟨hEn48, hIdx31⟩ : (g.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 := by
    have ⟨_hIdxCnt, _, _, _, _, _hEndLeTot, _hTot48, _, _⟩ := group_slot_bounds hGWf hIdx
    have _hLast31 : g.lastIdx ≤ 31 := hGWf.2.1; have _hCntEq : g.cnt = g.lastIdx + 1 := rfl
    exact ⟨by omega, by omega⟩
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have hBlkP : MallocngBlockWf p eff := hSWf.2.2.2.2.1
  have _hPLo := hSWf.2.2.2.2.2.1; have _hPHi := hSWf.2.2.2.2.2.2.1
  let a16 : BitVec 64 := if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64
  let delta : BitVec 64 := (0#64 - p) &&& (a16 - 1#64)
  let new_p : BitVec 64 := p + delta
  obtain ⟨_, hDelta16, _, hNewNat, hNewFitEff, hAlignDvd, hBlkNew, _⟩ :=
    alignedAlloc_snap_props hAlignOk hAlignMax hNoOvf hBlkP
  have ⟨_hNewLo, _hNewHi⟩ : new_p.toNat ≤ p.toNat + delta.toNat ∧ p.toNat + delta.toNat ≤ new_p.toNat :=
    ⟨Nat.le_of_eq hNewNat, Nat.le_of_eq hNewNat.symm⟩
  clear hNewNat
  change 16 ∣ delta.toNat at hDelta16; change new_p.toNat + len.toNat ≤ p.toNat + eff at hNewFitEff
  change max align.toNat 16 ∣ new_p.toNat at hAlignDvd; change MallocngBlockWf new_p len.toNat at hBlkNew
  obtain ⟨hRes31, hLargeProps⟩ := alignedAlloc_reframe_bounds hwf hg hIdx hSlot hOff255 hSc63 hAlignOk hAlignMax hNoOvf
  change (g.slotEnd idx).toNat - (new_p.toNat + len.toNat) < 2 ^ 31 at hRes31
  change ¬ (new_p.toNat - g.storage.toNat) / 16 ≤ 0xffff →
    g.sc = 63 ∧ idx = 0 ∧ (new_p.toNat - g.storage.toNat) / 16 < 2 ^ 27 at hLargeProps
  obtain ⟨hAbsEq, hInBand, hOut0, hLtP0⟩ := alignedAlloc_absorb_user_pre hwf hg hIdx hSlot hBsLen
  let bv0 := writeBytesToMap st.byteVal p bs
  let Rest :=
    MallocngRoTablesA maddrs ∗ MallocngLiveAuth γ st.liveMap ∗ MallocngBlockToken γ p eff ∗
    (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    ((maddrs.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st) ∗
    MallocngRuntime maddrs tp ∗ stackFrameAt (sp0 - 32#64) 704
  have hPreRearr :
      (MallocngRoTablesA maddrs ∗ MallocngCoreStA γ maddrs brkStart s4.brk b1.liveCost b1.peakCost st ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
        stackFrameAt (sp0 - 32#64) 704 ∗ AlignedSpillSlots sp0 s0) ⊢
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest) := by
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA, mallocngIface, Rest, bv0]
    rw [pure_sepConj_of_true hwf, ← hAbsEq]; sep_frame
  refine SepWP.weaken_pre hPreRearr ?_
  have hSlotEndEq : g.mem + 16#64 +
      (BitVec.setWidth 64 (BitVec.ofNat 32 idx + 1#32) &&& 0xffffffff#64 |||
        (if (BitVec.ofNat 32 idx + 1#32)[31] = true then 0xffffffffffffffff#64 else 0#64) &&&
          0xffffffff00000000#64) * BitVec.ofNat 64 g.stride - 4#64 = g.slotEnd idx := by
    rw [sbfm_idx_add1 hIdx31]; exact bv_madd_slotEnd hStr16 hEn48 hIdx31
  have hRun : SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s4
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest (ReframeBvSpec st g idx new_p len)) oom := by
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hDeltaEq0
    · have hD0 : delta = 0#64 := by simpa [arm64_norm, hx0, hx19, delta, a16] using hDeltaEq0
      have hNewP : new_p = p := by dsimp only [new_p]; rw [hD0, BitVec.add_zero]
      rw [hNewP]
      exact alignedAlloc_reframe_delta0_ok hb hprog hwf hg hIdx hSlot
        (by rw [← hNewP]; omega) (by rw [← hNewP]; exact hRes31) hInBand hOut0 hLtP0
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl rfl (by simp [arm64_norm])
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, hx2]) (by simpa [arm64_norm, hx2, hx4, hx6] using hSlotEndEq)
        (by simp [arm64_norm, hx20])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
    · have hDNe0 : delta ≠ 0#64 := fun hz => hDeltaEq0 (by simpa [arm64_norm, hx0, hx19, delta, a16] using hz)
      have _hDPos : 0 < delta.toNat := Nat.pos_of_ne_zero fun hz => hDNe0 (BitVec.eq_of_toNat_eq hz)
      have ⟨_qD, _hqD⟩ := hDelta16
      exact alignedAlloc_reframe_deltaPos_ok (p := p) (delta := delta) (new_p := new_p) (len := len)
        hb hwf hg hIdx rfl (by omega) (Nat.le_trans hNewFitEff _hPHi) hRes31 hLargeProps hInBand hOut0
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) hcl rfl (by simp [arm64_norm])
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by simp [arm64_norm, hsp]) hsp0 hspAl0
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm, delta, a16])
        (by simp [arm64_norm, hx2]) (by simpa [arm64_norm, hx2, hx4, hx6] using hSlotEndEq)
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm]) (by simp [arm64_norm, hx20])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1], by simp [arm64_norm, hcs21_28.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1], by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩
  refine SepWP.seq hRun ?_
  rintro sf Pf hpc_f hrun_f ⟨bv, ⟨hOut, hHdr3, hHdrOff, hTrl1, hTrl5⟩, hEnt, hcl_f, hperm_f, hbrk_f, hproc_f, hx0_f, hsp_f, hcs_f⟩
  refine SepWP.weaken_pre hEnt ?_
  have hEffEq : eff = len.toNat + (max align.toNat 16 - 16) := by
    dsimp only [eff]; unfold mallocngAlignedEffSize; split <;> omega
  have _hCostLe : max eff MallocngMinBlockCost ≤ max len.toNat MallocngMinBlockCost + (max align.toNat 16 - 16) := by
    rw [hEffEq]; generalize MallocngMinBlockCost = c; omega
  have hFinish := alignedAlloc_reframe_finish (A := maddrs) (brkStart := brkStart) (brk := sf.brk)
    (b1 := b1) (b2 := b2) γ (hbrk_f ▸ hwf) hCnt hg hIdx hSlot hOff255 hSc24_26 hSc63
    hAlignOk hAlignMax hNoOvf rfl
    (by simp only [b1, b2, mallocngAllocBudget, mallocngAlignedBudget, ↓reduceIte]; omega)
    (by simp only [b2, mallocngAlignedBudget, ↓reduceIte]; exact Nat.le_max_right _ _)
    (by simp only [b1, b2, mallocngAllocBudget, mallocngAlignedBudget, ↓reduceIte]; omega)
    rfl (Nat.le_refl _) hOut hHdr3 hHdrOff hTrl1 hTrl5
  refine sepWP_bupd_pre
    (Q := stackFrameAt sp0 736 ∗ MallocngCoreImpl γ maddrs brkStart sf.brk b2 (dynamicRootRegions st) ∗
      MallocngRuntime maddrs tp ∗ (MallocngTokBlock (B γ)).interp new_p (len.toNat, max align.toNat 16)) ?_ ?_
  · refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left hFinish)
        (Entails.trans (bupd_frame_r _ (MallocngRuntime maddrs tp ∗ stackFrameAt sp0 736)) (bupd_mono ?_)))
    · have hStk := spillSlots_repack_736 sp0 s0
      dsimp only [Rest]; refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hStk)); sep_frame
    · refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (hB γ new_p len.toNat (max align.toNat 16))))) ?_
      dsimp only [MallocngTokBlock]; sep_frame
  · have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    refine SepWP.done hpc_f hrun_f
      ⟨⟨new_p, hx0_f, ⟨hBlkNew.1, hAlignDvd, by have := hBlkNew.2.2.1; omega⟩, Entails.refl _⟩,
       hcl_f, hperm_f, hbrk_f, hproc_f, hsp_f, hcs_f⟩

end VerifiedLibraries.Mallocng.Proofs
