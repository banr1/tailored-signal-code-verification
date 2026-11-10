/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage1
public import VerifiedLibraries.Mallocng.Proofs.Cost.RootLen

/-!
# Placed `alloc_group` Stage 2: Count Selection and Dispatch

Placed symbolic-execution lemmas for `alloc_group` group-count selection (`wp_cnt_loop1`,
`wp_cnt_loop2`, `wp_alloc_group_cnt_join`), root/nested dispatch (`wp_alloc_group_cnt_check`,
`wp_alloc_group_cnt_dispatch`), zeroing (`wp_unmap_zero_loop`), and bounce/sequence updates.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

arm64_proof_prelude

/-! ## Group Count Selection -/

private theorem asr32_cnt_half {cnt : Nat} (hhi : cnt ≤ 32) :
    BitVec.setWidth 64 (BitVec.sshiftRight (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) 1) =
      BitVec.ofNat 64 (cnt / 2) := by
  have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
  have h2 : BitVec.sshiftRight (BitVec.ofNat 32 cnt) 1 = BitVec.ushiftRight (BitVec.ofNat 32 cnt) 1 := by
    have hlt : (BitVec.ofNat 32 cnt).ult (1#32 <<< 31) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change cnt % (2 ^ 32) < 2 ^ 31
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    revert hlt; bv_robdd
  rw [h1, h2]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change ((cnt % (2 ^ 32)) >>> 1) % (2 ^ 64) = (cnt / 2) % (2 ^ 64)
  rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]; omega

private theorem smull_stride_cnt {cnt stride : Nat} (hhi : cnt ≤ 32) (hshi : stride ≤ 131056) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 stride)) *
      BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) =
      BitVec.ofNat 64 (cnt * stride) := by
  have hs : BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 stride)) =
      BitVec.ofNat 64 stride := by
    have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 stride) = BitVec.ofNat 32 stride := by bv_omega
    have hlt : (BitVec.ofNat 32 stride).ult (1#32 <<< 31) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change stride % (2 ^ 32) < 2 ^ 31
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hse : (BitVec.ofNat 32 stride).signExtend 64 = (BitVec.ofNat 32 stride).zeroExtend 64 := by
      revert hlt; bv_robdd
    rw [h1, hse]; bv_omega
  have hc : BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) =
      BitVec.ofNat 64 cnt := by
    have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
    have hlt : (BitVec.ofNat 32 cnt).ult (1#32 <<< 31) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change cnt % (2 ^ 32) < 2 ^ 31
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hse : (BitVec.ofNat 32 cnt).signExtend 64 = (BitVec.ofNat 32 cnt).zeroExtend 64 := by
      revert hlt; bv_robdd
    rw [h1, hse]; bv_omega
  rw [hs, hc, Nat.mul_comm]; exact (BitVec.ofNat_mul stride cnt).symm

private theorem sext_lsl2_cnt {cnt : Nat} (hhi : cnt ≤ 32) :
    BitVec.signExtend 64
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) <<< 2)) =
      BitVec.ofNat 64 (4 * cnt) := by
  have hlt : (BitVec.ofNat 64 cnt).ult 33#64 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    change cnt % (2 ^ 64) < 33
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hsh : BitVec.ofNat 64 (4 * cnt) = (BitVec.ofNat 64 cnt) <<< 2 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    change (4 * cnt) % (2 ^ 64) = ((cnt % (2 ^ 64)) <<< 2) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64), Nat.shiftLeft_eq]
    congr 1; omega
  rw [hsh]; revert hlt; bv_robdd

private theorem ofNat64_lsb_iff {cnt : Nat} :
    (BitVec.ofNat 64 cnt).getLsbD 0 = true ↔ cnt % 2 = 1 := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_zero]
  simp only [show (0 : Nat) < 64 by decide, decide_true, Bool.true_and, decide_eq_true_eq]

private theorem ult_4cnt_iff {cnt : Nat} (hhi : cnt ≤ 32) (u : BitVec 64) :
    u.ult (BitVec.signExtend 64
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) <<< 2))) =
      true ↔ u.toNat < 4 * cnt := by
  rw [sext_lsl2_cnt hhi, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

private theorem zext8_shl2_ule_iff (b : BitVec 8) (u : BitVec 64) :
    (BitVec.zeroExtend 64 b <<< 2).ule u = true ↔ 4 * b.toNat ≤ u.toNat := by
  have hb := b.isLt
  have h : (BitVec.zeroExtend 64 b <<< 2).toNat = 4 * b.toNat := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.ule, decide_eq_true_eq, h]

theorem wp_cnt_loop1 [MallocngMultiPlacement]
    (hw768 : Blk08HasWords768 mallocngFaultSvc) :
    ∀ (cnt : Nat) (s : State) (useOld : BitVec 64) (Frame : SepProp),
      1 ≤ cnt → cnt ≤ 32 →
      s.pc = mbase 8 + allocSlotOff_cnt1 → s.status = .Running →
      s.readReg64 .x20 = BitVec.ofNat 64 cnt →
      s.readReg64 .x2 = useOld →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_cnt2) s Frame
        (fun sf P_f => ∃ cnt1, 1 ≤ cnt1 ∧ cnt1 ≤ cnt ∧
          (∀ f, cnt < 2 ^ f → cnt1 = Cost.halveUsage f useOld.toNat cnt) ∧
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          sf.readReg64 .x1 = 1048575#64 ∧
          sf.readReg64 .x20 = BitVec.ofNat 64 cnt1 ∧
          (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = Frame)
        (fun _ => ⌜False⌝) := by
  intro cnt
  induction cnt using Nat.strongRecOn with
  | ind cnt ih =>
    intro s useOld Frame hlo hhi hpc hrun hx20 hx2
    dsimp only [allocSlotOff_cnt1, allocSlotOff_cnt2] at hpc ⊢
    wp_sym_steps
    wp_if hodd
    · have hfix : ∀ f, cnt < 2 ^ f → cnt = Cost.halveUsage f useOld.toNat cnt := by
        have hodd' : cnt % 2 = 1 := ofNat64_lsb_iff.mp hodd
        intro f _; cases f with
        | zero => rfl
        | succ f => simp only [Cost.halveUsage]; split <;> first | omega | rfl
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨cnt, hlo, Nat.le_refl _, hfix, by simp [hrun],
        by simp, by simp [State.spAligned], psp_rfl, by simp, by simpa using hx20, ?_, rfl⟩
      intro r _ h1 _
      simp only [State.readReg64_setPC, State.readReg64_writeReg64_ne _ _ _ _ h1]
    · have hge2 : 2 ≤ cnt := by
        apply Classical.byContradiction; intro hlt
        have hc1 : cnt = 1 := by omega
        subst hc1; exact hodd rfl
      wp_sym_steps
      wp_if hcmp
      · have hcmpN : useOld.toNat < 4 * cnt := (ult_4cnt_iff hhi useOld).mp hcmp
        have hev : cnt % 2 = 0 := by have := mt ofNat64_lsb_iff.mpr hodd; omega
        refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_cnt1)
          (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
            sj.readReg64 .x20 = BitVec.ofNat 64 (cnt / 2) ∧ sj.readReg64 .x2 = useOld ∧
            ∀ r, r ≠ .x0 → r ≠ .x20 → sj.readReg64 r = s.readReg64 r) ?_ ?_
        · dsimp only [allocSlotOff_cnt1]
          wp_sym_steps
          refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
            by simpa using asr32_cnt_half hhi, by simpa using hx2, ?_⟩, by sep_entail⟩
          intro r hr0 hr20
          simp only [State.readReg64_setPC, State.readReg64_setPState,
            State.readReg64_writeReg64_ne _ _ _ _ hr20,
            State.readReg64_writeReg64_ne _ _ _ _ hr0]
        · intro sj hjpc hjrun ⟨hjsp, hjal, hjpsp, hj20, hj2, hjr⟩
          have hstep := ih (cnt / 2) (by omega) sj useOld Frame (by omega) (by omega)
            hjpc hjrun hj20 hj2
          dsimp only [allocSlotOff_cnt2] at hstep
          refine SepWP.mono hstep ?_
          intro sf P_f _ _ ⟨cnt1, hc1lo, hc1hi, hhalf, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
          refine ⟨cnt1, hc1lo, by omega, ?_, h1, h2.trans hjsp, h3.trans hjal,
            hjpsp.trans hpsp2, h6, h7, ?_, hPf⟩
          · intro f hf
            cases f with
            | zero => rw [Nat.pow_zero] at hf; omega
            | succ f =>
              simp only [Cost.halveUsage]; split
              · exact hhalf f (by rw [Nat.pow_succ] at hf; omega)
              · omega
          · intro r hr0 hr1 hr20; exact (hregs r hr0 hr1 hr20).trans (hjr r hr0 hr20)
      · have hcmpN : 4 * cnt ≤ useOld.toNat := by
          have := mt (ult_4cnt_iff hhi useOld).mpr hcmp; omega
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨cnt, hlo, Nat.le_refl _,
          fun f _ => (Cost.halveUsage_of_le f _ _ hcmpN).symm, by simp [hrun],
          by simp, by simp [State.spAligned], psp_rfl, by simp, by simpa using hx20, ?_, rfl⟩
        intro r hr0 hr1 _
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr1,
          State.readReg64_writeReg64_ne _ _ _ _ hr0]

theorem wp_cnt_loop2 [MallocngMultiPlacement]
    (hw768 : Blk08HasWords768 mallocngFaultSvc) :
    ∀ (cnt : Nat) (s : State) (stride : Nat) (Frame : SepProp),
      1 ≤ cnt → cnt ≤ 32 → 16 ≤ stride → stride ≤ 131056 →
      s.pc = mbase 8 + allocSlotOff_cnt2 → s.status = .Running →
      s.readReg64 .x20 = BitVec.ofNat 64 cnt →
      s.readReg64 .x27 = BitVec.ofNat 64 stride →
      s.readReg64 .x1 = 1048575#64 →
      SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_cnt_join) s Frame
        (fun sf P_f => ∃ cnt2, 1 ≤ cnt2 ∧ cnt2 ≤ cnt ∧ cnt2 * stride ≤ 1048575 ∧
          (∀ f, cnt < 2 ^ f → cnt2 = Cost.halveSize f stride cnt) ∧
          sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
          PureStatePres s sf ∧
          sf.readReg64 .x20 = BitVec.ofNat 64 cnt2 ∧
          (∀ r, r ≠ .x0 → r ≠ .x20 → sf.readReg64 r = s.readReg64 r) ∧
          P_f = Frame)
        (fun _ => ⌜False⌝) := by
  intro cnt
  induction cnt using Nat.strongRecOn with
  | ind cnt ih =>
    intro s stride Frame hlo hhi hslo hshi hpc hrun hx20 hx27 hx1
    have hprod_bd : cnt * stride ≤ 32 * 131056 := Nat.mul_le_mul hhi hshi
    dsimp only [allocSlotOff_cnt2, allocSlotOff_cnt_join] at hpc ⊢
    wp_sym_steps
    wp_if hgt
    · rw [smull_stride_cnt hhi hshi, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hgt
      change 1048575 < (cnt * stride) % (2 ^ 64) at hgt
      rw [Nat.mod_eq_of_lt (by omega)] at hgt
      have hge2 : 2 ≤ cnt := by
        apply Classical.byContradiction; intro hlt
        have hc1 : cnt = 1 := by omega
        subst hc1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_cnt2)
        (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
          sj.readReg64 .x20 = BitVec.ofNat 64 (cnt / 2) ∧
          sj.readReg64 .x27 = BitVec.ofNat 64 stride ∧ sj.readReg64 .x1 = 1048575#64 ∧
          ∀ r, r ≠ .x0 → r ≠ .x20 → sj.readReg64 r = s.readReg64 r) ?_ ?_
      · dsimp only [allocSlotOff_cnt2]
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
          by simpa using asr32_cnt_half hhi, by simpa using hx27, by simpa using hx1, ?_⟩,
          by sep_entail⟩
        intro r hr0 hr20
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr20,
          State.readReg64_writeReg64_ne _ _ _ _ hr0]
      · intro sj hjpc hjrun ⟨hjsp, hjal, hjpsp, hj20, hj27, hj1, hjr⟩
        have hstep := ih (cnt / 2) (by omega) sj stride Frame (by omega) (by omega) hslo hshi
          hjpc hjrun hj20 hj27 hj1
        dsimp only [allocSlotOff_cnt_join] at hstep
        refine SepWP.mono hstep ?_
        intro sf P_f _ _ ⟨cnt2, hc2lo, hc2hi, hprod, hhalf, h1, h2, h3, hpsp2, h6, hregs, hPf⟩
        refine ⟨cnt2, hc2lo, by omega, hprod, ?_, h1, h2.trans hjsp, h3.trans hjal,
          hjpsp.trans hpsp2, h6, ?_, hPf⟩
        · have hcomm : stride * cnt = cnt * stride := Nat.mul_comm _ _
          intro f hf
          cases f with
          | zero => rw [Nat.pow_zero] at hf; omega
          | succ f =>
            simp only [Cost.halveSize]; split
            · exact hhalf f (by rw [Nat.pow_succ] at hf; omega)
            · omega
        · intro r hr0 hr20; exact (hregs r hr0 hr20).trans (hjr r hr0 hr20)
    · rw [smull_stride_cnt hhi hshi, BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hgt
      change ¬ (1048575 < (cnt * stride) % (2 ^ 64)) at hgt
      rw [Nat.mod_eq_of_lt (by omega)] at hgt
      have hfix : ∀ f, cnt < 2 ^ f → cnt = Cost.halveSize f stride cnt := by
        have hcomm : stride * cnt = cnt * stride := Nat.mul_comm _ _
        intro f _; cases f with
        | zero => rfl
        | succ f => simp only [Cost.halveSize]; split <;> first | omega | rfl
      refine SepWP.done rfl (by simp [hrun]) ⟨cnt, hlo, Nat.le_refl _, by omega, hfix,
        by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20, ?_, rfl⟩
      intro r hr0 _
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ hr0]

private theorem cnt_tab_stride_check :
    (((List.range 9).all fun sc =>
      (List.range 3).all fun j =>
        let c := (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat
        (2 ≤ c) && (c ≤ 31) && (c * slotStride sc + 20 ≤ 4096)) &&
     ((List.range 48).all fun sc =>
        (sc < 9) ||
        (let c := (medCntTabBytes.getD (sc % 4) 0#8).toNat
         (20 ≤ c) && (c ≤ 32) && ((25 < sc) || (c * slotStride sc + 20 ≤ 65536))))) = true := by
  decide +kernel

private theorem smallCnt_entry_bounds {sc j : Nat} (hsc : sc ≤ 8) (hj : j < 3) :
    let c := (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat
    2 ≤ c ∧ c ≤ 31 ∧ c * slotStride sc + 20 ≤ 4096 := by
  have h := (Bool.and_eq_true _ _).mp cnt_tab_stride_check
  have h1 := List.all_eq_true.mp h.1 sc (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  simpa [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h2

private theorem medCnt_entry_bounds {sc : Nat} (hsc9 : 9 ≤ sc) (hsc : sc < 48) :
    let c := (medCntTabBytes.getD (sc % 4) 0#8).toNat
    20 ≤ c ∧ c ≤ 32 ∧ (sc ≤ 25 → c * slotStride sc + 20 ≤ 65536) := by
  have h := (Bool.and_eq_true _ _).mp cnt_tab_stride_check
  have h1 := List.all_eq_true.mp h.2 sc (List.mem_range.mpr hsc)
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  rcases h1 with hlt | ⟨⟨hlo, hhi⟩, h25⟩
  · omega
  · exact ⟨hlo, hhi, fun hle => by rcases h25 with hgt | hbd; omega; exact hbd⟩

private theorem zext8_eq_ofNat (b : BitVec 8) :
    BitVec.zeroExtend 64 b = BitVec.ofNat 64 b.toNat := by bv_omega

private theorem med_cnt_addr_eq (medAddr : BitVec 64) {sc : Nat} (_hsc : sc < 48) :
    medAddr +
      BitVec.signExtend 64
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 sc)) &&& 3#64)) =
    medAddr + BitVec.ofNat 64 (sc % 4) := by
  have h1 : BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 sc)) &&& 3#64) =
      BitVec.ofNat 32 (sc % 4) := by
    have ha : BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 sc)) &&& 3#64) =
        BitVec.setWidth 32 (BitVec.ofNat 64 sc) &&& 3#32 := by bv_robdd
    rw [ha]
    apply BitVec.eq_of_toNat_eq
    change ((sc % (2 ^ 64)) % (2 ^ 32)) &&& 3 = (sc % 4) % (2 ^ 32)
    rw [Nat.and_two_pow_sub_one_eq_mod _ 2, Nat.mod_mod_of_dvd _ (by decide),
      Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt (by omega : sc % 4 < 2 ^ 32)]
  have hlt : (BitVec.ofNat 32 (sc % 4)).ult (1#32 <<< 31) = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
    change (sc % 4) % (2 ^ 32) < 2 ^ 31
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hse : (BitVec.ofNat 32 (sc % 4)).signExtend 64 =
      (BitVec.ofNat 32 (sc % 4)).zeroExtend 64 := by revert hlt; bv_robdd
  have hz : (BitVec.ofNat 32 (sc % 4)).zeroExtend 64 = BitVec.ofNat 64 (sc % 4) := by bv_omega
  rw [h1, hse, hz]

private theorem small_cnt_addr_eq (smAddr : BitVec 64) {sc : Nat} (hsc : sc ≤ 8) :
    smAddr + (BitVec.ofNat 64 sc + (BitVec.ofNat 64 sc <<< 1)) =
      smAddr + BitVec.ofNat 64 (3 * sc) := by
  have hm : BitVec.ofNat 64 sc + (BitVec.ofNat 64 sc <<< 1) = BitVec.ofNat 64 (3 * sc) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    change (sc % (2 ^ 64) + ((sc % (2 ^ 64)) <<< 1) % (2 ^ 64)) % (2 ^ 64) = (3 * sc) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : sc < 2 ^ 64), Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : sc * 2 ^ 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : sc + sc * 2 ^ 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 3 * sc < 2 ^ 64)]
    omega
  rw [hm]

private theorem cmp_sc8_slt {sc : Nat} (hsc : sc < 48) :
    ((8#32).slt (BitVec.setWidth 32 (BitVec.ofNat 64 sc)) = true) ↔ 9 ≤ sc := by
  have hw : BitVec.setWidth 32 (BitVec.ofNat 64 sc) = BitVec.ofNat 32 sc := by bv_omega
  rw [hw, BitVec.slt, decide_eq_true_eq]
  have hs1 : (8#32).toInt = 8 := rfl
  have hs2 : (BitVec.ofNat 32 sc).toInt = (sc : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sc < 2 ^ 32)]
    simp [show ¬ (2 * sc ≥ 2 ^ 32) by omega]
  rw [hs1, hs2]; omega

set_option maxHeartbeats 800000 in
theorem wp_alloc_group_cnt_join [MallocngMultiPlacement]
    (s : State) (m useOld : BitVec 64) (sc : Nat) (Frame : SepProp)
    (_hw564 : Blk08HasWords564 mallocngFaultSvc) (_hr564 : Blk08Range564)
    (_hw712 : Blk08HasWords712 mallocngFaultSvc) (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hmNe0 : m ≠ 0#64)
    (hpc : s.pc = mbase 8 + allocSlotOff_after_meta) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = m)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    let Pre :=
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ useOld) ∗
      (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗
      (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗ Frame
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_cnt_join) s Pre
      (fun sf P_f => ∃ cnt, 1 ≤ cnt ∧ cnt ≤ 32 ∧
        cnt * slotStride sc ≤ 1048575 ∧
        (sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) ∧
        (sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat) ∧
        (cnt = 1 → 9 ≤ sc) ∧
        cnt = Cost.cntRaw sc useOld.toNat ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x19 = m ∧ sf.readReg64 .x2 = useOld ∧ sf.readReg64 .x4 = 4096#64 ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt ∧
        sf.readReg64 .x21 = BitVec.ofNat 64 sc ∧ sf.readReg64 .x23 = BitVec.ofNat 64 sc ∧
        sf.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
        sf.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc) ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x19 → r ≠ .x20 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Pre)
      (fun _ => ⌜False⌝) := by
  intro Pre
  dsimp only [allocSlotOff_after_meta, allocSlotOff_cnt_join] at hpc ⊢
  conv => arg 4; dsimp only [Pre]
  have hm0 : (m == 0#64) = false := beq_false_of_ne hmNe0
  have hoff_u := ctx_off_usage (ctxAddr := maddrs.ctx) hsc
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  wp_sym_steps
  wp_if hgt8
  · have hsc9 : 9 ≤ sc := (cmp_sc8_slt hsc).mp hgt8
    have ⟨hmed_lo, hmed_hi, hmed_25⟩ := medCnt_entry_bounds hsc9 hsc
    obtain ⟨RestM, hsp_med⟩ := split_medCnt_ro maddrs.medCntTab hsc
      ((maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗ Frame)
    have hmad := med_cnt_addr_eq maddrs.medCntTab hsc
    refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_cnt1)
      (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
        sj.readReg64 .x19 = m ∧ sj.readReg64 .x2 = useOld ∧ sj.readReg64 .x4 = 4096#64 ∧
        sj.readReg64 .x20 = BitVec.ofNat 64 (medCntTabBytes.getD (sc % 4) 0#8).toNat ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x19 → r ≠ .x20 →
          sj.readReg64 r = s.readReg64 r)) ?_ ?_
    · dsimp only [allocSlotOff_cnt1]
      conv => arg 4; simp only [sepConj_assoc]; rw [hsp_med]
      wp_sym_steps
      refine Obj.MultiPlacedLib.sepWP_relaxablePair (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
        (i := 8) (by decide) (off := 760) (rd := 0#5) (X := fun _ => none) (svc := mallocngFaultSvc)
        MallocngMultiPlacement.placeable rfl rfl (by decide) (by decide)
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
      simp only [resolve_med_cnt_tab, show Obj.addSignedAddr maddrs.medCntTab 0 = maddrs.medCntTab from rfl,
        show BitVec.ofNat 64 (760 + 8) = 768#64 from rfl]
      wp_sym_steps
      conv => arg 4; rw [← hsp_med]
      refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
        by simp, by simp, by simp, by simp [-BitVec.ofNat_toNat, zext8_eq_ofNat], ?_⟩, by sep_entail⟩
      intro r hr0 hr1 hr2 hr4 hr19 hr20
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ hr20, State.readReg64_writeReg64_ne _ _ _ _ hr19,
        State.readReg64_writeReg64_ne _ _ _ _ hr4, State.readReg64_writeReg64_ne _ _ _ _ hr2,
        State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr0]
    · intro sj1 hj1pc hj1run ⟨hsp1, hal1, hpsp1, h19_1, h2_1, h4_1, h20_1, hr1⟩
      change SepWP _ (mbase 8 + allocSlotOff_cnt_join) sj1 Pre _ _
      have hl1 := wp_cnt_loop1 hw768
        (medCntTabBytes.getD (sc % 4) 0#8).toNat sj1 useOld Pre
        (by omega) hmed_hi hj1pc hj1run h20_1 h2_1
      refine SepWP.seq hl1 ?_
      intro sj2 P2 hj2pc hj2run ⟨cnt1, hc1lo, hc1hi, hhalf1, _, hsp2, hal2, hpsp2, h1_2, h20_2, hr2, hP2⟩
      subst hP2
      have h27_2 : sj2.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc) := by
        rw [hr2 .x27 (by decide) (by decide) (by decide),
          hr1 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx27]
      have hl2 := wp_cnt_loop2 hw768 cnt1 sj2 (slotStride sc) Pre
        hc1lo (by omega) hslo hshi hj2pc hj2run h20_2 h27_2 h1_2
      dsimp only [allocSlotOff_cnt_join] at hl2
      refine SepWP.mono hl2 ?_
      intro sf P_f _ _ ⟨cnt2, hc2lo, hc2hi, hprod, hhalf2, hsfrun, hsp3, hal3, hpsp3, h20_3, hr3, hPf⟩
      have hraw : cnt2 = Cost.cntRaw sc useOld.toNat := by
        rw [hhalf2 8 (by omega), hhalf1 8 (by omega)]
        simp only [Cost.cntRaw, Cost.medCnt, show ¬ sc < 9 by omega, ↓reduceIte]
      have hreg : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x19 → r ≠ .x20 →
          sf.readReg64 r = s.readReg64 r := fun r h0 h1 h2 _ h4 h19 h20 =>
        (hr3 r h0 h20).trans ((hr2 r h0 h1 h20).trans (hr1 r h0 h1 h2 h4 h19 h20))
      refine ⟨cnt2, hc2lo, by omega, hprod, fun h25 => ?_, fun hle8 => by omega,
        fun _ => hsc9, hraw, hsfrun, hsp3.trans (hsp2.trans hsp1), hal3.trans (hal2.trans hal1),
        (hpsp1.trans hpsp2).trans hpsp3,
        by rw [hr3 .x19 (by decide) (by decide), hr2 .x19 (by decide) (by decide) (by decide), h19_1],
        by rw [hr3 .x2 (by decide) (by decide), hr2 .x2 (by decide) (by decide) (by decide), h2_1],
        by rw [hr3 .x4 (by decide) (by decide), hr2 .x4 (by decide) (by decide) (by decide), h4_1],
        h20_3,
        by rw [hreg .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21],
        by rw [hreg .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx23],
        by rw [hreg .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx22],
        by rw [hreg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx24],
        by rw [hr3 .x27 (by decide) (by decide), h27_2],
        hreg, hPf⟩
      have hmul : cnt2 * slotStride sc ≤ (medCntTabBytes.getD (sc % 4) 0#8).toNat * slotStride sc :=
        Nat.mul_le_mul_right _ (by omega)
      have := hmed_25 h25; omega
  · have hsc8 : sc ≤ 8 := by have := mt (cmp_sc8_slt hsc).mpr hgt8; omega
    obtain ⟨RestS, hsp_sm⟩ := split_smallCnt_ro maddrs.smallCntTab hsc8 Frame
    have hsad := small_cnt_addr_eq maddrs.smallCntTab hsc8
    conv => arg 4; simp only [sepConj_assoc]; rw [hsp_sm, ← hsad]
    wp_sym_steps
    refine Obj.MultiPlacedLib.sepWP_relaxablePair (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
      (i := 8) (by decide) (off := 704) (rd := 1#5) (X := fun _ => none) (svc := mallocngFaultSvc)
      MallocngMultiPlacement.placeable rfl rfl (by decide) (by decide)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) ?_
    simp only [resolve_small_cnt_tab, show Obj.addSignedAddr maddrs.smallCntTab 0 = maddrs.smallCntTab from rfl,
      show BitVec.ofNat 64 (704 + 8) = 712#64 from rfl]
    wp_sym_steps
    wp_if hb0
    · conv => arg 4; rw [hsad, ← hsp_sm]
      have ⟨hc_lo, hc_hi, hc_bd⟩ := smallCnt_entry_bounds hsc8 (j := 0) (by omega)
      simp only [Nat.add_zero] at hc_lo hc_hi hc_bd
      have hraw : (smallCntTabBytes.getD (3 * sc) 0#8).toNat = Cost.cntRaw sc useOld.toNat := by
        have h0 := (zext8_shl2_ule_iff _ useOld).mp hb0
        simp only [Cost.cntRaw, Cost.smallCnt, Nat.add_zero, show sc < 9 by omega, h0, ↓reduceIte]
      refine SepWP.done rfl (by simp [hrun]) ⟨(smallCntTabBytes.getD (3 * sc) 0#8).toNat,
        by omega, by omega, by omega, fun _ => by omega,
        fun _ => ⟨0, by omega, by simp⟩, fun hc1 => by omega, hraw,
        by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
        by simp, by simp, by simp, by simp [-BitVec.ofNat_toNat, zext8_eq_ofNat],
        by simpa using hx21, by simpa using hx23, by simpa using hx22,
        by simpa using hx24, by simpa using hx27, ?_, by simp only [Pre]⟩
      intro r h0 h1 h2 h3 h4 h19 h20
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h19,
        State.readReg64_writeReg64_ne _ _ _ _ h4, State.readReg64_writeReg64_ne _ _ _ _ h3,
        State.readReg64_writeReg64_ne _ _ _ _ h2, State.readReg64_writeReg64_ne _ _ _ _ h1,
        State.readReg64_writeReg64_ne _ _ _ _ h0]
    · wp_sym_steps
      wp_if hb1
      · conv => arg 4; rw [hsad, ← hsp_sm]
        have ⟨hc_lo, hc_hi, hc_bd⟩ := smallCnt_entry_bounds hsc8 (j := 1) (by omega)
        have hraw : (smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat = Cost.cntRaw sc useOld.toNat := by
          have h0 := mt (zext8_shl2_ule_iff _ useOld).mpr hb0
          have h1 := (zext8_shl2_ule_iff _ useOld).mp hb1
          simp only [Cost.cntRaw, Cost.smallCnt, Nat.add_zero, show sc < 9 by omega, h0, h1,
            ↓reduceIte]
        refine SepWP.done rfl (by simp [hrun]) ⟨(smallCntTabBytes.getD (3 * sc + 1) 0#8).toNat,
          by omega, by omega, by omega, fun _ => by omega,
          fun _ => ⟨1, by omega, rfl⟩, fun hc1 => by omega, hraw,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, by simp, by simp [-BitVec.ofNat_toNat, zext8_eq_ofNat],
          by simpa using hx21, by simpa using hx23, by simpa using hx22,
          by simpa using hx24, by simpa using hx27, ?_, by simp only [Pre]⟩
        intro r h0 h1 h2 h3 h4 h19 h20
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h19,
          State.readReg64_writeReg64_ne _ _ _ _ h4, State.readReg64_writeReg64_ne _ _ _ _ h3,
          State.readReg64_writeReg64_ne _ _ _ _ h2, State.readReg64_writeReg64_ne _ _ _ _ h1,
          State.readReg64_writeReg64_ne _ _ _ _ h0]
      · wp_sym_steps
        conv => arg 4; rw [hsad, ← hsp_sm]
        have ⟨hc_lo, hc_hi, hc_bd⟩ := smallCnt_entry_bounds hsc8 (j := 2) (by omega)
        have hraw : (smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat = Cost.cntRaw sc useOld.toNat := by
          have h0 := mt (zext8_shl2_ule_iff _ useOld).mpr hb0
          have h1 := mt (zext8_shl2_ule_iff _ useOld).mpr hb1
          simp only [Cost.cntRaw, Cost.smallCnt, Nat.add_zero, show sc < 9 by omega, h0, h1,
            ↓reduceIte]
        refine SepWP.done rfl (by simp [hrun]) ⟨(smallCntTabBytes.getD (3 * sc + 2) 0#8).toNat,
          by omega, by omega, by omega, fun _ => by omega,
          fun _ => ⟨2, by omega, rfl⟩, fun hc1 => by omega, hraw,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, by simp, by simp [-BitVec.ofNat_toNat, zext8_eq_ofNat],
          by simpa using hx21, by simpa using hx23, by simpa using hx22,
          by simpa using hx24, by simpa using hx27, ?_, by simp only [Pre]⟩
        intro r h0 h1 h2 h3 h4 h19 h20
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h19,
          State.readReg64_writeReg64_ne _ _ _ _ h4, State.readReg64_writeReg64_ne _ _ _ _ h3,
          State.readReg64_writeReg64_ne _ _ _ _ h2, State.readReg64_writeReg64_ne _ _ _ _ h1,
          State.readReg64_writeReg64_ne _ _ _ _ h0]

/-! ## Count Check and Root/Nested Dispatch -/

macro "Blk08HasWords768Msvc" : term =>
  `((mallocngBlockProg mmpl 8 msvc).hasWords (mbase 8 + 768#64)
      (Obj.patchRelocs blk08Relocs768 blk08Words768 (mbase 8 + 768#64) (VerifiedLibraries.mallocngLib.resolve mmpl)))

theorem blk08_seg768_msvc [MallocngMultiPlacement] :
    (Blk08HasWords768Msvc) ∧ Blk08Range768 :=
  hasWords_blk_seg (i := 8) (by decide) 768
    (ws := blk08Words768) (R := blk08Relocs768) (by decide +kernel)

private theorem cnt_ult_33 {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 64 cnt).ult 33#64 = true := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
  change cnt % (2 ^ 64) < 33
  rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem cnt64_bit31_false {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 64 cnt)[31] = false := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  change Nat.testBit (cnt % (2 ^ 64)) 31 = false
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow (by omega)

private theorem cnt32_bit29_false {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 32 cnt)[29] = false := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  change Nat.testBit (cnt % (2 ^ 32)) 29 = false
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow (by omega)

private theorem and_m32_eq_self (v m32 : BitVec 64)
    (hm32 : m32 = (1#64 <<< 32) - 1#64) (hlt : v.ult 33#64 = true) :
    v &&& m32 = v := by
  subst hm32; revert hlt; bv_robdd

private theorem lsl2_and_m32_eq {cnt : Nat} (hhi : cnt ≤ 32) (m32 : BitVec 64)
    (hm32 : m32 = (1#64 <<< 32) - 1#64) :
    BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 2) &&& m32 = BitVec.ofNat 64 (4 * cnt) := by
  subst hm32
  have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 2) = (BitVec.ofNat 64 cnt) <<< 2 := by
    have hw : BitVec.ofNat 32 cnt = BitVec.setWidth 32 (BitVec.ofNat 64 cnt) := by bv_omega
    have hlt := cnt_ult_33 hhi
    rw [hw]; revert hlt; bv_robdd
  have hsh : BitVec.ofNat 64 (4 * cnt) = (BitVec.ofNat 64 cnt) <<< 2 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    change (4 * cnt) % (2 ^ 64) = ((cnt % (2 ^ 64)) <<< 2) % (2 ^ 64)
    rw [Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64), Nat.shiftLeft_eq]
    congr 1; omega
  have hlt := cnt_ult_33 hhi
  rw [h1, hsh]; revert hlt; bv_robdd

private theorem mul_stride_cnt_eq {cnt stride : Nat} :
    BitVec.ofNat 64 stride * BitVec.ofNat 64 cnt = BitVec.ofNat 64 (cnt * stride) := by
  rw [Nat.mul_comm]; exact (BitVec.ofNat_mul stride cnt).symm

theorem wp_alloc_group_cnt_check [MallocngMultiPlacement]
    (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (_hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 2 ≤ cnt) (hhi : cnt ≤ 32)
    (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_check) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx1 : s.readReg64 .x1 = 2048#64)
    (hNested : ∀ sn : State, sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running →
      sn.sp = s.sp → sn.spAligned = s.spAligned → PureStatePres s sn →
      ValidNestedCnt sc cnt →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) →
      sn.readReg64 .x20 = BitVec.ofNat 64 cnt →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt →
      (∀ r, r ≠ .x0 → r ≠ .x3 → sn.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ sr : State, sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running →
      sr.sp = s.sp → sr.spAligned = s.spAligned → PureStatePres s sr →
      2048 < cnt * slotStride sc + 16 →
      cnt * slotStride sc ≤ 1048575 →
      (sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) →
      sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt →
      sr.readReg64 .x28 = BitVec.ofNat 64 cnt →
      (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_check] at hpc
  have ⟨_, hshi⟩ := slotStride_bounds_48 hsc
  have hbd : cnt * slotStride sc ≤ 32 * 131056 := Nat.mul_le_mul hhi hshi
  wp_sym_steps
  wp_if hls
  · rw [mul_stride_cnt_eq] at hls
    have hle2048 : cnt * slotStride sc + 16 ≤ 2048 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048 at hls
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; exact hls
    have hvnc : ValidNestedCnt sc cnt := by
      refine ⟨hlo, hhi, hle2048, fun h8 => ?_⟩
      obtain ⟨j, hj, rfl⟩ := hsm h8
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    refine hNested _ rfl (by simp [hrun]) (by simp) (by simp [State.spAligned]) psp_rfl hvnc
      (by simpa using mul_stride_cnt_eq) (by simpa using hx20) (by simpa using hx28) ?_
    intro r hr0 hr3
    simp only [State.readReg64_setPC, State.readReg64_setPState,
      State.readReg64_writeReg64_ne _ _ _ _ hr3, State.readReg64_writeReg64_ne _ _ _ _ hr0]
  · rw [mul_stride_cnt_eq] at hls
    have hgt2048 : 2048 < cnt * slotStride sc + 16 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ¬ (((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048) at hls
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; omega
    refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
      (fun sr => sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧
        sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) ∧
        sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) ∧
        sr.readReg64 .x20 = BitVec.ofNat 64 cnt ∧
        sr.readReg64 .x28 = BitVec.ofNat 64 cnt ∧
        ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) ?_ ?_
    · dsimp only [allocSlotOff_root]
      wp_sym_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
        by simpa using mul_stride_cnt_eq, ?_, by simpa using hx20, by simpa using hx28, ?_⟩,
        by sep_entail⟩
      · simp [cnt32_bit29_false hhi]
        exact lsl2_and_m32_eq hhi _ rfl
      · intro r hr0 hr3 hr6
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr3,
          State.readReg64_writeReg64_ne _ _ _ _ hr0]
    · intro sr hpcr hrunr ⟨hspr, halr, hpspr, h0r, h6r, h20r, h28r, hrr⟩
      exact hRoot sr hpcr hrunr hspr halr hpspr hgt2048 hprod h25 h0r h6r h20r h28r hrr

theorem wp_alloc_group_cnt_dispatch [MallocngMultiPlacement]
    (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 1 ≤ cnt) (hhi : cnt ≤ 32)
    (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hc1 : cnt = 1 → 9 ≤ sc)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_join) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx4 : s.readReg64 .x4 = 4096#64)
    (hNested : ∀ (cnt' : Nat) (sn : State),
      sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running →
      sn.sp = s.sp → sn.spAligned = s.spAligned → PureStatePres s sn →
      ValidNestedCnt sc cnt' →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) →
      sn.readReg64 .x20 = BitVec.ofNat 64 cnt' →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x28 →
        sn.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ (cnt' : Nat) (sr : State),
      sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running →
      sr.sp = s.sp → sr.spAligned = s.spAligned → PureStatePres s sr →
      1 ≤ cnt' → cnt' ≤ 32 →
      2048 < cnt' * slotStride sc + 16 →
      cnt' * slotStride sc ≤ 1048575 →
      (sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) →
      sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt') →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt' →
      sr.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 →
        sr.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_join] at hpc
  have ⟨_, hshi⟩ := slotStride_bounds_48 hsc
  wp_sym_steps
  wp_if heq1
  · have hcnt1 : cnt = 1 := by
      have hw : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
      rw [hw] at heq1
      have ht := congrArg BitVec.toNat heq1
      simp only [BitVec.toNat_ofNat] at ht
      change cnt % (2 ^ 32) = 1 at ht
      rw [Nat.mod_eq_of_lt (by omega)] at ht; exact ht
    subst hcnt1
    have hsc9 : 9 ≤ sc := hc1 rfl
    wp_sym_steps
    wp_if hhi1
    · have hgt2048 : 2048 < 1 * slotStride sc + 16 := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hhi1
        change 2048 < (slotStride sc % (2 ^ 64) + 16) % (2 ^ 64) at hhi1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hhi1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
        (fun sr => sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧
          sr.readReg64 .x0 = BitVec.ofNat 64 (1 * slotStride sc) ∧
          sr.readReg64 .x6 = BitVec.ofNat 64 (4 * 1) ∧
          sr.readReg64 .x20 = BitVec.ofNat 64 1 ∧
          sr.readReg64 .x28 = BitVec.ofNat 64 1 ∧
          ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 →
            sr.readReg64 r = s.readReg64 r) ?_ ?_
      · dsimp only [allocSlotOff_root]
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, by simpa using hx20, by simp, ?_⟩, by sep_entail⟩
        intro r hr0 hr1 _ hr6 _ hr28
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr6, State.readReg64_writeReg64_ne _ _ _ _ hr0,
          State.readReg64_writeReg64_ne _ _ _ _ hr1, State.readReg64_writeReg64_ne _ _ _ _ hr28]
      · intro sr hpcr hrunr ⟨hspr, halr, hpspr, h0r, h6r, h20r, h28r, hrr⟩
        exact hRoot 1 sr hpcr hrunr hspr halr hpspr (by omega) (by omega) hgt2048 hprod h25
          h0r h6r h20r h28r hrr
    · have hle2048 : slotStride sc + 16 ≤ 2048 := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hhi1
        change ¬ (2048 < (slotStride sc % (2 ^ 64) + 16) % (2 ^ 64)) at hhi1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hhi1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_cnt_check)
        (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
          sj.readReg64 .x20 = BitVec.ofNat 64 2 ∧ sj.readReg64 .x28 = BitVec.ofNat 64 2 ∧
          sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧ sj.readReg64 .x1 = 2048#64 ∧
          ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → r ≠ .x28 → sj.readReg64 r = s.readReg64 r) ?_ ?_
      · dsimp only [allocSlotOff_cnt_check]
        wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
          by simp, by simp, by simpa using hx24, by simp, ?_⟩, by sep_entail⟩
        intro r hr0 hr1 hr20 hr28
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ hr20, State.readReg64_writeReg64_ne _ _ _ _ hr28,
          State.readReg64_writeReg64_ne _ _ _ _ hr0, State.readReg64_writeReg64_ne _ _ _ _ hr1]
      · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj20, hj28, hj24, hj1, hjr⟩
        exact wp_alloc_group_cnt_check target_pc sj sc 2 P hw768 hsc
          (by omega) (by omega) (by omega) (fun _ => by omega) (fun _ => by omega)
          hjpc hjrun hj20 hj28 hj24 hj1
          (fun sn hpcn hrunn hspn haln hpspn hvnc h0n h20n h28n hrn =>
            hNested 2 sn hpcn hrunn (hspn.trans hsp) (haln.trans hal) (hpsp.trans hpspn)
              hvnc h0n h20n h28n fun r h0 h1 h3 h20 h28 => (hrn r h0 h3).trans (hjr r h0 h1 h20 h28))
          (fun sr hpcr hrunr hspr halr hpspr hgt hpr h25' h0r h6r h20r h28r hrr =>
            hRoot 2 sr hpcr hrunr (hspr.trans hsp) (halr.trans hal) (hpsp.trans hpspr)
              (by omega) (by omega) hgt hpr h25' h0r h6r h20r h28r
              fun r h0 h1 h3 h6 h20 h28 => (hrr r h0 h3 h6).trans (hjr r h0 h1 h20 h28))
  · have hge2 : 2 ≤ cnt := by
      apply Classical.byContradiction; intro hlt
      have hc : cnt = 1 := by omega
      subst hc; exact heq1 rfl
    exact wp_alloc_group_cnt_check target_pc _ sc cnt P hw768 hsc
      hge2 hhi hprod h25 hsm rfl (by simp [hrun])
      (by simpa using hx20)
      (by simp [cnt64_bit31_false hhi]; exact and_m32_eq_self _ _ rfl (cnt_ult_33 hhi))
      (by simpa using hx24) (by simp)
      (fun sn hpcn hrunn hspn haln hpspn hvnc h0n h20n h28n hrn =>
        hNested cnt sn hpcn hrunn (hspn.trans (by simp)) (haln.trans (by simp [State.spAligned]))
          (PureStatePres.trans psp_rfl hpspn) hvnc h0n h20n h28n fun r h0 h1 h3 _ h28 => by
            rw [hrn r h0 h3]
            simp only [State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64_ne _ _ _ _ h1, State.readReg64_writeReg64_ne _ _ _ _ h28])
      (fun sr hpcr hrunr hspr halr hpspr hgt hpr h25' h0r h6r h20r h28r hrr =>
        hRoot cnt sr hpcr hrunr (hspr.trans (by simp)) (halr.trans (by simp [State.spAligned]))
          (PureStatePres.trans psp_rfl hpspr) (by omega) hhi hgt hpr h25' h0r h6r h20r h28r
          fun r h0 h1 h3 h6 _ h28 => by
            rw [hrr r h0 h3 h6]
            simp only [State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64_ne _ _ _ _ h1, State.readReg64_writeReg64_ne _ _ _ _ h28])

end VerifiedLibraries.Mallocng.Proofs
