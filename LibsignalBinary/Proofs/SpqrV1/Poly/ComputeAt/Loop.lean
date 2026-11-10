/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::Poly>::compute_at`: Loop Proofs

Fixed-base (`0x61914`) and relocatable `[LibsignalPlacement]` (Block `371`) symbolic execution of
the power-table loop (`powersLoopPure`) and dot-product loop (`dotLoopPure`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.ComputeAt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre
attribute [local wp_norm] zeroExtend_16_truncate_32_64
attribute [local arm64_norm, local wp_norm]
  ofNat_shl_one ofNat_shl_one_bv truncate16_zext64_trunc32 zext16_xor_trunc32
  Arm64.Obj.pageOf_add_lo12Of

gen_decodes libsignalSessionCode_tree computeAtBin [0x5c51c → 0x5c824]

theorem fnAddr_adrp_6197c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 104#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_6198c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 120#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61994 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 128#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_619a4 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 144#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_619ac {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 152#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61ac4 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 432#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_61ad0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr computeAtName + 444#64) &&&
      0xfffffffffffff000#64) = b + 0x5c000#64 := by
  rw [Program.fnAddr_rebase, computeAt_fnOff]
  revert hb; bv_bits

/-! ## Loop 1 (`0x619ec..0x619e8`): Power Table Loop (`powersLoopPure`) -/

private theorem perm_powers_post (R T X S1 S2 S3 F : SepProp) :
    R ∗ T ∗ X ∗ S1 ∗ S2 ∗ S3 ∗ F =
      X ∗ S1 ∗ S2 ∗ S3 ∗ T ∗ R ∗ F := by
  ac_rfl

set_option maxHeartbeats 1600000 in
theorem powersStep_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 p_xs : BitVec 64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len i : Nat) (_hi2 : 2 ≤ i) (hi_lt : i < len) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (xs : List GF16) (hxs_len : xs.length = i)
    (h1 : i / 2 < xs.length) (h2 : (i / 2) + (i % 2) < xs.length)
    (v_slot : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 216#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 len)
    (hx23 : s.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c))
    (hx25 : s.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 i)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 212#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      sf.pstate = subsPState64 (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 1)) →
      sf.readReg64 .x1 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = BitVec.ofNat 64 len →
      sf.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
      sf.readReg64 .x27 = p_xs →
      sf.readReg64 .x28 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         tokenInitAt b ∗ reduceTableAt b ∗ F) Q) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_xs xs ∗
       ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
       ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
       ((sp0 - 128#64) ↦₆₄ p_xs) ∗
       ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName + BitVec.ofNat 64 9104)
      (unacceleratedMulSpec b) := unacceleratedMul_at_computeAt b ext
  have hfn : libsignalSessionCode.fnOff computeAtName = 0x5c51c := computeAt_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
    (Rust.withPanics ext) hfn 0x5c51c 0xa8 104
  dsimp only [tripleRatchetProgAtExt] at hmul
  clear hfn
  have halign_bd8 := LagrangePrepare.aligned_86bd8 b hb
  have hshr := ofNat_ushr_one (i := i) (by omega)
  have hshr_bv := ofNat_ushr_one_bv (i := i) (by omega)
  have hule1 := ofNat_ule_false_of_lt (m := i / 2) (n := i) (by omega) (by omega)
  have hand1 := ofNat_and_one i
  have hadd1 := ofNat_add_ofNat (i / 2) (i % 2)
  have hule2 := ofNat_ule_false_of_lt (m := (i / 2) + (i % 2)) (n := i) (by omega) (by omega)
  have hal1 := aligned16_add_mul_two p_xs hp_xs (i / 2)
  have hal2 := aligned16_add_mul_two p_xs hp_xs ((i / 2) + (i % 2))
  have hal_i := aligned16_add_mul_two p_xs hp_xs i
  rcases ofNat_beq_false_of_lt hi_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
  have hadd_i := ofNat_add_one i
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
  examples_hide_fetches
  wp_steps 7
  wp_conv_pre => rw [LagrangeComplete.gf16SliceAt_focus_assoc h1 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← LagrangeComplete.gf16SliceAt_focus_assoc h1 p_xs, LagrangeComplete.gf16SliceAt_focus_assoc h2 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← LagrangeComplete.gf16SliceAt_focus_assoc h2 p_xs]
  wp_simp_pre [tokenInitAt]
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_assumption
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_bd8
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
  wp_call hmul
  wp_steps 10
  have hptr_eq : p_xs + BitVec.ofNat 64 (2 * i) = p_xs + BitVec.ofNat 64 (2 * xs.length) := by
    rw [hxs_len]
  have hval_eq : unaccelerated.mul (xs[i / 2]'h1).value (xs[(i / 2) + (i % 2)]'h2).value =
      (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)).value := rfl
  wp_conv_pre =>
    rw [hptr_eq, hval_eq,
        gf16SliceAt_append_singleton_assoc p_xs xs (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)),
        perm_powers_post]
  exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm, hsp_sf] using hsp)
    (by simpa [arm64_norm, wp_norm] using hpost)
    (by wp_norm_lhs)
    (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using h)
    (by simpa [arm64_norm, wp_norm, h_1] using hx20)
    (by simpa [arm64_norm, wp_norm, h_4] using hx23)
    (by simpa [arm64_norm, wp_norm] using h_5)
    (by simpa [arm64_norm, wp_norm, h_6] using hx25)
    (by wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hcs_sf)
    (by simpa [arm64_norm, wp_norm] using hvregs)

set_option maxHeartbeats 1600000 in
theorem powersLoop_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len : Nat) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r i : Nat) (xs : List GF16)
      (_hi2 : 2 ≤ i) (_hir : i + (r + 1) = len) (_hxs_len : xs.length = i)
      (s : State) (F : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 216#64 →
      s.status = .Running →
      s.sp = sp0 - 144#64 →
      s.readReg64 .x1 = BitVec.ofNat 64 i →
      s.readReg64 .x20 = BitVec.ofNat 64 len →
      s.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
      s.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
      s.readReg64 .x27 = p_xs →
      s.readReg64 .x28 = BitVec.ofNat 64 i →
      (∀ sf : State,
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 416#64 →
        sf.status = .Running →
        sf.sp = sp0 - 144#64 →
        sf.trace = s.trace →
        sf.readReg64 .x1 = BitVec.ofNat 64 len →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = BitVec.ofNat 64 len →
        sf.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
        sf.readReg64 .x27 = p_xs →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_xs (powersLoopPure i (r + 1) xs) ∗
           ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           ((sp0 - 128#64) ↦₆₄ p_xs) ∗
           ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           tokenInitAt b ∗ reduceTableAt b ∗ F) Q) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_xs xs ∗
         memRegion (p_xs + BitVec.ofNat 64 (2 * i)) (2 * (r + 1)) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro i xs hi2 hir hxs_len s F hpc hrun hsp hx1 hx20 hx23 hx25 hx27 hx28 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hlen_eq : i + 1 = len := by omega
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) 0 (by omega),
        memRegion_zero, sepConj_emp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    apply powersStep_sepWP b ext hb sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len h1 h2 v_slot
      ret_pc Q s F hpc hrun hsp hsp0 hx1 hx20 hx23 hx25 hx27 hx28
    intro s1 hpc1 hrun1 hsp1 htr1 hpst1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    rw [hlen_eq] at hpst1 hx1_1 hx28_1 ⊢
    have hfn : libsignalSessionCode.fnOff computeAtName = 0x5c51c := computeAt_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
      (Rust.withPanics ext) hfn 0x5c51c 0xd4 4
    clear hfn
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
    examples_hide_fetches
    wp_steps 1
    rw [powersLoopPure_succ i 0 xs h1 h2] at hnext
    dsimp only [powersLoopPure] at hnext
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro i xs hi2 hir hxs_len s F hpc hrun hsp hx1 hx20 hx23 hx25 hx27 hx28 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hi1_lt : i + 1 < len := by omega
    rcases ofNat_beq_false_of_lt hi1_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) (r' + 1) (by omega),
        ptr_add_two_step p_xs i]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs xs ∗
            (((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
             memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1))) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            tokenInitAt b ∗ reduceTableAt b ∗ F =
          gf16SliceAt p_xs xs ∗
            ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            tokenInitAt b ∗ reduceTableAt b ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) by ac_rfl]
    apply powersStep_sepWP b ext hb sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len h1 h2 v_slot
      ret_pc Q s (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F)
      hpc hrun hsp hsp0 hx1 hx20 hx23 hx25 hx27 hx28
    intro s1 hpc1 hrun1 hsp1 htr1 hpst1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    have hfn : libsignalSessionCode.fnOff computeAtName = 0x5c51c := computeAt_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
      (Rust.withPanics ext) hfn 0x5c51c 0xd4 4
    clear hfn
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
    examples_hide_fetches
    wp_steps 1
    rw [← hentry]
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            tokenInitAt b ∗ reduceTableAt b ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) =
          gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            tokenInitAt b ∗ reduceTableAt b ∗ F by ac_rfl]
    apply ih (i + 1) (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)])
      (by omega) (by omega) (by simp [hxs_len]) _ F
      (by rw [hentry]; wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
    intro sf hpc_f hrun_f hsp_f htr_f hx1_f hx19_f hx20_f hx23_f hx24_f hx25_f hx27_f hx29_f hvregs_f
    rw [powersLoopPure_succ i (r' + 1) xs h1 h2] at hnext
    exact hnext sf hpc_f hrun_f hsp_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      hx1_f
      (by rw [hx19_f]; simpa [arm64_norm, wp_norm] using hx19_1)
      hx20_f hx23_f
      (by rw [hx24_f]; simpa [arm64_norm, wp_norm] using hx24_1)
      hx25_f hx27_f
      (by rw [hx29_f]; simpa [arm64_norm, wp_norm] using hx29_1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

/-! ## Loop 2 (`0x61aec..0x61ae8`): Dot-Product Loop (`dotLoopPure`) -/

private theorem perm_dot_post (R T C X F : SepProp) :
    R ∗ T ∗ C ∗ X ∗ F = C ∗ X ∗ T ∗ R ∗ F := by
  ac_rfl

set_option maxHeartbeats 1600000 in
theorem dotStep_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (p_coeffs p_xs : BitVec 64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (r k : Nat) (acc : GF16)
    (hkc : k < coeffs.length) (hkx : k < xs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 472#64)
    (hrun : s.status = .Running)
    (hsp_al : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k))
    (hx20 : BitVec.truncate 16 (s.readReg64 .x20) = acc.value)
    (hx23 : s.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c))
    (hx25 : s.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)))
    (hx27 : s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k))
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (r + 1))
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 468#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      (sf.sp &&& 15#64 == 0#64) = true →
      sf.trace = s.trace →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (r + 1)) 1#64 →
      sf.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * (k + 1)) →
      BitVec.truncate 16 (sf.readReg64 .x20) = (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx))).value →
      sf.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
      sf.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
      sf.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x28 = BitVec.ofNat 64 r →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         tokenInitAt b ∗ reduceTableAt b ∗ F) Q) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_coeffs coeffs ∗
       gf16SliceAt p_xs xs ∗
       tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  have hmul : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr computeAtName + BitVec.ofNat 64 9104)
      (unacceleratedMulSpec b) := unacceleratedMul_at_computeAt b ext
  have hfn : libsignalSessionCode.fnOff computeAtName = 0x5c51c := computeAt_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
    (Rust.withPanics ext) hfn 0x5c51c 0x1c8 44
  dsimp only [tripleRatchetProgAtExt] at hmul
  clear hfn
  have halign_bd8 := LagrangePrepare.aligned_86bd8 b hb
  have hal_x := aligned16_add_mul_two p_xs hpx_al k
  have hstep_c := ptr_add_two_step p_coeffs k
  have hstep_x := ptr_add_two_step p_xs k
  have hsub_r := ofNat_sub_one_succ r
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
  examples_hide_fetches
  wp_conv_pre => rw [LagrangeComplete.gf16SliceAt_focus_assoc hkc p_coeffs]
  wp_steps 1
  wp_conv_pre =>
    rw [← LagrangeComplete.gf16SliceAt_focus_assoc hkc p_coeffs,
        LagrangeComplete.gf16SliceAt_focus_assoc hkx p_xs]
  wp_steps 1
  wp_conv_pre =>
    rw [← LagrangeComplete.gf16SliceAt_focus_assoc hkx p_xs]
  wp_simp_pre [tokenInitAt]
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_assumption
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_bd8
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold (tokenInitAt_fold b) (by sep_focus)
  wp_call hmul
  wp_steps 2
  wp_conv_pre => rw [perm_dot_post]
  exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp_sf)
    (by simpa [arm64_norm, wp_norm, hsp_sf] using hsp_al)
    (by simpa [arm64_norm, wp_norm] using hpost)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using h)
    (by simp only [arm64_norm, wp_norm]
        rw [h_10, hx20]
        exact eor_gf16_add_comm acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
    (by simpa [arm64_norm, wp_norm, h_4] using hx23)
    (by simpa [arm64_norm, wp_norm, h_6] using hx25)
    (by simpa [arm64_norm, wp_norm] using h_8)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hcs_sf)
    (by simpa [arm64_norm, wp_norm] using hvregs)

set_option maxHeartbeats 1600000 in
theorem dotLoop_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (p_coeffs p_xs : BitVec 64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (hlen_le : coeffs.length ≤ xs.length) (hlen_bound : 2 * coeffs.length + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r k : Nat) (acc : GF16)
      (_hkr : k + (r + 1) = coeffs.length)
      (s : State) (F : SepProp),
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 472#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k) →
      BitVec.truncate 16 (s.readReg64 .x20) = acc.value →
      s.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c) →
      s.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)) →
      s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x28 = BitVec.ofNat 64 (r + 1) →
      (∀ sf : State,
        sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 616#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        (sf.sp &&& 15#64 == 0#64) = true →
        sf.trace = s.trace →
        BitVec.truncate 16 (sf.readReg64 .x20) = (dotLoopPure k (r + 1) coeffs xs acc).value →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_coeffs coeffs ∗
           gf16SliceAt p_xs xs ∗
           tokenInitAt b ∗ reduceTableAt b ∗ F) Q) →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro k acc hkr s F hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    apply dotStep_sepWP b ext hb p_coeffs p_xs hpx_al coeffs xs 0 k acc hkc hkx
      ret_pc Q s F hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28
    intro s1 hpc1 hrun1 hsp1 hsp_al1 htr1 hpst1 _hx19_1 hx20_1 _hx23_1 _hx25_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    have hfn : libsignalSessionCode.fnOff computeAtName = 0x5c51c := computeAt_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
      (Rust.withPanics ext) hfn 0x5c51c 0x1d4 4
    clear hfn
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
    examples_hide_fetches
    wp_steps 1
    rw [dotLoopPure_succ k 0 coeffs xs acc hkc hkx] at hnext
    dsimp only [dotLoopPure] at hnext
    exact hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hsp_al1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro k acc hkr s F hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    rcases subs_succ_one_ne_zero (r := r') (by omega) with ⟨hneq1, hneq2⟩
    apply dotStep_sepWP b ext hb p_coeffs p_xs hpx_al coeffs xs (r' + 1) k acc hkc hkx
      ret_pc Q s F hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28
    intro s1 hpc1 hrun1 hsp1 hsp_al1 htr1 hpst1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    have hfn : libsignalSessionCode.fnOff computeAtName = 0x5c51c := computeAt_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
      (Rust.withPanics ext) hfn 0x5c51c 0x1d4 4
    clear hfn
    generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
    examples_hide_fetches
    wp_steps 1
    rw [← hentry]
    apply ih (k + 1) (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
      (by omega) _ F
      (by rw [hentry]; wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp_al1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
    intro sf hpc_f hrun_f hsp_f hsp_al_f htr_f hx20_f hx29_f hvregs_f
    rw [dotLoopPure_succ k (r' + 1) coeffs xs acc hkc hkx] at hnext
    exact hnext sf hpc_f hrun_f
      (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp1)
      hsp_al_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      hx20_f
      (by rw [hx29_f]; simpa [arm64_norm, wp_norm] using hx29_1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

/-! ## Shared Dot-Product Phase (`0x61ab4..0x61b7c`) for `1 ≤ len` -/

set_option maxHeartbeats 1600000 in
theorem dot_from_61ab4_sepWP
    (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (a : ComputeAtArgs) (hlen_pos : 0 < a.poly.coefficients.length)
    (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx23 : s.readReg64 .x23 = b + bv% (ls_xref% 0x5e628 0x5e62c))
    (hx25 : s.readReg64 .x25 = b + bv% (page% (ls_xref% 0x5e638 0x5e63c)))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hnext : ∀ sf : State,
      sf.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName + 616#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      BitVec.truncate 16 (sf.readReg64 .x20) = (computeAtPure a.poly a.x).value →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
         gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
         tokenInitAt b ∗ reduceTableAt b ∗ F) Q) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
       tokenInitAt b ∗ reduceTableAt b ∗ F) Q := by
  have hfn : libsignalSessionCode.fnOff computeAtName =
      num% (ls_off% "<spqr::encoding::polynomial::Poly>::compute_at") := computeAt_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode computeAtBin b
    (Rust.withPanics ext) hfn 0x5c51c 0x1a0 40
  clear hfn
  rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hlen_ne0, _⟩
  have hult_false :
      (BitVec.ofNat 64 (max 2 a.poly.coefficients.length)).ult
        (BitVec.ofNat 64 a.poly.coefficients.length) = false :=
    ult_max_two_false a.poly.coefficients.length hlen_bound
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, beq_iff_eq]; revert hsp0; bv_bits
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr computeAtName = entry
  examples_hide_fetches
  wp_steps 10
  rw [← hentry]
  have hle_powers :
      a.poly.coefficients.length ≤
        (computeAtPowersPure a.poly.coefficients.length a.x).length := by
    rw [computeAtPowersPure_length]; omega
  have hr_eq :
      BitVec.ofNat 64 a.poly.coefficients.length =
        BitVec.ofNat 64 (a.poly.coefficients.length - 1 + 1) := by
    congr 1; omega
  apply dotLoop_sepWP b ext hb a.p_coeffs p_xs hp_xs
    a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x)
    hle_powers hlen_bound ret_pc Q
    (a.poly.coefficients.length - 1) 0 GF16.ZERO (by omega)
    _ F
    (by rw [hentry]; wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp_al)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by rfl)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by simpa [arm64_norm, wp_norm] using hx25)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm, hr_eq])
  intro sf hpc_f hrun_f hsp_f _hsp_al_f htr_f hx20_f hx29_f hvregs_f
  have hdot_eq :
      dotLoopPure 0 (a.poly.coefficients.length - 1 + 1)
        a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x) GF16.ZERO =
        computeAtPure a.poly a.x := by
    rw [Nat.sub_add_cancel hlen_pos, ← computeAtPure_eq_dotLoopPure]
  rw [hdot_eq] at hx20_f
  rw [hentry] at hpc_f
  exact hnext sf hpc_f hrun_f
    (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp)
    (by simpa [arm64_norm, wp_norm] using htr_f)
    hx20_f
    (by simpa [arm64_norm, wp_norm] using hx29_f)
    (by simpa [arm64_norm, wp_norm] using hvregs_f)

/-! ## Relocatable `[LibsignalPlacement]` Loops (Block `371`) -/

set_option maxHeartbeats 1600000 in
theorem powersStep_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 p_xs : BitVec 64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len i : Nat) (_hi2 : 2 ≤ i) (hi_lt : i < len) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (xs : List GF16) (hxs_len : xs.length = i)
    (h1 : i / 2 < xs.length) (h2 : (i / 2) + (i % 2) < xs.length)
    (v_slot : BitVec 16)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 216#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 len)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 i)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 212#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      sf.pstate = subsPState64 (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 1)) →
      sf.readReg64 .x1 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = BitVec.ofNat 64 len →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs →
      sf.readReg64 .x28 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_xs xs ∗
       ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
       ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
       ((sp0 - 128#64) ↦₆₄ p_xs) ∗
       ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have halign_tok := aligned_tokenOnce_placed
  have hshr := ofNat_ushr_one (i := i) (by omega)
  have hshr_bv := ofNat_ushr_one_bv (i := i) (by omega)
  have hule1 := ofNat_ule_false_of_lt (m := i / 2) (n := i) (by omega) (by omega)
  have hand1 := ofNat_and_one i
  have hadd1 := ofNat_add_ofNat (i / 2) (i % 2)
  have hule2 := ofNat_ule_false_of_lt (m := (i / 2) + (i % 2)) (n := i) (by omega) (by omega)
  have hal1 := aligned16_add_mul_two p_xs hp_xs (i / 2)
  have hal2 := aligned16_add_mul_two p_xs hp_xs ((i / 2) + (i % 2))
  have hal_i := aligned16_add_mul_two p_xs hp_xs i
  rcases ofNat_beq_false_of_lt hi_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
  have hadd_i := ofNat_add_one i
  have h_fetch_ldar := blkPC_371_rebase_fetch_0xfc (blkPl_371).base (Rust.withPanics ext)
  have hmul := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
    (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 212#64)
  wp_steps 7
  wp_conv_pre => rw [LagrangeComplete.gf16SliceAt_focus_assoc h1 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← LagrangeComplete.gf16SliceAt_focus_assoc h1 p_xs, LagrangeComplete.gf16SliceAt_focus_assoc h2 p_xs]
  wp_steps 1
  wp_conv_pre => rw [← LagrangeComplete.gf16SliceAt_focus_assoc h2 p_xs]
  wp_simp_pre [tokenInitPlacedAt]
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact h_fetch_ldar
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_tok
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_call hmul
  wp_steps 10
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_next
  have hptr_eq : p_xs + BitVec.ofNat 64 (2 * i) = p_xs + BitVec.ofNat 64 (2 * xs.length) := by
    rw [hxs_len]
  have hval_eq : unaccelerated.mul (xs[i / 2]'h1).value (xs[(i / 2) + (i % 2)]'h2).value =
      (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)).value := rfl
  wp_conv_pre =>
    rw [hptr_eq, hval_eq,
        gf16SliceAt_append_singleton_assoc p_xs xs (GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)),
        perm_powers_post]
  exact hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm, hsp_sf] using hsp)
    (by simpa [arm64_norm, wp_norm] using hpost)
    (by wp_norm_lhs)
    (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using h)
    (by simpa [arm64_norm, wp_norm, h_1] using hx20)
    (by simpa [arm64_norm, wp_norm, h_4] using hx23)
    (by simpa [arm64_norm, wp_norm] using h_5)
    (by simpa [arm64_norm, wp_norm, h_6] using hx25)
    (by wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hcs_sf)
    (by simpa [arm64_norm, wp_norm] using hvregs)

set_option maxHeartbeats 1600000 in
theorem powersLoop_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (len : Nat) (hlen_bound : 2 * len + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r i : Nat) (xs : List GF16)
      (_hi2 : 2 ≤ i) (_hir : i + (r + 1) = len) (_hxs_len : xs.length = i)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_371).base + 216#64 →
      s.status = .Running →
      s.sp = sp0 - 144#64 →
      s.readReg64 .x1 = BitVec.ofNat 64 i →
      s.readReg64 .x20 = BitVec.ofNat 64 len →
      s.readReg64 .x23 = lsρ tokenName + 8#64 →
      s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x27 = p_xs →
      s.readReg64 .x28 = BitVec.ofNat 64 i →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_371).base + 416#64 →
        sf.status = .Running →
        sf.sp = sp0 - 144#64 →
        sf.trace = s.trace →
        sf.readReg64 .x1 = BitVec.ofNat 64 len →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = BitVec.ofNat 64 len →
        sf.readReg64 .x23 = lsρ tokenName + 8#64 →
        sf.readReg64 .x24 = s.readReg64 .x24 →
        sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
        sf.readReg64 .x27 = p_xs →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_xs (powersLoopPure i (r + 1) xs) ∗
           ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           ((sp0 - 128#64) ↦₆₄ p_xs) ∗
           ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 len) ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_xs xs ∗
         memRegion (p_xs + BitVec.ofNat 64 (2 * i)) (2 * (r + 1)) ∗
         ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
         ((sp0 - 128#64) ↦₆₄ p_xs) ∗
         ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro i xs hi2 hir hxs_len s F hcl hpc hrun hsp hx1 hx20 hx23 hx25 hx27 hx28 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hlen_eq : i + 1 = len := by omega
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) 0 (by omega),
        memRegion_zero, sepConj_emp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    apply powersStep_placed_sepWP ext sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len h1 h2 v_slot
      ret_pc Q s F hcl hpc hrun hsp hsp0 hx1 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hpst1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    rw [hlen_eq] at hpst1 hx1_1 hx28_1 ⊢
    wp_steps 1
    rw [powersLoopPure_succ i 0 xs h1 h2] at hnext
    dsimp only [powersLoopPure] at hnext
    exact hnext _ hcl1 (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx24_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro i xs hi2 hir hxs_len s F hcl hpc hrun hsp hx1 hx20 hx23 hx25 hx27 hx28 hnext
    have h1 : i / 2 < xs.length := by omega
    have h2 : (i / 2) + (i % 2) < xs.length := by omega
    have hi_lt : i < len := by omega
    have hi1_lt : i + 1 < len := by omega
    rcases ofNat_beq_false_of_lt hi1_lt (by omega) with ⟨hneq1, hneq2, hneq3, hneq4⟩
    rw [memRegion_two_succ (p_xs + BitVec.ofNat 64 (2 * i)) (r' + 1) (by omega),
        ptr_add_two_step p_xs i]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_left fun v_slot => ?_
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs xs ∗
            (((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
             memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1))) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F =
          gf16SliceAt p_xs xs ∗
            ((p_xs + BitVec.ofNat 64 (2 * i)) ↦₁₆ v_slot) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) by ac_rfl]
    apply powersStep_placed_sepWP ext sp0 p_xs hp_xs len i hi2 hi_lt hlen_bound xs hxs_len h1 h2 v_slot
      ret_pc Q s (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F)
      hcl hpc hrun hsp hsp0 hx1 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 htr1 hpst1 hx1_1 hx19_1 hx20_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    wp_steps 1
    wp_conv_pre =>
      rw [show gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            (memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗ F) =
          gf16SliceAt p_xs (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)]) ∗
            memRegion (p_xs + BitVec.ofNat 64 (2 * (i + 1))) (2 * (r' + 1)) ∗
            ((sp0 - 136#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((sp0 - 128#64) ↦₆₄ p_xs) ∗
            ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F by ac_rfl]
    apply ih (i + 1) (xs ++ [GF16.mul (xs[i / 2]'h1) (xs[(i / 2) + (i % 2)]'h2)])
      (by omega) (by omega) (by simp [hxs_len]) _ F (by exact hcl1)
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hx1_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
    intro sf hcl_f hpc_f hrun_f hsp_f htr_f hx1_f hx19_f hx20_f hx23_f hx24_f hx25_f hx27_f hx29_f hvregs_f
    rw [powersLoopPure_succ i (r' + 1) xs h1 h2] at hnext
    exact hnext sf hcl_f hpc_f hrun_f hsp_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      hx1_f
      (by rw [hx19_f]; simpa [arm64_norm, wp_norm] using hx19_1)
      hx20_f hx23_f
      (by rw [hx24_f]; simpa [arm64_norm, wp_norm] using hx24_1)
      hx25_f hx27_f
      (by rw [hx29_f]; simpa [arm64_norm, wp_norm] using hx29_1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
theorem dotStep_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (p_coeffs p_xs : BitVec 64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (r k : Nat) (acc : GF16)
    (hkc : k < coeffs.length) (hkx : k < xs.length)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 472#64)
    (hrun : s.status = .Running)
    (hsp_al : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k))
    (hx20 : BitVec.truncate 16 (s.readReg64 .x20) = acc.value)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k))
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (r + 1))
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 468#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      (sf.sp &&& 15#64 == 0#64) = true →
      sf.trace = s.trace →
      sf.pstate = subsPState64 (BitVec.ofNat 64 (r + 1)) 1#64 →
      sf.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * (k + 1)) →
      BitVec.truncate 16 (sf.readReg64 .x20) = (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx))).value →
      sf.readReg64 .x23 = lsρ tokenName + 8#64 →
      sf.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      sf.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x28 = BitVec.ofNat 64 r →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt p_coeffs coeffs ∗
       gf16SliceAt p_xs xs ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  have halign_tok := aligned_tokenOnce_placed
  have hal_x := aligned16_add_mul_two p_xs hpx_al k
  have hstep_c := ptr_add_two_step p_coeffs k
  have hstep_x := ptr_add_two_step p_xs k
  have hsub_r := ofNat_sub_one_succ r
  have h_fetch_ldar := blkPC_371_rebase_fetch_0x1e0 (blkPl_371).base (Rust.withPanics ext)
  have hmul := lscall_blk (callerProg := (blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext))
    (unacceleratedMul_placed_ok (Rust.withPanics ext)) hcl
  simp only [withMemEq, unacceleratedMulPlacedSpec] at hmul
  apply sepWP_seq_lscl (by exact hcl) (mid := (blkPl_371).base + 468#64)
  wp_conv_pre => rw [LagrangeComplete.gf16SliceAt_focus_assoc hkc p_coeffs]
  wp_steps 1
  wp_conv_pre =>
    rw [← LagrangeComplete.gf16SliceAt_focus_assoc hkc p_coeffs,
        LagrangeComplete.gf16SliceAt_focus_assoc hkx p_xs]
  wp_steps 1
  wp_conv_pre =>
    rw [← LagrangeComplete.gf16SliceAt_focus_assoc hkx p_xs]
  wp_simp_pre [tokenInitPlacedAt]
  apply step_ldar32
  · wp_norm_lhs
  · wp_norm_lhs
  · exact h_fetch_ldar
  · wp_norm_lhs
  · wp_norm_lhs
  · exact halign_tok
  · wp_sep_access
  · wp_norm_lhs
  wp_steps 5
  apply SepWP.fold tokenInitPlacedAt_fold (by sep_focus)
  wp_call hmul
  wp_steps 2
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  intro hcl_next
  wp_conv_pre => rw [perm_dot_post]
  exact hnext _ hcl_next (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp_sf)
    (by simpa [arm64_norm, wp_norm, hsp_sf] using hsp_al)
    (by simpa [arm64_norm, wp_norm] using hpost)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using h)
    (by simp only [arm64_norm, wp_norm]
        rw [h_10, hx20]
        exact eor_gf16_add_comm acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
    (by simpa [arm64_norm, wp_norm, h_4] using hx23)
    (by simpa [arm64_norm, wp_norm, h_6] using hx25)
    (by simpa [arm64_norm, wp_norm] using h_8)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hcs_sf)
    (by simpa [arm64_norm, wp_norm] using hvregs)

set_option maxHeartbeats 1600000 in
theorem dotLoop_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (p_coeffs p_xs : BitVec 64) (hpx_al : p_xs &&& 1#64 = 0#64)
    (coeffs xs : List GF16)
    (hlen_le : coeffs.length ≤ xs.length) (hlen_bound : 2 * coeffs.length + 2 ≤ 2 ^ 63)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop) :
    ∀ (r k : Nat) (acc : GF16)
      (_hkr : k + (r + 1) = coeffs.length)
      (s : State) (F : SepProp),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_371).base + 472#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = p_coeffs + BitVec.ofNat 64 (2 * k) →
      BitVec.truncate 16 (s.readReg64 .x20) = acc.value →
      s.readReg64 .x23 = lsρ tokenName + 8#64 →
      s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName) →
      s.readReg64 .x27 = p_xs + BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x28 = BitVec.ofNat 64 (r + 1) →
      (∀ sf : State,
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.pc = (blkPl_371).base + 616#64 →
        sf.status = .Running →
        sf.sp = s.sp →
        (sf.sp &&& 15#64 == 0#64) = true →
        sf.trace = s.trace →
        BitVec.truncate 16 (sf.readReg64 .x20) = (dotLoopPure k (r + 1) coeffs xs acc).value →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt p_coeffs coeffs ∗
           gf16SliceAt p_xs xs ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt p_coeffs coeffs ∗
         gf16SliceAt p_xs xs ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  intro r
  induction r with
  | zero =>
    intro k acc hkr s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    apply dotStep_placed_sepWP ext p_coeffs p_xs hpx_al coeffs xs 0 k acc hkc hkx
      ret_pc Q s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 hsp_al1 htr1 hpst1 _hx19_1 hx20_1 _hx23_1 _hx25_1 _hx27_1 _hx28_1 hx29_1 hvregs1
    wp_steps 1
    rw [dotLoopPure_succ k 0 coeffs xs acc hkc hkx] at hnext
    dsimp only [dotLoopPure] at hnext
    exact hnext _ hcl1 (by wp_norm_lhs) (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp1)
      (by simpa [arm64_norm, wp_norm] using hsp_al1)
      (by simpa [arm64_norm, wp_norm] using htr1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx29_1)
      (by simpa [arm64_norm, wp_norm] using hvregs1)
  | succ r' ih =>
    intro k acc hkr s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28 hnext
    have hkc : k < coeffs.length := by omega
    have hkx : k < xs.length := by omega
    rcases subs_succ_one_ne_zero (r := r') (by omega) with ⟨hneq1, hneq2⟩
    apply dotStep_placed_sepWP ext p_coeffs p_xs hpx_al coeffs xs (r' + 1) k acc hkc hkx
      ret_pc Q s F hcl hpc hrun hsp_al hx19 hx20 hx23 hx25 hx27 hx28
    intro s1 hcl1 hpc1 hrun1 hsp1 hsp_al1 htr1 hpst1 hx19_1 hx20_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1
    wp_steps 1
    apply ih (k + 1) (GF16.add acc (GF16.mul (coeffs[k]'hkc) (xs[k]'hkx)))
      (by omega) _ F (by exact hcl1)
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hsp_al1)
      (by simpa [arm64_norm, wp_norm] using hx19_1)
      (by simpa [arm64_norm, wp_norm] using hx20_1)
      (by simpa [arm64_norm, wp_norm] using hx23_1)
      (by simpa [arm64_norm, wp_norm] using hx25_1)
      (by simpa [arm64_norm, wp_norm] using hx27_1)
      (by simpa [arm64_norm, wp_norm] using hx28_1)
    intro sf hcl_f hpc_f hrun_f hsp_f hsp_al_f htr_f hx20_f hx29_f hvregs_f
    rw [dotLoopPure_succ k (r' + 1) coeffs xs acc hkc hkx] at hnext
    exact hnext sf hcl_f hpc_f hrun_f
      (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp1)
      hsp_al_f
      (by rw [htr_f]; simpa [arm64_norm, wp_norm] using htr1)
      hx20_f
      (by rw [hx29_f]; simpa [arm64_norm, wp_norm] using hx29_1)
      (by rw [hvregs_f]; simpa [arm64_norm, wp_norm] using hvregs1)

set_option maxHeartbeats 1600000 in
theorem dot_from_61ab4_placed_sepWP [LibsignalPlacement]
    (ext : String → Option (State → State))
    (a : ComputeAtArgs) (hlen_pos : 0 < a.poly.coefficients.length)
    (hlen_bound : 2 * a.poly.coefficients.length + 2 ≤ 2 ^ 63)
    (sp0 p_xs : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64) (hp_xs : p_xs &&& 1#64 = 0#64)
    (ret_pc : BitVec 64) (Q : State → SepProp → Prop)
    (s : State) (F : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_371).base + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 144#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (max 2 a.poly.coefficients.length))
    (hx19 : s.readReg64 .x19 = a.p_coeffs)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.poly.coefficients.length)
    (hx23 : s.readReg64 .x23 = lsρ tokenName + 8#64)
    (hx25 : s.readReg64 .x25 = Arm64.Obj.pageOf (lsρ tokenStorageName))
    (hx27 : s.readReg64 .x27 = p_xs)
    (hnext : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_371).base + 616#64 →
      sf.status = .Running →
      sf.sp = sp0 - 144#64 →
      sf.trace = s.trace →
      BitVec.truncate 16 (sf.readReg64 .x20) = (computeAtPure a.poly a.x).value →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
         gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q) :
    SepWP ((blkPC_371).rebase (blkPl_371).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt a.p_coeffs a.poly.coefficients ∗
       gf16SliceAt p_xs (computeAtPowersPure a.poly.coefficients.length a.x) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ F) Q := by
  rcases ofNat_beq_false_of_lt hlen_pos (by omega) with ⟨_, _, hlen_ne0, _⟩
  have hult_false :
      (BitVec.ofNat 64 (max 2 a.poly.coefficients.length)).ult
        (BitVec.ofNat 64 a.poly.coefficients.length) = false :=
    ult_max_two_false a.poly.coefficients.length hlen_bound
  have hsp_al : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, beq_iff_eq]; revert hsp0; bv_bits
  wp_steps 10
  have hle_powers :
      a.poly.coefficients.length ≤
        (computeAtPowersPure a.poly.coefficients.length a.x).length := by
    rw [computeAtPowersPure_length]; omega
  have hr_eq :
      BitVec.ofNat 64 a.poly.coefficients.length =
        BitVec.ofNat 64 (a.poly.coefficients.length - 1 + 1) := by
    congr 1; omega
  apply dotLoop_placed_sepWP ext a.p_coeffs p_xs hp_xs
    a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x)
    hle_powers hlen_bound ret_pc Q
    (a.poly.coefficients.length - 1) 0 GF16.ZERO (by omega)
    _ F (by exact hcl)
    (by wp_norm_lhs)
    (by wp_norm_lhs)
    (by simpa [arm64_norm, wp_norm] using hsp_al)
    (by simpa [arm64_norm, wp_norm] using hx19)
    (by rfl)
    (by simpa [arm64_norm, wp_norm] using hx23)
    (by simpa [arm64_norm, wp_norm] using hx25)
    (by simpa [arm64_norm, wp_norm] using hx27)
    (by simp only [arm64_norm, wp_norm, hr_eq])
  intro sf hcl_f hpc_f hrun_f hsp_f _hsp_al_f htr_f hx20_f hx29_f hvregs_f
  have hdot_eq :
      dotLoopPure 0 (a.poly.coefficients.length - 1 + 1)
        a.poly.coefficients (computeAtPowersPure a.poly.coefficients.length a.x) GF16.ZERO =
        computeAtPure a.poly a.x := by
    rw [Nat.sub_add_cancel hlen_pos, ← computeAtPure_eq_dotLoopPure]
  rw [hdot_eq] at hx20_f
  exact hnext sf hcl_f hpc_f hrun_f
    (by rw [hsp_f]; simpa [arm64_norm, wp_norm] using hsp)
    (by simpa [arm64_norm, wp_norm] using htr_f)
    hx20_f
    (by simpa [arm64_norm, wp_norm] using hx29_f)
    (by simpa [arm64_norm, wp_norm] using hvregs_f)

end CryptoVerification.SpqrV1.Poly.ComputeAt
