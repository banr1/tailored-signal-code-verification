/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolatePlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyDecoder as Decoder>::decoded_message` (Block `418`, Part 1): `withLsCodeLoaded` Inlined `lagrange_interpolate`

Threads `LibsignalCodeLoaded lsmpl` through the relocatable inlined `lagrange_interpolate`
helpers on Block `418` so cross-block calls to `lagrangePrepare` (Block `372`) and
`lagrangeComplete` (Block `373`) compose under `withLsCodeLoaded lsmpl`.
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.DecodedMessage

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt reduceTablePlacedAt)
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareName lagrangePrepare_fnOff LagrangePrepareArgs lagrangePrepareSpec
   lagrangePreparePlacedSpec lagrangePreparePure lagrangePreparePure_length
   lagrangePrepareStack polyOf_eq)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.States.Leaves (sepWP_seq_lscl of_sepWP_lscl)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local wp_unfold] withLsCodeLoaded
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  LagrangeComplete.sp_setPC_pre LagrangeComplete.sp_setMem_setPC_pre
  LagrangeComplete.readReg64_setPC_pre LagrangeComplete.readReg64_setMem_setPC_pre
  LagrangeComplete.readReg32_setPC_pre LagrangeComplete.readReg32_setMem_setPC_pre
  LagrangeComplete.readReg_setPC_pre LagrangeComplete.readReg_setMem_setPC_pre

attribute [local wp_norm, local arm64_norm]
  bv64_lsl1_norm bv64_add1_norm bv32_xor_gf16 umaddl_24_ofNat
  bv64_lsl1_norm' bv64_lsl4_norm' bv64_add1_norm' umaddl_24_ofNat'
attribute [local wp_norm ↓, local arm64_norm ↓]
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64
  sp96_sub_56 sp96_sub_48 sp96_sub_40 sp96_sub_32
  sp216_add_48 sp192_add_8 sp168_add_8 sp144_add_8 sp144_add_16

/-! ## 1. `SepWPp` Sequencing Helper for `LibsignalCodeLoaded` -/

theorem sepWPp_seq_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h R hm hL with ⟨sm, hst1, ⟨_, _, Pm, hmm, hcont⟩ | hpan | hoom⟩
  · obtain ⟨sf, hst2, hout⟩ :=
      hcont (hcl.of_keepsFrozen hst1.keepsFrozen) R hmm (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hst1, Or.inr (Or.inr hoom)⟩

/-! ## 2. Outer Loop with `withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec` -/

theorem lagrangeInterpolateOuterStep_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k i : Nat) (b_init : Poly) (pts_slice : List Pt)
    (outCoeffs workingCoeffs : List GF16)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536) (hi_lt : i < k)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k)
    (hout_len : outCoeffs.length = k)
    (hwork_len : workingCoeffs.length = k + 1)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 940#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx23 : s.readReg64 .x23 = pt_ptr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx26 : s.readReg64 .x26 = ptr_l)
    (hx27 : s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_418).base + 1036#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x19 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = pt_ptr →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
      sf.readReg64 .x28 = BitVec.ofNat 64 i →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt acc_ptr
          (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
            (lagrangeCompletePure b_init pts_slice i).coefficients) ∗
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
        post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (gf16SliceAt acc_ptr outCoeffs ∗
        gf16SliceAt ptr_l workingCoeffs ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      post := by
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpyRegionSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  have hinner := @lagrangeAccumulateInner_placed_sepWP _ ext ((blkPl_418).base + 1036#64) acc_ptr ptr_l k
    (lagrangeCompletePure b_init pts_slice i).coefficients hk_pos hk_le
    (by rw [lagrangeCompletePure_length, hb_len]) k 0 outCoeffs
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy hcomp hinner hpc hcont ⊢
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 373)
  refine SepWP.weaken_pre
    (show _ ⊢
      gf16SliceAt ptr_l workingCoeffs ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        (gf16SliceAt acc_ptr outCoeffs ∗ ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWP.weaken_pre (memcpy_gf16Slice_pre ptr_l ptr_b workingCoeffs b_init.coefficients
    (by omega) _) ?_
  wp_steps 6
  wp_call hmemcpy
  wp_conv_pre =>
    rw [← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
  have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by
    rw [hb_len]
  have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by
    rw [hpts_len]
  have hi_pts : i < pts_slice.length := by omega
  have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
  have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  wp_steps 6
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
  intro hcl1
  apply sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 1036#64)
  wp_call hcomp ⟨ptr_l, pt_ptr, b_init, pts_slice, i⟩
  wp_conv_pre => rw [hsp_sf, hsp]
  wp_steps 2
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hinner _
      (gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitPlacedAt ∗
        reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
      _ (by omega) (by omega) hout_len
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun_sf_1])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (fun sf3 hpc3 hstat3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
        hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 _ => ?_))
  apply SepWP.done hpc3 hstat3
  intro hcl3
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont sf3 hcl3 hpc3 hstat3
      (by rw [hsp3]; simp [wp_norm, arm64_norm, *])
      (by rw [htr3]; simp [traceVRegs, wp_norm, arm64_norm, *])
      (by rw [hx19_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx20_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx21_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx22_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx23_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx24_3]; simp [wp_norm, arm64_norm, *])
      hx25_3 hx26_3 hx27_3
      (by rw [hx28_3]; simp [wp_norm, arm64_norm, *])
      (by rw [hx29_3]; simp [wp_norm, arm64_norm, *]))

theorem lagrangeInterpolateOuter_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k) :
    ∀ (rem i : Nat) (outCoeffs workingCoeffs : List GF16)
      (s : State) (P : SepProp) (post : State → SepProp → Prop),
      rem > 0 →
      i + rem = k →
      outCoeffs.length = k →
      workingCoeffs.length = k + 1 →
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_418).base + 940#64 →
      s.status = .Running →
      s.sp = sp0 - 672#64 →
      s.readReg64 .x19 = BitVec.ofNat 64 i →
      s.readReg64 .x21 = BitVec.ofNat 64 k →
      s.readReg64 .x23 = pt_ptr →
      s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      s.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      s.readReg64 .x26 = ptr_l →
      s.readReg64 .x27 = 0#64 - BitVec.ofNat 64 k →
      s.readReg64 .x29 = sp0 - 96#64 →
      (∀ sf : State,
        sf.pc = (blkPl_418).base + 1136#64 →
        sf.status = .Running →
        sf.sp = sp0 - 672#64 →
        traceVRegs sf = traceVRegs s →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = BitVec.ofNat 64 k →
        sf.readReg64 .x22 = s.readReg64 .x22 →
        sf.readReg64 .x23 = pt_ptr →
        sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
        sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
        sf.readReg64 .x26 = ptr_l →
        sf.readReg64 .x29 = sp0 - 96#64 →
        SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
          (gf16SliceAt acc_ptr
            (lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs) ∗
            memRegion ptr_l (2 * (k + 1)) ∗
            gf16SliceAt ptr_b b_init.coefficients ∗
            ptSliceAt pt_ptr pts_slice ∗
            ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
          post) →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
        (gf16SliceAt acc_ptr outCoeffs ∗
          gf16SliceAt ptr_l workingCoeffs ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P)
        post := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro i outCoeffs workingCoeffs s P post hrem hsum hout_len hwork_len
      hcl hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hcont
    have hi_lt : i < k := by omega
    refine lagrangeInterpolateOuterStep_cl_placed_sepWP hmemcpy_sat hcomp sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0
      k i b_init pts_slice outCoeffs workingCoeffs hk_pos hk_le hi_lt hb_len hpts_len hout_len hwork_len
      s P post hcl hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29
      (fun s1 hcl1 hpc1 hstat1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => ?_)
    have hbne := bv64_succ_bne_of_le i k hi_lt hk_le
    have hrem_eq : rem = (rem - 1) + 1 := by omega
    have hstep_pure :
        lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs =
          lagrangeInterpolateLoopTotal b_init pts_slice (i + 1) (rem - 1)
            (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
              (lagrangeCompletePure b_init pts_slice i).coefficients) := by
      conv => lhs; rw [hrem_eq]
      simp [lagrangeInterpolateLoopTotal, hout_len]
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc1 hcont ⊢
    wp_steps 2
    by_cases hieq : i + 1 = k
    · have hrem1 : rem - 1 = 0 := by omega
      have hdec : decide (i + 1 ≠ k) = false := by simp [hieq]
      simp only [hdec, Bool.false_eq_true, ↓reduceIte]
      wp_steps 1
      have hdone :
          lagrangeAccumulateCoeffsTotal 0 k outCoeffs
            (lagrangeCompletePure b_init pts_slice i).coefficients =
            lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs := by
        rw [hstep_pure, hrem1, lagrangeInterpolateLoopTotal]
      have hlen_w' : (lagrangeCompletePure b_init pts_slice i).coefficients.length = k + 1 := by
        rw [lagrangeCompletePure_length, hb_len]
      have hto_mem :
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ⊢
            memRegion ptr_l (2 * (k + 1)) := by
        rw [← hlen_w']
        exact gf16SliceAt_to_memRegion ptr_l _
      rw [hdone]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left hto_mem)) ?_
      apply hcont <;> simp [wp_norm, arm64_norm, *]
    · have hdec : decide (i + 1 ≠ k) = true := by simp [hieq]
      simp only [hdec, ↓reduceIte]
      refine ih (rem - 1) (by omega) (i + 1)
        (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
          (lagrangeCompletePure b_init pts_slice i).coefficients)
        (lagrangeCompletePure b_init pts_slice i).coefficients
        _ P post (by omega) (by omega)
        (by rw [lagrangeAccumulateCoeffsTotal_length, hout_len])
        (by rw [lagrangeCompletePure_length, hb_len])
        hcl1
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hstat1])
        (by simp [wp_norm, arm64_norm, hsp1])
        (by simp [wp_norm, arm64_norm, hx19_1])
        (by simp [wp_norm, arm64_norm, hx21_1])
        (by simp [wp_norm, arm64_norm, hx23_1])
        (by simp [wp_norm, arm64_norm, hx24_1])
        (by simp [wp_norm, arm64_norm, hx25_1])
        (by simp [wp_norm, arm64_norm, hx26_1])
        (by simp [wp_norm, arm64_norm, hx27_1])
        (by simp [wp_norm, arm64_norm, hx29_1])
        (fun sf hpc_f hstat_f hsp_f htr_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hx26_f hx29_f => ?_)
      rw [← hstep_pure]
      apply hcont sf hpc_f hstat_f hsp_f
      · rw [htr_f]; simpa [wp_norm, arm64_norm] using htr1
      · rw [hx20_f]; simpa [wp_norm, arm64_norm] using hx20_1
      · exact hx21_f
      · rw [hx22_f]; simpa [wp_norm, arm64_norm] using hx22_1
      · exact hx23_f
      · exact hx24_f
      · exact hx25_f
      · exact hx26_f
      · exact hx29_f

/-! ## 3. Iteration `i = 0` and Cache-Miss Sub-Steps -/

theorem lagrangeInterpolate_copyAndComplete0_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (sp0 ptr_l ptr_b pt_ptr x19_slot v664 v640 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hptr_l_ne : ptr_l ≠ 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (_hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 796#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx0 : s.readReg64 .x0 = ptr_l)
    (hx19 : s.readReg64 .x19 = x19_slot)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx23 : s.readReg64 .x23 = ptr_b)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = (blkPl_418).base + 848#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion ptr_l (2 * (k + 1)) ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 664#64) ↦₆₄ v664) ∗
        ((sp0 - 640#64) ↦₆₄ v640) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpyRegionSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy hcomp hpc hcont ⊢
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  have hptr_l_ne0 : (ptr_l == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_l_ne
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 373)
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre ptr_l ptr_b b_init.coefficients (2 * (k + 1)) (by omega)]
  wp_steps 7
  wp_call hmemcpy
  wp_conv_pre =>
    rw [← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
  have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by
    rw [hb_len]
  have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by
    rw [hpts_len]
  have h0_pts : 0 < pts_slice.length := by omega
  have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
  have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
  wp_steps 6
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
  intro hcl1
  apply sepWP_seq_lscl hcl1 (mid := (blkPl_418).base + 848#64)
  wp_call hcomp ⟨ptr_l, pt_ptr, b_init, pts_slice, 0⟩
  wp_conv_pre => rw [hsp_sf, hsp]
  apply SepWP.done hpc_sf_1 hrun_sf_1
  intro hcl2
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont _ hcl2
      (by exact hpc_sf_1)
      (by exact hrun_sf_1)
      (by rw [hsp_sf_1, hsp_sf, hsp])
      (by simp [traceVRegs, wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *]))

theorem lagrangeInterpolate_copyFirstAcc_cl_placed_sepWP [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr v152 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_eq : b_init = lagrangePreparePure pts_slice)
    (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 848#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx26 : s.readReg64 .x26 = ptr_l)
    (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1136#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc sf
        (gf16SliceAt acc_ptr (lagrangeInterpolateTotal pts_slice).coefficients ∗
          memRegion ptr_l (2 * (k + 1)) ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post) :
    SepWP ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) ret_pc s
      (memRegion acc_ptr (2 * k) ∗
        gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) post := by
  have hb_len : b_init.coefficients.length = k + 1 := by
    rw [hb_eq, lagrangePreparePure_length, hpts_len]
  have hmemcpy : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpyRegionSpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  have houter := @lagrangeInterpolateOuter_cl_placed_sepWP _ ext ret_pc hmemcpy_sat hcomp
    sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0 k b_init pts_slice hk_pos hk_le hb_len hpts_len
  try dsimp only [BitVec.ofNat_eq_ofNat] at hmemcpy houter hpc hcont ⊢
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  let working0 := lagrangeCompletePure b_init pts_slice 0
  have hw0_len : working0.coefficients.length = k + 1 := by
    dsimp [working0]
    rw [lagrangeCompletePure_length, hb_len]
  have htoNat_k : (BitVec.ofNat 64 (2 * k)).toNat = (gf16ListBytes (working0.coefficients.drop 1)).length :=
    toNat_two_mul_eq_gf16ListBytes k (working0.coefficients.drop 1) hk_le
      (by rw [List.length_drop, hw0_len]; omega)
  have hand_k1 : BitVec.ofNat 64 (k + 1) &&& 0x7fffffffffffffff#64 = BitVec.ofNat 64 (k + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change (k + 1) &&& (2 ^ 63 - 1) = k + 1
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hsub1_k1 : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
    rw [← bv64_add1_norm' k, BitVec.add_sub_cancel]
  have hand_k : BitVec.ofNat 64 k &&& 0x7fffffffffffffff#64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change k &&& (2 ^ 63 - 1) = k
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hult_k_self : (BitVec.ofNat 64 k).ult (BitVec.ofNat 64 k) = false := by
    simp [BitVec.ult]
  have hk_ne0 : (BitVec.ofNat 64 k == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change k = 0 at h1
    omega
  have hlsl_k : (BitVec.ofNat 64 k) <<< 1 = BitVec.ofNat 64 (2 * k) :=
    bv64_lsl1_norm k
  have hsplit_w0 := gf16SliceAt_split_first' ptr_l working0.coefficients (by omega)
  apply sepWP_seq_lscl hcl
    (mid := if k = 1 then (blkPl_418).base + 1136#64 else (blkPl_418).base + 940#64)
  change SepWP _ _ _ (memRegion acc_ptr (2 * k) ∗ gf16SliceAt ptr_l working0.coefficients ∗ _) _
  wp_conv_pre => rw [hsplit_w0]
  wp_steps 15
  refine SepWP.weaken_pre
    (show _ ⊢
      memRegion acc_ptr (2 * k) ∗
        gf16SliceAt (ptr_l + 2#64) (working0.coefficients.drop 1) ∗
        (gf16At (working0.coefficients[0]'(by omega)) ptr_l ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 152#64) ↦₆₄ v152) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre acc_ptr (ptr_l + 2#64) (working0.coefficients.drop 1) (2 * k)
      (by rw [List.length_drop, hw0_len]; omega)]
  wp_call hmemcpy
  wp_conv_pre =>
    rw [← gf16SliceAt_eq_pointsToBytes (working0.coefficients.drop 1) acc_ptr,
        ← gf16SliceAt_eq_pointsToBytes (working0.coefficients.drop 1) (ptr_l + 2#64)]
  refine SepWP.weaken_pre
    (show _ ⊢
      (gf16At (working0.coefficients[0]'(by omega)) ptr_l ∗
        gf16SliceAt (ptr_l + 2#64) (working0.coefficients.drop 1)) ∗
        (gf16SliceAt acc_ptr (working0.coefficients.drop 1) ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 152#64) ↦₆₄ v152) ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          stackAt (sp0 - 672#64) lagrangeCompleteStack ∗ P) by
      exact Entails.of_eq (by ac_rfl)) ?_
  wp_conv_pre => rw [← hsplit_w0]
  have hbeq_k1 : (BitVec.ofNat 64 k - 1#64 == 0#64) = decide (k = 1) := by
    by_cases hk1 : k = 1
    · subst hk1; rfl
    · simp only [hk1, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h
      have h1 := congrArg (fun x => (x + 1#64).toNat) h
      rw [BitVec.sub_add_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      exact hk1 h1
  wp_steps 5
  by_cases hk1 : k = 1
  · subst hk1
    simp only [↓reduceIte]
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
    intro _hcl_sf
    have hinterp_k1 : working0.coefficients.drop 1 = (lagrangeInterpolateTotal pts_slice).coefficients := by
      have houter0 := lagrangeInterpolateTotal_coeffs_eq pts_slice (by omega)
      rw [hpts_len, Nat.sub_self, ← hb_eq] at houter0
      simpa [lagrangeInterpolateLoopTotal, working0] using houter0.symm
    rw [hinterp_k1]
    have hmem_l := gf16SliceAt_to_memRegion ptr_l working0.coefficients
    rw [hw0_len, Nat.mul_comm] at hmem_l
    refine SepWP.weaken_pre (sepConj_mono_left hmem_l) ?_
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont _
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_sf])
        (by
          simp only [wp_norm, arm64_norm]
          rw [hsp_sf, hsp])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        (by
          simp only [wp_norm, arm64_norm]
          exact h_1)
        (by
          simp only [wp_norm, arm64_norm]
          exact h_3)
        (by
          simp only [wp_norm, arm64_norm]
          rw [h_5]
          simp only [wp_norm, arm64_norm, hx24])
        (by
          simp only [wp_norm, arm64_norm]
          rw [h_7]
          exact hx26)
        (by
          simp only [wp_norm, arm64_norm]
          rw [hcs_sf]
          exact hx29))
  · simp only [hk1, ↓reduceIte]
    have hbeq_false : (BitVec.ofNat 64 k - 1#64 == 0#64) = false := by
      rw [hbeq_k1, decide_eq_false hk1]
    wp_steps 3
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf])
    intro hcl_sf
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (houter (k - 1) 1 (working0.coefficients.drop 1) working0.coefficients _
        (((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P)
        post
        (by omega) (by omega)
        (by rw [List.length_drop, hw0_len]; omega)
        hw0_len
        hcl_sf
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_sf])
        (by
          simp only [wp_norm, arm64_norm]
          rw [hsp_sf, hsp])
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm]
          rw [h_2]
          exact hx21)
        (by
          simp only [wp_norm, arm64_norm]
          exact h_4)
        (by
          simp only [wp_norm, arm64_norm]
          rw [h_5]
          exact hx24)
        (by
          simp only [wp_norm, arm64_norm]
          rw [h_6]
          exact hx25)
        (by
          simp only [wp_norm, arm64_norm]
          rw [h_7]
          exact hx26)
        (by simp [wp_norm, arm64_norm])
        (by
          simp only [wp_norm, arm64_norm]
          rw [hcs_sf]
          exact hx29)
        (fun sf_f hpc_f hstat_f hsp_f htr_f hx20_f _ hx22_f _ hx24_f _ hx26_f hx29_f => ?_))
    have hinterp_k :
      lagrangeInterpolateLoopTotal b_init pts_slice 1 (k - 1) (working0.coefficients.drop 1) =
        (lagrangeInterpolateTotal pts_slice).coefficients := by
      have houter_eq := lagrangeInterpolateTotal_coeffs_eq pts_slice (by omega)
      rw [hpts_len, ← hb_eq] at houter_eq
      exact houter_eq.symm
    rw [hinterp_k]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (hcont sf_f hpc_f hstat_f hsp_f
        (by rw [htr_f]; simp [traceVRegs, wp_norm, arm64_norm, *])
        (by
          rw [hx20_f]
          simp only [wp_norm, arm64_norm]
          exact h_1)
        (by
          rw [hx22_f]
          simp only [wp_norm, arm64_norm]
          exact h_3)
        hx24_f
        hx26_f
        hx29_f)

theorem lagrangeInterpolate_miss_prepare_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)))
    (sp0 acc_ptr pt_ptr v168 v160 v152 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hpts_len : pts_slice.length = k)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 732#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = acc_ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ (b_cap ptr_b : BitVec 64) (sf : State),
      (lagrangePreparePure pts_slice).coefficients.length ≤ b_cap.toNat →
      b_cap.toNat * 2 < 2 ^ 63 →
      ptr_b ≠ 0#64 →
      sf.pc = (blkPl_418).base + 760#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = acc_ptr →
      sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 152#64) ↦₆₄ 0#64) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          ptSliceAt pt_ptr pts_slice ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (((sp0 - 168#64) ↦₆₄ v168) ∗
        ((sp0 - 160#64) ↦₆₄ v160) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗
        memRegion (sp0 - 144#64) 24 ∗
        ptSliceAt pt_ptr pts_slice ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hprep hpc hnext ⊢
  apply of_sepWP_lscl hcl (mid := lsmpl.base 372)
  wp_steps 7
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
  intro hcl1
  let a : LagrangePrepareArgs := {
    out := sp0 - 144#64
    ptsPtr := pt_ptr
    pts := pts_slice
    hlen_bound := by omega
  }
  refine SepWPp.call (x := a) (ret_pc := (blkPl_418).base + 760#64)
    (F := ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
      ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
      ((sp0 - 152#64) ↦₆₄ 0#64) ∗ F)
    hprep
    (by simp [wp_norm, arm64_norm])
    (by simp [wp_norm, arm64_norm, hstat])
    (by
      unfold State.spAligned
      simp only [wp_norm, arm64_norm, hsp, sp672_aligned sp0 hsp0])
    (by simp [wp_norm, arm64_norm])
    (fun R' hm => ?_)
    (fun sf code R' _ hex => ?_)
    (fun sf _ hm => ?_)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
  · dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl1, ?_⟩
    simp only [lagrangePreparePlacedSpec, a, wp_norm, arm64_norm, hx29, hx27, hx21, hx0, hsp, hpts_len]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · simp only [withLsCodeLoaded, lagrangePreparePlacedSpec] at hex
    exact not_satisfies_false_sepConj hex
  · simp only [withLsCodeLoaded, lagrangePreparePlacedSpec] at hm
    exact allowPanic_frame (fun ⟨hal, hpre⟩ => by
      simp only [allocFailedIn, wp_norm, arm64_norm, htr_tr] at hal hpre ⊢
      exact ⟨hal, hpre⟩) hm
  · conv => arg 4; simp only [withLsCodeLoaded, lagrangePreparePlacedSpec, a, wp_norm, arm64_norm, htr_tr, hsp]
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = k + 1 := by
      rw [lagrangePreparePure_length, hpts_len]
    rcases hcs_f with ⟨hx19_f, hx20_f, hx21_f, hx22_f, _, hx24_f, _, _, hx27_f, _, hx29_f, hvregs_f⟩
    refine SepWPp.pure_elim_focus (sf.trace = s0.trace) (fun htr_f' => ?_) (by sep_focus)
    rw [polyOf_eq A (sp0 - 144#64) (lagrangePreparePure pts_slice)]
    rw [sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro b_cap
    rw [sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro ptr_b
    refine SepWPp.pure_elim_focus
      ((lagrangePreparePure pts_slice).coefficients.length ≤ b_cap.toNat ∧
        b_cap.toNat * 2 < 2 ^ 63 ∧ ptr_b ≠ 0) (fun ⟨hcap_ge, hcap_lt, hptr_b_ne⟩ => ?_) (by sep_focus)
    have hcap_ne0 : b_cap ≠ 0 := by
      intro h0
      rw [h0] at hcap_ge
      change (lagrangePreparePure pts_slice).coefficients.length ≤ 0 at hcap_ge
      omega
    conv => arg 4; simp only [hcap_ne0, ↓reduceIte]
    refine SepWPp.weaken_pre ?_
      (hnext b_cap ptr_b sf hcap_ge hcap_lt hptr_b_ne hpc_f hrun_f
        (by simpa [wp_norm, arm64_norm, hsp] using hsp_f)
        (by simp [traceVRegs, wp_norm, arm64_norm, htr_vr, hvregs_f, htr_f'])
        (by simpa [wp_norm, arm64_norm] using hx19_f)
        (by simpa [wp_norm, arm64_norm] using hx20_f)
        (by simpa [wp_norm, arm64_norm, hx21] using hx21_f)
        (by simpa [wp_norm, arm64_norm] using hx22_f)
        (by simpa [wp_norm, arm64_norm, hx0] using hx24_f)
        (by simpa [wp_norm, arm64_norm, hx27] using hx27_f)
        (by simpa [wp_norm, arm64_norm, hx29] using hx29_f))
    rw [show (sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (lagrangePreparePure pts_slice).coefficients.length =
          (sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1) by rw [hb_len]]
    exact Entails.of_eq (by ac_rfl)

theorem lagrangeInterpolate_inlined_cl_placed_wpp [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (h_panic : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionSpec)
    (hprep : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 372) (withLsCodeLoaded lsmpl (lagrangePreparePlacedSpec A)))
    (hcomp : subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
      (lsmpl.base 373) (withLsCodeLoaded lsmpl lagrangeCompletePlacedSpec))
    (sp0 pts_vec_ptr pt_ptr x24_saved : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx : Nat) (optPoly : Option Poly) (pts_slice : List Pt)
    (hpoly : polyIdx < 16) (hk_pos : 1 ≤ pts_slice.length) (hk_le : pts_slice.length ≤ 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_418).base + 660#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx) (hx24 : s.readReg64 .x24 = x24_saved)
    (hx25 : s.readReg64 .x25 = 24#64) (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_418).base + 1284#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = x24_saved → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc sf
        (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (optPoly.getD (lagrangeInterpolateTotal pts_slice))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext)) target_pc s
      (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) optPoly ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
        ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
        reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  cases optPoly with
  | some p =>
    simp only [Option.getD_some] at hnext
    apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1284#64)
    refine lagrangeInterpolate_hit_placed_sepWP sp0 polyIdx p hpoly s _ _ hpc hstat hx0 hx25 hx26 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx24_f hx25_f hx26_f hx29_f _
    apply SepWP.done hpc_f hrun_f
    exact hnext sf hpc_f hrun_f (hsp_f.trans hsp) (htr_f.trans htr)
      hx19_f hx20_f hx22_f (hx24_f.trans hx24) hx25_f hx26_f (hx29_f.trans hx29)
  | none =>
    simp only [Option.getD_none] at hnext
    refine SepWPp.weaken_pre
      (show _ ⊢
        interpolateScratchAt sp0 ∗
        (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        exact Entails.of_eq (by ac_rfl)) ?_
    unfold interpolateScratchAt
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v664
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v656
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v640
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v192
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v184
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v176
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v168
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v160
    rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v152
    apply sepWPp_seq_lscl hcl (mid := (blkPl_418).base + 732#64)
    refine SepWPp.weaken_pre ?_
      (lagrangeInterpolate_miss_allocAcc_placed_wpp h_panic hshim_sat halloc_sat sp0 pts_vec_ptr pt_ptr hsp0
        polyIdx pts_slice.length hpoly hk_pos hk_le s0 s
        (((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
          memRegion (sp0 - 144#64) 24 ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        R _ hpc hstat hsp htr hx0 hx25 hx26 hx29 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]
      exact Entails.of_eq (by ac_rfl)
    intro sf1 hpc1 hrun1 hsp1 htr1 hacc_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1
    apply SepWPp.done hpc1 hrun1
    intro hcl1
    apply sepWPp_seq_lscl hcl1 (mid := (blkPl_418).base + 760#64)
    refine SepWPp.weaken_pre ?_
      (lagrangeInterpolate_miss_prepare_cl_placed_wpp hprep sp0 (sf1.readReg64 .x0) pt_ptr v168 v160 v152
        hsp0 pts_slice.length pts_slice hk_pos hk_le rfl s0 sf1
        (A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        R _ hcl1 hpc1 hrun1 hsp1 htr1 rfl hx21_1 hx27_1 hx29_1 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]
      exact Entails.of_eq (by ac_rfl)
    intro b_cap ptr_b sf2 hb_cap_ge hb_cap_lt hptr_b_ne hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx27_2 hx29_2
    apply SepWPp.done hpc2 hrun2
    intro hcl2
    apply sepWPp_seq_lscl hcl2 (mid := (blkPl_418).base + 796#64)
    refine SepWPp.weaken_pre ?_
      (lagrangeInterpolate_miss_allocL_placed_wpp h_panic hshim_sat halloc_sat sp0 (sf1.readReg64 .x0) ptr_b pt_ptr
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) v656 hsp0
        pts_slice.length hk_pos hk_le s0 sf2
        (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ A.live ptr_b (b_cap.toNat * 2) 2 ∗
          gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 640#64) ↦₆₄ v640) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        R _ hpc2 hrun2 hsp2 htr2 (hx19_2.trans hx19_1) hx21_2 hx24_2 hx27_2 hx29_2 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]
      exact Entails.of_eq (by ac_rfl)
    intro sf3 hpc3 hrun3 hsp3 htr3 hptr_l_ne hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3
    apply SepWPp.done hpc3 hrun3
    intro hcl3
    apply SepWPp.of_sepWP (mid := (blkPl_418).base + 1284#64)
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = pts_slice.length + 1 :=
      lagrangePreparePure_length pts_slice
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyAndComplete0_cl_placed_sepWP hmemcpy_sat hcomp sp0 (sf3.readReg64 .x0) ptr_b pt_ptr
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) v664 v640 hsp0 hptr_l_ne
        pts_slice.length (lagrangePreparePure pts_slice) pts_slice hk_pos hk_le hb_len rfl
        sf3
        (A.live (sf3.readReg64 .x0) (2 * (pts_slice.length + 1)) 2 ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          A.pool ∗ memRegion ((sp0 - 672#64) - 4096#64) 3856 ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hcl3 hpc3 hrun3 hsp3 rfl hx19_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3 ?_)
    · rw [stackAt_alloc_eq_complete (sp0 - 672#64)]
      exact Entails.of_eq (by ac_rfl)
    intro sf4 hcl4 hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx22_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyFirstAcc_cl_placed_sepWP hmemcpy_sat hcomp sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0)
        ptr_b pt_ptr 0#64 hsp0 pts_slice.length (lagrangePreparePure pts_slice) pts_slice
        hk_pos hk_le rfl rfl sf4
        (A.live (sf3.readReg64 .x0) (2 * (pts_slice.length + 1)) 2 ∗
          A.live ptr_b (b_cap.toNat * 2) 2 ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          A.pool ∗ memRegion ((sp0 - 672#64) - 4096#64) 3856 ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hcl4 hpc4 hrun4 hsp4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 ?_)
    · exact Entails.of_eq (by ac_rfl)
    intro sf5 hpc5 hrun5 hsp5 htr5 hx20_5 hx22_5 hx24_5 hx26_5 hx29_5
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolateDealloc_placed_sepWP hdealloc_sat sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0) ptr_b b_cap
        v192 v184 v176 hsp0 pts_slice.length (lagrangePreparePure pts_slice)
        hk_le hb_len hb_cap_ge hb_cap_lt sf5
        (A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          gf16SliceAt (sf1.readReg64 .x0) (lagrangeInterpolateTotal pts_slice).coefficients ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (pts_slice.length + 1)) ∗
          reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc5 hrun5 hsp5 hx24_5 hx26_5 hx29_5 ?_)
    · rw [stackAt_alloc_eq_complete (sp0 - 672#64)]
      exact Entails.of_eq (by ac_rfl)
    intro sf6 hpc6 hrun6 hsp6 htr6 hx20_6 hx22_6 hx29_6
    have hout_len : (lagrangeInterpolateTotal pts_slice).coefficients.length = pts_slice.length :=
      lagrangeInterpolateTotal_length pts_slice
    refine SepWP.weaken_pre ?_
      (@lagrangeInterpolateStoreSlot_placed_sepWP _ A ext _ sp0 (sf1.readReg64 .x0)
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) x24_saved
        b_cap ptr_b (BitVec.ofNat 64 (pts_slice.length + 1))
        hsp0 pts_slice.length (lagrangeInterpolateTotal pts_slice).coefficients
        hk_pos hk_le hout_len hacc_ne sf6
        (((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
          stackAt (sp0 - 672#64) allocHookStack ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc6 hrun6 hsp6 hx29_6 ?_)
    · exact Entails.of_eq (by ac_rfl)
    intro sf7 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx22_7 hx24_7 hx25_7 hx26_7 hx29_7
    refine SepWP.weaken_pre
      (show _ ⊢
        ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 136#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          (((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
            ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
            ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
            ((sp0 - 184#64) ↦₆₄ sf1.readReg64 .x0) ∗
            ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
            ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
            ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
            ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
            optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
              (some (lagrangeInterpolateTotal pts_slice)) ∗
            ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
            ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
            stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; exact Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.weaken_pre (pointsTo64_three_entails_memRegion_24 sp0 _ _ _ _) ?_
    refine SepWP.weaken_pre
      (show _ ⊢
        ((sp0 - 664#64) ↦₆₄ ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))) ∗
          ((sp0 - 656#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 184#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          memRegion (sp0 - 144#64) 24 ∗
          (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
              (some (lagrangeInterpolateTotal pts_slice)) ∗
            ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
            ((sp0 - 608#64) ↦₆₄ 16#64) ∗
            ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
            ptSliceAt pt_ptr pts_slice ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ A.pool ∗
            stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        exact Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.weaken_pre (fold_interpolateScratchAt sp0 _ _ _ _ _ _ _ _ _ _) ?_
    apply SepWP.done hpc7 hrun7
    refine SepWPp.weaken_pre ?_
      (hnext sf7 hpc7 hrun7 hsp7 (by rw [htr7, htr6, htr5, htr4, htr3])
        hx19_7
        (by rw [hx20_7, hx20_6, hx20_5, hx20_4, hx20_3, hx20_2, hx20_1])
        (by rw [hx22_7, hx22_6, hx22_5, hx22_4, hx22_3, hx22_2, hx22_1])
        hx24_7 hx25_7 hx26_7 hx29_7)
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.DecodedMessage
