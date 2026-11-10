/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Loop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: 4K-Stack Inlined `lagrange_interpolate` Subroutines

**Checked by Lean.**

Lifts the outer loop, deallocation cleanup, and `i = 0` setup/complete subroutines of
`Interpolate.lean` to `AllocContracts4K b A ext`.
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompleteName lagrangeCompleteSpec
  lagrangeCompletePure lagrangeCompletePure_length lagrangeCompleteStack lagrangeComplete_fnOff)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageName decodedMessage_fnOff
  traceVRegs sp672_aligned gf16ListBytes gf16SliceAt_eq_pointsToBytes gf16SliceAt_to_memRegion
  lagrangeAccumulateCoeffsTotal lagrangeAccumulateCoeffsTotal_length lagrangeInterpolateLoopTotal
  lagrangeAccumulateInner_sepWP sub_ok_at_backward memcpy_gf16Slice_pre
  toNat_two_mul_succ_eq_gf16ListBytes bv64_succ_bne_of_le gf16Slice_spare_to_memRegion
  memcpy_memRegion_gf16Slice_pre stackAt_alloc_eq_complete
  bv64_lsl1_norm bv64_add1_norm bv32_xor_gf16
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64 sp96_sub_56
  sp96_sub_48 sp96_sub_40 sp96_sub_32 sp216_add_48 sp192_add_8 sp168_add_8
  sp144_add_8 sp144_add_16)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm, local arm64_norm] bv64_lsl1_norm bv64_add1_norm bv32_xor_gf16
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64 sp96_sub_56
  sp96_sub_48 sp96_sub_40 sp96_sub_32 sp216_add_48 sp192_add_8 sp168_add_8
  sp144_add_8 sp144_add_16

open Lean Elab Tactic in
local elab "decoded_message_fetches_range_ext " b:term:max H:term:max k0:num len:num : tactic => do
  let codeName := `CryptoVerification.libsignalSessionCode
  let binName := `CryptoVerification.SpqrV1.Poly.DecodedMessage.decodedMessageBin
  let eOff ← ProofLib.CodeLookup.lookup codeName .fnOff
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range $(mkCIdent codeName) $(mkIdent binName) $b $H $hfn $offLit $k0 $len))

/-! ## Outer Loop (`entry + 940#64` to `entry + 1136#64`) under `AllocContracts4K` -/

/-- Single iteration of the outer loop (`entry + 940#64` to `entry + 1036#64`) for `1 ≤ i < k`. -/
theorem lagrangeInterpolateOuterStep_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
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
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 940#64)
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
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1036#64 →
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
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (gf16SliceAt acc_ptr
          (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
            (lagrangeCompletePure b_init pts_slice i).coefficients) ∗
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitAt b ∗
          reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P)
        post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (gf16SliceAt acc_ptr outCoeffs ∗
        gf16SliceAt ptr_l workingCoeffs ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        stackAt (sp0 - 672#64) allocHookStack ∗ P)
      post := by
  have hmemcpy := hA.session_memcpy_region_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" "memcpy")
    (hk := by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hcomp_at := sub_ok_at_backward hcomp decodedMessageName
    (num% (2 ^ 64 - ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete"
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
    (by rw [lagrangeComplete_fnOff, decodedMessage_fnOff]; rfl)
  have hinner := @lagrangeAccumulateInner_sepWP b ext ret_pc acc_ptr ptr_l k
    (lagrangeCompletePure b_init pts_slice i).coefficients hk_pos hk_le
    (by rw [lagrangeCompletePure_length, hb_len]) k 0 outCoeffs
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 940 56
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hmemcpy hcomp_at hinner hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  refine SepWP.weaken_pre
    (show _ ⊢
      gf16SliceAt ptr_l workingCoeffs ∗ gf16SliceAt ptr_b b_init.coefficients ∗
        (gf16SliceAt acc_ptr outCoeffs ∗ ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗ ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) by
      sep_frame) ?_
  refine SepWP.weaken_pre (memcpy_gf16Slice_pre ptr_l ptr_b workingCoeffs b_init.coefficients
    (by omega) _) ?_
  wp_steps 6
  wp_call hmemcpy
  wp_conv_pre =>
    simp only [wp_norm, arm64_norm, hsp]
    rw [stackAt_alloc_eq_complete (sp0 - 672#64),
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
  have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by
    rw [hb_len]
  have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by
    rw [hpts_len]
  have hi_pts : i < pts_slice.length := by omega
  have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
  have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
  wp_steps 6
  wp_call hcomp_at ⟨ptr_l, pt_ptr, b_init, pts_slice, i⟩
  wp_conv_pre => simp only [wp_norm, arm64_norm, hsp_sf, hsp]
  refine SepWP.weaken_pre
    (show _ ⊢
      (memRegion (sp0 - 672#64 - 4096#64) 3856 ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack) ∗
        (gf16SliceAt acc_ptr outCoeffs ∗
          gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice i).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitAt b ∗
          reduceTableAt b ∗ P) by
      sep_frame) ?_
  wp_conv_pre => rw [← stackAt_alloc_eq_complete (sp0 - 672#64)]
  wp_steps 2
  refine SepWP.weaken_pre (by sep_frame)
    (hinner _
      (gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        stackAt (sp0 - 672#64) allocHookStack ∗ P)
      post (by omega) (by omega) hout_len
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, hrun_sf_1])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (fun sf3 hpc3 hstat3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
        hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 _ => ?_))
  refine SepWP.weaken_pre (by sep_frame)
    (hcont sf3 hpc3 hstat3
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

/-- Outer loop (`entry + 940#64` to `entry + 1136#64`) for `i` from `i0` to `k - 1` (`rem = k - i0 > 0`). -/
theorem lagrangeInterpolateOuter_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
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
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 940#64 →
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
        sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1136#64 →
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
        SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
          (gf16SliceAt acc_ptr
            (lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs) ∗
            memRegion ptr_l (2 * (k + 1)) ∗
            gf16SliceAt ptr_b b_init.coefficients ∗
            ptSliceAt pt_ptr pts_slice ∗
            ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
            ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
            tokenInitAt b ∗
            reduceTableAt b ∗
            stackAt (sp0 - 672#64) allocHookStack ∗ P)
          post) →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc s
        (gf16SliceAt acc_ptr outCoeffs ∗
          gf16SliceAt ptr_l workingCoeffs ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitAt b ∗
          reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P)
        post := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro i outCoeffs workingCoeffs s P post hrem hsum hout_len hwork_len
      hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29 hcont
    have hi_lt : i < k := by omega
    refine lagrangeInterpolateOuterStep_sepWP_4k hb hA hcomp sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0
      k i b_init pts_slice outCoeffs workingCoeffs hk_pos hk_le hi_lt hb_len hpts_len hout_len hwork_len
      s P post hpc hstat hsp hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx29
      (fun s1 hpc1 hstat1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => ?_)
    have hbne := bv64_succ_bne_of_le i k hi_lt hk_le
    have hrem_eq : rem = (rem - 1) + 1 := by omega
    have hstep_pure :
        lagrangeInterpolateLoopTotal b_init pts_slice i rem outCoeffs =
          lagrangeInterpolateLoopTotal b_init pts_slice (i + 1) (rem - 1)
            (lagrangeAccumulateCoeffsTotal 0 k outCoeffs
              (lagrangeCompletePure b_init pts_slice i).coefficients) := by
      conv => lhs; rw [hrem_eq]
      simp [lagrangeInterpolateLoopTotal, hout_len]
    decoded_message_fetches_range_ext b (Rust.withPanics ext) 1036 12
    dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hpc1 hcont ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
    examples_hide_fetches
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

/-! ## Cleanup (`entry + 1136#64` to `entry + 1196#64`) & Copy+Complete `i = 0` (`entry + 796#64` to `entry + 848#64`) -/

/-- First half of cleanup (`entry + 1136#64` to `entry + 1196#64`):
    copies `(k, acc_ptr, k)` from `[X29 - 72]` to `[X29 - 96]` and deallocates `ptr_l` and `ptr_b`. -/
theorem lagrangeInterpolateDealloc_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (sp0 acc_ptr ptr_l ptr_b b_cap : BitVec 64)
    (v192 v184 v176 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly)
    (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hb_cap_ge : b_init.coefficients.length ≤ b_cap.toNat)
    (hb_cap_lt : b_cap.toNat * 2 < 2 ^ 63)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1136#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx26 : s.readReg64 .x26 = ptr_l)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1196#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (A.live ptr_l (2 * (k + 1)) 2 ∗
        memRegion ptr_l (2 * (k + 1)) ∗
        A.live ptr_b (b_cap.toNat * 2) 2 ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        memRegion (ptr_b + BitVec.ofNat 64 (b_init.coefficients.length * 2))
          ((b_cap.toNat - b_init.coefficients.length) * 2) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 192#64) ↦₆₄ v192) ∗
        ((sp0 - 184#64) ↦₆₄ v184) ∗
        ((sp0 - 176#64) ↦₆₄ v176) ∗
        ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
        ((sp0 - 144#64) ↦₆₄ b_cap) ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have hdealloc1 := hA.dealloc_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_dealloc")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 1136 60
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hdealloc1 hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  have htoNat_l : (BitVec.ofNat 64 (2 * (k + 1))).toNat = 2 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb_cap_ne0 : (b_cap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    change b_cap.toNat = 0 at h1
    omega
  have hb_cap_shl : (b_cap <<< 1).toNat = b_cap.toNat * 2 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
  wp_steps 9
  wp_call hdealloc1
  wp_conv_pre => rw [hsp]
  refine SepWP.weaken_pre
    (show _ ⊢
      gf16SliceAt ptr_b b_init.coefficients ∗
        memRegion (ptr_b + BitVec.ofNat 64 (b_init.coefficients.length * 2))
          ((b_cap.toNat - b_init.coefficients.length) * 2) ∗
        (A.live ptr_b (b_cap.toNat * 2) 2 ∗ A.pool ∗
          stackAt (sp0 - 672#64) allocHookStack ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 192#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 184#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 160#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ P) by
      sep_frame) ?_
  refine SepWP.weaken_pre
    (gf16Slice_spare_to_memRegion ptr_b b_init.coefficients b_cap.toNat hb_cap_ge hb_cap_lt _) ?_
  wp_steps 6
  wp_call hdealloc1
  wp_conv_pre => rw [hsp_sf, hsp]
  refine SepWP.weaken_pre (by sep_frame)
    (hcont _
      (by exact hpc_sf_1)
      (by exact hrun_sf_1)
      (by rw [hsp_sf_1, hsp_sf, hsp])
      (by simp [traceVRegs, wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *])
      (by simp [wp_norm, arm64_norm, *]))

/-- First part of iteration `i = 0` (`entry + 796#64` to `entry + 848#64`):
    copies `b_init` to `ptr_l`, stores `x19_slot` and `ptr_b` on stack, and calls
    `lagrange_interpolate_complete(ptr_l, k + 1, pt_ptr, k, 0)`. -/
theorem lagrangeInterpolate_copyAndComplete0_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
    (sp0 ptr_l ptr_b pt_ptr x19_slot v664 v640 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (hptr_l_ne : ptr_l ≠ 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_len : b_init.coefficients.length = k + 1)
    (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 796#64)
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
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 848#64 →
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
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (memRegion ptr_l (2 * (k + 1)) ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 664#64) ↦₆₄ v664) ∗
        ((sp0 - 640#64) ↦₆₄ v640) ∗
        tokenInitAt b ∗ reduceTableAt b ∗
        stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have hmemcpy := hA.session_memcpy_region_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" "memcpy")
    (hk := by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hcomp_at := sub_ok_at_backward hcomp decodedMessageName
    (num% (2 ^ 64 - ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete"
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
    (by rw [lagrangeComplete_fnOff, decodedMessage_fnOff]; rfl)
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 796 52
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hmemcpy hcomp_at hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  have hptr_l_ne0 : (ptr_l == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_l_ne
  have htoNat_b : (BitVec.ofNat 64 (2 * (k + 1))).toNat = (gf16ListBytes b_init.coefficients).length :=
    toNat_two_mul_succ_eq_gf16ListBytes k b_init.coefficients hk_le hb_len
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre ptr_l ptr_b b_init.coefficients (2 * (k + 1)) (by omega)]
  wp_steps 7
  wp_call hmemcpy
  wp_conv_pre =>
    simp only [wp_norm, arm64_norm, hsp]
    rw [stackAt_alloc_eq_complete (sp0 - 672#64),
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_l,
        ← gf16SliceAt_eq_pointsToBytes b_init.coefficients ptr_b]
  have h1_len : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 b_init.coefficients.length := by
    rw [hb_len]
  have h3_len : BitVec.ofNat 64 k = BitVec.ofNat 64 pts_slice.length := by
    rw [hpts_len]
  have h0_pts : 0 < pts_slice.length := by omega
  have h2_lt : 2 * b_init.coefficients.length < 2 ^ 64 := by omega
  have h4_lt : 4 * pts_slice.length < 2 ^ 64 := by omega
  wp_steps 6
  wp_call hcomp_at ⟨ptr_l, pt_ptr, b_init, pts_slice, 0⟩
  wp_conv_pre => simp only [wp_norm, arm64_norm, hsp_sf, hsp]
  refine SepWP.weaken_pre
    (show _ ⊢
      (memRegion (sp0 - 672#64 - 4096#64) 3856 ∗
        stackAt (sp0 - 672#64) lagrangeCompleteStack) ∗
        (gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 664#64) ↦₆₄ x19_slot) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          tokenInitAt b ∗ reduceTableAt b ∗ P) by
      sep_frame) ?_
  wp_conv_pre => rw [← stackAt_alloc_eq_complete (sp0 - 672#64)]
  refine SepWP.weaken_pre (by sep_frame)
    (hcont _
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

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateExt
