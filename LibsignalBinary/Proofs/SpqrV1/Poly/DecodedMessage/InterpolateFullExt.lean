/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFull
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Interpolate
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateExt
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.ProofExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message`: 4K-Stack Full Inlined `lagrange_interpolate`

**Checked by Lean.**

Lifts the cache-miss steps and full inlined `Poly::lagrange_interpolate` block (`+660..+1284`) to
`AllocContracts4K b A ext` (`lagrangeInterpolate_inlined_wpp_4k`).
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack allocFailedEvent allocFailedIn)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.LibsignalTripleRatchet (panic_at_handle_error_ext tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTableAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitAt)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly (gf16At gf16SliceAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (
  lagrangePrepareName lagrangePrepare_fnOff LagrangePrepareArgs lagrangePrepareSpec
  lagrangePreparePure lagrangePreparePure_length lagrangePrepareStack lagrangePrepare_ok_4k
  polyOf_eq sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (
  lagrangeCompleteName lagrangeCompleteSpec lagrangeCompletePure lagrangeCompletePure_length)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  decodedMessageName decodedMessage_fnOff traceVRegs sp672_aligned optPolyCacheSlotAt ptSliceRefAt
  gf16ListBytes gf16SliceAt_eq_pointsToBytes gf16SliceAt_to_memRegion memcpy_memRegion_gf16Slice_pre
  toNat_two_mul_eq_gf16ListBytes lagrangeInterpolateLoopTotal lagrangeInterpolateTotal
  lagrangeInterpolateTotal_length lagrangeInterpolate_hit_sepWP lagrangeInterpolateStoreSlot_sepWP
  sub_ok_at_backward bv64_lsl1_norm bv64_lsl4_norm bv64_add1_norm umaddl_24_ofNat
  gf16SliceAt_split_first' lagrangeInterpolateTotal_coeffs_eq stackAt_prepare_eq_alloc
  allocFailedIn_of_trace_eq' interpolateScratchAt pointsTo64_three_entails_memRegion_24
  fold_interpolateScratchAt
  sp96_sub_120 sp96_sub_96 sp96_sub_80 sp96_sub_72 sp96_sub_64 sp96_sub_56
  sp96_sub_48 sp96_sub_40 sp96_sub_32 sp216_add_48 sp192_add_8 sp168_add_8
  sp144_add_8 sp144_add_16)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateExt (
  lagrangeInterpolateOuter_sepWP_4k lagrangeInterpolateDealloc_sepWP_4k
  lagrangeInterpolate_copyAndComplete0_sepWP_4k)

namespace LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullExt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm, local arm64_norm]
  bv64_lsl1_norm bv64_lsl4_norm bv64_add1_norm umaddl_24_ofNat
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

/-! ## Pure & Alloc Post Helpers -/

private theorem pull_pure_after_two_4k (P1 P2 : SepProp) (φ : Prop) (Rest : SepProp) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  rw [← sepConj_assoc P2 ⌜φ⌝ Rest, sepConj_comm P2 ⌜φ⌝, sepConj_assoc ⌜φ⌝ P2 Rest,
      ← sepConj_assoc P1 ⌜φ⌝ _, sepConj_comm P1 ⌜φ⌝, sepConj_assoc ⌜φ⌝ P1 _]

private theorem alloc_post_pos_4k {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ : Prop} {Q : SepProp}
    (h0 : x0 = 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else Q) ∗ Rest = ⌜φ⌝ ∗ P1 ∗ P2 ∗ Rest := by
  have h0' : x0 = 0 := h0
  simp only [h0', ↓reduceIte]
  exact pull_pure_after_two_4k P1 P2 φ Rest

private theorem alloc_post_neg_4k {P1 P2 Rest : SepProp} {x0 : BitVec 64} {φ ψ : Prop} {Q : SepProp}
    (h0 : x0 ≠ 0#64) :
    P1 ∗ P2 ∗ (if x0 = 0 then ⌜φ⌝ else ⌜ψ⌝ ∗ Q) ∗ Rest = ⌜ψ⌝ ∗ P1 ∗ P2 ∗ Q ∗ Rest := by
  have h0' : x0 ≠ 0 := h0
  simp only [h0', ↓reduceIte]
  rw [sepConj_assoc ⌜ψ⌝ Q Rest]
  exact pull_pure_after_two_4k P1 P2 ψ (Q ∗ Rest)

private theorem pure_elim_focus_4k {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P' Q Qp)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp := by
  rw [hf]
  exact SepWPp.pure_left h

/-! ## Second Part of `i = 0` (`entry + 848#64`) + Outer Loop to `entry + 1136#64` -/

/-- Second part of iteration `i = 0` (`entry + 848#64` to `entry + 936#64`) plus
    `lagrangeInterpolateOuter_sepWP_4k` (when `k ≥ 2`), reaching `entry + 1136#64` with
    `gf16SliceAt acc_ptr (lagrangeInterpolateTotal pts_slice).coefficients`. -/
theorem lagrangeInterpolate_copyFirstAcc_sepWP_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
    (sp0 acc_ptr ptr_l ptr_b pt_ptr v152 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (b_init : Poly) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hb_eq : b_init = lagrangePreparePure pts_slice)
    (hpts_len : pts_slice.length = k)
    (s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 848#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (k + 1))
    (hx26 : s.readReg64 .x26 = ptr_l)
    (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hcont : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1136#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x26 = ptr_l →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWP (tripleRatchetProgAtExt b ext) ret_pc sf
        (gf16SliceAt acc_ptr (lagrangeInterpolateTotal pts_slice).coefficients ∗
          memRegion ptr_l (2 * (k + 1)) ∗
          gf16SliceAt ptr_b b_init.coefficients ∗
          ptSliceAt pt_ptr pts_slice ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) post) :
    SepWP (tripleRatchetProgAtExt b ext) ret_pc s
      (memRegion acc_ptr (2 * k) ∗
        gf16SliceAt ptr_l (lagrangeCompletePure b_init pts_slice 0).coefficients ∗
        gf16SliceAt ptr_b b_init.coefficients ∗
        ptSliceAt pt_ptr pts_slice ∗
        ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
        ((sp0 - 640#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗
        tokenInitAt b ∗ reduceTableAt b ∗
        stackAt (sp0 - 672#64) allocHookStack ∗ P) post := by
  have hb_len : b_init.coefficients.length = k + 1 := by
    rw [hb_eq, lagrangePreparePure_length, hpts_len]
  have hmemcpy := hA.session_memcpy_region_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" "memcpy")
    (hk := by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have houter := @lagrangeInterpolateOuter_sepWP_4k b A ext ret_pc hb hA hcomp
    sp0 acc_ptr ptr_l ptr_b pt_ptr hsp0 k b_init pts_slice hk_pos hk_le hb_len hpts_len
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 848 92
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hmemcpy houter hpc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
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
    rw [← bv64_add1_norm k, BitVec.add_sub_cancel]
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
          tokenInitAt b ∗ reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) by
      sep_frame) ?_
  wp_conv_pre =>
    rw [memcpy_memRegion_gf16Slice_pre acc_ptr (ptr_l + 2#64) (working0.coefficients.drop 1) (2 * k)
      (by rw [List.length_drop, hw0_len]; omega)]
  wp_call hmemcpy
  wp_conv_pre =>
    rw [← gf16SliceAt_eq_pointsToBytes (working0.coefficients.drop 1) acc_ptr,
        ← gf16SliceAt_eq_pointsToBytes (working0.coefficients.drop 1) (ptr_l + 2#64), hsp]
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
          tokenInitAt b ∗ reduceTableAt b ∗
          stackAt (sp0 - 672#64) allocHookStack ∗ P) by
      sep_frame) ?_
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
    have hinterp_k1 : working0.coefficients.drop 1 = (lagrangeInterpolateTotal pts_slice).coefficients := by
      have houter0 := lagrangeInterpolateTotal_coeffs_eq pts_slice (by omega)
      rw [hpts_len, Nat.sub_self, ← hb_eq] at houter0
      simpa [lagrangeInterpolateLoopTotal, working0] using houter0.symm
    rw [hinterp_k1]
    have hmem_l := gf16SliceAt_to_memRegion ptr_l working0.coefficients
    rw [hw0_len, Nat.mul_comm] at hmem_l
    refine SepWP.weaken_pre (sepConj_mono_left hmem_l) ?_
    refine SepWP.weaken_pre (by sep_frame)
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
  · have hbeq_false : (BitVec.ofNat 64 k - 1#64 == 0#64) = false := by
      rw [hbeq_k1, decide_eq_false hk1]
    wp_steps 3
    refine SepWP.weaken_pre (by sep_frame)
      (houter (k - 1) 1 (working0.coefficients.drop 1) working0.coefficients _
        (((sp0 - 152#64) ↦₆₄ BitVec.ofNat 64 k) ∗ P)
        post
        (by omega) (by omega)
        (by rw [List.length_drop, hw0_len]; omega)
        hw0_len
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
    refine SepWP.weaken_pre (by sep_frame)
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

/-! ## Cache-Miss Substeps (`+660..+796`) under `AllocContracts4K` -/

/-- Cache-miss Step 1 (`entry + 660#64` to `entry + 732#64`, plus OOM panic `+728 → +2040..+2048`):
    checks `polys[polyIdx]` is `None`, reads `(pt_ptr, k)` from `points_vecs[polyIdx]`, and allocates
    the `2 * k`-byte `acc` buffer via `__rdl_alloc_0` and `__rust_alloc`. -/
theorem lagrangeInterpolate_miss_allocAcc_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (sp0 pts_vec_ptr pt_ptr : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx k : Nat)
    (hpoly : polyIdx < 16)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 660#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 732#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x0 ≠ 0#64 →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = BitVec.ofNat 64 (2 * k) →
      sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (A.live (sf.readReg64 .x0) (2 * k) 2 ∗
          memRegion (sf.readReg64 .x0) (2 * k) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr k ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
        ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr k ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := hA.shim_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have halloc := hA.alloc_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_alloc")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hpan_err :
      (tripleRatchetProgAtExt b ext).externAt?
        ((tripleRatchetProgAtExt b ext).fnAddr decodedMessageName +
          bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
            "alloc::raw_vec::handle_error")) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext decodedMessageName
      (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error")
      (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hmod : polyIdx % 4294967296 = polyIdx := Nat.mod_eq_of_lt (by omega)
  have hule16 : (16#64).ule (BitVec.ofNat 64 polyIdx) = false := by
    rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
    intro h
    simp only [BitVec.toNat_ofNat] at h
    omega
  have hk_ne0 : (BitVec.ofNat 64 k == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change k = 0 at h1
    omega
  have htoNat_2k : (BitVec.ofNat 64 (2 * k)).toNat = 2 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ m, 2 = 2 ^ m := ⟨1, rfl⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 660 72
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 2040 12
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc hnext ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 728#64)
  wp_simp_pre only [optPolyCacheSlotAt, noneCap, ptSliceRefAt]
  wp_steps 14
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
    wp_conv_pre => rw [alloc_post_pos_4k hptr0]
    apply SepWPp.pure_left
    intro htr_fail
    apply SepWPp.of_sepWP (mid := entry +
      bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error"))
    wp_steps 4
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 2#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * k))).writeReg64 (Reg.gpr 30#5)
          (entry + 2052#64)).setPC (entry +
            bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
              "alloc::raw_vec::handle_error")))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htr_fail, h, htr_tr]
    refine SepWPp.panic (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => ?_)
    refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
    · exact allocFailedIn_of_trace_eq' htr_panic_eq
    · rw [htr_panic_eq]
      exact List.prefix_append s0.trace [allocFailedEvent]
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hptr0
    wp_conv_pre => rw [alloc_post_neg_4k hptr0]
    apply SepWPp.pure_left
    rintro ⟨_hptr_mod, htr_ok⟩
    apply SepWPp.of_sepWP (mid := entry + 732#64)
    wp_steps 1
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_sf_1])
    rw [h_1, hsp]
    refine SepWPp.weaken_pre
      (show _ ⊢
        A.live (sf_1.readReg64 (Reg.gpr 0#5)) (2 * k) 2 ∗
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (2 * k) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr k ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F by
        simp only [optPolyCacheSlotAt, noneCap, ptSliceRefAt]
        sep_frame)
      (hnext _
        (by simp [wp_norm, arm64_norm])
        (by simp [wp_norm, arm64_norm, hrun_sf_1])
        (by simp [wp_norm, arm64_norm, hsp_sf, h_1, hsp])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        (by simpa [wp_norm, arm64_norm] using hptr0)
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))

/-- Cache-miss Step 2 (`entry + 732#64` to `entry + 760#64`):
    saves `(k, acc_ptr)` on stack, zeroes `[x29, #-56]`, and calls `lagrange_interpolate_prepare`. -/
theorem lagrangeInterpolate_miss_prepare_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts4K b A ext)
    (sp0 acc_ptr pt_ptr v168 v160 v152 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat) (pts_slice : List Pt)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (hpts_len : pts_slice.length = k)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 732#64)
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
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 760#64 →
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
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
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
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (((sp0 - 168#64) ↦₆₄ v168) ∗
        ((sp0 - 160#64) ↦₆₄ v160) ∗
        ((sp0 - 152#64) ↦₆₄ v152) ∗
        memRegion (sp0 - 144#64) 24 ∗
        ptSliceAt pt_ptr pts_slice ∗
        reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hprep := sub_ok_at_backward (lagrangePrepare_ok_4k b hb A ext hA) decodedMessageName
    (num% (2 ^ 64 - ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
    (by rw [decodedMessage_fnOff, lagrangePrepare_fnOff]; rfl)
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 732 28
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hprep hpc hnext ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry +
    bv% (2 ^ 64 - ls_rel% "<spqr::encoding::polynomial::Poly>::lagrange_interpolate_prepare"
      "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"))
  wp_steps 7
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hstat])
  let a : LagrangePrepareArgs := {
    out := sp0 - 144#64
    ptsPtr := pt_ptr
    pts := pts_slice
    hlen_bound := by omega
  }
  refine SepWPp.call (x := a) (ret_pc := entry + 760#64)
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
  · simp only [lagrangePrepareSpec, a, wp_norm, arm64_norm, hsp, hpts_len]
    exact Satisfies.mono (by sep_frame) hm
  · simp only [lagrangePrepareSpec] at hex
    exact not_satisfies_false_sepConj hex
  · simp only [lagrangePrepareSpec] at hm
    exact allowPanic_frame (fun ⟨hal, hpre⟩ => by
      simp only [allocFailedIn, wp_norm, arm64_norm, htr_tr] at hal hpre ⊢
      exact ⟨hal, hpre⟩) hm
  · conv => arg 4; simp only [lagrangePrepareSpec, a, wp_norm, arm64_norm, htr_tr, hsp]
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = k + 1 := by
      rw [lagrangePreparePure_length, hpts_len]
    rcases hcs_f with ⟨hx19_f, hx20_f, hx21_f, hx22_f, _, hx24_f, _, _, hx27_f, _, hx29_f, hvregs_f⟩
    refine pure_elim_focus_4k (sf.trace = s0.trace) (fun htr_f' => ?_) (by sep_focus)
    rw [polyOf_eq A (sp0 - 144#64) (lagrangePreparePure pts_slice)]
    rw [sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro b_cap
    rw [sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro ptr_b
    refine pure_elim_focus_4k
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
    sep_frame

/-- Cache-miss Step 3 (`entry + 760#64` to `entry + 796#64`, plus OOM panic `+796 → +1980..+1988`):
    loads `k + 1` and `ptr_b` from `b_init` header, stores `acc_ptr` at `[sp, #0x10]`, and allocates
    the `2 * (k + 1)`-byte working buffer `l` via `__rdl_alloc_0` and `__rust_alloc`. -/
theorem lagrangeInterpolate_miss_allocL_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hA : AllocContracts4K b A ext)
    (sp0 acc_ptr ptr_b pt_ptr x19_slot v656 : BitVec 64)
    (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (k : Nat)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 760#64)
    (hstat : s.status = .Running)
    (hsp : s.sp = sp0 - 672#64)
    (htr : traceVRegs s = traceVRegs s0)
    (hx19 : s.readReg64 .x19 = x19_slot)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 k)
    (hx24 : s.readReg64 .x24 = acc_ptr)
    (hx27 : s.readReg64 .x27 = pt_ptr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 796#64 →
      sf.status = .Running →
      sf.sp = sp0 - 672#64 →
      traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x0 ≠ 0#64 →
      sf.readReg64 .x19 = x19_slot →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = BitVec.ofNat 64 k →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = ptr_b →
      sf.readReg64 .x24 = BitVec.ofNat 64 (2 * (k + 1)) →
      sf.readReg64 .x25 = BitVec.ofNat 64 (k + 1) →
      sf.readReg64 .x27 = pt_ptr →
      sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (A.live (sf.readReg64 .x0) (2 * (k + 1)) 2 ∗
          memRegion (sf.readReg64 .x0) (2 * (k + 1)) ∗
          ((sp0 - 656#64) ↦₆₄ acc_ptr) ∗
          ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
          ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (((sp0 - 656#64) ↦₆₄ v656) ∗
        ((sp0 - 136#64) ↦₆₄ ptr_b) ∗
        ((sp0 - 128#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        A.pool ∗ stackAt (sp0 - 672#64) allocHookStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := hA.shim_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have halloc := hA.alloc_ok_at decodedMessageName
    (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
      "__rustc::__rust_alloc")
    (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hpan_err :
      (tripleRatchetProgAtExt b ext).externAt?
        ((tripleRatchetProgAtExt b ext).fnAddr decodedMessageName +
          bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
            "alloc::raw_vec::handle_error")) =
        some Rust.panicked :=
    panic_at_handle_error_ext b ext decodedMessageName
      (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error")
      (by rw [decodedMessage_fnOff]; simp only [arm64_norm])
  have hk1_ne0 : (BitVec.ofNat 64 (k + 1) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change k + 1 = 0 at h1
    omega
  have htoNat_2k1 : (BitVec.ofNat 64 (2 * (k + 1))).toNat = 2 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ m, 2 = 2 ^ m := ⟨1, rfl⟩
  rcases Prod.mk.inj htr with ⟨htr_tr, htr_vr⟩
  have hsp_al_s : s.spAligned = true := by
    unfold State.spAligned
    rw [hsp, sp672_aligned sp0 hsp0]
    rfl
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 760 40
  decoded_message_fetches_range_ext b (Rust.withPanics ext) 1980 12
  dsimp only [tripleRatchetProgAtExt, decodedMessageName, BitVec.ofNat_eq_ofNat] at hshim halloc hpan_err hpc hnext ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 796#64)
  wp_steps 6
  wp_call hshim
  wp_steps 3
  wp_call halloc
  apply SepWP.done hpc_sf_1 (by wp_norm_lhs)
  by_cases hptr0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · have hcbz : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true := beq_iff_eq.mpr hptr0
    wp_conv_pre => rw [alloc_post_pos_4k hptr0]
    apply SepWPp.pure_left
    intro htr_fail
    apply SepWPp.of_sepWP (mid := entry +
      bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
        "alloc::raw_vec::handle_error"))
    wp_steps 4
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have htr_panic_eq :
        (Rust.panicked ((((sf_1.writeReg64 (Reg.gpr 0#5) 2#64).writeReg64 (Reg.gpr 1#5)
          (BitVec.ofNat 64 (2 * (k + 1)))).writeReg64 (Reg.gpr 30#5)
          (entry + 1992#64)).setPC (entry +
            bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"
              "alloc::raw_vec::handle_error")))).trace = s0.trace ++ [allocFailedEvent] := by
      change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htr_fail, h, htr_tr]
    refine SepWPp.panic (by wp_norm_lhs)
      (by simpa [arm64_norm, wp_norm] using hpan_err)
      (fun hm => ?_)
    refine allowPanic_panicked (φ := allocFailedIn s0 _ ∧ s0.trace <+: _) ⟨?_, ?_⟩ hm
    · exact allocFailedIn_of_trace_eq' htr_panic_eq
    · rw [htr_panic_eq]
      exact List.prefix_append s0.trace [allocFailedEvent]
  · wp_conv_pre => rw [alloc_post_neg_4k hptr0]
    apply SepWPp.pure_left
    rintro ⟨_hptr_mod, htr_ok⟩
    rw [h_1, hsp]
    refine SepWPp.weaken_pre (by dsimp only [Reg.x0]; sep_frame)
      (hnext _
        hpc_sf_1
        (by wp_norm_lhs)
        (by simp [wp_norm, arm64_norm, hsp_sf, h_1, hsp])
        (by simp [traceVRegs, wp_norm, arm64_norm, *])
        hptr0
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *])
        (by simp [wp_norm, arm64_norm, *]))

/-! ## Full Inlined `lagrange_interpolate` (`entry + 660#64` to `entry + 1284#64`) -/

/-- Full inlined `lagrange_interpolate` block (`entry + 660#64` to `entry + 1284#64`) under
    `AllocContracts4K b A ext`: handles both cache hit (`optPoly = some p`) and cache miss
    (`optPoly = none`, interpolating `lagrangeInterpolateTotal pts_slice` and storing it in
    `polys[polyIdx]`). -/
theorem lagrangeInterpolate_inlined_wpp_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (hA : AllocContracts4K b A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr lagrangeCompleteName)
      (lagrangeCompleteSpec b))
    (sp0 pts_vec_ptr pt_ptr x24_saved : BitVec 64) (hsp0 : sp0 &&& 0xf#64 = 0#64)
    (polyIdx : Nat) (optPoly : Option Poly) (pts_slice : List Pt)
    (hpoly : polyIdx < 16) (hk_pos : 1 ≤ pts_slice.length) (hk_le : pts_slice.length ≤ 65536)
    (s0 s : State) (F R : SepProp) (Q : State → SepProp → Prop)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 660#64)
    (hstat : s.status = .Running) (hsp : s.sp = sp0 - 672#64) (htr : traceVRegs s = traceVRegs s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 polyIdx) (hx24 : s.readReg64 .x24 = x24_saved)
    (hx25 : s.readReg64 .x25 = 24#64) (hx26 : s.readReg64 .x26 = sp0 - 600#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1284#64 →
      sf.status = .Running → sf.sp = sp0 - 672#64 → traceVRegs sf = traceVRegs s0 →
      sf.readReg64 .x19 = (sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx) →
      sf.readReg64 .x20 = s.readReg64 .x20 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x24 = x24_saved → sf.readReg64 .x25 = 24#64 →
      sf.readReg64 .x26 = sp0 - 600#64 → sf.readReg64 .x29 = sp0 - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) target_pc sf
        (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx))
            (some (optPoly.getD (lagrangeInterpolateTotal pts_slice))) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
          reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
        Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) target_pc s
      (optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) optPoly ∗
        ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
        ((sp0 - 608#64) ↦₆₄ 16#64) ∗
        ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
        ptSliceAt pt_ptr pts_slice ∗ interpolateScratchAt sp0 ∗
        reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
        stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F)
      Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  cases optPoly with
  | some p =>
    simp only [Option.getD_some] at hnext
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1284#64)
    refine lagrangeInterpolate_hit_sepWP sp0 polyIdx p hpoly s _ _ hpc hstat hx0 hx25 hx26 ?_
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
          ptSliceAt pt_ptr pts_slice ∗ reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        sep_frame) ?_
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
    refine SepWPp.weaken_pre ?_
      (lagrangeInterpolate_miss_allocAcc_wpp_4k hA sp0 pts_vec_ptr pt_ptr hsp0
        polyIdx pts_slice.length hpoly hk_pos hk_le s0 s
        (((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗
          ((sp0 - 168#64) ↦₆₄ v168) ∗ ((sp0 - 160#64) ↦₆₄ v160) ∗ ((sp0 - 152#64) ↦₆₄ v152) ∗
          memRegion (sp0 - 144#64) 24 ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTableAt b ∗ tokenInitAt b ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        R Q hpc hstat hsp htr hx0 hx25 hx26 hx29 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]
      sep_frame
    intro sf1 hpc1 hrun1 hsp1 htr1 hacc_ne hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1
    refine SepWPp.weaken_pre ?_
      (lagrangeInterpolate_miss_prepare_wpp_4k hb hA sp0 (sf1.readReg64 .x0) pt_ptr v168 v160 v152
        hsp0 pts_slice.length pts_slice hk_pos hk_le rfl s0 sf1
        (A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 656#64) ↦₆₄ v656) ∗
          ((sp0 - 648#64) ↦₆₄ x24_saved) ∗ ((sp0 - 640#64) ↦₆₄ v640) ∗
          ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗ ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        R Q hpc1 hrun1 hsp1 htr1 rfl hx21_1 hx27_1 hx29_1 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]
      sep_frame
    intro b_cap ptr_b sf2 hb_cap_ge hb_cap_lt hptr_b_ne hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx27_2 hx29_2
    refine SepWPp.weaken_pre ?_
      (lagrangeInterpolate_miss_allocL_wpp_4k hA sp0 (sf1.readReg64 .x0) ptr_b pt_ptr
        ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) v656 hsp0
        pts_slice.length hk_pos hk_le s0 sf2
        (((sp0 - 168#64) ↦₆₄ BitVec.ofNat 64 pts_slice.length) ∗
          ((sp0 - 160#64) ↦₆₄ sf1.readReg64 .x0) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
          ((sp0 - 144#64) ↦₆₄ b_cap) ∗ A.live ptr_b (b_cap.toNat * 2) 2 ∗
          gf16SliceAt ptr_b (lagrangePreparePure pts_slice).coefficients ∗
          memRegion (ptr_b + BitVec.ofNat 64 ((lagrangePreparePure pts_slice).coefficients.length * 2))
            ((b_cap.toNat - (lagrangePreparePure pts_slice).coefficients.length) * 2) ∗
          ptSliceAt pt_ptr pts_slice ∗ reduceTableAt b ∗ tokenInitAt b ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗
          A.live (sf1.readReg64 .x0) (2 * pts_slice.length) 2 ∗
          memRegion (sf1.readReg64 .x0) (2 * pts_slice.length) ∗
          optPolyCacheSlotAt A ((sp0 - 600#64) + BitVec.ofNat 64 (24 * polyIdx)) none ∗
          ((sp0 - 664#64) ↦₆₄ v664) ∗ ((sp0 - 648#64) ↦₆₄ x24_saved) ∗
          ((sp0 - 640#64) ↦₆₄ v640) ∗ ((sp0 - 616#64) ↦₆₄ pts_vec_ptr) ∗
          ((sp0 - 608#64) ↦₆₄ 16#64) ∗
          ptSliceRefAt (pts_vec_ptr + BitVec.ofNat 64 (16 * polyIdx)) pt_ptr pts_slice.length ∗
          ((sp0 - 192#64) ↦₆₄ v192) ∗ ((sp0 - 184#64) ↦₆₄ v184) ∗ ((sp0 - 176#64) ↦₆₄ v176) ∗ F)
        R Q hpc2 hrun2 hsp2 htr2 (hx19_2.trans hx19_1) hx21_2 hx24_2 hx27_2 hx29_2 ?_)
    · rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]
      sep_frame
    intro sf3 hpc3 hrun3 hsp3 htr3 hptr_l_ne hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3
    apply SepWPp.of_sepWP (mid := (tripleRatchetProgAtExt b ext).fnAddr decodedMessageName + 1284#64)
    have hb_len : (lagrangePreparePure pts_slice).coefficients.length = pts_slice.length + 1 :=
      lagrangePreparePure_length pts_slice
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyAndComplete0_sepWP_4k hb hA hcomp sp0 (sf3.readReg64 .x0) ptr_b pt_ptr
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
          A.pool ∗ memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc3 hrun3 hsp3 rfl hx19_3 hx21_3 hx23_3 hx24_3 hx25_3 hx27_3 hx29_3 ?_)
    · sep_frame
    intro sf4 hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx22_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolate_copyFirstAcc_sepWP_4k hb hA hcomp sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0)
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
          A.pool ∗ memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc4 hrun4 hsp4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 ?_)
    · sep_frame
    intro sf5 hpc5 hrun5 hsp5 htr5 hx20_5 hx22_5 hx24_5 hx26_5 hx29_5
    refine SepWP.weaken_pre ?_
      (lagrangeInterpolateDealloc_sepWP_4k hA sp0 (sf1.readReg64 .x0) (sf3.readReg64 .x0) ptr_b b_cap
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
          reduceTableAt b ∗ tokenInitAt b ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc5 hrun5 hsp5 hx24_5 hx26_5 hx29_5 ?_)
    · sep_frame
    intro sf6 hpc6 hrun6 hsp6 htr6 hx20_6 hx22_6 hx29_6
    have hout_len : (lagrangeInterpolateTotal pts_slice).coefficients.length = pts_slice.length :=
      lagrangeInterpolateTotal_length pts_slice
    refine SepWP.weaken_pre ?_
      (@lagrangeInterpolateStoreSlot_sepWP b A ext _ sp0 (sf1.readReg64 .x0)
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
          ptSliceAt pt_ptr pts_slice ∗ reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
          stackAt (sp0 - 672#64) allocHookStack ∗
          memRegion ((sp0 - 672#64) - 4304#64) 208 ∗ F)
        _ hpc6 hrun6 hsp6 hx29_6 ?_)
    · sep_frame
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
            ptSliceAt pt_ptr pts_slice ∗ reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        rw [stackAt_prepare_eq_alloc (sp0 - 672#64)]; sep_frame) ?_
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
            ptSliceAt pt_ptr pts_slice ∗ reduceTableAt b ∗ tokenInitAt b ∗ A.pool ∗
            stackAt (sp0 - 672#64) lagrangePrepareStack ∗ F) by
        sep_frame) ?_
    refine SepWP.weaken_pre (fold_interpolateScratchAt sp0 _ _ _ _ _ _ _ _ _ _) ?_
    apply SepWP.done hpc7 hrun7
    refine SepWPp.weaken_pre ?_
      (hnext sf7 hpc7 hrun7 hsp7 (by rw [htr7, htr6, htr5, htr4, htr3])
        hx19_7
        (by rw [hx20_7, hx20_6, hx20_5, hx20_4, hx20_3, hx20_2, hx20_1])
        (by rw [hx22_7, hx22_6, hx22_5, hx22_4, hx22_3, hx22_2, hx22_1])
        hx24_7 hx25_7 hx26_7 hx29_7)
    sep_frame

end LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.InterpolateFullExt
