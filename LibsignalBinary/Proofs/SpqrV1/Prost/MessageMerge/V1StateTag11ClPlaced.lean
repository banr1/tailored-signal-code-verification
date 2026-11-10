/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Tag Arm 11 (`Ct2Sampled`) for `V1State::merge` (Block `298`)

Verifies tag arm 11 (`Ct2Sampled`, entry `+700`) under `[LibsignalPlacement]` to
`(blkPl_298).base + 2700#64` with `withLsCl`-wrapped cross-block drops.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlaced
end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag11ClPlaced

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop hiding cap_add_one_beq_zero_false
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTableExpanded optProtoInnerStateJumpTableAt v1StateSavedRegsAt
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero v1StateMerge_fnOff

private theorem v1Tag11_err_dealloc_w7_1884_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1884#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = w7) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1900#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A w7 w8 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw7 : (w7 == 0#64) = true <;>
    simp only [hw7, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = true := by rw [hx1]; exact hw7
    wp_steps; wp_done
  · have hbr : (s.readReg64 (Reg.gpr 1#5) == 0#64) = false := by
      rw [hx1]; exact Bool.eq_false_iff.mpr hw7
    wp_steps; wp_apply
    refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

private theorem v1Tag11_err_dealloc_w10_1900_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1900#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        vecCapPtrDealloc A w10 w11 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [rustDeallocSpec] at hDealloc
  have h304 : (fsp + 296#64) + 8#64 = fsp + 304#64 := by bv_lin
  have h312 : (fsp + 296#64) + 16#64 = fsp + 312#64 := by bv_lin
  have h320 : (fsp + 296#64) + 24#64 = fsp + 320#64 := by bv_lin
  have h328 : (fsp + 296#64) + 32#64 = fsp + 328#64 := by bv_lin
  have h336 : (fsp + 296#64) + 40#64 = fsp + 336#64 := by bv_lin
  have h344 : (fsp + 296#64) + 48#64 = fsp + 344#64 := by bv_lin
  dsimp only [words7At, vecCapPtrDealloc]
  rw [h304, h312, h320, h328, h336, h344]
  by_cases hw10 : (w10 == 0#64) = true <;>
    simp only [hw10, ↓reduceIte, Bool.false_eq_true, sepConj_emp, emp_sepConj]
  · wp_steps; wp_done
  · have hbr : (w10 == 0#64) = false := Bool.eq_false_iff.mpr hw10
    wp_steps; wp_apply
    refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done

private theorem v1Tag11_err_uc_1864_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    {s : State} {fsp w7 w8 w9 w10 w11 w12 w13 : BitVec 64} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1920#64) s
      (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 296#64) 56 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  have hfold56 : words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ⊢ memRegion (fsp + 296#64) 56 := by
    rw [memRegion_56_eq_words7 (fsp + 296#64)]
    refine Entails.trans ?_ (Entails.sepExists_intro w13); refine Entails.trans ?_ (Entails.sepExists_intro w12)
    refine Entails.trans ?_ (Entails.sepExists_intro w11); refine Entails.trans ?_ (Entails.sepExists_intro w10)
    refine Entails.trans ?_ (Entails.sepExists_intro w9); refine Entails.trans ?_ (Entails.sepExists_intro w8)
    refine Entails.trans ?_ (Entails.sepExists_intro w7); exact Entails.refl _
  by_cases h2 : (w7 + 2#64 == 0#64) = true
  · simp only [h2, Bool.true_or, ↓reduceIte, emp_sepConj]
    dsimp only [words7At] at hfold56 ⊢
    wp_steps; apply SepWP.fold hfold56 (by sep_focus); wp_done
  · have h2f : (w7 + 2#64 == 0#64) = false := Bool.eq_false_iff.mpr h2
    by_cases h1 : (w7 + 1#64 == 0#64) = true
    · simp only [h2f, h1, Bool.or_true, ↓reduceIte, emp_sepConj]
      dsimp only [words7At] at hfold56 ⊢
      wp_steps; apply SepWP.fold hfold56 (by sep_focus); wp_done
    · have h1f : (w7 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr h1
      simp only [h2f, h1f, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      have hstep1 : SepWP ((blkPC_298).rebase (blkPl_298).base H)
          ((blkPl_298).base + 1884#64) s
          (words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
            (vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun s1 P1 =>
            (P1 ⊢ words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
              vecCapPtrDealloc A w7 w8 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              (vecCapPtrDealloc A w10 w11 ∗ Frame)) ∧
            s1.sp = s.sp ∧ s1.v1TraceEq s ∧
            s1.readReg64 (Reg.gpr 1#5) = w7 ∧
            s1.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
        dsimp only [words7At]
        wp_steps; wp_done
      refine SepWP.seq hstep1 ?_
      rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx1_1, hx21_1⟩
      refine SepWP.weaken_pre hP1 ?_
      refine SepWP.seq (v1Tag11_err_dealloc_w7_1884_placed hDealloc hsp_align hpc1 hrun1 (hsp1.trans hsp) hx1_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
      refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ (vecCapPtrDealloc A w10 w11 ∗ Frame) =
        words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗ vecCapPtrDealloc A w10 w11 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame))) ?_
      refine SepWP.mono (v1Tag11_err_dealloc_w10_1900_placed hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))) ?_
      rintro s3 P3 _ _ ⟨hP3, hsp3, htr3, hx21_3⟩
      exact ⟨Entails.trans hP3 (sepConj_mono_left hfold56),
        hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1),
        hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1Tag11_err_enc_1920_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1920#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialEncoderAt A (fsp + 240#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 56 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoPolyEncoderSpec] at hDropEnc
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 48 ⊢ memRegion (fsp + 240#64) 56 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 240#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none', show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A (fsp + 240#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps_lscl (lsmpl.base 271)
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A (fsp + 240#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    wp_apply; dsimp only [protoPolynomialEncoderSize]; wp_steps; wp_done

private theorem v1Tag11_setup_1800_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp72 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1800#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt2SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧
        s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧
        s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1820#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        s1.readReg64 (Reg.gpr 27#5) = 0xfffffffffffffffe#64 ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      chunkedCt2SampledPBCapAt A (fsp + 16#64) restLen default := by
    change ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 48 ∗
        ((fsp + 72#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (fsp + 80#64) 48 ⊢
      (((fsp + 16#64) ↦₆₄ noneCap) ∗ memRegion ((fsp + 16#64) + 8#64) 48) ∗
      (((fsp + 16#64) + 0x38#64) ↦₆₄ noneCap2 ∗ memRegion (((fsp + 16#64) + 0x38#64) + 8#64) 48)
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h72 : (fsp + 16#64) + 0x38#64 = fsp + 72#64 := by bv_lin
    have h80 : (fsp + 72#64) + 8#64 = fsp + 80#64 := by bv_lin
    rw [h24, h72, h80]; exact Entails.of_eq (by unfold noneCap noneCap2; ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag11_copy_ok_1820_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3040#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag11_words14At_entails_memRegion_112 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  conv =>
    arg 4
    rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag11_words14At, words7At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag11_copy_err_1820_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp352 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1820#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1864#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          ((fsp + 352#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5)) := by
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag11_pre_drop_3040_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3040#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 3076#64) s
      (v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 112 ∗
          v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag11_words14At_entails_memRegion_112 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  rw [v1Tag11_memRegion_112_eq_words14 (fsp + 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag11_post_drop_3076_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s : State} {fsp mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 3076#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 480#64) 112 ∗
          (mPtr ↦₆₄ 0x800000000000000a#64) ∗
          v1Tag11_words14At (mPtr + 8#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          memRegion (mPtr + 120#64) 104 ∗
          A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag11_words14At_entails_memRegion_112 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps_lscl (lsmpl.base 267); wp_apply
  dsimp only [optProtoInnerStateSize]
  rw [v1Tag11_memRegion_224_split_ok mPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro vd
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11
  apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  dsimp only [v1Tag11_words14At, words7At] at hfold480 ⊢
  wp_steps
  apply SepWP.fold hfold480 (by sep_focus)
  wp_done

theorem v1Tag11_inplace_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {c2 : V1State.Chunked.Ct2Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 700#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 11 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_eq : s.readReg64 (Reg.gpr 9#5) = 0x800000000000000a#64 := by
    rw [hm_is] at hx9; exact hx9
  have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := by
    rw [hx9_eq]; decide
  have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x800000000000000a#64) = false := by
    rw [hx9_eq]; decide
  have hpe_bound : OptPolyEncoderBound c2.sendingCt2 rest.length := by
    simpa only [hm_is, OptInnerStatePolyBound, InnerStatePolyBound] using hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 301) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr + 8#64, c2, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 740#64) hC2Call
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt2SampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, hpe_bound⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr + 8#64 = x.msgPtr + 8#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound c2.sendingCt2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt2SampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag11 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hc2_res : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) c2 rest 99).toOption with
  | none =>
    rw [hc2_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro c2'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : (x.msgPtr ↦₆₄ 0x800000000000000a#64) ∗
        chunkedCt2SampledPBAt A (x.msgPtr + 8#64) c2' ∗ memRegion (x.msgPtr + 120#64) 104 ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt2SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct2Sampled c2'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨c2', rest'⟩
    rw [hc2_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hc2_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct2Sampled c2')) :=
      innerStatePolyBound_of_ct2Sampled hpe_bound hc2_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct2Sampled c2') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ct2Sampled c2') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

theorem v1Tag11_at_1800_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1800#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 11 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 301) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_le hrest_suf,
      v1Tag11_memRegion_split_temp fsp, v1Tag11_memRegion_112_split_init fsp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp352
  apply SepWP.exists_elim; intro w_sp72
  apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 48 ∗
      ((fsp + 72#64) ↦₆₄ w_sp72) ∗ memRegion (fsp + 80#64) 48 ∗
      (optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗
        A.pool ∗ stackAt fsp chunkedInlStack ∗
        memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
        memRegion (fsp + 592#64) 128 ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [fsp, restPtr]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag11_setup_1800_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23 hx27) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr_1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  apply SepWP.weaken_pre hP1
  refine SepWP.done hpc1 hrun1 (fun hinv1 => ?_)
  rw [hsp] at hsp1
  rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest.length :=
    optPolyEncoderBound_none h56
  refine SepWPp.call_frame_lscro (hinv := hinv1)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1820#64) hC2Call
    hpc1 hrun1
    (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr_1
    (by dsimp only [chunkedCt2SampledMergeSpec]; rw [hx0_1, hx0, hx1_1, hx2_1, hsp1])
    (⟨rfl, rfl, rfl, hpe0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        fsp + 16#64 = fsp + 16#64 ∧
        x.bufRef = x.bufRef ∧
        OptPolyEncoderBound (default : V1State.Chunked.Ct2Sampled).sendingCt2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt2SampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 11) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct2Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag11]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct2Sampled c2 => exact absurd h (hm_not c2)
      | _ => rfl
  cases hc2_res : (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hc2_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro c2'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hc2_words : chunkedCt2SampledPBAt A (fsp + 16#64) c2' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64,
          v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          v1Tag11_capHeap A 0 c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 :=
      Entails.trans (v1Tag11_pb_entails_cap_zero A (fsp + 16#64) c2')
        (v1Tag11_extract_words A (fsp + 16#64) 0 c2')
    apply SepWP.fold hc2_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    let Frame_err : SepProp :=
      v1Tag11_capHeap A 0 c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag11_copy_err_1820_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx21_2⟩
    apply SepWP.weaken_pre hP2
    dsimp only [Frame_err]
    apply SepWP.fold (v1Tag11_words_entails_err_dealloc A (fsp + 240#64) c2'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
    rw [v1StateBelow_allocHook fsp]
    have h296 : (fsp + 240#64) + 56#64 = fsp + 296#64 := by bv_lin
    rw [h296]
    let Frame_uc : SepProp :=
      optProtoPolynomialEncoderAt A (fsp + 240#64) (c2'.sendingCt2.map pbToProtoPolyEncoder) ∗
      v1StateBelowRest fsp allocHookStack ∗
      memRegion (fsp + 16#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      words7At (fsp + 296#64) w7 w8 w9 w10 w11 w12 w13 ∗
        (if (w7 + 2#64 == 0#64) || (w7 + 1#64 == 0#64) then emp
         else vecCapPtrDealloc A w7 w8 ∗ vecCapPtrDealloc A w10 w11) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame_uc)
      (Entails.of_eq (by dsimp only [Frame_uc]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1Tag11_err_uc_1864_placed hDealloc hfsp_align hpc2 hrun2 (hsp2.trans hspm)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_uc]
    apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
    rw [v1StateBelow_dropStack48 fsp]
    let Frame_enc : SepProp :=
      v1StateBelowRest fsp dropStack48 ∗
      memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 296#64) 56 ∗
      ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 480#64) 112 ∗
      memRegion (fsp + 592#64) 128 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗
      (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      optProtoPolynomialEncoderAt A (fsp + 240#64) (c2'.sendingCt2.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame_enc)
      (Entails.of_eq (by dsimp only [Frame_enc]; ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_err_enc_1920_cl_placed hDropEnc hfsp_align hpc3 hrun3 (hsp3.trans (hsp2.trans hspm)) hcl3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx21_4⟩
    apply SepWP.weaken_pre hP4
    dsimp only [Frame_enc]
    have hjoin240 : memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 56 ⊢ memRegion (fsp + 240#64) 112 := by
      let k56 := 56
      have s1 := memRegion_split' (b := fsp + 240#64) (b' := fsp + 296#64) (n := 56) (k := k56) (N := 112) rfl (by bv_lin) (by decide)
      rw [s1]; exact Entails.refl _
    apply SepWP.fold hjoin240 (by sep_focus)
    apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field s4 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc4 hrun4
      (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2)) hsm0 hn_err hinv4
  | some p =>
    rcases p with ⟨c2', rest'⟩
    rw [hc2_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hc2_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct2Sampled c2')) :=
      innerStatePolyBound_of_ct2Sampled hpe0 hc2_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt2SampledMergeSpec, hc2_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag11_extract_words A (fsp + 16#64) rest'.length c2') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
    apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9
    apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13
    rw [v1StateBelow_dropStack96 fsp]
    rw [← hfsp720] at hfp_m
    dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag11_capHeap A rest'.length c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗
      optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
      v1StateBelowRest fsp dropStack96 ∗
      memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
      memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
      v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ w_sp352) ∗
        (memRegion (fsp + 480#64) 112 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag11_copy_ok_1820_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
        (memRegion (fsp + 480#64) 112 ∗ Frame_ok) =
      v1Tag11_words14At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        memRegion (fsp + 480#64) 112 ∗
        (memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1Tag11_pre_drop_3040_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3
    dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
        stackAt fsp dropStack96 ∗
        v1Tag11_words14At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
        (memRegion (fsp + 16#64) 112 ∗ memRegion (fsp + 240#64) 112 ∗ ((fsp + 352#64) ↦₆₄ x.msgPtr) ∗
          v1Tag11_capHeap A rest'.length c2' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 128#64) 112 ∗
          memRegion (fsp + 360#64) 120 ∗ memRegion (fsp + 592#64) 128 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗
          v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag11_post_drop_3076_cl_placed hDropInner hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3 hcl3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag11_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag11_reconstruct_innerState A x.msgPtr rest'.length c2'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct2Sampled c2') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct2Sampled c2') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)),
       hx20_4,
       hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_m)),
       hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_m)),
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)),
       hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)),
       hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)),
       hx29_4.trans hfsp720⟩
      hinv4

private theorem v1Tag11_branch_1800_cl_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 700#64)
    (hcont : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1800#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1800#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ c2, is ≠ .ct2Sampled c2 := fun c2 h => hm_not c2 (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : (s.readReg64 (Reg.gpr 9#5) != 0x800000000000000a#64) = true :=
      v1Tag11_discrFull_other hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag11_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hC2Call : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 301)
      (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271)
      (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267)
      (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 700#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 11 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ c2, m.innerState = some (.ct2Sampled c2)
  · rcases hex with ⟨c2, hm_is⟩
    exact v1Tag11_inplace_cl_placed hC2Call hm_is hentry hpc hcont
  · have hm_not : ∀ c2, m.innerState ≠ some (.ct2Sampled c2) := fun c2 h => hex ⟨c2, h⟩
    refine v1Tag11_branch_1800_cl_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag11_at_1800_cl_placed hC2Call hDropEnc hDealloc hDropInner hm_not hentry' hpc' hcont

end CryptoVerification.SpqrV1.Prost.MessageMerge
