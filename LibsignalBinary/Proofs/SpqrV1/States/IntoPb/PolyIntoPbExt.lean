/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPt
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefs
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProof
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Proof
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<PolyEncoder>::into_pb` & `<PolyDecoder>::into_pb`: 4-KiB Allocator Contracts

Lifts `encoder_into_pb_ok_ext`, `encoder_into_pb_ok_x`, `decoder_into_pb_ok_ext`, and
`decoder_into_pb_ok_x` from `AllocContracts` to `SpqrV1.Alloc.AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Poly.EncoderIntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
  (vecGF16Of vecGF16ListOf pointListOf_eq_vecGF16ListOf polyListOf_eq_vecGF16ListOf
   dropGluePoly16Stack DropGluePoly16Ghost dropGluePoly16Spec
   dropProgAtExt dropPoly16Name dropPoly16_fnOff)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem drop_glue_poly16_ok_at_intoPb_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + (0#64 - 92576#64))
      (dropGluePoly16Spec A) := by
  have h := Drop.drop_glue_poly16_ok_ext hA.dealloc
  unfold dropProgAtExt at h
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr encoderIntoPbName + (0#64 - 92576#64) =
      (tripleRatchetProgAtExt b ext).fnAddr dropPoly16Name := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, encoderIntoPb_fnOff, dropPoly16_fnOff]
    bv_omega
  rw [haddr]
  exact h

/-- `<spqr::encoding::polynomial::PolyEncoder>::into_pb` (176 instructions)
    satisfies `encoderIntoPbSpec A` on `tripleRatchetProgAtExt b ext` under `AllocContracts4K`. -/
theorem encoder_into_pb_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    EncoderIntoPbOkExt b A ext := by
  unfold EncoderIntoPbOkExt
  have hshim_raw := hA.shim_ok_at encoderIntoPbName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::into_pb"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc_raw := hA.alloc_ok_at encoderIntoPbName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder>::into_pb"
      "__rustc::__rust_alloc"))
  have hdrop := drop_glue_poly16_ok_at_intoPb_4k hA
  apply subroutine_ok_of_sepWPp
  intro ⟨out, encA, ⟨idx, encState⟩⟩ R s0 hpc hrun hpre hsp0
  simp only [encoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialEncoderSize ∗
      polyEncoderAt A encA { idx := idx, s := encState } ∗
      A.pool ∗ stackAt s0.sp encoderIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  dsimp only [encoderIntoPbSpec, polyEncoderAt, polyEncoderIdxOff, polyEncoderPadOff,
    polyEncoderPadSize, protoPolynomialEncoderSize, polyEncoderSize, BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 224#64
  have hfsp : HiddenEq fsp (s0.sp - 224#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 224#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_encoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  refine SepWPp.weaken_pre (P' :=
      memRegion out 56 ∗ cells fsp 28 ∗
      encoderStateAt A encA encState ∗ ((encA + 392#64) ↦₃₂ idx) ∗ memRegion (encA + 396#64) 4 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack)
    (Entails.of_eq (by ac_rfl)) ?_
  conv => arg 4; simp only [memRegion_56_split out, cells28_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
    SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
    SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 => SepWPp.exists_elim fun v4 =>
    SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
    SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => SepWPp.exists_elim fun v10 =>
    SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 => SepWPp.exists_elim fun v13 =>
    SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 => SepWPp.exists_elim fun v19 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v22 =>
    SepWPp.exists_elim fun v23 => SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v25 =>
    SepWPp.exists_elim fun v26 => SepWPp.exists_elim fun v27 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue hshim_raw halloc_raw s0 fsp out encA hfsp hfsp_align idx
      v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
      (encoderStateAt A encA encState ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗
        ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗ ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ v12) ∗ ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        memRegion (fsp - 4128#64) 32)
      ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_points ptr_polys hptr_pts hptr_polys hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx0_1 hx22_1 htr1 hvregs1
  let s_ref := withSaved19_20 s0 encA out
  cases encState with
  | points points =>
    dsimp only [encoderStateAt, polyEncoderPointsTag, polyEncoderVecsOff, BitVec.ofNat_eq_ofNat]
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
    rw [pointListOf_eq_vecGF16ListOf]
    have hrem_len : (points.map Point.value).length = 16 := by
      simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
    have hrem_ne : points.map Point.value ≠ [] := by
      intro h; simp [h] at hrem_len
    have hdisp := into_pb_dispatch_points (b := b) (ext := ext)
      s0 fsp out encA ptr_points ptr_polys hfsp_align idx v0 v1 v2 v3 v4 v5 v6 s1
      (((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
        ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        vecGF16ListOf A (encA + 8#64) (points.map Point.value) ∗
        memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx0_1 hx22_1 htr1 hvregs1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hdisp ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, htr2, hvregs2⟩
    generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
    have hloop := points_outer_loop (R := R) (Q := Q_goal) hshim_raw halloc_raw s_ref fsp ptr_points hfsp_align
      (points.map Point.value) hrem_ne 0 (by omega) v7 v8 v9 s2
      (((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
        ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
        ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        memRegion encA 8 ∗ memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
        memRegion (fsp - 4128#64) 32)
      hpc2 hrun2 hsp2 hx29_2
      (by simpa [s_ref] using hx19_2)
      (by simpa [s_ref] using hx20_2)
      (by simpa [s_ref] using hx22_2)
      hx23_2 hx24_2 hx25_2
      (by simpa [s_ref] using htr2)
      (by simpa [s_ref] using hvregs2)
    dsimp only [s_ref] at hloop
    simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20,
      withSaved19_20_trace, withSaved19_20_vregs, withSaved19_20_onPanic, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, hrem_len] at hloop
    change _ → SepWPp _ _ _ _ _ _ at hloop
    refine SepWPp.weaken_pre (by dsimp only [vecGF16ListOf]; exact Entails.of_eq (by ac_rfl)) (hloop ?_)
    intro s3 w56 w64 w72 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
    have hep := into_pb_epilogue hdrop s0 fsp out encA hfsp idx (v6.extractLsb' 32 32)
      hfsp_align (points.map Point.value) (by simp [hpts_len])
      16#64 ptr_points 16#64 16#64 ptr_polys 0#64 w56 w64 w72 v10 v11 v12 v13 v14 v15
      d0 d1 d2 d3 d4 d5 d6 s3
      (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
          ((points.map Point.value).map serializeGF16List) ∗
        A.live ptr_points 384 8 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384)
      hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
    have hpre3 :
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 (encA + 8#64) (points.map Point.value) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
            ((points.map Point.value).map serializeGF16List) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
            ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
            ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
            ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
            (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
            ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
            ((out + 48#64) ↦₆₄ d6) ∗
            memRegion encA 8 ∗ memRegion (encA + 392#64) 8 ∗
            A.live ptr_points 384 8 ∗
            A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
            memRegion (fsp - 4128#64) 32)) ⊢
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗ ((fsp + 72#64) ↦₆₄ w72) ∗
          ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
          ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
          ((out + 48#64) ↦₆₄ d6) ∗
          memRegion encA 8 ∗
          vecGF16ListOf A (encA + 8#64) (points.map Point.value) ∗
          memRegion (encA + 392#64) 8 ∗
          A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
          (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_points
              ((points.map Point.value).map serializeGF16List) ∗
            A.live ptr_points 384 8 ∗
            A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384)) := by
      rw [stackAt_dropGluePoly16_split_bottom fsp]
      dsimp only [vecGF16ListOf]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpre3 (SepWPp.seq_clean hep ?_)
    intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
    have hpost_pts := protoPolynomialEncoderAt_points_entails A out ptr_points ptr_polys idx points
      hpts_len hptr_pts hptr_polys
    subst hQ_goal
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
      hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩⟩
    exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (sepConj_mono_left (Q := memRegion encA 400 ∗ A.pool ∗ stackAt s0.sp encoderIntoPbStack) hpost_pts)
        (Entails.of_eq (by ac_rfl))))
  | polys polys =>
    dsimp only [encoderStateAt, polyEncoderPolysTag, polyEncoderVecsOff, BitVec.ofNat_eq_ofNat]
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_elim_pure fun hpolys_len => ?_
    rw [polyListOf_eq_vecGF16ListOf]
    have hrem_len : (polys.map LibsignalSpqrV1.Poly.coefficients).length = 16 := by simp [hpolys_len, NUM_POLYS, CHUNK_SIZE]
    have hrem_ne : polys.map LibsignalSpqrV1.Poly.coefficients ≠ [] := by intro h; simp [h] at hrem_len
    have hdisp := into_pb_dispatch_polys (b := b) (ext := ext)
      s0 fsp out encA ptr_points ptr_polys hfsp_align idx v0 v1 v2 v3 v4 v5 v6 s1
      (((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 80#64) ↦₆₄ v10) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗ ((fsp + 96#64) ↦₆₄ v12) ∗
        ((fsp + 104#64) ↦₆₄ v13) ∗ ((fsp + 112#64) ↦₆₄ v14) ∗ ((fsp + 120#64) ↦₆₄ v15) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        vecGF16ListOf A (encA + 8#64) (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
        memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        A.live ptr_polys 384 8 ∗ memRegion ptr_polys 384 ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ memRegion (fsp - 4128#64) 32)
      hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx0_1 hx22_1 htr1 hvregs1
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.seq_clean hdisp ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx20_2, hx22_2, hx23_2, hx28_2, hx24_2, hx25_2, hx26_2, htr2, hvregs2⟩
    generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
    have hloop := polys_outer_loop (R := R) (Q := Q_goal) hshim_raw halloc_raw s_ref fsp ptr_polys hfsp_align
      (polys.map LibsignalSpqrV1.Poly.coefficients) hrem_ne 0 (by omega) v10 v11 v12 v13 v14 v15 s2
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
        ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
        ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
        ((out + 48#64) ↦₆₄ d6) ∗
        memRegion encA 8 ∗ memRegion (encA + 392#64) 8 ∗
        A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        A.live ptr_polys 384 8 ∗
        memRegion (fsp - 4128#64) 32)
      hpc2 hrun2 hsp2 hx29_2
      (by simpa [s_ref] using hx19_2)
      (by simpa [s_ref] using hx20_2)
      (by simpa [s_ref] using hx22_2)
      hx23_2 hx28_2 hx24_2 hx25_2 hx26_2
      (by simpa [s_ref] using htr2)
      (by simpa [s_ref] using hvregs2)
    dsimp only [s_ref] at hloop
    simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20,
      withSaved19_20_trace, withSaved19_20_vregs, withSaved19_20_onPanic, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, hrem_len] at hloop
    change _ → SepWPp _ _ _ _ _ _ at hloop
    refine SepWPp.weaken_pre (by dsimp only [vecGF16ListOf]; exact Entails.of_eq (by ac_rfl)) (hloop ?_)
    intro s3 w80 w88 w96 w104 w112 w120 hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
    have hep := into_pb_epilogue hdrop s0 fsp out encA hfsp idx (v6.extractLsb' 32 32)
      hfsp_align (polys.map LibsignalSpqrV1.Poly.coefficients) (by simp [hpolys_len])
      16#64 ptr_points 0#64 16#64 ptr_polys 16#64 v7 v8 v9 w80 w88 w96 w104 w112 w120
      d0 d1 d2 d3 d4 d5 d6 s3
      (A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
          ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
        A.live ptr_polys 384 8)
      hpc3 hrun3 hsp3 hx29_3 hx19_3 hx20_3 htr3 hvregs3
    have hpre3 :
        (((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 16#64) ∗
          ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 88#64) ↦₆₄ w88) ∗ ((fsp + 96#64) ↦₆₄ w96) ∗
          ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
          arrayAt (fun cs addr => vecGF16Of A addr cs) 24 (encA + 8#64)
            (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
            ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
            ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
            ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
            ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
            (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
            ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
            ((out + 48#64) ↦₆₄ d6) ∗
            memRegion encA 8 ∗ memRegion (encA + 392#64) 8 ∗
            A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
            A.live ptr_polys 384 8 ∗
            memRegion (fsp - 4128#64) 32)) ⊢
        ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 16#64) ∗
          ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
          ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗ ((fsp + 72#64) ↦₆₄ v9) ∗
          ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 88#64) ↦₆₄ w88) ∗ ((fsp + 96#64) ↦₆₄ w96) ∗
          ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x28) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((fsp + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
          ((out + 48#64) ↦₆₄ d6) ∗
          memRegion encA 8 ∗
          vecGF16ListOf A (encA + 8#64) (polys.map LibsignalSpqrV1.Poly.coefficients) ∗
          memRegion (encA + 392#64) 8 ∗
          A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
          (A.live ptr_points 384 8 ∗ memRegion ptr_points 384 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_polys
              ((polys.map LibsignalSpqrV1.Poly.coefficients).map serializeGF16List) ∗
            A.live ptr_polys 384 8)) := by
      rw [stackAt_dropGluePoly16_split_bottom fsp]
      dsimp only [vecGF16ListOf]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpre3 (SepWPp.seq_clean hep ?_)
    intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
    have hpost_polys := protoPolynomialEncoderAt_polys_entails A out ptr_points ptr_polys idx polys
      hpolys_len hptr_pts hptr_polys
    subst hQ_goal
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
      hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩⟩
    exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans (sepConj_mono_left (Q := memRegion encA 400 ∗ A.pool ∗ stackAt s0.sp encoderIntoPbStack) hpost_polys)
        (Entails.of_eq (by ac_rfl))))

/-- `<spqr::encoding::polynomial::PolyEncoder>::into_pb` (176 instructions)
    satisfies `(encoderIntoPbSpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`
    under `AllocContracts4K`. -/
theorem encoder_into_pb_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    EncoderIntoPbOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (encoderIntoPbSpecX_of_encoderIntoPbSpec (encoder_into_pb_ok_ext_4k hA))

end CryptoVerification.SpqrV1.Poly.EncoderIntoPb

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
  (vecPtOf vecPtListOf sortedSetPtOf_eq_vecPtOf sortedSetPtListOf_eq_vecPtListOf
   dropGluePoly16Stack DropGlueSortedSetPt16Ghost dropGlueSortedSetPt16Spec
   dropProgAtExt dropSortedSetPt16Name dropSortedSetPt16_fnOff)
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem drop_glue_sorted_set_pt16_ok_at_intoPb_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + (0#64 - 95000#64))
      (dropGlueSortedSetPt16Spec A) := by
  have h := Drop.drop_glue_sorted_set_pt16_ok_ext hA.dealloc
  unfold dropProgAtExt at h
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + (0#64 - 95000#64) =
      (tripleRatchetProgAtExt b ext).fnAddr dropSortedSetPt16Name := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      decoderIntoPb_fnOff, dropSortedSetPt16_fnOff]
    bv_omega
  rw [haddr]
  exact h

/-- `<spqr::encoding::polynomial::PolyDecoder>::into_pb` (102 instructions)
    satisfies `decoderIntoPbSpec A` on `tripleRatchetProgAtExt b ext` under `AllocContracts4K`. -/
theorem decoder_into_pb_ok_ext_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    DecoderIntoPbOkExt b A ext := by
  unfold DecoderIntoPbOkExt
  have hshim_raw := hA.shim_ok_at decoderIntoPbName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc_raw := hA.alloc_ok_at decoderIntoPbName
    (num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb"
      "__rustc::__rust_alloc"))
  have hdrop := drop_glue_sorted_set_pt16_ok_at_intoPb_4k hA
  apply subroutine_ok_of_sepWPp
  intro ⟨out, decA, dec⟩ R s0 hpc hrun hpre hsp0
  simp only [decoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialDecoderSize ∗
      polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  dsimp only [decoderIntoPbSpec, polyDecoderAt, polyDecoderPtsNeededOff, polyDecoderIsCompleteOff,
    polyDecoderPadOff, polyDecoderPadSize, protoPolynomialDecoderSize, polyDecoderSize,
    BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 160#64
  have hfsp : HiddenEq fsp (s0.sp - 160#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_decoderIntoPb_split s0.sp, ← hfsp.eq, stackAt_dropGluePoly16_split_bottom fsp]
  conv => arg 4; simp only [sepConj_assoc]
  refine SepWPp.weaken_pre (P' :=
      ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
      memRegion out 40 ∗ cells fsp 20 ∗
      sortedSetPtListOf A decA dec.pts ∗
      ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ boolByte dec.isComplete) ∗
      memRegion (decA + 393#64) 7 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack)
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; simp only [memRegion_40_split out, cells20_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun v0 =>
    SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 =>
    SepWPp.exists_elim fun v7 => SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue_and_init hshim_raw halloc_raw s0 fsp out decA hfsp hfsp_align
      dec.ptsNeeded dec.isComplete
      v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      (vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 88#64) ↦₆₄ v11) ∗
        memRegion (fsp - 4128#64) 32)
      ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_pts hptr_pts hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
  let s_ref := withSaved19_20 s0 decA out
  have hrem_len : (dec.pts.map SortedSetPt.vec).length = 16 := by
    simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
  have hrem_ne : dec.pts.map SortedSetPt.vec ≠ [] := by
    intro h; simp [h] at hrem_len
  generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
  have hloop := pts_outer_loop (R := R) (Q := Q_goal) hshim_raw halloc_raw s_ref fsp ptr_pts hfsp_align
    (dec.pts.map SortedSetPt.vec) hrem_ne 0 (by omega) v5 v6 v7 s1
    (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
      ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
      (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
      ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
      memRegion (decA + 384#64) 16 ∗
      A.live ptr_pts 384 8 ∗
      memRegion (fsp - 4128#64) 32)
    hpc1 hrun1 hsp1 hx29_1
    (by simpa [s_ref] using hx19_1)
    (by simpa [s_ref] using hx20_1)
    hx22_1 hx23_1 hx24_1
    (by simpa [s_ref] using hx28_1)
    (by simpa [s_ref] using htr1)
    (by simpa [s_ref] using hvregs1)
  dsimp only [s_ref] at hloop
  simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20, withSaved19_20_x28,
    withSaved19_20_trace, withSaved19_20_vregs, withSaved19_20_onPanic, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, hrem_len] at hloop
  change _ → SepWPp _ _ _ _ _ _ at hloop
  refine SepWPp.weaken_pre (by dsimp only [vecPtListOf]; exact Entails.of_eq (by ac_rfl)) (hloop ?_)
  intro s2 w40 w48 w56 hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2
  have hep := into_pb_epilogue hdrop s0 fsp out decA hfsp
    (BitVec.ofNat 32 dec.ptsNeeded) 16#32 v4 (boolByte dec.isComplete)
    hfsp_align (dec.pts.map SortedSetPt.vec) (by simp [hpts_len])
    16#64 ptr_pts 16#64 w40 w48 w56 v11
    d0 d1 d2 d3 d4 s2
    (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
      A.live ptr_pts 384 8)
    hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2
  have hpre2 :
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
          memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗
          memRegion (fsp - 4128#64) 32)) ⊢
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗
        memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
          A.live ptr_pts 384 8)) := by
    rw [stackAt_dropGluePoly16_split_bottom fsp]
    dsimp only [vecPtListOf]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 (SepWPp.seq_clean hep ?_)
  intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
  have hpost_dec := protoPolynomialDecoderAt_entails A out ptr_pts dec hpts_len hptr_pts
  subst hQ_goal
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
    hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f.trans hx28_2, hx29f, hvregsf⟩⟩
  exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack) hpost_dec)
      (Entails.of_eq (by ac_rfl))))

/-- `<spqr::encoding::polynomial::PolyDecoder>::into_pb` (102 instructions)
    satisfies `(decoderIntoPbSpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`
    under `AllocContracts4K`. -/
theorem decoder_into_pb_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    DecoderIntoPbOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img
    (decoderIntoPbSpecX_of_decoderIntoPbSpec (decoder_into_pb_ok_ext_4k hA))

end CryptoVerification.SpqrV1.Poly.DecoderPb
