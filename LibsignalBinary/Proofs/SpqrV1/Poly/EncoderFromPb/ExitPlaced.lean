/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Exit
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Relocatable Epilogue and Exit Blocks

Relocatable `[LibsignalPlacement]` proofs of the shared epilogue (`+1460`), error exits (`+1448`,
`+1496`, `+1612`), and success header copy (`+1572 → s0.lr`) on Block `374`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L1
open CryptoVerification.SpqrV1.Layout.L22

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  bv384_toNat bv8_toNat
  sp_sub_1024_add_928 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_add_96
  sp_sub_88_add_8 sp_sub_80_add_8 sp_sub_72_add_8 sp_sub_64_add_8 sp_sub_56_add_8
  sp_sub_48_add_8 sp_sub_40_add_8 sp_sub_32_add_8 sp_sub_24_add_8 sp_sub_16_add_8

theorem from_pb_epilogue_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (pbA : BitVec 64) (pb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        A.pool ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack ∗ Frame) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  simp only [dropProtoPolyEncoderSpec, BitVec.ofNat_eq_ofNat] at hdrop_pb
  dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpc hdrop_pb ⊢
  unfold savedCells
  wp_steps
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        (protoPolynomialEncoderAt A pbA pb ∗ A.pool ∗ Frame) by unfold savedCells; ac_rfl))
      (savedCells_restore_stack s0 (protoPolynomialEncoderAt A pbA pb ∗ A.pool ∗ Frame))) ?_
  rw [stackAt_encoderFromPb_split_dropStack48 s0.sp]
  wp_call hdrop_pb (⟨pbA, pb⟩ : DropProtoPolyEncoderGhost)
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

theorem from_pb_err_header_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (out pbA : BitVec 64) (pb : ProtoPolynomialEncoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1448#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_clean
    (mid := (blkPl_374).base + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = s0.sp - 1024#64 ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    refine align_pre (by
      dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        polynomialErrorByte, resultPolyEncoderErrTailSize]
      exact Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hep := from_pb_epilogue_placed hdrop_pb s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

theorem from_pb_err_polys_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec A))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (pb : ProtoPolynomialEncoder)
    (errPolys : List (List GF16)) (herr_len : errPolys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = 2#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        vecGF16ListOf A (fsp + 480#64) errPolys ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hdrop16' := hdrop16
  simp only [dropGluePoly16Spec, BitVec.ofNat_eq_ofNat] at hdrop16'
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_clean
    (mid := (blkPl_374).base + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · dsimp only [polyArrayBytes, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat] at hpc hdrop16' ⊢
    wp_steps
    wp_call hdrop16' (⟨fsp + 480#64, errPolys⟩ : DropGluePoly16Ghost)
    wp_steps
    refine align_pre ?_ ?_
    · rw [hsp]
      have hfsp := hfsp_fn trivial
      subst hfsp
      have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out pbA
      have hfr := frame_928_rejoin_dropGlue s0.sp
      dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        polynomialErrorByte, resultPolyEncoderErrTailSize]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((cells (s0.sp - 1024#64) 7 ∗
            (((s0.sp - 1024#64) + 56#64) ↦₆₄ out) ∗
            (((s0.sp - 1024#64) + 64#64) ↦₆₄ pbA)) ∗
           memRegion ((s0.sp - 1024#64) + 72#64) 384 ∗
           cells ((s0.sp - 1024#64) + 456#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 480#64) 384 ∗
           cells ((s0.sp - 1024#64) + 864#64) 4 ∗
           cells ((s0.sp - 1024#64) + 896#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 920#64) 8 ∗
           stackAt (s0.sp - 1024#64) dropGluePoly16Stack) ∗
          (protoPolynomialEncoderAt A pbA pb ∗
           savedCells s0 ∗
           A.pool ∗
           ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391)) by ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono_left (Entails.trans (sepConj_mono_left hc9) hfr)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hfsp := hfsp_fn trivial
    subst hfsp
    have hep := from_pb_epilogue_placed hdrop_pb s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

theorem from_pb_err_pts_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop16 : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec A))
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (pb : ProtoPolynomialEncoder)
    (errPts : List (List GF16)) (herr_len : errPts.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1612#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        vecGF16ListOf A (fsp + 480#64) errPts ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A pbA pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.error .serializationInvalid) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hdrop16' := hdrop16
  simp only [dropGluePoly16Spec, BitVec.ofNat_eq_ofNat] at hdrop16'
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_clean
    (mid := (blkPl_374).base + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · dsimp only [polyArrayBytes, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat] at hpc hdrop16' ⊢
    wp_steps
    wp_call hdrop16' (⟨fsp + 480#64, errPts⟩ : DropGluePoly16Ghost)
    wp_steps
    refine align_pre ?_ ?_
    · rw [hsp]
      have hfsp := hfsp_fn trivial
      subst hfsp
      have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out v64
      have hfr := frame_928_rejoin_dropGlue s0.sp
      dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        polynomialErrorByte, resultPolyEncoderErrTailSize]
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((cells (s0.sp - 1024#64) 7 ∗
            (((s0.sp - 1024#64) + 56#64) ↦₆₄ out) ∗
            (((s0.sp - 1024#64) + 64#64) ↦₆₄ v64)) ∗
           memRegion ((s0.sp - 1024#64) + 72#64) 384 ∗
           cells ((s0.sp - 1024#64) + 456#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 480#64) 384 ∗
           cells ((s0.sp - 1024#64) + 864#64) 4 ∗
           cells ((s0.sp - 1024#64) + 896#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 920#64) 8 ∗
           stackAt (s0.sp - 1024#64) dropGluePoly16Stack) ∗
          (protoPolynomialEncoderAt A pbA pb ∗
           savedCells s0 ∗
           A.pool ∗
           ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391)) by ac_rfl)) ?_
      refine Entails.trans
        (sepConj_mono_left (Entails.trans (sepConj_mono_left hc9) hfr)) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hfsp := hfsp_fn trivial
    subst hfsp
    have hep := from_pb_epilogue_placed hdrop_pb s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

theorem from_pb_ok_copy_out_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (s0 s : State) (fsp out pbA v64 tag : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) (enc : PolyEncoder)
    (pins : List VecPin) (vecs : List (List GF16))
    (hpins_len : pins.length = vecs.length) (hvecs_len : vecs.length = 16)
    (hres :
      (out ↦₆₄ tag) ∗
      vecGF16ListOf A (out + 8#64) vecs ∗
      ((out + 392#64) ↦₃₂ pb.idx) ∗
      memRegion (out + 396#64) 4 ⊢
        resultPolyEncoderFromPbAt A out (.ok enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = tag)
    (hx20 : s.readReg64 .x20 = pbA)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
        vecGF16HeapList A pins vecs ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
        stackAt fsp allocHookStack ∗
        cells fsp 7 ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        cells (fsp + 456#64) 3 ∗
        memRegion (fsp + 480#64) 384 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        memRegion (fsp - 4128#64) 32 ∗
        ((pbA + 8#64) ↦₆₄ ptsPtr) ∗
        ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A out (.ok enc) ∗
          memRegion pbA protoPolynomialEncoderSize ∗
          A.pool ∗ stackAt s0.sp encoderFromPbStack) ∧
        CalleeSavedPreserved s0 sf ∧
        sf.sp = s0.sp ∧
        sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  have hbs_len : (vecHeadersBytesOf pins vecs).length = 384 := by
    rw [length_vecHeadersBytesOf pins vecs hpins_len, hvecs_len]
  have hmemcpy : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    SpqrV1.Alloc.spqr_hook_ok_of_mem hmemcpy_sat
  simp only [sessionMemcpySpec, BitVec.ofNat_eq_ofNat] at hmemcpy
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_ok_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d392
  refine seq_clean
    (mid := (blkPl_374).base + 1460#64)
    (P_mid := protoPolynomialEncoderAt A pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool ∗
      resultPolyEncoderFromPbAt A out (.ok enc))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    wp_call hmemcpy (out + 8#64, fsp + 72#64, vecHeadersBytesOf pins vecs)
    wp_steps
    refine align_pre ?_ ?_
    · rw [hsp]
      have hfsp := hfsp_fn trivial
      subst hfsp
      have hvec := headers_heaps_entails_vecGF16ListOf A pins vecs (out + 8#64) hpins_len
      have hsrc : (((s0.sp - 1024#64) + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ⊢
          memRegion ((s0.sp - 1024#64) + 72#64) 384 := by
        rw [← hbs_len]
        exact ProofLib.pointsToBytes_entails_memRegion ((s0.sp - 1024#64) + 72#64) (vecHeadersBytesOf pins vecs)
      have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out v64
      have hfr := frame_928_rejoin s0.sp
      have hpb := protoPolyEncoder_close A pbA ptsCap ptsPtr polysCap polysPtr pb
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
           ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((pbA + 32#64) ↦₆₄ polysPtr) ∗
           ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
           ((pbA + 48#64) ↦₃₂ pb.idx) ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pb.pts ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 polysPtr pb.polys ∗
           protoPolyEncoderRest A pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
          savedCells s0 ∗
          ((cells (s0.sp - 1024#64) 7 ∗
            (((s0.sp - 1024#64) + 56#64) ↦₆₄ out) ∗
            (((s0.sp - 1024#64) + 64#64) ↦₆₄ v64)) ∗
           (((s0.sp - 1024#64) + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
           cells ((s0.sp - 1024#64) + 456#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 480#64) 384 ∗
           cells ((s0.sp - 1024#64) + 864#64) 4 ∗
           cells ((s0.sp - 1024#64) + 896#64) 3 ∗
           memRegion ((s0.sp - 1024#64) + 920#64) 8 ∗
           memRegion ((s0.sp - 1024#64) - 4128#64) 32 ∗
           stackAt (s0.sp - 1024#64) allocHookStack) ∗
          A.pool ∗
          ((out ↦₆₄ tag) ∗
           (((out + 8#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs) ∗
           ((out + 392#64) ↦₃₂ pb.idx) ∗
           memRegion (out + 396#64) 4) by ac_rfl)) ?_
      exact sepConj_mono hpb
        (sepConj_mono_right
          (sepConj_mono
            (Entails.trans (sepConj_mono hc9 (sepConj_mono_left hsrc)) hfr)
            (sepConj_mono_right
              (Entails.trans (sepConj_mono_right (sepConj_mono_left hvec)) hres))))
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hfsp := hfsp_fn trivial
    subst hfsp
    have hep := from_pb_epilogue_placed hdrop_pb s0 s1 pbA pb
      (resultPolyEncoderFromPbAt A out (.ok enc))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hvregs1
    exact SepWP.mono hep fun sf Pf _ _ ⟨hPf, hcs, hspf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hcs, hspf, htrf⟩

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
