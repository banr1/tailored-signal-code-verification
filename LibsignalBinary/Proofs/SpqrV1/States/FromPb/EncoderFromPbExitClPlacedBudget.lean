/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Exit
import LibsignalBinary.Heap.IfaceSimp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbExitClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Closed `[LibsignalPlacement]` Epilogue & Exit Blocks for `<PolyEncoder>::from_pb`

Discharges the cross-block callees `core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>`
(Block `265`) and `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>` (Block `271`)
in the 5 exit theorems of `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (Block `374`) under
`LibsignalCodeLoaded` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbExitClPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_374 blkPl_374 lsmpl lsρ sepWP_seq_lscl withMemEq
)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (
  CHUNK_SIZE GF16 NUM_POLYS PolyEncoder ProtoPolynomialEncoder
)
open CryptoVerification.SpqrV1.Poly (
  polyArrayBytes polyEncoderNicheTag polyEncoderSize polynomialErrorByte
  protoPolynomialEncoderAt protoPolynomialEncoderSize
  resultPolyEncoderErrByteOff resultPolyEncoderErrTailSize resultPolyEncoderFromPbAt
)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  align_pre bv384_toNat bv8_toNat bv_lit_add_lit cells7_56_64_entails_cells9
  encoderFromPbStack frame_928_rejoin frame_928_rejoin_dropGlue
  headers_heaps_entails_vecGF16ListOf length_vecHeadersBytesOf
  memRegion_out_err_open memRegion_out_ok_open protoPolyEncoderRest
  protoPolyEncoder_close savedCells savedCells_restore_stack
  sp_sub_1024_add_928 sp_sub_16_add_8 sp_sub_24_add_8 sp_sub_32_add_8
  sp_sub_40_add_8 sp_sub_48_add_8 sp_sub_56_add_8 sp_sub_64_add_8
  sp_sub_72_add_8 sp_sub_80_add_8 sp_sub_88_add_8 sp_sub_96_add_16
  sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_add_96 spqrRustDeallocSym
  stackAt_encoderFromPb_split_dropStack48 vecGF16HeapList vecHeadersBytesOf
)
open CryptoVerification.SpqrV1.Drop (
  DropGluePoly16Ghost DropProtoPolyEncoderGhost dropGluePoly16Stack
  dropStack48 vecGF16ListOf
)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved allocMemcpyVmSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  framelessMemcpyAcpSpec framelessMemcpyAcp_of_allocMemcpyVm
  session2MemcpyAcpSpecWithStack session2MemcpyAcpWithStack_of_frameless
)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (
  drop_glue_poly16_mem_on drop_glue_proto_poly_encoder_mem_on
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  bv384_toNat bv8_toNat
  sp_sub_1024_add_928 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_add_96
  sp_sub_88_add_8 sp_sub_80_add_8 sp_sub_72_add_8 sp_sub_64_add_8 sp_sub_56_add_8
  sp_sub_48_add_8 sp_sub_40_add_8 sp_sub_32_add_8 sp_sub_24_add_8 sp_sub_16_add_8

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P_mid (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.weaken_pre hent hwp

private theorem seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ AllocCallPreserved s sm ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → AllocCallPreserved s sm →
      Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hacp, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hvm hacp hQ))

private theorem seq_lscl_st [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

private theorem seq_evs_lscl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {mid target : BitVec 64}
    {st : M.σ} {s : State} {P X1 X2 X3 : SepProp}
    {P_mid : M.σ → State → SepProp} {Q_mid Q_out : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs1, FreeOnlyEvs evs1 ∧ (Pm ⊢ P_mid (M.stepEvents evs1 st) sm) ∧ Q_mid sm))
    (h2 : ∀ (st1 : M.σ) (sm : State),
      sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm →
      SepWP prog target sm (P_mid st1 sm) (fun sf Pf =>
        ∃ evs2, FreeOnlyEvs evs2 ∧
          (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs2 st1) sf ∗ X3) ∧ Q_out sf)) :
    SepWP prog target s P (fun sf Pf =>
      ∃ evs, FreeOnlyEvs evs ∧
        (Pf ⊢ X1 ∗ X2 ∗ A.pool lim (M.stepEvents evs st) sf ∗ X3) ∧ Q_out sf) :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨evs1, hevs1, hent, hQ⟩ hcl' =>
    SepWP.mono (SepWP.weaken_pre hent (h2 (M.stepEvents evs1 st) sm hpc hrun hcl' hQ))
      fun sf _ _ _ ⟨evs2, hevs2, hPf, hQo⟩ =>
        ⟨evs1 ++ evs2, hevs1.append hevs2, by
          rwa [AllocCostModel.stepEvents_append], hQo⟩)

/-- Placed shared epilogue at `+1460` with `LibsignalCodeLoaded`
and `RustCliAllocBudget M`. -/
theorem from_pb_epilogue_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (pbA : BitVec 64) (pb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        savedCells s0 ∗
        stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack ∗ Frame) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  refine seq_vm_lscl hcl
    (mid := lsmpl.base 271)
    (P_mid := protoPolynomialEncoderAt A.repAlloc pbA pb ∗
      stackAt s0.sp encoderFromPbStack ∗
      A.pool lim st s ∗ Frame)
    (Q := fun sc => CalleeSavedPreserved s0 sc ∧ sc.sp = s0.sp ∧ sc.trace = s0.trace ∧
      sc.readReg64 .x0 = pbA ∧ sc.readReg64 .lr = s0.readReg64 (Reg.gpr 30#5))
    ?_ ?_
  · by_vm_steps
      unfold savedCells
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans (Entails.of_eq (show _ =
          savedCells s0 ∗ stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
            (protoPolynomialEncoderAt A.repAlloc pbA pb ∗ A.pool lim st s ∗ Frame) by
              unfold savedCells; sep_ac_rfl))
          (savedCells_restore_stack s0
            (protoPolynomialEncoderAt A.repAlloc pbA pb ∗ A.pool lim st s ∗ Frame))) ?_
      refine align_pre_vm (Entails.of_eq (by sep_ac_rfl)) ?_
      wp_done
  · intro sc hpcc hrunc hcl_c hvm_c hacp_sc ⟨hcs_c, hsp_c, htr_c, hx0_c, hlr_c⟩
    have hacp_c : AllocCallPreserved s0 sc := hacp.trans hacp_sc
    have hdrop_pb : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
        (lsmpl.base 271) (withMemEq sc.mem (dropProtoPolyEncoderSpec M A lim)) :=
      drop_glue_proto_poly_encoder_mem_on
        (callerProg := (blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) hdealloc_sat hcl_c
    simp only [withMemEq, dropProtoPolyEncoderSpec, BitVec.ofNat_eq_ofNat] at hdrop_pb
    dsimp only [protoPolynomialEncoderSize, BitVec.ofNat_eq_ofNat] at hpcc hdrop_pb ⊢
    rw [← A.pool_of_vmPreserved hvm_c, stackAt_encoderFromPb_split_dropStack48 s0.sp, ← hsp_c, ← hlr_c]
    have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := hlr_c ▸ hlr0
    wp_call hdrop_pb ((⟨pbA, pb⟩ : DropProtoPolyEncoderGhost), st)
    rw [hlr_c, hsp_c]
    have hsp_sf : sf.sp = sc.sp := by assumption
    have hacp_cf : AllocCallPreserved sc sf := by assumption
    have hevs_w : FreeOnlyEvs w := by assumption
    have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
    have hsp_f : sf.sp = s0.sp := hsp_sf.trans hsp_c
    have htr_f : sf.trace = s0.trace := hacp_cf.2.1.trans htr_c
    have hcs_f : CalleeSavedPreserved s0 sf := by
      unfold CalleeSavedPreserved at hcs_c ⊢
      simp_all only [and_self]
    exact SepWP.done (by assumption) (by assumption)
      ⟨w, hevs_w, Entails.of_eq (by sep_ac_rfl), hcs_f, hacp_f, hsp_f, htr_f⟩

/-- Placed header error exit (`+1448 -> s0.lr`) with `LibsignalCodeLoaded`
and `RustCliAllocBudget M`. -/
theorem from_pb_err_header_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA : BitVec 64) (pb : ProtoPolynomialEncoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1448#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        savedCells s0 ∗
        stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
        A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_vm_lscl hcl
    (mid := (blkPl_374).base + 1460#64)
    (P_mid := protoPolynomialEncoderAt A.repAlloc pbA pb ∗
      savedCells s0 ∗
      stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
      A.pool lim st s ∗
      resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
    (Q := fun sm => sm.sp = s0.sp - 1024#64 ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · by_vm_steps
      wp_steps
      refine align_pre_vm (by
        dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
          polynomialErrorByte, resultPolyEncoderErrTailSize]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 hvm1 hacp_s1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
    have hacp1 : AllocCallPreserved s0 s1 := hacp.trans hacp_s1
    rw [← A.pool_of_vmPreserved hvm1]
    have hep := from_pb_epilogue_cl_placed hdealloc_sat st s0 s1 hcl1 pbA pb
      (resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
      hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hacp1 hvregs1 hlr0
    exact SepWP.mono hep fun sf Pf _ _ ⟨evs, hevs, hPf, hcs, hacpf, hspf, htrf⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hcs, hacpf, hspf, htrf⟩

/-- Placed `.polys` loop error exit (`+1496 -> s0.lr`) with `LibsignalCodeLoaded`
and `RustCliAllocBudget M`. -/
theorem from_pb_err_polys_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pbA : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (pb : ProtoPolynomialEncoder)
    (errPolys : List (List GF16)) (herr_len : errPolys.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = 2#64)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        vecGF16ListOf A.repAlloc (fsp + 480#64) errPolys ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        savedCells s0 ∗
        A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_vm_lscl hcl
    (mid := lsmpl.base 265)
    (P_mid := ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391) ∗
      vecGF16ListOf A.repAlloc (fsp + 480#64) errPolys ∗
      cells fsp 7 ∗
      ((fsp + 56#64) ↦₆₄ out) ∗
      ((fsp + 64#64) ↦₆₄ pbA) ∗
      memRegion (fsp + 72#64) 384 ∗
      cells (fsp + 456#64) 3 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 ∗
      stackAt fsp dropGluePoly16Stack ∗
      protoPolynomialEncoderAt A.repAlloc pbA pb ∗
      savedCells s0 ∗
      A.pool lim st s)
    (Q := fun sc => sc.sp = fsp ∧ sc.readReg64 .x0 = fsp + 480#64 ∧
      sc.readReg64 .x30 = (blkPl_374).base + 1520#64 ∧ sc.trace = s0.trace ∧
      calleeSavedVRegs sc = calleeSavedVRegs s0)
    ?_ ?_
  · by_vm_steps
      wp_steps 6
      wp_done
  · intro sc hpcc hrunc hcl_c hvm_c hacp_sc ⟨hspc, hx0c, hx30c, htrc, hvregsc⟩
    have hacp_c : AllocCallPreserved s0 sc := hacp.trans hacp_sc
    rw [← A.pool_of_vmPreserved hvm_c]
    have hdrop16' : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
        (lsmpl.base 265) (withMemEq sc.mem (dropGluePoly16Spec M A lim)) :=
      drop_glue_poly16_mem_on
        (callerProg := (blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) hdealloc_sat hcl_c
    simp only [withMemEq, dropGluePoly16Spec, BitVec.ofNat_eq_ofNat] at hdrop16'
    refine seq_evs_lscl (A := A) (lim := lim) (st := st)
      (X1 := resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
      (X2 := memRegion pbA protoPolynomialEncoderSize)
      (X3 := stackAt s0.sp encoderFromPbStack)
      hcl_c
      (mid := (blkPl_374).base + 1520#64)
      (P_mid := fun st1 sm =>
        ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391) ∗
        memRegion (fsp + 480#64) 384 ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ pbA) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        savedCells s0 ∗
        A.pool lim st1 sm)
      (Q_mid := fun sm => sm.sp = fsp ∧ sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [polyArrayBytes, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat] at hpcc hdrop16' ⊢
      wp_call hdrop16' ((⟨fsp + 480#64, errPolys⟩ : DropGluePoly16Ghost), st)
      have hsp_sf : sf.sp = sc.sp := by assumption
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
      have hsp_f : sf.sp = fsp := hsp_sf.trans hspc
      have htr_f : sf.trace = s0.trace := hacp_cf.2.1.trans htrc
      have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by assumption : calleeSavedVRegs sf = calleeSavedVRegs sc).trans hvregsc
      rw [hspc]
      exact SepWP.done (by assumption) (by assumption)
        ⟨w, hevs_w, Entails.of_eq (by sep_ac_rfl), hsp_f, htr_f, hacp_f, hvregs_f⟩
    · intro st1 sf hpcf hrunf hcl_f ⟨hsp_f, htr_f, hacp_f, hvregs_f⟩
      refine seq_vm_lscl hcl_f
        (mid := (blkPl_374).base + 1460#64)
        (P_mid := protoPolynomialEncoderAt A.repAlloc pbA pb ∗
          savedCells s0 ∗
          stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
          A.pool lim st1 sf ∗
          resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · by_vm_steps
          wp_steps
          refine align_pre_vm ?_ ?_
          · have hfsp := hfsp_fn trivial
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
                (protoPolynomialEncoderAt A.repAlloc pbA pb ∗
                 savedCells s0 ∗
                 A.pool lim st1 sf ∗
                 ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391)) by sep_ac_rfl)) ?_
            refine Entails.trans
              (sepConj_mono_left (Entails.trans (sepConj_mono_left hc9) hfr)) ?_
            exact Entails.of_eq (by sep_ac_rfl)
          · wp_done
      · intro s1 hpc1 hrun1 hcl1 hvm1 hacp_fs1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
        have hfsp := hfsp_fn trivial
        subst hfsp
        have hacp1 : AllocCallPreserved s0 s1 := hacp_f.trans hacp_fs1
        rw [← A.pool_of_vmPreserved hvm1]
        have hep := from_pb_epilogue_cl_placed hdealloc_sat st1 s0 s1 hcl1 pbA pb
          (resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
          hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hacp1 hvregs1 hlr0
        exact SepWP.mono hep fun sf' Pf _ _ ⟨evs2, hevs2, hPf, hcs, hacpf, hspf, htrf⟩ =>
          ⟨evs2, hevs2, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hcs, hacpf, hspf, htrf⟩

/-- Placed `.points` loop error exit (`+1612 -> s0.lr`) with `LibsignalCodeLoaded`
and `RustCliAllocBudget M`. -/
theorem from_pb_err_pts_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pbA v64 : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (pb : ProtoPolynomialEncoder)
    (errPts : List (List GF16)) (herr_len : errPts.length = 16)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1612#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        vecGF16ListOf A.repAlloc (fsp + 480#64) errPts ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        savedCells s0 ∗
        A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
          sf.sp = s0.sp ∧
          sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]
    exact ProofLib.spAligned_sub s0.sp 1024#64 hsp0_align
  have hfsp_fn : True → fsp = s0.sp - 1024#64 := fun _ => hfsp
  clear hfsp
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d8
  refine seq_vm_lscl hcl
    (mid := lsmpl.base 265)
    (P_mid := ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391) ∗
      vecGF16ListOf A.repAlloc (fsp + 480#64) errPts ∗
      cells fsp 7 ∗
      ((fsp + 56#64) ↦₆₄ out) ∗
      ((fsp + 64#64) ↦₆₄ v64) ∗
      memRegion (fsp + 72#64) 384 ∗
      cells (fsp + 456#64) 3 ∗
      cells (fsp + 864#64) 4 ∗
      cells (fsp + 896#64) 3 ∗
      memRegion (fsp + 920#64) 8 ∗
      stackAt fsp dropGluePoly16Stack ∗
      protoPolynomialEncoderAt A.repAlloc pbA pb ∗
      savedCells s0 ∗
      A.pool lim st s)
    (Q := fun sc => sc.sp = fsp ∧ sc.readReg64 .x0 = fsp + 480#64 ∧
      sc.readReg64 .x19 = pbA ∧ sc.readReg64 .x30 = (blkPl_374).base + 1640#64 ∧
      sc.trace = s0.trace ∧ calleeSavedVRegs sc = calleeSavedVRegs s0)
    ?_ ?_
  · by_vm_steps
      wp_steps 7
      wp_done
  · intro sc hpcc hrunc hcl_c hvm_c hacp_sc ⟨hspc, hx0c, hx19c, hx30c, htrc, hvregsc⟩
    have hacp_c : AllocCallPreserved s0 sc := hacp.trans hacp_sc
    rw [← A.pool_of_vmPreserved hvm_c]
    have hdrop16' : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
        (lsmpl.base 265) (withMemEq sc.mem (dropGluePoly16Spec M A lim)) :=
      drop_glue_poly16_mem_on
        (callerProg := (blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) hdealloc_sat hcl_c
    simp only [withMemEq, dropGluePoly16Spec, BitVec.ofNat_eq_ofNat] at hdrop16'
    refine seq_evs_lscl (A := A) (lim := lim) (st := st)
      (X1 := resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
      (X2 := memRegion pbA protoPolynomialEncoderSize)
      (X3 := stackAt s0.sp encoderFromPbStack)
      hcl_c
      (mid := (blkPl_374).base + 1640#64)
      (P_mid := fun st1 sm =>
        ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391) ∗
        memRegion (fsp + 480#64) 384 ∗
        cells fsp 7 ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((fsp + 64#64) ↦₆₄ v64) ∗
        memRegion (fsp + 72#64) 384 ∗
        cells (fsp + 456#64) 3 ∗
        cells (fsp + 864#64) 4 ∗
        cells (fsp + 896#64) 3 ∗
        memRegion (fsp + 920#64) 8 ∗
        stackAt fsp dropGluePoly16Stack ∗
        protoPolynomialEncoderAt A.repAlloc pbA pb ∗
        savedCells s0 ∗
        A.pool lim st1 sm)
      (Q_mid := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = pbA ∧ sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [polyArrayBytes, NUM_POLYS, CHUNK_SIZE, BitVec.ofNat_eq_ofNat] at hpcc hdrop16' ⊢
      wp_call hdrop16' ((⟨fsp + 480#64, errPts⟩ : DropGluePoly16Ghost), st)
      have hsp_sf : sf.sp = sc.sp := by assumption
      have hx19_sf : sf.readReg64 (Reg.gpr 19#5) = sc.readReg64 (Reg.gpr 19#5) := by assumption
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_c.trans hacp_cf
      have hsp_f : sf.sp = fsp := hsp_sf.trans hspc
      have hx19_f : sf.readReg64 .x19 = pbA := hx19_sf.trans hx19c
      have htr_f : sf.trace = s0.trace := hacp_cf.2.1.trans htrc
      have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by assumption : calleeSavedVRegs sf = calleeSavedVRegs sc).trans hvregsc
      rw [hspc]
      exact SepWP.done (by assumption) (by assumption)
        ⟨w, hevs_w, Entails.of_eq (by sep_ac_rfl), hsp_f, hx19_f, htr_f, hacp_f, hvregs_f⟩
    · intro st1 sf hpcf hrunf hcl_f ⟨hsp_f, hx19_f, htr_f, hacp_f, hvregs_f⟩
      refine seq_vm_lscl hcl_f
        (mid := (blkPl_374).base + 1460#64)
        (P_mid := protoPolynomialEncoderAt A.repAlloc pbA pb ∗
          savedCells s0 ∗
          stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
          A.pool lim st1 sf ∗
          resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · by_vm_steps
          wp_steps
          refine align_pre_vm ?_ ?_
          · have hfsp := hfsp_fn trivial
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
                (protoPolynomialEncoderAt A.repAlloc pbA pb ∗
                 savedCells s0 ∗
                 A.pool lim st1 sf ∗
                 ((out ↦₆₄ 2#64) ∗ ((out + 8#64) ↦₈ 2#8) ∗ memRegion (out + 9#64) 391)) by sep_ac_rfl)) ?_
            refine Entails.trans
              (sepConj_mono_left (Entails.trans (sepConj_mono_left hc9) hfr)) ?_
            exact Entails.of_eq (by sep_ac_rfl)
          · wp_done
      · intro s1 hpc1 hrun1 hcl1 hvm1 hacp_fs1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
        have hfsp := hfsp_fn trivial
        subst hfsp
        have hacp1 : AllocCallPreserved s0 s1 := hacp_f.trans hacp_fs1
        rw [← A.pool_of_vmPreserved hvm1]
        have hep := from_pb_epilogue_cl_placed hdealloc_sat st1 s0 s1 hcl1 pbA pb
          (resultPolyEncoderFromPbAt A.repAlloc out (.error .serializationInvalid))
          hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hacp1 hvregs1 hlr0
        exact SepWP.mono hep fun sf' Pf _ _ ⟨evs2, hevs2, hPf, hcs, hacpf, hspf, htrf⟩ =>
          ⟨evs2, hevs2, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hcs, hacpf, hspf, htrf⟩

/-- Placed shared success tail at `+1572 -> s0.lr` with `LibsignalCodeLoaded`
and `RustCliAllocBudget M`. -/
theorem from_pb_ok_copy_out_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym
      (session2MemcpyAcpSpecWithStack allocHookStack))
    (hdealloc_sat : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pbA v64 tag : BitVec 64) (hfsp : fsp = s0.sp - 1024#64)
    (ptsCap ptsPtr polysCap polysPtr : BitVec 64)
    (pb : ProtoPolynomialEncoder) (enc : PolyEncoder)
    (pins : List VecPin) (vecs : List (List GF16))
    (hpins_len : pins.length = vecs.length) (hvecs_len : vecs.length = 16)
    (hres :
      (out ↦₆₄ tag) ∗
      vecGF16ListOf A.repAlloc (out + 8#64) vecs ∗
      ((out + 392#64) ↦₃₂ pb.idx) ∗
      memRegion (out + 396#64) 4 ⊢
        resultPolyEncoderFromPbAt A.repAlloc out (.ok enc))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_374).base + 1572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = tag)
    (hx20 : s.readReg64 .x20 = pbA)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗
        ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
        vecGF16HeapList A.repAlloc pins vecs ∗
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
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool lim st s)
      (fun sf Pf =>
        ∃ evs, FreeOnlyEvs evs ∧
          (Pf ⊢ resultPolyEncoderFromPbAt A.repAlloc out (.ok enc) ∗
            memRegion pbA protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp encoderFromPbStack) ∧
          CalleeSavedPreserved s0 sf ∧
          AllocCallPreserved s0 sf ∧
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
      (lsρ spqrMemcpySym) (session2MemcpyAcpSpecWithStack allocHookStack) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [session2MemcpyAcpSpecWithStack, BitVec.ofNat_eq_ofNat] at hmemcpy
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_ok_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro d392
  refine seq_vm_lscl hcl
    (mid := lsρ spqrMemcpySym)
    (P_mid := ((out ↦₆₄ tag) ∗ memRegion (out + 8#64) 384 ∗
        ((out + 392#64) ↦₃₂ d392) ∗ memRegion (out + 396#64) 4) ∗
      ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
      vecGF16HeapList A.repAlloc pins vecs ∗
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
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
      arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
      protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
      savedCells s0 ∗
      A.pool lim st s)
    (Q := fun sc => sc.sp = fsp ∧ sc.readReg64 .x0 = out + 8#64 ∧
      sc.readReg64 .x1 = fsp + 72#64 ∧ sc.readReg64 .x2 = 384#64 ∧
      sc.readReg64 .x19 = BitVec.zeroExtend 64 pb.idx ∧ sc.readReg64 .x20 = pbA ∧
      sc.readReg64 .x21 = out ∧
      sc.readReg64 .x30 = (blkPl_374).base + 1600#64 ∧
      sc.trace = s0.trace ∧ calleeSavedVRegs sc = calleeSavedVRegs s0)
    ?_ ?_
  · by_vm_steps
      wp_steps
      wp_done
  · intro sc hpcc hrunc hcl_c hvm_c hacp_sc
      ⟨hspc, hx0c, hx1c, hx2c, hx19c, hx20c, hx21c, hx30c, htrc, hvregsc⟩
    have hacp_c : AllocCallPreserved s0 sc := hacp.trans hacp_sc
    rw [← A.pool_of_vmPreserved hvm_c]
    refine seq_lscl_st hcl_c
      (mid := (blkPl_374).base + 1600#64)
      (P_mid := fun sf =>
        ((out + 8#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
        ((fsp + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗
        stackAt fsp allocHookStack ∗
        (out ↦₆₄ tag) ∗
        ((out + 392#64) ↦₃₂ d392) ∗
        memRegion (out + 396#64) 4 ∗
        vecGF16HeapList A.repAlloc pins vecs ∗
        ((fsp + 56#64) ↦₆₄ out) ∗
        ((pbA + 48#64) ↦₃₂ pb.idx) ∗
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
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
        protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb ∗
        savedCells s0 ∗
        A.pool lim st sf)
      (Q := fun sf =>
        sf.sp = fsp ∧ sf.readReg64 .x19 = BitVec.zeroExtend 64 pb.idx ∧
        sf.readReg64 .x20 = pbA ∧ sf.readReg64 .x21 = out ∧
        AllocCallPreserved s0 sf ∧ sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      ?_ ?_
    · wp_call hmemcpy (out + 8#64, fsp + 72#64, vecHeadersBytesOf pins vecs)
      have hsp_sf_sc : sf.sp = sc.sp := by assumption
      have hx19_sf_sc : sf.readReg64 (Reg.gpr 19#5) = sc.readReg64 (Reg.gpr 19#5) := by assumption
      have hx20_sf_sc : sf.readReg64 (Reg.gpr 20#5) = sc.readReg64 (Reg.gpr 20#5) := by assumption
      have hx21_sf_sc : sf.readReg64 (Reg.gpr 21#5) = sc.readReg64 (Reg.gpr 21#5) := by assumption
      have hvm_cf : VmPreserved sc sf := by assumption
      have hacp_cf : AllocCallPreserved sc sf := by assumption
      have hsp_sf : sf.sp = fsp := hsp_sf_sc.trans hspc
      have hx19f : sf.readReg64 .x19 = BitVec.zeroExtend 64 pb.idx := hx19_sf_sc.trans hx19c
      have hx20f : sf.readReg64 .x20 = pbA := hx20_sf_sc.trans hx20c
      have hx21f : sf.readReg64 .x21 = out := hx21_sf_sc.trans hx21c
      have htr_sf : sf.trace = s0.trace := hacp_cf.2.1.trans htrc
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        (by assumption : calleeSavedVRegs sf = calleeSavedVRegs sc).trans hvregsc
      rw [← A.pool_of_vmPreserved hvm_cf, hspc]
      exact SepWP.done (by assumption) (by assumption)
        ⟨Entails.of_eq (by sep_ac_rfl), hsp_sf, hx19f, hx20f, hx21f, hacp_c.trans hacp_cf, htr_sf, hvregs_sf⟩
    · intro sf hpcf hrunf hcl_f ⟨hsp_sf, hx19f, hx20f, hx21f, hacp_f, htr_sf, hvregs_sf⟩
      refine seq_vm_lscl hcl_f
        (mid := (blkPl_374).base + 1460#64)
        (P_mid := protoPolynomialEncoderAt A.repAlloc pbA pb ∗
          savedCells s0 ∗
          stackAt (s0.sp - 96#64) (dropGluePoly16Stack + 928) ∗
          A.pool lim st sf ∗
          resultPolyEncoderFromPbAt A.repAlloc out (.ok enc))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = pbA ∧ sm.trace = s0.trace ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0)
        ?_ ?_
      · by_vm_steps
          wp_steps
          refine align_pre_vm ?_ ?_
          · have hfsp := hfsp_fn trivial
            subst hfsp
            have hvec := headers_heaps_entails_vecGF16ListOf A.repAlloc pins vecs (out + 8#64) hpins_len
            have hsrc : (((s0.sp - 1024#64) + 72#64) ↦ₛ vecHeadersBytesOf pins vecs) ⊢
                memRegion ((s0.sp - 1024#64) + 72#64) 384 := by
              rw [← hbs_len]
              exact ProofLib.pointsToBytes_entails_memRegion
                ((s0.sp - 1024#64) + 72#64) (vecHeadersBytesOf pins vecs)
            have hc9 := cells7_56_64_entails_cells9 (s0.sp - 1024#64) out v64
            have hfr := frame_928_rejoin s0.sp
            have hpb := protoPolyEncoder_close A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb
            refine Entails.trans
              (Entails.of_eq (show _ =
                (((pbA + 8#64) ↦₆₄ ptsPtr) ∗
                 ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                 ((pbA + 32#64) ↦₆₄ polysPtr) ∗
                 ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
                 ((pbA + 48#64) ↦₃₂ pb.idx) ∗
                 arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pb.pts ∗
                 arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 polysPtr pb.polys ∗
                 protoPolyEncoderRest A.repAlloc pbA ptsCap ptsPtr polysCap polysPtr pb) ∗
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
                A.pool lim st sf ∗
                ((out ↦₆₄ tag) ∗
                 (((out + 8#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A.repAlloc pins vecs) ∗
                 ((out + 392#64) ↦₃₂ pb.idx) ∗
                 memRegion (out + 396#64) 4) by sep_ac_rfl)) ?_
            exact sepConj_mono hpb
              (sepConj_mono_right
                (sepConj_mono
                  (Entails.trans (sepConj_mono hc9 (sepConj_mono_left hsrc)) hfr)
                  (sepConj_mono_right
                    (Entails.trans (sepConj_mono_right (sepConj_mono_left hvec)) hres))))
          · wp_done
      · intro s1 hpc1 hrun1 hcl1 hvm1 hacp_fs1 ⟨hsp1, hx1_1, htr1, hvregs1⟩
        have hfsp := hfsp_fn trivial
        subst hfsp
        have hacp1 : AllocCallPreserved s0 s1 := hacp_f.trans hacp_fs1
        rw [← A.pool_of_vmPreserved hvm1]
        have hep := from_pb_epilogue_cl_placed hdealloc_sat st s0 s1 hcl1 pbA pb
          (resultPolyEncoderFromPbAt A.repAlloc out (.ok enc))
          hsp0_align hpc1 hrun1 hsp1 hx1_1 htr1 hacp1 hvregs1 hlr0
        exact SepWP.mono hep fun sf' Pf _ _ ⟨evs, hevs, hPf', hcs, hacpf, hspf, htrf⟩ =>
          ⟨evs, hevs, Entails.trans hPf' (Entails.of_eq (by sep_ac_rfl)), hcs, hacpf, hspf, htrf⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.EncoderFromPbExitClPlacedBudget
