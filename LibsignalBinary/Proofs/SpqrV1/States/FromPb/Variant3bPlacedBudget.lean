/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 3 (`Ct1Received`) — Error Cleanup

Relocatable Block-`333` subroutine bridges and `FreeOnlyEvs` error-cleanup paths (`+4968`,
`+4176`, `+4924`, `+4908`, `+4884`, `+1024`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (Error PolynomialEncoder pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (DropProtoPolyEncoderGhost cap_add_one_beq_zero_false chunkedStatesSize
   dropStack48 vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (optProtoPolynomialEncoderAt optProtoPolynomialEncoderNoneTailSize
   protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbSavedCells statesFromPbStack
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_shl8_extract_0_8
   v1_stackAt_encoder_split_dropStack48
   v10_optEncoderCapProp v10_optProtoPolyEncoderTail
   v10_optProtoPolyEncoder_expose_cap v10_optProtoPolyEncoder_unexpose_cap
   v3cr_fsp_1496_56_entails_2304 v3cr_fsp_1496_none_entails_2304)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget
   seq_clean_lscl_st v1_dealloc_ok_of_dealloc_placed
   v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed
   v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed
   v1_encoder_from_pb_mem_ok_at_statesFromPb_placed
   withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Subroutine Call Relocation Helpers -/

theorem v3cr_sub_ok_encoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hE : EncoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  hE

theorem v3cr_sub_ok_encoder_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hE : EncoderFromPbPlacedOkExt M A lim ext)
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 374)
      (withMemEq m (encoderFromPbSpec M A lim)) :=
  v1_encoder_from_pb_mem_ok_at_statesFromPb_placed hE hcl

theorem v3cr_sub_ok_drop_proto_poly_encoder_4192_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded
    (v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed hA) hcl

/-! ## Shared Error Cleanup Paths (`+4968`, `+4176`, `+4924`, `+4908`, `+4884`, `+1024`) -/

/-- `VmPreserved`-strengthened shared `Err(err)` exit at `+4968` (`lsmpl.base 333 + 4968 -> s0.x30`):
    when `x22` has low byte `spqrErrorByte err` and `x19 = out`, writes `x24, x28` to `[out + 16..32]`,
    sets `x8 = noneCap`, writes `x22` to `[out + 8]`, and branches to `+60`. -/
theorem v3cr_states_from_pb_err_4968_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4968#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : (s1.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_states_from_pb_err_4968_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v3cr_states_from_pb_err_4968_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4968#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : (s1.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          A.pool lim st sf ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v3cr_states_from_pb_err_4968_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Error-cleanup path at `+4176` (`lsmpl.base 333 + 4176 -> +4968 -> s0.x30`) under an explicit
    Block-`271` `withLsCodeLoaded` drop-glue contract: drops
    `optProtoPolynomialEncoderAt A.repAlloc (fsp + 1496) (sendingEk.map pbToProtoPolyEncoder)`
    and exits via `+4968` with `err` in low byte of `x22`. -/
theorem v3cr_states_from_pb_err_4176_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out : BitVec 64) (err : Error)
    (sendingEk : Option PolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : (s1.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
          (sendingEk.map pbToProtoPolyEncoder) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  cases sendingEk with
  | none =>
    simp only [Option.map_none]
    dsimp only [optProtoPolynomialEncoderAt, optProtoPolynomialEncoderNoneTailSize]
    have h1504 : ((s0.sp - 2400#64) + 1496#64) + 8#64 = (s0.sp - 2400#64) + 1504#64 := by bv_omega
    rw [h1504]
    refine Variant1bPlacedBudgetAux2.seq_clean_st
      (mid := lsmpl.base 333 + 4968#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st sm ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        (sm.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 4176#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4968#64) s1 _ _
      dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      wp_steps_sync_333 ((blkPl_333).base + 4968#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        have hfsp := v3cr_fsp_1496_none_entails_2304 (s0.sp - 2400#64)
        dsimp only [noneCap] at hfsp
        simp only [arm64_norm] at hfsp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 1496 ∗
           ((s0.sp - 904#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion (s0.sp - 896#64) 48 ∗
           memRegion (s0.sp - 848#64) 752) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           A.pool lim st sc ∗ Rest) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htr2⟩
      have herr := v3cr_states_from_pb_err_4968_placed_budget A lim st (F := F) (ext := ext)
        s0 s2 out err Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, ?_, hsp_f, hcc_f, htr_f⟩
      simpa only [M.stepEvents_nil] using hPf
  | some pbEnc =>
    simp only [Option.map_some]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (v10_optProtoPolyEncoder_expose_cap A.repAlloc ((s0.sp - 2400#64) + 1496#64)
          (some (pbToProtoPolyEncoder pbEnc)))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left
    intro cap
    rw [show
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        ⌜v10_optEncoderCapProp cap (some (pbToProtoPolyEncoder pbEnc))⌝ ∗
        (((s0.sp - 2400#64) + 1496#64) ↦₆₄ cap) ∗
        v10_optProtoPolyEncoderTail A.repAlloc ((s0.sp - 2400#64) + 1496#64) cap
          (some (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest =
      ⌜v10_optEncoderCapProp cap (some (pbToProtoPolyEncoder pbEnc))⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        (((s0.sp - 2400#64) + 1496#64) ↦₆₄ cap) ∗
        v10_optProtoPolyEncoderTail A.repAlloc ((s0.sp - 2400#64) + 1496#64) cap
          (some (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest) by sep_ac_rfl]
    apply ProofLib.SepWP.pure_elim
    intro hcap_lt
    dsimp only [v10_optEncoderCapProp] at hcap_lt
    have hne_none := cap_add_one_beq_zero_false hcap_lt
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      sp_sub_2400_align s0.sp hsp0_align
    have h904 : (s0.sp - 2400#64) + 1496#64 = s0.sp - 904#64 := by bv_omega
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 271)
      (P_mid := fun sm =>
        protoPolynomialEncoderAt A.repAlloc (s0.sp - 904#64) (pbToProtoPolyEncoder pbEnc) ∗
        A.pool lim st sm ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 1496 ∗
         memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 904#64 ∧
        sm.readReg64 .lr = (blkPl_333).base + 4200#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = s1.readReg64 .x22 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 4176#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsmpl.base 271) s1 _ _
      wp_steps_sync_333 (lsmpl.base 271)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        have hunexp := v10_optProtoPolyEncoder_unexpose_cap A.repAlloc
          ((s0.sp - 2400#64) + 1496#64) cap (some (pbToProtoPolyEncoder pbEnc))
        dsimp only [optProtoPolynomialEncoderAt] at hunexp
        rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h904]
        refine Entails.trans (Entails.of_eq (show _ =
          ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ cap) ∗
           v10_optProtoPolyEncoderTail A.repAlloc ((s0.sp - 2400#64) + 1496#64) cap
             (some (pbToProtoPolyEncoder pbEnc))) ∗
          (A.pool lim st sc ∗
           stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion ((s0.sp - 2400#64) - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 1496 ∗
            memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            Rest)) by simp only [arm64_norm]; sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hunexp) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx22_2, htr2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      have hdrop : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 271) (withMemEq s2.mem (dropProtoPolyEncoderSpec M A lim)) :=
        withMemEq_of_withLsCodeLoaded hdrop_cl hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine Variant1bPlacedBudgetAux2.seq_clean_evs
        (mid := lsmpl.base 333 + 4968#64)
        (P_evs := fun evs sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          (sm.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4968#64) s2 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack48 = stackAt s2.sp dropStack48 from hsp2 ▸ rfl]
        wp_call hdrop ((⟨s0.sp - 904#64, pbToProtoPolyEncoder pbEnc⟩ : DropProtoPolyEncoderGhost), st)
        rw [hsp2]
        rw [hlr_2] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        have hx22_sf : sf.readReg64 .x22 = s1.readReg64 .x22 :=
          ‹sf.readReg64 .x22 = s2.readReg64 .x22›.trans hx22_2
        refine SepWP.mono
          (post := fun sm Pm =>
            (Pm ⊢
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              memRegion (s0.sp - 2400#64) 2304 ∗
              statesFromPbSavedCells s0 ∗
              memRegion out chunkedStatesSize ∗
              A.pool lim (M.stepEvents w st) sm ∗
              Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x19 = out ∧
            (sm.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err ∧
            TraceCalleeSaved sm s0)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
        wp_steps_sync_333 ((blkPl_333).base + 4968#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h904]
          have hfsp := v3cr_fsp_1496_56_entails_2304 (s0.sp - 2400#64)
          dsimp only [protoPolynomialEncoderSize]
          simp only [arm64_norm] at hfsp ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 1496 ∗
             memRegion (s0.sp - 904#64) 56 ∗
             memRegion (s0.sp - 848#64) 752) ∗
            (memRegion (s0.sp - 7552#64) 1008 ∗
             stackAt (s0.sp - 2400#64) dropStack48 ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             A.pool lim (M.stepEvents w st) sc ∗
             Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro evs s3 hevs hpc3 hrun3 ⟨hsp3, hx19_3, hx22_3, htr3⟩
        have herr := v3cr_states_from_pb_err_4968_placed_budget A lim (M.stepEvents evs st)
          (F := F) (ext := ext) s0 s3 out err Rest hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ =>
          ⟨evs, hevs, hPf, hsp_f, hcc_f, htr_f⟩

theorem v3cr_states_from_pb_err_4176_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out : BitVec 64) (err : Error)
    (sendingEk : Option PolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : (s1.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
          (sendingEk.map pbToProtoPolyEncoder) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v3cr_states_from_pb_err_4176_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 hcl1 out err sendingEk Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1

/-- Error-cleanup path at `+4176` (`lsmpl.base 333 + 4176 -> +4968 -> s0.x30`):
    drops `optProtoPolynomialEncoderAt A.repAlloc (fsp + 1496) (sendingEk.map pbToProtoPolyEncoder)`
    and exits via `+4968` with `err` in low byte of `x22`. -/
theorem v3cr_states_from_pb_err_4176_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out : BitVec 64) (err : Error)
    (sendingEk : Option PolynomialEncoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : (s1.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        optProtoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 1496#64)
          (sendingEk.map pbToProtoPolyEncoder) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v3cr_states_from_pb_err_4176_of_dealloc_placed hA.dealloc
    st s0 s1 hcl1 out err sendingEk Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1

/-- Shared `+4924` error-cleanup path (`lsmpl.base 333 + 4924 -> +4968`) under an explicit
    Block-`333` `__rust_dealloc` contract: deallocates `vecCapPtrDealloc A.repAlloc ca3 pa3`
    (`x26 = ca3`, `[sp + 176] = pa3`) and `vecCapPtrDealloc A.repAlloc ca4 pa4`
    (`[sp + 224] = ca4`, `x21 = pa4`), sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_4924_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4924#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  nth_rw 1 [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine Variant1bPlacedBudgetAux2.seq_clean_evs
    (mid := lsmpl.base 333 + 4944#64)
    (P_evs := fun evs1 s2 =>
      memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4924#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4944#64) s1 _ _
    by_cases hca3 : (ca3 == 0#64) = true <;>
      simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4944#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc ca3.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa3, ca3.toNat, 1, st)
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by
        refine Eq.trans ?_ hsp1
        simpa only [wp_norm, arm64_norm] using ‹sf.sp = _›
      have htr_sf : sf.trace = s0.trace := by
        refine Eq.trans ?_ htr1.1
        simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        refine Eq.trans ?_ htr1.2
        simpa only [wp_norm, arm64_norm] using ‹calleeSavedVRegs sf = _›
      refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
  ·
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
    change s2.pc = (blkPl_333).base + 4944#64 at hpc2
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4968#64) s2 _ _
    by_cases hca4 : (ca4 == 0#64) = true <;>
      simp only [hca4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · refine SepWP.mono
        (post := fun sm Pm =>
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim st1 sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0)
        ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩)
      wp_steps_sync_333 ((blkPl_333).base + 4968#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
    · have hevs_all : FreeOnlyEvs (evs1 ++ rustDeallocEvents ca4.toNat 1) :=
        FreeOnlyEvs.append hevs1 (FreeOnlyEvs.singleton 1 ca4.toNat)
      refine SepWP.mono
        (post := fun sm Pm =>
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents (evs1 ++ rustDeallocEvents ca4.toNat 1) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0)
        ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1 ++ rustDeallocEvents ca4.toNat 1, hevs_all, hp, hq⟩)
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa4, ca4.toNat, 1, st1)
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by
        refine Eq.trans ?_ hsp2
        simpa only [wp_norm, arm64_norm] using ‹sf.sp = _›
      have htr_sf : sf.trace = s0.trace := by
        refine Eq.trans ?_ htr2.1
        simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        refine Eq.trans ?_ htr2.2
        simpa only [wp_norm, arm64_norm] using ‹calleeSavedVRegs sf = _›
      wp_steps_sync_333 ((blkPl_333).base + 4968#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        have hst_eq : M.stepEvents (rustDeallocEvents ca4.toNat 1) st1 =
            M.stepEvents (evs1 ++ rustDeallocEvents ca4.toNat 1) st := by
          dsimp only [st1]
          rw [M.stepEvents_append]
        rw [← hsc, hsp2, hst_eq, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done

theorem v3cr_states_from_pb_err_4924_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4924#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_4924_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out ca3 pa3 ca4 pa4 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 hx21_1 htr1

/-- Shared `+4924` error-cleanup path (`lsmpl.base 333 + 4924 -> +4968`):
    deallocates `vecCapPtrDealloc A.repAlloc ca3 pa3` (`x26 = ca3`, `[sp + 176] = pa3`) and
    `vecCapPtrDealloc A.repAlloc ca4 pa4` (`[sp + 224] = ca4`, `x21 = pa4`), sets `x22 = 0`,
    and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_4924_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4924#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_4924_of_dealloc_placed hA.dealloc
    st s0 s1 out ca3 pa3 ca4 pa4 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 hx21_1 htr1

/-- Shared `+4908` error-cleanup path (`lsmpl.base 333 + 4908 -> +4968`) under an explicit
    Block-`333` `__rust_dealloc` contract: deallocates `vecCapPtrDealloc A.repAlloc ca2 pa2`
    (`x28 = ca2`, `x0 = pa2`) and then chains to `+4924`. -/
theorem v3cr_states_from_pb_err_4908_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  nth_rw 1 [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine Variant1bPlacedBudgetAux2.seq_clean_evs
    (mid := lsmpl.base 333 + 4924#64)
    (P_evs := fun evs1 s2 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x26 = ca3 ∧
      s2.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4908#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4924#64) s1 _ _
    by_cases hca2 : (ca2 == 0#64) = true <;>
      simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4924#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
    · apply sepWP_evs_dealloc ca2.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa2, ca2.toNat, 1, st)
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by
        refine Eq.trans ?_ hsp1
        simpa only [wp_norm, arm64_norm] using ‹sf.sp = _›
      have htr_sf : sf.trace = s0.trace := by
        refine Eq.trans ?_ htr1.1
        simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        refine Eq.trans ?_ htr1.2
        simpa only [wp_norm, arm64_norm] using ‹calleeSavedVRegs sf = _›
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx26_2, hx21_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    have h4924 := v3cr_states_from_pb_err_4924_of_sub_placed hdealloc_ok st1 s0 s2
      out ca3 pa3 ca4 pa4 Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx26_2 hx21_2 htr2
    refine SepWP.mono h4924 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hx19_f, hx22_f, htr_f⟩ => ?_
    refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hsp_f, hx19_f, hx22_f, htr_f⟩
    have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
      dsimp only [st1]
      rw [M.stepEvents_append]
    rwa [← hst_eq]

theorem v3cr_states_from_pb_err_4908_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_4908_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx0_1 hx28_1 hx26_1 hx21_1 htr1

/-- Shared `+4908` error-cleanup path (`lsmpl.base 333 + 4908 -> +4968`):
    deallocates `vecCapPtrDealloc A.repAlloc ca2 pa2` (`x28 = ca2`, `x0 = pa2`) and then chains
    to `+4924`. -/
theorem v3cr_states_from_pb_err_4908_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_4908_of_dealloc_placed hA.dealloc
    st s0 s1 out ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx0_1 hx28_1 hx26_1 hx21_1 htr1

/-- Shared `+4884` error-cleanup path (`lsmpl.base 333 + 4884 -> +4968`) under an explicit
    Block-`333` `__rust_dealloc` contract: deallocates all 4 `EkSentCt1Received` vectors
    (`rootKey`, `macKey`, `dk`, `ct1`) when `sendingEk = none`, sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_4884_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4884#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx1_1 : s1.readReg64 .x1 = ca1)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  nth_rw 1 [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine Variant1bPlacedBudgetAux2.seq_clean_evs
    (mid := lsmpl.base 333 + 4908#64)
    (P_evs := fun evs1 s2 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x0 = pa2 ∧
      s2.readReg64 .x28 = ca2 ∧
      s2.readReg64 .x26 = ca3 ∧
      s2.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4884#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4908#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 4908#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
    · apply sepWP_evs_dealloc ca1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by
        refine Eq.trans ?_ hsp1
        simpa only [wp_norm, arm64_norm] using ‹sf.sp = _›
      have htr_sf : sf.trace = s0.trace := by
        refine Eq.trans ?_ htr1.1
        simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        refine Eq.trans ?_ htr1.2
        simpa only [wp_norm, arm64_norm] using ‹calleeSavedVRegs sf = _›
      wp_steps_sync_333 ((blkPl_333).base + 4908#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx0_2, hx28_2, hx26_2, hx21_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    have h4908 := v3cr_states_from_pb_err_4908_of_sub_placed hdealloc_ok st1 s0 s2
      out ca2 pa2 ca3 pa3 ca4 pa4 Rest
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx0_2 hx28_2 hx26_2 hx21_2 htr2
    refine SepWP.mono h4908 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hx19_f, hx22_f, htr_f⟩ => ?_
    refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hsp_f, hx19_f, hx22_f, htr_f⟩
    have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
      dsimp only [st1]
      rw [M.stepEvents_append]
    rwa [← hst_eq]

theorem v3cr_states_from_pb_err_4884_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4884#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx1_1 : s1.readReg64 .x1 = ca1)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_4884_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx1_1 hx22_1 hx0_1 hx28_1 hx26_1 hx21_1 htr1

/-- Shared `+4884` error-cleanup path (`lsmpl.base 333 + 4884 -> +4968`):
    deallocates all 4 `EkSentCt1Received` vectors (`rootKey`, `macKey`, `dk`, `ct1`) when
    `sendingEk = none`, sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_4884_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4884#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx1_1 : s1.readReg64 .x1 = ca1)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_4884_of_dealloc_placed hA.dealloc
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx1_1 hx22_1 hx0_1 hx28_1 hx26_1 hx21_1 htr1

/-- Shared `+1024` error-cleanup path (`lsmpl.base 333 + 1024 -> +4968`) under an explicit
    Block-`333` `__rust_dealloc` contract: deallocates all 4 `EkSentCt1Received` vectors when
    `<PolyEncoder>::from_pb` returns `Err`, sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_1024_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  nth_rw 1 [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine Variant1bPlacedBudgetAux2.seq_clean_evs
    (mid := lsmpl.base 333 + 1044#64)
    (P_evs := fun evs1 s2 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x28 = ca2 ∧
      s2.readReg64 .x26 = ca3 ∧
      s2.readReg64 .x21 = pa4 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 1024#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 1044#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 1044#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
    · apply sepWP_evs_dealloc ca1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by
        refine Eq.trans ?_ hsp1
        simpa only [wp_norm, arm64_norm] using ‹sf.sp = _›
      have htr_sf : sf.trace = s0.trace := by
        refine Eq.trans ?_ htr1.1
        simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
        refine Eq.trans ?_ htr1.2
        simpa only [wp_norm, arm64_norm] using ‹calleeSavedVRegs sf = _›
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
        exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
      · wp_done
  ·
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx28_2, hx26_2, hx21_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    by_cases hca2 : (ca2 == 0#64) = true
    · have hdealloc_ca2 : vecCapPtrDealloc A.repAlloc ca2 pa2 = emp := by
        simp only [vecCapPtrDealloc, hca2, ↓reduceIte]
      rw [hdealloc_ca2]
      simp only [sepConj_emp, emp_sepConj]
      refine Variant1bPlacedBudgetAux2.seq_clean_st
        (mid := lsmpl.base 333 + 4924#64)
        (P_mid := fun s3 =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
          vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
          A.pool lim st1 s3 ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest))
        (Q := fun s3 =>
          s3.sp = s0.sp - 2400#64 ∧
          s3.readReg64 .x19 = out ∧
          s3.readReg64 .x26 = ca3 ∧
          s3.readReg64 .x21 = pa4 ∧
          TraceCalleeSaved s3 s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 1044#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4924#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 4924#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st (fun sc hsc => by rw [← hsc]; exact Entails.of_eq (by sep_ac_rfl)) ?_
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, hx21_3, htr3⟩
        have h4924 := v3cr_states_from_pb_err_4924_of_sub_placed hdealloc_ok st1 s0 s3
          out ca3 pa3 ca4 pa4
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 hx21_3 htr3
        refine SepWP.mono h4924 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hx19_f, hx22_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hsp_f, hx19_f, hx22_f, htr_f⟩
        have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
          dsimp only [st1]
          rw [M.stepEvents_append]
        rw [hst_eq] at hPf
        exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
    · have hca2_f : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine Variant1bPlacedBudgetAux2.seq_clean_st
        (mid := lsmpl.base 333 + 4912#64)
        (P_mid := fun s3 =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
          vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
          vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
          A.pool lim st1 s3 ∗
          ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ Rest))
        (Q := fun s3 =>
          s3.sp = s0.sp - 2400#64 ∧
          s3.readReg64 .x19 = out ∧
          s3.readReg64 .x0 = pa2 ∧
          s3.readReg64 .x28 = ca2 ∧
          s3.readReg64 .x26 = ca3 ∧
          s3.readReg64 .x21 = pa4 ∧
          TraceCalleeSaved s3 s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 1044#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4912#64) s2 _ _
        wp_steps_sync_333 ((blkPl_333).base + 4912#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc]
          exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx0_3, hx28_3, hx26_3, hx21_3, htr3⟩
        refine Variant1bPlacedBudgetAux2.seq_clean_evs
          (mid := lsmpl.base 333 + 4924#64)
          (P_evs := fun evs2 s4 =>
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
            vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
            A.pool lim (M.stepEvents evs2 st1) s4 ∗
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
             (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest))
          (Q := fun s4 =>
            s4.sp = s0.sp - 2400#64 ∧
            s4.readReg64 .x19 = out ∧
            s4.readReg64 .x26 = ca3 ∧
            s4.readReg64 .x21 = pa4 ∧
            TraceCalleeSaved s4 s0)
          ?_ ?_
        · have hdealloc_ca2 :
              vecCapPtrDealloc A.repAlloc ca2 pa2 =
                (A.repAlloc.live pa2 ca2.toNat 1 ∗ memRegion pa2 ca2.toNat) := by
            simp only [vecCapPtrDealloc, hca2_f, Bool.false_eq_true, ↓reduceIte]
          rw [hdealloc_ca2]
          nth_rw 1 [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
            BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
          change s3.pc = (blkPl_333).base + 4912#64 at hpc3
          change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
            ((blkPl_333).base + 4924#64) s3 _ _
          apply sepWP_evs_dealloc ca2.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          simp only [State.setMem_setMem]
          wp_call hdealloc_fo (pa2, ca2.toNat, 1, st1)
          have hsp_sf : sf.sp = s0.sp - 2400#64 := by
            refine Eq.trans ?_ hsp3
            simpa only [wp_norm, arm64_norm] using ‹sf.sp = _›
          have htr_sf : sf.trace = s0.trace := by
            refine Eq.trans ?_ htr3.1
            simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
            refine Eq.trans ?_ htr3.2
            simpa only [wp_norm, arm64_norm] using ‹calleeSavedVRegs sf = _›
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, hsp3, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            exact Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl)
          · wp_done
        · intro evs2 s4 hevs2 hpc4 hrun4 ⟨hsp4, hx19_4, hx26_4, hx21_4, htr4⟩
          let st2 := M.stepEvents evs2 st1
          have h4924 := v3cr_states_from_pb_err_4924_of_sub_placed hdealloc_ok st2 s0 s4
            out ca3 pa3 ca4 pa4
            ((((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
             (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ Rest)
            hsp0_align hpc4 hrun4 hsp4 hx19_4 hx26_4 hx21_4 htr4
          refine SepWP.mono h4924 fun sf Pf _ _ ⟨evs3, hevs3, hPf, hsp_f, hx19_f, hx22_f, htr_f⟩ => ?_
          refine ⟨evs1 ++ evs2 ++ evs3,
            FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3,
            ?_, hsp_f, hx19_f, hx22_f, htr_f⟩
          have hst_eq : M.stepEvents evs3 st2 = M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
            dsimp only [st2, st1]
            rw [M.stepEvents_append, M.stepEvents_append]
          rw [hst_eq] at hPf
          exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

theorem v3cr_states_from_pb_err_1024_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_1024_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx28_1 hx26_1 hx21_1 htr1

/-- Shared `+1024` error-cleanup path (`lsmpl.base 333 + 1024 -> +4968`):
    deallocates all 4 `EkSentCt1Received` vectors when `<PolyEncoder>::from_pb` returns `Err`,
    sets `x22 = 0`, and reaches `+4968`. -/
theorem v3cr_states_from_pb_err_1024_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1024#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = pa1)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx21_1 : s1.readReg64 .x21 = pa4)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4968#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = 0#64 ∧
          TraceCalleeSaved sm s0) :=
  v3cr_states_from_pb_err_1024_of_dealloc_placed hA.dealloc
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx28_1 hx26_1 hx21_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
