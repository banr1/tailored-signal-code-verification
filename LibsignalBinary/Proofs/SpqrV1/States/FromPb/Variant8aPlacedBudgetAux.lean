/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Auxiliary Error-Exit Lemmas for `Variant8aPlacedBudget`

Lifts the Variant 8 (`EkReceivedCt1Sampled`, Block `333`) `+4240` `Err(StateDecode)` exit,
`+4216` / `+4212` / `+2208` `sendingCt1` drop exits, and `+2148` `es`/`ek`/`ct1` cleanup path to
`VmPreserved`, `RustCliAllocBudget M`, and `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (DropProtoPolyEncoderGhost cap_add_one_beq_zero_false chunkedStatesSize dropStack48
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbSavedCells statesFromPbStack
   v1_optProtoPolyEncoderAt_pack_some v1_optProtoPolyEncoderHeap
   v1_optProtoPolyEncoderHeap_extract_w0 v1_optProtoPolyEncoderWordsAt
   v1_optProtoPolyEncoderWordsAt_entails_56 v1_stackAt_encoder_split_dropStack48
   v8_bv_add_add_lit v8_bv_sub_sub_lit v8_merge_stack_1520_56_728
   v8_merge_stack_896_128_496_1520 v8_ucWordsAt)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks
   sepWP_lsBlock_vmPreserved stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp
   stripS_status stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_st
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget seq_clean_evs_lscl seq_clean_lscl_st v1_dealloc_ok_of_dealloc_placed
   v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v8_bv_sub_sub_lit v8_bv_add_add_lit

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

/-! ## 1. Error Exit at `+4240` and `sendingCt1` Drop at `+4216` / `+4212` -/

/-- `VmPreserved`-strengthened shared `Err(StateDecode)` exit at `+4240`
    (`lsmpl.base 333 + 4240 -> +60 -> s0.x30`). -/
theorem v8_err_4240_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8aPlaced.v8_err_4240_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx20_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, by simpa using hsp_f, hcc_f, by simpa using htr_f⟩

theorem v8_err_4240_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4240#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
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
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          A.pool lim st sf ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := v8_err_4240_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1520` (`s0.sp - 880`) and return
    `Err(StateDecode)` (`+4216 -> +4240 -> s0.x30`) from a Block-`271` `withLsCodeLoaded` contract. -/
theorem v8_drop_sendingCt1_4216_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4216#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            Rest ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hex := v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hex)))) ?_
  wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  apply SepWP.pure_elim; intro hw0_cond
  have hmerge := v8_merge_stack_1520_56_728 (s0.sp - 2400#64)
  cases optEnc with
  | none =>
    subst hw0_cond
    dsimp only [v1_optProtoPolyEncoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    refine seq_clean_st
      (mid := lsmpl.base 333 + 4240#64)
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
        (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4216#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4240#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4240#64)
      simp only [State.setMem_setMem]
      have hw_mem := v1_optProtoPolyEncoderWordsAt_entails_56
        (s0.sp - 2400#64 + 1520#64) noneCap w8 w16 w24 w32 w40 w48
      dsimp only [v1_optProtoPolyEncoderWordsAt, noneCap] at hw_mem
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 1520 ∗
           (((s0.sp - 2400#64 + 1520#64) ↦₆₄ noneCap) ∗
            ((s0.sp - 2400#64 + 1520#64 + 8#64) ↦₆₄ w8) ∗
            ((s0.sp - 2400#64 + 1520#64 + 16#64) ↦₆₄ w16) ∗
            ((s0.sp - 2400#64 + 1520#64 + 24#64) ↦₆₄ w24) ∗
            ((s0.sp - 2400#64 + 1520#64 + 32#64) ↦₆₄ w32) ∗
            ((s0.sp - 2400#64 + 1520#64 + 40#64) ↦₆₄ w40) ∗
            ((s0.sp - 2400#64 + 1520#64 + 48#64) ↦₆₄ w48)) ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim st sc ∗ Rest) by
          dsimp only [noneCap]
          sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hw_mem))) ?_
        exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
      have herr := v8_err_4240_placed_budget A lim st (F := F) (ext := ext) s0 s2 out Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2
      refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ => ?_
      refine ⟨[], FreeOnlyEvs.nil, ?_, hsp_f, hcc_f, htr_f⟩
      simpa only [M.stepEvents_nil] using hPf
  | some pbEnc =>
    have hpack := v1_optProtoPolyEncoderAt_pack_some A.repAlloc (s0.sp - 2400#64 + 1520#64) pbEnc
      w0 w8 w16 w24 w32 w40 w48
    have hne := cap_add_one_beq_zero_false hw0_cond
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have h880 : s0.sp - 2400#64 + 1520#64 = s0.sp - 880#64 := by bv_omega
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 271)
      (P_mid := fun sm =>
        protoPolynomialEncoderAt A.repAlloc (s0.sp - 880#64) pbEnc ∗
        A.pool lim st sm ∗
        stackAt (s0.sp - 2400#64) dropStack48 ∗
        (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
         memRegion (s0.sp - 2400#64) 1520 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = s0.sp - 880#64 ∧
        sm.readReg64 .lr = (blkPl_333).base + 4240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s1.readReg64 .x20 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [v1_optProtoPolyEncoderWordsAt, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
      change s1.pc = (blkPl_333).base + 4216#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsmpl.base 271) s1 _ _
      wp_steps_sync_333 (lsmpl.base 271)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), ← h880]
        refine Entails.trans (Entails.of_eq (show _ =
          (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48) ∗
          (A.pool lim st sc ∗ stackAt (s0.sp - 2400#64) dropStack48 ∗
           (memRegion (s0.sp - 2400#64 - 5152#64) 1008 ∗
            memRegion (s0.sp - 2400#64) 1520 ∗
            memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)) by
            dsimp only [v1_optProtoPolyEncoderWordsAt]
            sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (by sep_ac_rfl))
      · wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx0_2, hlr_2, hx19_2, hx20_2, htr2⟩
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hfsp_align
      have hdrop : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          (lsmpl.base 271) (withMemEq s2.mem (dropProtoPolyEncoderSpec M A lim)) :=
        withMemEq_of_withLsCodeLoaded hdrop_cl hcl2
      simp only [withMemEq, dropProtoPolyEncoderSpec] at hdrop
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 4240#64)
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
          (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4240#64) s2 _ _
        rw [show stackAt (s0.sp - 2400#64) dropStack48 = stackAt s2.sp dropStack48 from hsp2 ▸ rfl]
        wp_call hdrop ((⟨s0.sp - 880#64, pbEnc⟩ : DropProtoPolyEncoderGhost), st)
        rw [hsp2]
        rw [hlr_2] at *
        have hevs_w : FreeOnlyEvs w := ‹_›
        have hacp_w : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have hx19_sf : sf.readReg64 .x19 = out := ‹sf.readReg64 .x19 = s2.readReg64 .x19›.trans hx19_2
        have hx20_sf : (sf.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
          rw [‹sf.readReg64 .x20 = s2.readReg64 .x20›, hx20_2, hx20_1]
        have htr_sf : sf.trace = s0.trace := hacp_w.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
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
            (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
            TraceCalleeSaved sm s0)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          have h7552 : s0.sp - 2400#64 - 5152#64 = s0.sp - 7552#64 := by bv_omega
          rw [← hsc, v1_stackAt_encoder_split_dropStack48 (s0.sp - 2400#64), h7552, ← h880]
          dsimp only [protoPolynomialEncoderSize]
          simp only [arm64_norm] at hmerge ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 1520 ∗
             memRegion (s0.sp - 880#64) 56 ∗
             memRegion (s0.sp - 824#64) 728) ∗
            (memRegion (s0.sp - 7552#64) 1008 ∗
             stackAt (s0.sp - 2400#64) dropStack48 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool lim (M.stepEvents w st) sc ∗ Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hmerge) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · intro evs s3 hevs hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, htr3⟩
        have herr := v8_err_4240_placed_budget A lim (M.stepEvents evs st) (F := F) (ext := ext)
          s0 s3 out Rest hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 htr3
        refine SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ =>
          ⟨evs, hevs, hPf, hsp_f, hcc_f, htr_f⟩

theorem v8_drop_sendingCt1_4216_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4216#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_sendingCt1_4216_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 htr1

/-- Drop `Option<ProtoPolynomialEncoder>` at `fsp + 1520` (`s0.sp - 880`) and return
    `Err(StateDecode)` (`+4216 -> +4240 -> s0.x30`). -/
theorem v8_drop_sendingCt1_4216_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4216#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : (s1.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_sendingCt1_4216_of_dealloc_placed hA.dealloc
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 htr1

/-- Error exit at `+4212` (`lsmpl.base 333 + 4212 -> +4216 -> s0.x30`): sets `x20 = 0`, drops
    `sendingCt1`, and returns `Err(StateDecode)` from a Block-`271` contract. -/
theorem v8_drop_sendingCt1_4212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 4216#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st sm ∗ Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [spqrErrorByte, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 4212#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4216#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 4216#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    exact v8_drop_sendingCt1_4216_of_sub_placed (F := F) hdrop_cl st s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2

theorem v8_drop_sendingCt1_4212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_sendingCt1_4212_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1

/-- Error exit at `+4212` (`lsmpl.base 333 + 4212 -> +4216 -> s0.x30`): sets `x20 = 0`, drops
    `sendingCt1`, and returns `Err(StateDecode)`. -/
theorem v8_drop_sendingCt1_4212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_sendingCt1_4212_of_dealloc_placed hA.dealloc
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1

/-! ## 2. Error Cleanup for `uc` (`es`, `ek`, `ct1`, `auth`) + `sendingCt1` (`+2100 -> +2148 -> +2208 -> +4216`) -/

/-- Error transition `+2208 -> +4216 -> s0.x30` from a Block-`271` contract. -/
theorem v8_drop_sendingCt1_2208_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2208#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine seq_clean_lscl_st hcl1
    (mid := lsmpl.base 333 + 4216#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 1520 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st sm ∗ Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [spqrErrorByte, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 2208#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4216#64) s1 _ _
    wp_steps_sync_333 ((blkPl_333).base + 4216#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    exact v8_drop_sendingCt1_4216_of_sub_placed (F := F) hdrop_cl st s0 s2 out optEnc
      w0 w8 w16 w24 w32 w40 w48 Rest hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 htr2

theorem v8_drop_sendingCt1_2208_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2208#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_sendingCt1_2208_of_sub_placed
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1

/-- Error transition `+2208 -> +4216 -> s0.x30`: sets `x20 = 0`, drops `sendingCt1` at
    `fsp + 1520`, and returns `Err(StateDecode)`. -/
theorem v8_drop_sendingCt1_2208_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2208#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1520 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_sendingCt1_2208_of_dealloc_placed hA.dealloc
    st s0 s1 out optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1

/-- Cleanup `es` (`x26 = u8`, `[fsp+904] = u16`), `ek` (`[fsp+920] = u32`, `[fsp+928] = u40`),
    `ct1` (`[fsp+944] = u56`, `[fsp+952] = u64`), and `sendingCt1` at `fsp + 1520..1576` from
    explicit Block-`333` `__rust_dealloc` and Block-`271` drop-glue contracts. -/
theorem v8_drop_uc_and_sendingCt1_2148_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State)
    (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2148#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗
        vecCapPtrDealloc A.repAlloc u32 u40 ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 2168#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 896 ∗
      v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
      memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A.repAlloc u32 u40 ∗
      vecCapPtrDealloc A.repAlloc u56 u64 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 2148#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2168#64) s1 _ _
    by_cases hc1 : (u8 == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 2168#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc u8.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (u16, u8.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs_lscl hcl2
      (mid := lsmpl.base 333 + 2188#64)
      (P_evs := fun evs2 s3 =>
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗
        A.pool lim (M.stepEvents evs2 st1) s3 ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
      change s2.pc = (blkPl_333).base + 2168#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 2188#64) s2 _ _
      by_cases hc2 : (u32 == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 2188#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · apply sepWP_evs_dealloc u32.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (u40, u32.toNat, 1, st1)
        have hacp2 : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
        have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        refine align_pre_st (by rw [hsp2]; simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, htr3⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs_lscl hcl3
        (mid := lsmpl.base 333 + 2208#64)
        (P_evs := fun evs3 s4 =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 1520 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs3 st2) s4 ∗
          Rest)
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧
          s4.readReg64 .x19 = out ∧
          TraceCalleeSaved s4 s0)
        ?_ ?_
      · dsimp only [v8_ucWordsAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
          BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
        change s3.pc = (blkPl_333).base + 2188#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 2208#64) s3 _ _
        have hm := v8_merge_stack_896_128_496_1520 (s0.sp - 2400#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        by_cases hc3 : (u56 == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps_sync_333 ((blkPl_333).base + 2208#64)
          simp only [State.setMem_setMem]
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 896 ∗
               v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
                 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
               memRegion (s0.sp - 2400#64 + 1024#64) 496) ∗
              (memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
               v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
               memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               A.pool lim st2 sc ∗ Rest) by
                 dsimp only [v8_ucWordsAt]; simp only [arm64_norm]; sep_ac_rfl)) ?_
            exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
          · wp_done
        · apply sepWP_evs_dealloc u56.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          simp only [State.setMem_setMem]
          wp_call hdealloc_fo (u64, u56.toNat, 1, st2)
          have hacp3 : AllocCallPreserved s3 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
          have htr_sf : sf.trace = s0.trace := hacp3.2.1.trans htr3.1
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp3]
            refine Entails.trans (Entails.of_eq (show _ =
              (memRegion (s0.sp - 2400#64) 896 ∗
               v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
                 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
               memRegion (s0.sp - 2400#64 + 1024#64) 496) ∗
              (memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
               stackAt (s0.sp - 2400#64) allocHookStack ∗
               v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
               v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
               memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
               A.pool lim (M.stepEvents (rustDeallocEvents u56.toNat 1) st2) sc ∗ Rest) by
                 dsimp only [v8_ucWordsAt]; simp only [arm64_norm]; sep_ac_rfl)) ?_
            exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
          · wp_done
      · intro evs3 s4 hevs3 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, htr4⟩
        let st3 := M.stepEvents evs3 st2
        have h2208 := v8_drop_sendingCt1_2208_of_sub_placed (F := F) hdrop_cl st3 s0 s4 out optEnc
          w0 w8 w16 w24 w32 w40 w48 Rest hcl4 hsp0_align hpc4 hrun4 hsp4 hx19_4 htr4
        refine SepWP.mono h2208 fun sf Pf _ _ ⟨evs4, hevs4, hPf, hsp_f, hcc_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4,
          FreeOnlyEvs.append (FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3) hevs4,
          ?_, hsp_f, hcc_f, htr_f⟩
        have hst_eq : M.stepEvents evs4 st3 = M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4) st := by
          dsimp only [st3, st2, st1]
          rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
        rwa [← hst_eq]

theorem v8_drop_uc_and_sendingCt1_2148_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State)
    (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2148#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_uc_and_sendingCt1_2148_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

/-- Cleanup `es`, `ek`, `ct1`, and `sendingCt1`, returning `Err(StateDecode)`
    (`+2148 -> +2208 -> +4216 -> s0.x30`). -/
theorem v8_drop_uc_and_sendingCt1_2148_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2148#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx26_1 : s1.readReg64 .x26 = u8)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        vecCapPtrDealloc A.repAlloc u56 u64 ∗ A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v8_drop_uc_and_sendingCt1_2148_of_dealloc_placed hA.dealloc
    st s0 s1 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudgetAux
