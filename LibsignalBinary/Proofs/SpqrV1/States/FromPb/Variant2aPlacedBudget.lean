/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 (`KeysSampled`) — Part A

Relocatable Block-`333` error-cleanup paths (`+3872`, `+3936 -> ret`) for `uc` and
`sendingHdr` under `RustCliAllocBudget M` and `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt sp_sub_2400_align spqrErrorByte
   stackAt_encoderFromPb_split_allocHook statesFromPbSavedCells statesFromPbStack
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_merge_stack_192_216_224_1496 v1_optProtoAuthHeap
   v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt v1_shl8_extract_0_8)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropProtoPolyEncoderSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 entails_pre_st)

export Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget EncoderFromPbPlacedOkExt encoder_from_pb_ok_of_alloc_placed
   seq_clean_lscl seq_clean_lscl_st)
export Variant2aPlacedBudgetAux
  (seq_clean_evs_lscl withMemEq_of_withLsCodeLoaded
   v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed
   v1_drop_glue_proto_poly_encoder_ok_at_statesFromPb_placed
   v1_drop_glue_proto_poly_encoder_mem_ok_of_dealloc_placed)
export Variant2aPlacedBudgetAux
  (v1_drop_glue_proto_poly_encoder_mem_ok_at_statesFromPb_placed
   v1_encoder_from_pb_ok_at_statesFromPb_placed
   v1_encoder_from_pb_mem_ok_at_statesFromPb_placed
   v1_dealloc_ok_of_dealloc_placed v1_dealloc_ok_at_statesFromPb_placed)
export Variant2aPlacedBudgetAux
  (v1_dealloc_ok_of_placedHooks v1_deallocFreeOnly_ok_at_statesFromPb_placed
   v1_err_5940_placed v1_err_5940_placed_budget v1_drop_sendingHdr_4332_of_sub_placed)
export Variant2aPlacedBudgetAux
  (v1_drop_sendingHdr_4332_of_dealloc_placed v1_drop_sendingHdr_4332_placed
   v1_drop_sendingHdr_4204_of_sub_placed v1_drop_sendingHdr_4204_of_dealloc_placed
   v1_drop_sendingHdr_4204_placed)

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

/-! ## Error Cleanup for `uc` (`ek`, `dk`, `auth`) + `sendingHdr` (`+3872 -> +3936 -> +4332`) -/

/-- Cleanup `ek`, `dk`, and `sendingHdr` from `+3936` (`+3936 -> s0.x30`) under explicit
    Block-`333` `__rust_dealloc` and Block-`271` drop-glue contracts. -/
theorem v1_drop_uc_and_sendingHdr_3936_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
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
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine seq_clean_evs_lscl hcl1
    (mid := lsmpl.base 333 + 3956#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      memRegion (s0.sp - 2400#64) 192 ∗
      ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
      memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
      memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧
      s2.readReg64 .x19 = out ∧
      s2.readReg64 .x20 = cap_ek ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    change s1.pc = (blkPl_333).base + 3936#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3956#64) s1 _ _
    by_cases hc_ek : (cap_ek == 0#64) = true <;>
      simp only [hc_ek, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 3956#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
    · apply sepWP_evs_dealloc cap_ek.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo (ptr_ek, cap_ek.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs_lscl hcl2
      (mid := lsmpl.base 333 + 4332#64)
      (P_evs := fun evs2 s3 =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1496 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim (M.stepEvents evs2 st1) s3 ∗
        Rest)
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧
        s3.readReg64 .x19 = out ∧
        (s3.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
        TraceCalleeSaved s3 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, spqrErrorByte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
      change s2.pc = (blkPl_333).base + 3956#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4332#64) s2 _ _
      by_cases hc_dk : (cap_dk == 0#64) = true <;>
        simp only [hc_dk, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 4332#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
          have hm := v1_merge_stack_192_216_224_1496 (s0.sp - 2400#64) w192 ptr_dk cap_dk
          simp only [arm64_norm] at hm ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 192 ∗
             ((s0.sp - 2208#64) ↦₆₄ w192) ∗
             memRegion (s0.sp - 2200#64) 16 ∗
             ((s0.sp - 2184#64) ↦₆₄ ptr_dk) ∗
             ((s0.sp - 2176#64) ↦₆₄ cap_dk) ∗
             memRegion (s0.sp - 2168#64) 1264) ∗
            (memRegion (s0.sp - 7552#64) 1056 ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool lim st1 sc ∗ Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
      · apply sepWP_evs_dealloc cap_dk.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (ptr_dk, cap_dk.toNat, 1, st1)
        have hacp2 : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
        wp_steps_sync_333 ((blkPl_333).base + 4332#64)
        simp only [State.setMem_setMem]
        refine entails_pre_st ?_ ?_
        · intro sc hsc
          rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
          have hm := v1_merge_stack_192_216_224_1496 (s0.sp - 2400#64)
            (s2.readReg64 .x22) ptr_dk cap_dk
          simp only [arm64_norm] at hm ⊢
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion (s0.sp - 2400#64) 192 ∗
             ((s0.sp - 2208#64) ↦₆₄ s2.readReg64 .x22) ∗
             memRegion (s0.sp - 2200#64) 16 ∗
             ((s0.sp - 2184#64) ↦₆₄ ptr_dk) ∗
             ((s0.sp - 2176#64) ↦₆₄ cap_dk) ∗
             memRegion (s0.sp - 2168#64) 1264) ∗
            (memRegion (s0.sp - 7552#64) 1056 ∗
             stackAt (s0.sp - 2400#64) allocHookStack ∗
             v1_optProtoPolyEncoderWordsAt (s0.sp - 904#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 848#64) 752 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool lim (M.stepEvents (rustDeallocEvents cap_dk.toNat 1) st1) sc ∗
             Rest) by sep_ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hm) (Entails.of_eq (by sep_ac_rfl))
        · wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx26_3, htr3⟩
      let st2 := M.stepEvents evs2 st1
      have h4332 := v1_drop_sendingHdr_4332_of_sub_placed (F := F) hdrop_cl st2 s0 s3 out optEnc
        w0 w8 w16 w24 w32 w40 w48 Rest hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
      refine SepWP.mono h4332 fun sf Pf _ _ ⟨evs3, hevs3, hPf, hsp_f, hcc_f, htr_f⟩ => ?_
      refine ⟨evs1 ++ evs2 ++ evs3,
        FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3, ?_, hsp_f, hcc_f, htr_f⟩
      have hst_eq : M.stepEvents evs3 st2 = M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
        dsimp only [st2, st1]
        rw [M.stepEvents_append, M.stepEvents_append]
      rwa [← hst_eq]

theorem v1_drop_uc_and_sendingHdr_3936_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
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
          sf.trace = s0.trace) :=
  v1_drop_uc_and_sendingHdr_3936_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx9_1 htr1

/-- Cleanup `ek` (`x9 = ptr_ek`, `x20 = cap_ek`), `dk` (`[fsp+216] = ptr_dk`, `[fsp+224] = cap_dk`),
    and `sendingHdr` at `fsp + 1496..1552`, returning `Err(StateDecode)` (`+3936 -> s0.x30`). -/
theorem v1_drop_uc_and_sendingHdr_3936_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
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
          sf.trace = s0.trace) :=
  v1_drop_uc_and_sendingHdr_3936_of_dealloc_placed hA.dealloc
    st s0 s1 out cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx9_1 htr1

/-- Cleanup `optAuth`, `ek`, `dk`, and `sendingHdr` from `+3872` (`+3872 -> +3936 -> s0.x30`)
    under explicit Block-`333` `__rust_dealloc` and Block-`271` drop-glue contracts. -/
theorem v1_drop_uc_and_sendingHdr_3872_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hdrop_cl : subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec M A lim)))
    (st : M.σ) (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (hx25_1 : s1.readReg64 .x25 = u56)
    (hx28_1 : s1.readReg64 .x28 = u64)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
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
  cases optAuth with
  | none =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim
    intro hu56
    subst hu56
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 333 + 3936#64)
      (P_mid := fun s2 =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
        A.pool lim st s2 ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = cap_ek ∧
        s2.readReg64 .x9 = ptr_ek ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hx25_1 ⊢
      change s1.pc = (blkPl_333).base + 3872#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3936#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 3936#64)
      simp only [State.setMem_setMem]
      refine align_pre_st (by sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, htr2⟩
      exact v1_drop_uc_and_sendingHdr_3936_of_sub_placed (F := F) hdealloc_ok hdrop_cl st s0 s2 out
        cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx9_2 htr2
  | some auth =>
    dsimp only [v1_optProtoAuthHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim
    rintro ⟨hu56, _, _⟩
    have hcmn : (u56 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hu56)
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
    have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
      subroutine_ok_deallocFreeOnly hdealloc_ok
    simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
    have hd_root := vecU8Payload_entails_dealloc A.repAlloc u56 u64 auth.rootKey
    have hd_mac := vecU8Payload_entails_dealloc A.repAlloc u80 u88 auth.macKey
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A.repAlloc u56 u64 auth.rootKey ∗
      vecU8Payload A.repAlloc u80 u88 auth.macKey ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 192 ∗
       ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
       memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
       ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
       memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
       vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
       A.pool lim st s1 ∗
       Rest) by sep_ac_rfl))
      (sepConj_mono hd_root (sepConj_mono_left hd_mac))) ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    wp_simp_pre [sepConj_assoc]
    refine seq_clean_evs_lscl hcl1
      (mid := lsmpl.base 333 + 3908#64)
      (P_evs := fun evs1 s2 =>
        vecCapPtrDealloc A.repAlloc u80 u88 ∗
        memRegion (s0.sp - 2400#64 - 5152#64) 1056 ∗
        stackAt (s0.sp - 2400#64) allocHookStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗
        Rest)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = cap_ek ∧
        s2.readReg64 .x9 = ptr_ek ∧
        s2.readReg64 .x23 = u80 ∧
        s2.readReg64 .x24 = u88 ∧
        TraceCalleeSaved s2 s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
      change s1.pc = (blkPl_333).base + 3872#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3908#64) s1 _ _
      by_cases hc_r : (u56 == 0#64) = true <;>
        simp only [hc_r, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil
        simp only [M.stepEvents_nil]
        wp_steps_sync_333 ((blkPl_333).base + 3908#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · apply sepWP_evs_dealloc u56.toNat 1
        wp_steps_sync_333 (lsρ spqrRustDeallocSym)
        simp only [State.setMem_setMem]
        wp_call hdealloc_fo (u64, u56.toNat, 1, st)
        have hacp1 : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
        have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
        wp_steps_sync_333 ((blkPl_333).base + 3908#64)
        simp only [State.setMem_setMem]
        refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
        wp_done
    · intro evs1 s2 hevs1 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx20_2, hx9_2, hx23_2, hx24_2, htr2⟩
      let st1 := M.stepEvents evs1 st
      refine seq_clean_evs_lscl hcl2
        (mid := lsmpl.base 333 + 3936#64)
        (P_evs := fun evs2 s3 =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 192 ∗
          ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
          memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
          memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
          vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
          A.pool lim (M.stepEvents evs2 st1) s3 ∗
          Rest)
        (Q := fun s3 =>
          s3.sp = s0.sp - 2400#64 ∧
          s3.readReg64 .x19 = out ∧
          s3.readReg64 .x20 = cap_ek ∧
          s3.readReg64 .x9 = ptr_ek ∧
          TraceCalleeSaved s3 s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
          BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
        change s2.pc = (blkPl_333).base + 3908#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3936#64) s2 _ _
        by_cases hc_m : (u80 == 0#64) = true <;>
          simp only [hc_m, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil
          simp only [M.stepEvents_nil]
          wp_steps_sync_333 ((blkPl_333).base + 3936#64)
          simp only [State.setMem_setMem]
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
            simp only [arm64_norm]
            exact Entails.of_eq (by sep_ac_rfl)
          · wp_done
        · apply sepWP_evs_dealloc u80.toNat 1
          wp_steps_sync_333 (lsρ spqrRustDeallocSym)
          simp only [State.setMem_setMem]
          wp_call hdealloc_fo (u88, u80.toNat, 1, st1)
          have hacp2 : AllocCallPreserved s2 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
          have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
            ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
          wp_steps_sync_333 ((blkPl_333).base + 3936#64)
          simp only [State.setMem_setMem]
          refine entails_pre_st ?_ ?_
          · intro sc hsc
            rw [← hsc, stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), hsp2]
            simp only [arm64_norm]
            exact Entails.of_eq (by sep_ac_rfl)
          · wp_done
      · intro evs2 s3 hevs2 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx20_3, hx9_3, htr3⟩
        let st2 := M.stepEvents evs2 st1
        have h3936 := v1_drop_uc_and_sendingHdr_3936_of_sub_placed (F := F) hdealloc_ok hdrop_cl
          st2 s0 s3 out cap_ek ptr_ek cap_dk ptr_dk w192 optEnc w0 w8 w16 w24 w32 w40 w48 Rest
          hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx9_3 htr3
        refine SepWP.mono h3936 fun sf Pf _ _ ⟨evs3, hevs3, hPf, hsp_f, hcc_f, htr_f⟩ => ?_
        refine ⟨evs1 ++ evs2 ++ evs3,
          FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3, ?_, hsp_f, hcc_f, htr_f⟩
        have hst_eq : M.stepEvents evs3 st2 = M.stepEvents (evs1 ++ evs2 ++ evs3) st := by
          dsimp only [st2, st1]
          rw [M.stepEvents_append, M.stepEvents_append]
        rwa [← hst_eq]

theorem v1_drop_uc_and_sendingHdr_3872_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (hx25_1 : s1.readReg64 .x25 = u56)
    (hx28_1 : s1.readReg64 .x28 = u64)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
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
          sf.trace = s0.trace) :=
  v1_drop_uc_and_sendingHdr_3872_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    (v1_drop_glue_proto_poly_encoder_ok_of_dealloc_placed hdealloc)
    st s0 s1 out cap_ek ptr_ek cap_dk ptr_dk w192
    optAuth u56 u64 u72 u80 u88 u96
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx9_1 hx25_1 hx28_1 hx23_1 hx24_1 htr1

/-- Cleanup `optAuth` (`x25 = u56, x28 = u64, x23 = u80, x24 = u88`), `ek`, `dk`, and `sendingHdr`,
    returning `Err(StateDecode)` (`+3872 -> +3936 -> s0.x30`). -/
theorem v1_drop_uc_and_sendingHdr_3872_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out cap_ek ptr_ek cap_dk ptr_dk w192 : BitVec 64)
    (optAuth : Option ProtoAuthenticator) (u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optEnc : Option ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = cap_ek)
    (hx9_1 : s1.readReg64 .x9 = ptr_ek)
    (hx25_1 : s1.readReg64 .x25 = u56)
    (hx28_1 : s1.readReg64 .x28 = u64)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 192 ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
        memRegion (s0.sp - 2400#64 + 200#64) 16 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ cap_dk) ∗
        memRegion (s0.sp - 2400#64 + 232#64) 1264 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc optEnc w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        vecCapPtrDealloc A.repAlloc cap_dk ptr_dk ∗
        v1_optProtoAuthHeap A.repAlloc optAuth u56 u64 u72 u80 u88 u96 ∗
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
          sf.trace = s0.trace) :=
  v1_drop_uc_and_sendingHdr_3872_of_dealloc_placed hA.dealloc
    st s0 s1 out cap_ek ptr_ek cap_dk ptr_dk w192
    optAuth u56 u64 u72 u80 u88 u96
    optEnc w0 w8 w16 w24 w32 w40 w48 Rest
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx9_1 hx25_1 hx28_1 hx23_1 hx24_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
