/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part A

Lifts the relocatable Variant 6 `+10396` error epilogue, inline `ProtoPolynomialDecoder`
deallocation loop (`+10316..+10396`, `FreeOnlyEvs`), and `+1464` header-load steps to
`VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop
  (add_24_add_8 cap_add_one_beq_zero_false cap_mul_24 chunkedStatesSize cons_len_mul
   header_cells_entails_memRegion_24 none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24 ofNat_succ_eq_add_one
   optProtoInnerStateSize sep_pull_body sep_push_body sep_rejoin_loop tail_len_mul_lt
   vecCapPtrDealloc vecU8_entails_capPtr_dealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v6hr_Regs1508 v6hr_Saved10324Preserved v6hr_headersAt v6hr_lowStackAt)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs seq_clean_st subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (FromPbAllocHooksBudget v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_dealloc_placed
   v1_dealloc_ok_of_placedHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Error Epilogue (`+10396`) & Relocatable Budget Callee Contracts -/

/-- `VmPreserved`-strengthened Variant 6 `Err(err)` exit at `+10396` (`+10396 -> +60 -> s0.x30`). -/
theorem v6hr_states_from_pb_err_10396_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64)
    (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx25_1 : (s1.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
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
    (Variant6aPlaced.v6hr_states_from_pb_err_10396_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx25_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem v6hr_states_from_pb_err_10396_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64)
    (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx25_1 : (s1.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
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
  have hwp := v6hr_states_from_pb_err_10396_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 err (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx25_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

theorem v6hr_sub_ok_dealloc_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_dealloc_placed hdealloc

theorem v6hr_sub_ok_dealloc_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_of_placedHooks hA

theorem v6hr_sub_ok_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

theorem v6hr_sub_ok_deallocFreeOnly_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
  subroutine_ok_deallocFreeOnly (v6hr_sub_ok_dealloc_placed hA)

/-! ## 2. `ProtoPolynomialDecoder` Deallocation Loop (`+10316..+10396`) -/

theorem v6hr_proto_decoder_dealloc_body_10348_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = cnt →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10336#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s sm ∧
            sm.readReg64 .x23 = cnt ∧
            sm.readReg64 .x20 = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hx23 hx20
  rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
  change s.pc = (blkPl_333).base + 10348#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10336#64) s _ _
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10336#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm ∧
          sm.readReg64 .x23 = cnt ∧
          sm.readReg64 .x20 = cur + 8#64) := by
      wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10336#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm ∧
          sm.readReg64 .x23 = cnt ∧
          sm.readReg64 .x20 = cur + 8#64) := by
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine align_pre_st (by rw [hsp]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
      wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

theorem v6hr_proto_decoder_dealloc_body_10348_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = cnt →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10336#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s sm ∧
            sm.readReg64 .x23 = cnt ∧
            sm.readReg64 .x20 = cur + 8#64) :=
  v6hr_proto_decoder_dealloc_body_10348_of_sub_placed hA.dealloc_ok
    s0 fsp out ptsPtr ptsCap x25_val hfsp_align

theorem v6hr_proto_decoder_dealloc_body_10348_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = cnt →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10336#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s sm ∧
            sm.readReg64 .x23 = cnt ∧
            sm.readReg64 .x20 = cur + 8#64) :=
  v6hr_proto_decoder_dealloc_body_10348_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    s0 fsp out ptsPtr ptsCap x25_val hfsp_align

theorem v6hr_proto_decoder_dealloc_loop_10348_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10372#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s sm) := by
  have hbody := v6hr_proto_decoder_dealloc_body_10348_of_sub_placed hdealloc_ok
    s0 fsp out ptsPtr ptsCap x25_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hx23 hx20
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := lsmpl.base 333 + 10336#64)
      (P_evs := fun evs_hd sm =>
        memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗
          (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm =>
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
        AllocCallPreserved s sm ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x20 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame)
        hpc hrun hpres hx23 hx20) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx23_1, hx20_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx23_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx21_1, hx28_1, hx25_1, htrace_1⟩
      change s1.pc = (blkPl_333).base + 10336#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10372#64) s1 _ _
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10372#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s1 sm) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hpres_f, hacp_f⟩ =>
        ⟨evs_hd, hevs_hd, hp, hpres_f, hacp1.trans hacp_f⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx23_1
      refine seq_clean_st (mid := lsmpl.base 333 + 10348#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
            A.pool lim (M.stepEvents evs_hd st) sm ∗ stackAt fsp allocHookStack ∗
            (memRegion cur 24 ∗ Frame))
        (Q := fun sm =>
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s1 sm ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x20 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx21_1, hx28_1, hx25_1, htrace_1⟩
        change s1.pc = (blkPl_333).base + 10336#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10348#64) s1 _ _
        rw [sep_push_body]
        wp_steps
        rw [add_24_add_8]
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hacp2, hx23_2, hx20_2⟩
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx23_2 hx20_2
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hpres_f, hacp_tl⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hpres_f,
          (hacp1.trans hacp2).trans hacp_tl⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit,
          ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v6hr_proto_decoder_dealloc_loop_10348_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10372#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s sm) :=
  v6hr_proto_decoder_dealloc_loop_10348_of_sub_placed hA.dealloc_ok
    s0 fsp out ptsPtr ptsCap x25_val hfsp_align

theorem v6hr_proto_decoder_dealloc_loop_10348_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10372#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs : List AllocEvent,
            FreeOnlyEvs evs ∧
            (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s sm) :=
  v6hr_proto_decoder_dealloc_loop_10348_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    s0 fsp out ptsPtr ptsCap x25_val hfsp_align

/-- Variant 6 `ProtoPolynomialDecoder` inline deallocation at `+10324 -> +10396` under an explicit
    Block-`333` `__rust_dealloc` contract: deallocates all `Vec<u8>` elements in `pts` and the
    `pts` buffer itself (`FreeOnlyEvs`), then reaches `+10396`. -/
theorem v6hr_states_from_pb_dealloc_proto_decoder_10324_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10324#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  have hloop := v6hr_proto_decoder_dealloc_loop_10348_of_sub_placed hdealloc_ok
    s0 fsp out ptsPtr ptsCap x25_val hfsp_align
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs (mid := lsmpl.base 333 + 10372#64)
    (P_evs := fun evs1 sm =>
      (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
      AllocCallPreserved s sm)
    ?_ ?_
  · cases pts with
    | nil =>
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx23 ⊢
      change s.pc = (blkPl_333).base + 10324#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10372#64) s _ _
      wp_steps
      refine align_pre_st (by simp only [wp_norm, arm64_norm]) ?_
      wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
      refine seq_clean_st (mid := lsmpl.base 333 + 10348#64)
        (P_mid := fun sm =>
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr (bs :: tl) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
             Frame))
        (Q := fun sm =>
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x20 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
        change s.pc = (blkPl_333).base + 10324#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10348#64) s _ _
        wp_steps
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hacp_loop, hx23_loop, hx20_loop⟩
        have hl := hloop (bs :: tl) ptsPtr st s_loop
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
            Frame)
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx23_loop hx20_loop
        refine SepWP.mono hl fun sm _Pm _ _ ⟨evs1, hevs1, hp, hpres_m, hacp_m⟩ => ?_
        refine ⟨evs1, hevs1, ?_, hpres_m, hacp_loop.trans hacp_m⟩
        have hsplit : ptsCap.toNat * 24 =
            (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion ptsPtr ((bs :: tl).length * 24) ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
            A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
          rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
            ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by sep_ac_rfl)
        refine Entails.trans hp ?_
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame by
              sep_ac_rfl))
          (sepConj_mono_left hjoin)
  · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hpres3, hacp3⟩
    rcases hpres3 with ⟨hsp_3, hx19_3, hx21_3, hx28_3, hx25_3, htrace_3⟩
    change s3.pc = (blkPl_333).base + 10372#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10396#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx28_3 ⊢
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10396#64) s3
          (A.pool lim (M.stepEvents evs1 st) s3 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr 0#64 x25_val ∧
            AllocCallPreserved s3 sm) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hpres_f, hacp_f⟩ =>
        ⟨evs1, hevs1, hp, hpres_f, hacp3.trans hacp_f⟩
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10396#64) s3
          ((A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
            A.pool lim (M.stepEvents evs1 st) s3 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim
                (M.stepEvents (rustDeallocEvents (ptsCap.toNat * 24) 8) (M.stepEvents evs1 st))
                sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
            AllocCallPreserved s3 sm) := by
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s3 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp_3]; sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hfin fun sm _Pm _ _ ⟨hp, hpres_f, hacp_f⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents (ptsCap.toNat * 24) 8,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (ptsCap.toNat * 24)),
        ?_, hpres_f, hacp3.trans hacp_f⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hp

theorem v6hr_states_from_pb_dealloc_proto_decoder_10324_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10324#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm) :=
  v6hr_states_from_pb_dealloc_proto_decoder_10324_of_sub_placed hA.dealloc_ok
    st s0 s fsp out ptsPtr ptsCap x25_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx23

theorem v6hr_states_from_pb_dealloc_proto_decoder_10324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10324#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm) :=
  v6hr_states_from_pb_dealloc_proto_decoder_10324_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s fsp out ptsPtr ptsCap x25_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx23

/-- `VmPreserved`-strengthened `+10316 -> +10396` branch when `receivingEk = none` (`ptsCap = noneCap`). -/
theorem v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x25_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr noneCap x25_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr noneCap x25_val ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm) := by
  rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
  dsimp only [noneCap] at hx28
  change s.pc = (blkPl_333).base + 10316#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10396#64) s P _
  wp_steps
  wp_done

theorem v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x25_val : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr noneCap x25_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      (A.pool lim st s ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool lim st sm ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr noneCap x25_val ∧
        VmPreserved s sm ∧
        AllocCallPreserved s sm) := by
  have hwp := v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed (ext := ext)
    s0 s fsp out ptsPtr x25_val (A.pool lim st s ∗ Frame) hpc hrun hpres
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hpres_m, hvm, hacp⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hpres_m, hvm, hacp⟩

theorem v6hr_states_from_pb_dealloc_some_proto_decoder_10316_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm) := by
  refine seq_clean_st (mid := lsmpl.base 333 + 10324#64)
    (P_mid := fun sm =>
      (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
      AllocCallPreserved s sm ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
    have hne : ¬((ptsCap + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false (by omega)
    change s.pc = (blkPl_333).base + 10316#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10324#64) s _ _
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hacp1, hx23_1⟩
    have h10324 := v6hr_states_from_pb_dealloc_proto_decoder_10324_of_sub_placed hdealloc_ok
      st s0 s1 fsp out ptsPtr ptsCap x25_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1
    exact SepWP.mono h10324 fun _ _ _ _ ⟨evs, hevs, hp, hpres_f, hacp_f⟩ =>
      ⟨evs, hevs, hp, hpres_f, hacp1.trans hacp_f⟩

theorem v6hr_states_from_pb_dealloc_some_proto_decoder_10316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm) :=
  v6hr_states_from_pb_dealloc_some_proto_decoder_10316_of_sub_placed hA.dealloc_ok
    st s0 s fsp out ptsPtr ptsCap x25_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx23

theorem v6hr_states_from_pb_dealloc_some_proto_decoder_10316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          AllocCallPreserved s sm) :=
  v6hr_states_from_pb_dealloc_some_proto_decoder_10316_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s fsp out ptsPtr ptsCap x25_val pts Frame
    hfsp_align hpts_le hpts_cap_lt hpc hrun hpres hx23

/-! ## 3. Header Load Steps (`+1464 -> +1520` / `+3760`) -/

private theorem v6hr_Regs1508_of_stripS {keep : BitVec 64 → Bool} {s0 sm : State}
    {out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 : BitVec 64}
    {d112 d116 : BitVec 32} {w120 : BitVec 64}
    (h : v6hr_Regs1508 s0 (ProofLib.stripS keep sm) out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88
      w104 d112 d116 w120) :
    v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120 := by
  simpa [v6hr_Regs1508, TraceCalleeSaved] using h

/-- `VmPreserved`-strengthened Variant 6 header load at `+1464 -> +3760` (`receivingEk = none`). -/
theorem v6hr_load_headers_1464_none_to_3760_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w104 d112 d116 w120) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6aPlaced.v6hr_load_headers_1464_none_to_3760_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 d112 d116 w120 v232 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hregs⟩ =>
      ⟨hPm, hvm, v6hr_Regs1508_of_stripS hregs⟩

theorem v6hr_load_headers_1464_none_to_3760_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w104 d112 d116 w120) := by
  have hwp := v6hr_load_headers_1464_none_to_3760_placed (ext := ext)
    s0 s1 out pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 d112 d116 w120 v232
    (A.pool lim st s1 ∗ Rest) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hregs⟩

/-- `VmPreserved`-strengthened Variant 6 header load at `+1464 -> +3760` (`d112 = 576`). -/
theorem v6hr_load_headers_1464_some_eq_to_3760_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 576#32 d116 w120) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6aPlaced.v6hr_load_headers_1464_some_eq_to_3760_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d116 w120 v232 Rest
      hsp0_align hw88
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hregs⟩ =>
      ⟨hPm, hvm, v6hr_Regs1508_of_stripS hregs⟩

theorem v6hr_load_headers_1464_some_eq_to_3760_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 576#32 d116 w120) := by
  have hwp := v6hr_load_headers_1464_some_eq_to_3760_placed (ext := ext)
    s0 s1 out pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d116 w120 v232
    (A.pool lim st s1 ∗ Rest) hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hregs⟩

/-- `VmPreserved`-strengthened Variant 6 header load at `+1464 -> +1520` (`d112 ≠ 576`). -/
theorem v6hr_load_headers_1464_some_ne_to_1520_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hd112 : (d112 == 576#32) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1520#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6aPlaced.v6hr_load_headers_1464_some_ne_to_1520_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v232 Rest
      hsp0_align hw88 hd112
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hregs⟩ =>
      ⟨hPm, hvm, v6hr_Regs1508_of_stripS hregs⟩

theorem v6hr_load_headers_1464_some_ne_to_1520_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hd112 : (d112 == 576#32) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1520#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) := by
  have hwp := v6hr_load_headers_1464_some_ne_to_1520_placed (ext := ext)
    s0 s1 out pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v232
    (A.pool lim st s1 ∗ Rest) hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hregs⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
