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
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8d
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`) — Part D

Lifts the Variant 8 `<PolyEncoder>::from_pb` setup (`+10836 -> +10900`), result dispatch (`+10904`),
`FreeOnlyEvs` 5-vector error cleanup (`+10916 -> +4240`), and `Ok(enc)` staging (`+11264 -> +8180`)
to `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved sp_sub_2400_align v1_optProtoPolyEncoderWordsAt v8_encCellsAt
   v8_stackAt_encoderFromPb_split_7552 v8_stagingSlotsPost v8_stagingSlotsPre v8_wordAt)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 v1_dealloc_ok_at_statesFromPb_placed
   v1_dealloc_ok_of_placedHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp]
private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

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

/-! ## 1. `PolyEncoder::from_pb` Result Check (`+10904`) and Error Cleanup (`+10916 -> +4240`) -/

/-- `VmPreserved`-strengthened placed `+10904 -> +10916` step when `PolyEncoder::from_pb` returns
    `Err` (`[sp + 1888] = 2#64`). -/
theorem v8_check_enc_res_10904_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10904#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10916#64) s
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest) ∧ VmPreserved s s2 ∧
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧ s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧ s2.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8dPlaced.v8_check_enc_res_10904_err_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      Rest hsp0_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx19_2, by simpa using hx21_2,
       by simpa using hx22_2, by simpa using hx26_2, by simpa using hx28_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v8_check_enc_res_10904_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10904#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10916#64) s
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest ∗ A.pool lim st s)
      (fun s2 P2 =>
        (P2 ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest ∗ A.pool lim st s2) ∧
        VmPreserved s s2 ∧ s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧ s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧ s2.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v8_check_enc_res_10904_err_placed (ext := ext)
    s0 s (Rest ∗ A.pool lim st s) hsp0_align hpc hrun hsp htr
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

/-- `VmPreserved`-strengthened placed `+10904 -> +11264` step when `PolyEncoder::from_pb` returns
    `Ok(enc)` (`tag = 0#64 ∨ tag = 1#64`). -/
theorem v8_check_enc_res_10904_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (tag : BitVec 64) (htag : tag = 0#64 ∨ tag = 1#64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10904#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 11264#64) s
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ Rest) ∧ VmPreserved s s2 ∧
        s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧ s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧ s2.readReg64 .x23 = s.readReg64 .x23 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧ s2.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8dPlaced.v8_check_enc_res_10904_ok_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      tag htag Rest hsp0_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx15_2, hx19_2, hx21_2, hx22_2, hx23_2, hx26_2, hx28_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx15_2, by simpa using hx19_2,
       by simpa using hx21_2, by simpa using hx22_2, by simpa using hx23_2,
       by simpa using hx26_2, by simpa using hx28_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v8_check_enc_res_10904_ok_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (tag : BitVec 64) (htag : tag = 0#64 ∨ tag = 1#64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 10904#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 11264#64) s
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ Rest ∗ A.pool lim st s)
      (fun s2 P2 =>
        (P2 ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ Rest ∗ A.pool lim st s2) ∧
        VmPreserved s s2 ∧ s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧ s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧ s2.readReg64 .x23 = s.readReg64 .x23 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧ s2.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v8_check_enc_res_10904_ok_placed (ext := ext)
    s0 s tag htag (Rest ∗ A.pool lim st s) hsp0_align hpc hrun hsp htr
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

/-- Tail at `+10992 -> +4240` (`lsmpl.base 333 + 10992 -> + 4240`) under an explicit
    Block-`333` `__rust_dealloc` budget contract, producing `FreeOnlyEvs`. -/
theorem v8_cleanup_vec5_10992_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10992#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  change s1.pc = (blkPl_333).base + 10992#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4240#64) s1 _ _
  by_cases hca5 : (ca5 == 0#64) = true <;>
    simp only [hca5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_evs_nil
      (P_evs := fun evs sm =>
        (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack) ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) ?_
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4240#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done
  · refine sepWP_evs_dealloc ca5.toNat 1
      (P_evs := fun evs sm =>
        (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack) ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) ?_
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa5, ca5.toNat, 1, st)
    have hacp1 : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
    have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
    wp_steps_sync_333 ((blkPl_333).base + 4240#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done

/-- Tail at `+10992 -> +4240` under `FromPbAllocHooksBudget`. -/
theorem v8_cleanup_vec5_10992_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10992#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_10992_of_sub_placed (v1_dealloc_ok_at_statesFromPb_placed hA)
    st s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 htr1

theorem v8_cleanup_vec5_10992_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10992#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_10992_of_sub_placed (v1_dealloc_ok_of_placedHooks hA)
    st s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 htr1

private theorem v8_cleanup_vec1_10916_10940 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10916#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5) (hx22_1 : s1.readReg64 .x22 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3) (hx28_1 : s1.readReg64 .x28 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10940#64) s1
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (P2 ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            A.pool lim (M.stepEvents evs st) s2 ∗ Rest) ∧
          s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x0 = pa2 ∧ s2.readReg64 .x19 = out ∧
          s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧
          TraceCalleeSaved s2 s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  change s1.pc = (blkPl_333).base + 10916#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10940#64) s1 _ _
  by_cases hca1 : (ca1 == 0#64) = true <;>
    simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_evs_nil
      (P_evs := fun evs s2 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        A.pool lim (M.stepEvents evs st) s2 ∗ Rest)
      (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x0 = pa2 ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved s2 s0) ?_
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 10940#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done
  · refine sepWP_evs_dealloc ca1.toNat 1
      (P_evs := fun evs s2 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        A.pool lim (M.stepEvents evs st) s2 ∗ Rest)
      (Q := fun s2 => s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x0 = pa2 ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved s2 s0) ?_
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
    have hacp1 : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
    have hfsp_sf : (sf.sp &&& 15#64 == 0#64) = true := hsp_sf ▸ hfsp_align
    have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
    wp_steps_sync_333 ((blkPl_333).base + 10940#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp1]; simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done

private theorem v8_cleanup_vec2_10940_10960 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s2 : State) (out ca2 pa2 ca3 pa3 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 10940#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64) (hx0_2 : s2.readReg64 .x0 = pa2)
    (hx19_2 : s2.readReg64 .x19 = out) (hx21_2 : s2.readReg64 .x21 = pa5)
    (hx26_2 : s2.readReg64 .x26 = ca3) (hx28_2 : s2.readReg64 .x28 = ca2)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10960#64) s2
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s2 ∗ Rest)
      (fun s3 P3 =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (P3 ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            A.pool lim (M.stepEvents evs st) s3 ∗ Rest) ∧
          s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x0 = pa3 ∧ s3.readReg64 .x19 = out ∧
          s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
  change s2.pc = (blkPl_333).base + 10940#64 at hpc2
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10960#64) s2 _ _
  by_cases hca2 : (ca2 == 0#64) = true <;>
    simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_evs_nil
      (P_evs := fun evs s3 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        A.pool lim (M.stepEvents evs st) s3 ∗ Rest)
      (Q := fun s3 => s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x0 = pa3 ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0) ?_
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 10960#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done
  · refine sepWP_evs_dealloc ca2.toNat 1
      (P_evs := fun evs s3 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        A.pool lim (M.stepEvents evs st) s3 ∗ Rest)
      (Q := fun s3 => s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x0 = pa3 ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0) ?_
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa2, ca2.toNat, 1, st)
    have hacp2 : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
    have hfsp_sf : (sf.sp &&& 15#64 == 0#64) = true := hsp_sf ▸ hfsp_align
    have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    wp_steps_sync_333 ((blkPl_333).base + 10960#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp2]; simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done

private theorem v8_cleanup_vec3_10960_10980 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s3 : State) (out ca3 pa3 ca4 pa4 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 10960#64) (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64) (hx0_3 : s3.readReg64 .x0 = pa3)
    (hx19_3 : s3.readReg64 .x19 = out) (hx21_3 : s3.readReg64 .x21 = pa5)
    (hx26_3 : s3.readReg64 .x26 = ca3) (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10980#64) s3
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ A.pool lim st s3 ∗ Rest)
      (fun s4 P4 =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (P4 ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) s4 ∗ Rest) ∧
          s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x0 = pa4 ∧ s4.readReg64 .x1 = ca4 ∧
          s4.readReg64 .x19 = out ∧ s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
  change s3.pc = (blkPl_333).base + 10960#64 at hpc3
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10980#64) s3 _ _
  by_cases hca3 : (ca3 == 0#64) = true <;>
    simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_evs_nil
      (P_evs := fun evs s4 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        A.pool lim (M.stepEvents evs st) s4 ∗ Rest)
      (Q := fun s4 => s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x0 = pa4 ∧ s4.readReg64 .x1 = ca4 ∧
        s4.readReg64 .x19 = out ∧ s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0) ?_
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 10980#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done
  · refine sepWP_evs_dealloc ca3.toNat 1
      (P_evs := fun evs s4 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        A.pool lim (M.stepEvents evs st) s4 ∗ Rest)
      (Q := fun s4 => s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x0 = pa4 ∧ s4.readReg64 .x1 = ca4 ∧
        s4.readReg64 .x19 = out ∧ s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0) ?_
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa3, ca3.toNat, 1, st)
    have hacp3 : AllocCallPreserved s3 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s3.sp›.trans hsp3
    have hfsp_sf : (sf.sp &&& 15#64 == 0#64) = true := hsp_sf ▸ hfsp_align
    have htr_sf : sf.trace = s0.trace := hacp3.2.1.trans htr3.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
    wp_steps_sync_333 ((blkPl_333).base + 10980#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [hsp3]; simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done

private theorem v8_cleanup_vec4_10980_10992 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s4 : State) (out ca4 pa4 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 333 + 10980#64) (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 2400#64) (hx0_4 : s4.readReg64 .x0 = pa4)
    (hx1_4 : s4.readReg64 .x1 = ca4) (hx19_4 : s4.readReg64 .x19 = out)
    (hx21_4 : s4.readReg64 .x21 = pa5) (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10992#64) s4
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗ A.pool lim st s4 ∗ Rest)
      (fun s5 P5 =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (P5 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs st) s5 ∗ Rest) ∧
          s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x19 = out ∧
          s5.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s5 s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc4 ⊢
  change s4.pc = (blkPl_333).base + 10980#64 at hpc4
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10992#64) s4 _ _
  by_cases hca4 : (ca4 == 0#64) = true <;>
    simp only [hca4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_evs_nil
      (P_evs := fun evs s5 =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        A.pool lim (M.stepEvents evs st) s5 ∗ Rest)
      (Q := fun s5 => s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x19 = out ∧
        s5.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s5 s0) ?_
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 10992#64)
    simp only [State.setMem_setMem]
    refine align_pre_st (by rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]; simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done
  · refine sepWP_evs_dealloc ca4.toNat 1
      (P_evs := fun evs s5 =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        A.pool lim (M.stepEvents evs st) s5 ∗ Rest)
      (Q := fun s5 => s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x19 = out ∧
        s5.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s5 s0) ?_
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa4, ca4.toNat, 1, st)
    have hacp4 : AllocCallPreserved s4 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s4.sp›.trans hsp4
    have hfsp_sf : (sf.sp &&& 15#64 == 0#64) = true := hsp_sf ▸ hfsp_align
    have htr_sf : sf.trace = s0.trace := hacp4.2.1.trans htr4.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s4›.trans htr4.2
    refine align_pre_st (by rw [v8_stackAt_encoderFromPb_split_7552 s0.sp, hsp4]; simp only [arm64_norm]; sep_ac_rfl) ?_
    wp_done

/-- 5-vector cleanup at `+10916 -> +4240` (`lsmpl.base 333 + 10916 -> + 4240`) under an explicit
    Block-`333` `__rust_dealloc` budget contract, producing `FreeOnlyEvs`. -/
theorem v8_cleanup_5vecs_10916_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10916#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_evs
      (v8_cleanup_vec1_10916_10940 hdealloc_ok st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa5
        ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
         vecCapPtrDealloc A.repAlloc ca4 pa4 ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
        hfsp_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1) ?_)
  intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx21_2, hx26_2, hx28_2, htr2⟩
  let st1 := M.stepEvents evs1 st
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_evs
      (v8_cleanup_vec2_10940_10960 hdealloc_ok st1 s0 s2 out ca2 pa2 ca3 pa3 pa5
        ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
         vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
        hfsp_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx21_2 hx26_2 hx28_2 htr2) ?_)
  intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx0_3, hx19_3, hx21_3, hx26_3, htr3⟩
  let st2 := M.stepEvents evs2 st1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_evs
      (v8_cleanup_vec3_10960_10980 hdealloc_ok st2 s0 s3 out ca3 pa3 ca4 pa4 pa5
        ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
         vecCapPtrDealloc A.repAlloc ca4 pa4 ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
        hfsp_align hpc3 hrun3 hsp3 hx0_3 hx19_3 hx21_3 hx26_3 htr3) ?_)
  intro evs3 s4 hevs3 hpc4 hrun4 ⟨hsp4, hx0_4, hx1_4, hx19_4, hx21_4, htr4⟩
  let st3 := M.stepEvents evs3 st2
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_evs
      (v8_cleanup_vec4_10980_10992 hdealloc_ok st3 s0 s4 out ca4 pa4 pa5
        ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
        hfsp_align hpc4 hrun4 hsp4 hx0_4 hx1_4 hx19_4 hx21_4 htr4) ?_)
  intro evs4 s5 hevs4 hpc5 hrun5 ⟨hsp5, hx19_5, hx21_5, htr5⟩
  let st4 := M.stepEvents evs4 st3
  have h5 := v8_cleanup_vec5_10992_of_sub_placed hdealloc_ok st4 s0 s5 out ca5 pa5
    ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest)
    hsp0_align hpc5 hrun5 hsp5 hx19_5 hx21_5 htr5
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono h5 fun sf Pf _ _ ⟨evs5, hevs5, hPf, hsp_f, hx19_f, hx20_f, htr_f⟩ => ?_)
  refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5,
    FreeOnlyEvs.append
      (FreeOnlyEvs.append
        (FreeOnlyEvs.append (FreeOnlyEvs.append hevs1 hevs2) hevs3)
        hevs4)
      hevs5,
    ?_, hsp_f, hx19_f, hx20_f, htr_f⟩
  have hst_eq :
      M.stepEvents evs5 st4 =
        M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5) st := by
    dsimp only [st4, st3, st2, st1]
    rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp, hst_eq] at hPf
  exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-- 5-vector cleanup at `+10916 -> +4240` under `FromPbAllocHooksBudget`. -/
theorem v8_cleanup_5vecs_10916_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10916#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_10916_of_sub_placed (v1_dealloc_ok_at_statesFromPb_placed hA)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

theorem v8_cleanup_5vecs_10916_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10916#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_10916_of_sub_placed (v1_dealloc_ok_of_placedHooks hA)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

/-! ## 2. `PolyEncoder::from_pb` Setup (`+10836 -> +10900`) -/

/-- `VmPreserved`-strengthened placed `+10836 -> +10900` setup step when `w0.toNat < 2 ^ 63`. -/
theorem v8_copy_enc_10836_to_10900_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA pa5 l1 u8 l2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (z240 z248 z256 z264 z272 z280 z288 : BitVec 64) (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10836#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10900#64) s1
      ((((s0.sp - 2400#64) + 240#64) ↦₆₄ z240) ∗ (((s0.sp - 2400#64) + 248#64) ↦₆₄ z248) ∗
        (((s0.sp - 2400#64) + 256#64) ↦₆₄ z256) ∗ (((s0.sp - 2400#64) + 264#64) ↦₆₄ z264) ∗
        (((s0.sp - 2400#64) + 272#64) ↦₆₄ z272) ∗ (((s0.sp - 2400#64) + 280#64) ↦₆₄ z280) ∗
        (((s0.sp - 2400#64) + 288#64) ↦₆₄ z288) ∗ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗
        (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗
        ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗
        ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
          ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗
          ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗
          Rest) ∧
        VmPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x1 = (s0.sp - 2400#64) + 240#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa5 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8dPlaced.v8_copy_enc_10836_to_10900_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA pa5 l1 u8 l2 w0 w8 w16 w24 w32 w40 w48
      z240 z248 z256 z264 z272 z280 z288 Rest hw0_lt hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx23_1) (by simpa using hx26_1) (by simpa using hx27_1)
      (by simpa using hx28_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx26_m, hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx26_m, by simpa using hx27_m,
       by simpa using hx28_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_copy_enc_10836_to_10900_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA pa5 l1 u8 l2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (z240 z248 z256 z264 z272 z280 z288 : BitVec 64) (Rest : SepProp)
    (hw0_lt : w0.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10836#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10900#64) s1
      ((((s0.sp - 2400#64) + 240#64) ↦₆₄ z240) ∗ (((s0.sp - 2400#64) + 248#64) ↦₆₄ z248) ∗
        (((s0.sp - 2400#64) + 256#64) ↦₆₄ z256) ∗ (((s0.sp - 2400#64) + 264#64) ↦₆₄ z264) ∗
        (((s0.sp - 2400#64) + 272#64) ↦₆₄ z272) ∗ (((s0.sp - 2400#64) + 280#64) ↦₆₄ z280) ∗
        (((s0.sp - 2400#64) + 288#64) ↦₆₄ z288) ∗ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗
        (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗
        ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗
        ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗ Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
          ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗
          ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        sm.readReg64 .x1 = (s0.sp - 2400#64) + 240#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa5 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) := by
  have hwp := v8_copy_enc_10836_to_10900_placed (ext := ext)
    s0 s1 out pbA pa5 l1 u8 l2 w0 w8 w16 w24 w32 w40 w48
    z240 z248 z256 z264 z272 z280 z288 (Rest ∗ A.pool lim st s1)
    hw0_lt hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 3. Staging `Ok(enc)` for Shared Epilogue (`+11264 -> +8180`, 77 instructions) -/

/-- `VmPreserved`-strengthened placed `+11264 -> +8180` staging step (Block `333`). -/
theorem v8_stage_11264_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 w2280 : BitVec 64)
    (bs : List (BitVec 8))
    (d96 : BitVec 32) (u104 u112 u160 : BitVec 64) (d172 : BitVec 32) (u192 u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u887 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 11264#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5)
    (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = l2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8180#64) s
      (((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗
        v8_stagingSlotsPre fsp d96 u104 u112 u160 d172 u192 u208 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u887 ∗
        v8_encCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗
          v8_stagingSlotsPost fsp bs pa5 l2 ∗
          v8_encCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest) ∧
        VmPreserved s s2 ∧ s2.sp = fsp ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧ s2.readReg64 .x8 = 10#64 ∧
        s2.readReg64 .x15 = tag ∧ s2.readReg64 .x20 = v8_wordAt bs 8 ∧
        s2.readReg64 .x13 = v8_wordAt bs 16 ∧ s2.readReg64 .x25 = v8_wordAt bs 24 ∧
        s2.readReg64 .x30 = v8_wordAt bs 32 ∧ s2.readReg64 .x9 = v8_wordAt bs 40 ∧
        s2.readReg64 .x14 = v8_wordAt bs 48 ∧ s2.readReg64 .x18 = v8_wordAt bs 56 ∧
        s2.readReg64 .x17 = v8_wordAt bs 64 ∧ s2.readReg64 .x0 = v8_wordAt bs 72 ∧
        (s2.readReg32 .x3).setWidth 8 = (v8_wordAt bs 80).extractLsb' 0 8 ∧
        s2.readReg32 .x27 = (v8_wordAt bs 80).extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v8_wordAt bs 80).extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v8_wordAt bs 80).extractLsb' 56 8 ∧
        s2.readReg64 .x4 = v8_wordAt bs 88 ∧ s2.readReg64 .x5 = v8_wordAt bs 96 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte (v8_wordAt bs 104) ∧
        s2.readReg64 .x7 = v8_wordAt bs 120 ∧ s2.readReg64 .x2 = w2280 ∧
        s2.readReg64 .x11 = l1 ∧ s2.readReg64 .x22 = pa1 ∧ s2.readReg64 .x24 = l1 ∧
        s2.readReg64 .x10 = pa2 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x12 = pa3 ∧
        s2.readReg64 .x1 = 2080#64 ∧ s2.readReg64 .x28 = pa4 ∧ s2.readReg64 .x16 = ca5 ∧
        s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8dPlaced.v8_stage_11264_to_8180_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 w2280 bs
      d96 u104 u112 u160 d172 u192 u208 u232
      uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
      u832 uq848 u864 u880 u887 Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx15) (by simpa using hx19) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx23) (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s2 P2 hvm
      ⟨hP2, hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2,
       hx18_2, hx17_2, hx0_2, hx3_2, hx27_2, hx27_hi16, hx27_hi8, hx4_2, hx5_2, hx21_2,
       hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2,
       hx16_2, hx19_2, hx23_2, htr2⟩ => by
      exact ⟨hP2, hvm, by simpa using hsp2, by simpa using hx6_2, by simpa using hx8_2,
        by simpa using hx15_2, by simpa using hx20_2, by simpa using hx13_2,
        by simpa using hx25_2, by simpa using hx30_2, by simpa using hx9_2,
        by simpa using hx14_2, by simpa using hx18_2, by simpa using hx17_2,
        by simpa using hx0_2, by simpa using hx3_2, by simpa using hx27_2,
        by simpa using hx27_hi16, by simpa using hx27_hi8, by simpa using hx4_2,
        by simpa using hx5_2, by simpa using hx21_2, by simpa using hx7_2,
        by simpa using hx2_2, by simpa using hx11_2, by simpa using hx22_2,
        by simpa using hx24_2, by simpa using hx10_2, by simpa using hx26_2,
        by simpa using hx12_2, by simpa using hx1_2, by simpa using hx28_2,
        by simpa using hx16_2, by simpa using hx19_2, by simpa using hx23_2,
        ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v8_stage_11264_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 w2280 : BitVec 64)
    (bs : List (BitVec 8))
    (d96 : BitVec 32) (u104 u112 u160 : BitVec 64) (d172 : BitVec 32) (u192 u208 u232 : BitVec 64)
    (uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 : BitVec 128)
    (u832 : BitVec 64) (uq848 : BitVec 128) (u864 u880 u887 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 11264#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5)
    (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = l2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 8180#64) s
      (((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗
        v8_stagingSlotsPre fsp d96 u104 u112 u160 d172 u192 u208 u232
          uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
          u832 uq848 u864 u880 u887 ∗
        v8_encCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗
        Rest ∗ A.pool lim st s)
      (fun s2 P2 =>
        (P2 ⊢
          ((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗
          v8_stagingSlotsPost fsp bs pa5 l2 ∗
          v8_encCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗
          Rest ∗ A.pool lim st s2) ∧
        VmPreserved s s2 ∧ s2.sp = fsp ∧
        s2.readReg64 .x6 = fsp + 576#64 ∧ s2.readReg64 .x8 = 10#64 ∧
        s2.readReg64 .x15 = tag ∧ s2.readReg64 .x20 = v8_wordAt bs 8 ∧
        s2.readReg64 .x13 = v8_wordAt bs 16 ∧ s2.readReg64 .x25 = v8_wordAt bs 24 ∧
        s2.readReg64 .x30 = v8_wordAt bs 32 ∧ s2.readReg64 .x9 = v8_wordAt bs 40 ∧
        s2.readReg64 .x14 = v8_wordAt bs 48 ∧ s2.readReg64 .x18 = v8_wordAt bs 56 ∧
        s2.readReg64 .x17 = v8_wordAt bs 64 ∧ s2.readReg64 .x0 = v8_wordAt bs 72 ∧
        (s2.readReg32 .x3).setWidth 8 = (v8_wordAt bs 80).extractLsb' 0 8 ∧
        s2.readReg32 .x27 = (v8_wordAt bs 80).extractLsb' 8 32 ∧
        ((s2.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v8_wordAt bs 80).extractLsb' 40 16 ∧
        ((s2.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v8_wordAt bs 80).extractLsb' 56 8 ∧
        s2.readReg64 .x4 = v8_wordAt bs 88 ∧ s2.readReg64 .x5 = v8_wordAt bs 96 ∧
        (s2.readReg32 .x21).setWidth 8 = loByte (v8_wordAt bs 104) ∧
        s2.readReg64 .x7 = v8_wordAt bs 120 ∧ s2.readReg64 .x2 = w2280 ∧
        s2.readReg64 .x11 = l1 ∧ s2.readReg64 .x22 = pa1 ∧ s2.readReg64 .x24 = l1 ∧
        s2.readReg64 .x10 = pa2 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x12 = pa3 ∧
        s2.readReg64 .x1 = 2080#64 ∧ s2.readReg64 .x28 = pa4 ∧ s2.readReg64 .x16 = ca5 ∧
        s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v8_stage_11264_to_8180_placed (ext := ext)
    s0 s fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 w2280 bs
    d96 u104 u112 u160 d172 u192 u208 u232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u887 (Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx26 hx28 htr
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlacedBudget

