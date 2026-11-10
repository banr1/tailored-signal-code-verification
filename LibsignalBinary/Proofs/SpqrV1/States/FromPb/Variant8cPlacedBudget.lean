/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`) — Part C

Proves `FreeOnlyEvs` deallocation of input `Authenticator` buffers (`+10740 -> +10836`) and the
`sendingCt1 = none` 5-vector cleanup (`+11120 -> +4240`), re-exporting pure steps and
`Authenticator` buffer clone theorems from `Variant8cPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved sp_sub_2400_align v10_cap_add_one_beq_zero_false
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_shl8_extract_0_8
   v8_stackAt_encoderFromPb_split_7552)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st
   v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_dealloc_placed
   v1_dealloc_ok_of_placedHooks)

export Variant8cPlacedBudgetAux
  (v8_step_1872_to_1972_len_ok_placed v8_step_1872_to_1972_len_ok_placed_budget
   v8_check_auth_1972_none_placed v8_check_auth_1972_none_placed_budget)
export Variant8cPlacedBudgetAux
  (v8_check_auth_1972_some_placed v8_check_auth_1972_some_placed_budget
   v8_check_sendingCt1_10836_none_placed v8_check_sendingCt1_10836_none_placed_budget)
export Variant8cPlacedBudgetAux
  (v8_clone_rootKey_1984_to_10680_of_placedHooks v8_clone_rootKey_1984_to_10680_placed
   v8_clone_macKey_10680_to_10740_of_placedHooks v8_clone_macKey_10680_to_10740_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

private theorem lsmpl_base_333_eq [LibsignalPlacement] : lsmpl.base 333 = (blkPl_333).base := rfl

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  try rw [lsmpl_base_333_eq]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. Deallocation of Original `Authenticator` Buffers (`+10740 -> +10836`) -/

private theorem v8_dealloc_old_auth_10800_to_10836_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim))
    (st : M.σ) (s0 s2 : State) (out pbA u8 u16 u32 u40 u56 u64 u104 u112 l1 l2 : BitVec 64)
    (Rest : SepProp)
    (hl1_ne : (l1 + 1#64 == 0#64) = false)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 10800#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx9_2 : s2.readReg64 .x9 = u64)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx20_2 : s2.readReg64 .x20 = u112)
    (hx21_2 : s2.readReg64 .x21 = u64)
    (hx22_2 : s2.readReg64 .x22 = l1)
    (hx26_2 : s2.readReg64 .x26 = u8)
    (hx27_2 : s2.readReg64 .x27 = pbA)
    (hx28_2 : s2.readReg64 .x28 = l2)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10836#64) s2
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A.repAlloc u104 u112 ∗ A.pool lim st s2 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
            (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
            (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
            (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
          sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
  rw [lsmpl_base_333_eq] at hpc2 ⊢
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s2 _ _
  by_cases hu104 : (u104 == 0#64) = true
  · simp only [hu104, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 10836#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, v8_stackAt_encoderFromPb_split_7552 s0.sp]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  · have hbeq : (u104 == 0#64) = false := Bool.eq_false_iff.mpr hu104
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc u104.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (u112, u104.toNat, 1, st)
    have hacp2 : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hx9_sf_pre : sf.readReg64 .x21 = u64 := by simp only [wp_norm, arm64_norm, *]
    have hx22_sf : sf.readReg64 .x22 = l1 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    wp_steps_sync_333 (lsmpl.base 333 + 10836#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, v8_stackAt_encoderFromPb_split_7552 s0.sp, hsp2]
      simp only [hsp_sf, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done

/-- Steps `+10740 -> +10836` from a Block-`333` `__rust_dealloc` contract:
    copies `u56` (`ct1.cap`) to `[sp + 64]`, `u40, u32` (`ek.ptr, ek.cap`) to `[sp + 216..232]`,
    `u16` (`es.ptr`) to `[sp + 176]`, deallocates the old `rootKey` (`u80, u88`) and `macKey`
    (`u104, u112`) buffers emitting `FreeOnlyEvs`, checks `cmn x22, #1` (`false` since
    `l1.toNat < 2 ^ 63`), and reaches `+10836`. -/
theorem v8_dealloc_old_auth_10740_to_10836_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10740#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u112)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗ vecCapPtrDealloc A.repAlloc u104 u112 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
            (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
            (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
            (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
          sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hl1_ne : (l1 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hl1_lt
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 10800#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
      (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
      (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
      (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
      vecCapPtrDealloc A.repAlloc u104 u112 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x9 = u64 ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x20 = u112 ∧ s2.readReg64 .x21 = u64 ∧ s2.readReg64 .x22 = l1 ∧
      s2.readReg64 .x26 = u8 ∧ s2.readReg64 .x27 = pbA ∧ s2.readReg64 .x28 = l2 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hdealloc_fo1 := hdealloc_fo
    simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo1
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo1 hpc1 ⊢
    rw [lsmpl_base_333_eq] at hpc1 ⊢
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
    by_cases hu80 : (u80 == 0#64) = true
    · simp only [hu80, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 (lsmpl.base 333 + 10800#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
    · have hbeq : (u80 == 0#64) = false := Bool.eq_false_iff.mpr hu80
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc u80.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo1 (u88, u80.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      wp_steps_sync_333 (lsmpl.base 333 + 10800#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1]
        simp only [hsp_sf, arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx26_2, hx27_2, hx28_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    have h2 := v8_dealloc_old_auth_10800_to_10836_of_sub_placed hdealloc_fo
      st1 s0 s2 out pbA u8 u16 u32 u40 u56 u64 u104 u112 l1 l2 Rest
      hl1_ne hfsp_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2 hx26_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h2 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hregs⟩ => ?_
    refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hregs⟩
    have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
      dsimp only [st1]; rw [M.stepEvents_append]
    rw [hst_eq, v8_stackAt_encoderFromPb_split_7552 s0.sp] at hPf
    exact hPf

/-- Deallocation of original `Authenticator` buffers at `+10740 -> +10836` from a `__rust_dealloc`
    `HookSat` contract. -/
theorem v8_dealloc_old_auth_10740_to_10836_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10740#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u112) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗ vecCapPtrDealloc A.repAlloc u104 u112 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
          (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) :=
  v8_dealloc_old_auth_10740_to_10836_of_sub_placed
    (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2
    v64 v176 v216 v224 Rest hl1_lt hsp0_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

/-- Deallocation of original `Authenticator` buffers at `+10740 -> +10836` from
    `FromPbAllocHooksPlacedBudget`. -/
theorem v8_dealloc_old_auth_10740_to_10836_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10740#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u112) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗ vecCapPtrDealloc A.repAlloc u104 u112 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
          (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) :=
  v8_dealloc_old_auth_10740_to_10836_of_sub_placed
    (v1_dealloc_ok_of_placedHooks hA)
    st s0 s1 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2
    v64 v176 v216 v224 Rest hl1_lt hsp0_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

/-- Deallocation of original `Authenticator` buffers at `+10740 -> +10836` from
    `FromPbAllocHooksBudget`. -/
theorem v8_dealloc_old_auth_10740_to_10836_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2 : BitVec 64)
    (v64 v176 v216 v224 : BitVec 64) (Rest : SepProp)
    (hl1_lt : l1.toNat < 2 ^ 63) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10740#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = u112) (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = l2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10836#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗
        (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
        (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
        (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
        vecCapPtrDealloc A.repAlloc u80 u88 ∗ vecCapPtrDealloc A.repAlloc u104 u112 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 904#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 920#64) ↦₆₄ u32) ∗
          (((s0.sp - 2400#64) + 928#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 944#64) ↦₆₄ u56) ∗
          (((s0.sp - 2400#64) + 952#64) ↦₆₄ u64) ∗ (((s0.sp - 2400#64) + 992#64) ↦₆₄ u104) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = u64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = u64 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 ∧ sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = l2 ∧ TraceCalleeSaved sm s0) :=
  v8_dealloc_old_auth_10740_to_10836_of_sub_placed
    (v1_dealloc_ok_at_statesFromPb_placed hA)
    st s0 s1 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 l1 l2
    v64 v176 v216 v224 Rest hl1_lt hsp0_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

/-! ## 2. 5-Vector Cleanup Path (`+11212 -> +4240` and `+11120 -> +4240`) -/

/-- Shared tail at `+11212 -> +4240` from a Block-`333` `__rust_dealloc` contract:
    loads `x1 = [sp + 64]` (`ca5`), deallocates `vecCapPtrDealloc A.repAlloc ca5 pa5` (`x9 = pa5`)
    emitting `FreeOnlyEvs`, sets `x20 = 0#64`, and branches to `+4240`. -/
theorem v8_cleanup_vec5_11212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        vecCapPtrDealloc A.repAlloc ca5 pa5 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  rw [lsmpl_base_333_eq] at hpc1 ⊢
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
  by_cases hca5 : (ca5 == 0#64) = true
  · simp only [hca5, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 4240#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  · have hbeq : (ca5 == 0#64) = false := Bool.eq_false_iff.mpr hca5
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc ca5.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa5, ca5.toNat, 1, st)
    have hacp1 : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
    wp_steps_sync_333 ((blkPl_333).base + 4240#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, hsp1]
      simp only [hsp_sf, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done

/-- Shared tail at `+11212 -> +4240` from a `__rust_dealloc` `HookSat` contract. -/
theorem v8_cleanup_vec5_11212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
    (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_11212_of_sub_placed (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 htr1

/-- Shared tail at `+11212 -> +4240` from `FromPbAllocHooksPlacedBudget`. -/
theorem v8_cleanup_vec5_11212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
    (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_11212_of_sub_placed (v1_dealloc_ok_of_placedHooks hA)
    st s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 htr1

/-- Shared tail at `+11212 -> +4240` from `FromPbAllocHooksBudget`. -/
theorem v8_cleanup_vec5_11212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca5 pa5 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11212#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
    (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4240#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_vec5_11212_of_sub_placed (v1_dealloc_ok_at_statesFromPb_placed hA)
    st s0 s1 out ca5 pa5 Rest hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 htr1

private theorem v8_cleanup_vec1_11120_11144 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 ca3 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11120#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1) (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 11144#64) s1
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = pa5 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s0) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
  rw [lsmpl_base_333_eq] at hpc1 ⊢
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
  by_cases hca1 : (ca1 == 0#64) = true
  · simp only [hca1, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11144#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun sc hsc => by rw [← hsc]; simp only [arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done
  · have hbeq : (ca1 == 0#64) = false := Bool.eq_false_iff.mpr hca1
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc ca1.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa1, ca1.toNat, 1, st)
    have hacp1 : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hx21_sf : sf.readReg64 .x21 = pa5 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
    wp_steps_sync_333 (lsmpl.base 333 + 11144#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun sc hsc => by rw [← hsc, hsp1]; simp only [hsp_sf, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done

private theorem v8_cleanup_vec2_11144_11168 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim))
    (st : M.σ) (s0 s2 : State) (out ca2 pa2 ca3 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 11144#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64) (hx9_2 : s2.readReg64 .x9 = pa5)
    (hx19_2 : s2.readReg64 .x19 = out) (hx21_2 : s2.readReg64 .x21 = pa5)
    (hx26_2 : s2.readReg64 .x26 = ca3) (hx28_2 : s2.readReg64 .x28 = ca2)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 11168#64) s2
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗ A.pool lim st s2 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = pa5 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧ sm.readReg64 .x26 = ca3 ∧ TraceCalleeSaved sm s0) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
  rw [lsmpl_base_333_eq] at hpc2 ⊢
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s2 _ _
  by_cases hca2 : (ca2 == 0#64) = true
  · simp only [hca2, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11168#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun sc hsc => by rw [← hsc]; simp only [arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done
  · have hbeq : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc ca2.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa2, ca2.toNat, 1, st)
    have hacp2 : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hx21_sf : sf.readReg64 .x21 = pa5 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    wp_steps_sync_333 (lsmpl.base 333 + 11168#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun sc hsc => by rw [← hsc, hsp2]; simp only [hsp_sf, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done

private theorem v8_cleanup_vec3_11168_11192 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim))
    (st : M.σ) (s0 s3 : State) (out ca3 pa3 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 333 + 11168#64) (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 2400#64) (hx9_3 : s3.readReg64 .x9 = pa5)
    (hx19_3 : s3.readReg64 .x19 = out) (hx21_3 : s3.readReg64 .x21 = pa5)
    (hx26_3 : s3.readReg64 .x26 = ca3) (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 11192#64) s3
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ A.pool lim st s3 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = pa5 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧ TraceCalleeSaved sm s0) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc3 ⊢
  rw [lsmpl_base_333_eq] at hpc3 ⊢
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s3 _ _
  by_cases hca3 : (ca3 == 0#64) = true
  · simp only [hca3, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11192#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun sc hsc => by rw [← hsc]; simp only [arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done
  · have hbeq : (ca3 == 0#64) = false := Bool.eq_false_iff.mpr hca3
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc ca3.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa3, ca3.toNat, 1, st)
    have hacp3 : AllocCallPreserved s3 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hx21_sf : sf.readReg64 .x21 = pa5 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf : sf.trace = s0.trace := hacp3.2.1.trans htr3.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s3›.trans htr3.2
    wp_steps_sync_333 (lsmpl.base 333 + 11192#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st (fun sc hsc => by rw [← hsc, hsp3]; simp only [hsp_sf, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    wp_done

private theorem v8_cleanup_vec4_11192_11212 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim))
    (st : M.σ) (s0 s4 : State) (out ca4 pa4 pa5 : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 333 + 11192#64) (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 2400#64) (hx9_4 : s4.readReg64 .x9 = pa5)
    (hx19_4 : s4.readReg64 .x19 = out) (hx21_4 : s4.readReg64 .x21 = pa5)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 11212#64) s4
      (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        vecCapPtrDealloc A.repAlloc ca4 pa4 ∗ A.pool lim st s4 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x9 = pa5 ∧ sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc4 ⊢
  rw [lsmpl_base_333_eq] at hpc4 ⊢
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s4 _ _
  by_cases hca4 : (ca4 == 0#64) = true
  · simp only [hca4, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 11212#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, v8_stackAt_encoderFromPb_split_7552 s0.sp]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  · have hbeq : (ca4 == 0#64) = false := Bool.eq_false_iff.mpr hca4
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc ca4.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (pa4, ca4.toNat, 1, st)
    have hacp4 : AllocCallPreserved s4 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hx21_sf : sf.readReg64 .x21 = pa5 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf : sf.trace = s0.trace := hacp4.2.1.trans htr4.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s4›.trans htr4.2
    wp_steps_sync_333 (lsmpl.base 333 + 11212#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, v8_stackAt_encoderFromPb_split_7552 s0.sp, hsp4]
      simp only [hsp_sf, arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done

/-- 5-vector cleanup at `+11120 -> +4240` when `sendingCt1 = none` from a Block-`333`
    `__rust_dealloc` contract: deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, `(ca4, pa4)`,
    `(ca5, pa5)` emitting `FreeOnlyEvs`, sets `x20 = 0#64`, and branches to `+4240`. -/
theorem v8_cleanup_5vecs_11120_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11120#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = pa5)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa5)
    (hx22_1 : s1.readReg64 .x22 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4240#64) s1
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
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  rw [v8_stackAt_encoderFromPb_split_7552 s0.sp]
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 11144#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
       vecCapPtrDealloc A.repAlloc ca4 pa4 ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest))
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x9 = pa5 ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x21 = pa5 ∧ s2.readReg64 .x26 = ca3 ∧ s2.readReg64 .x28 = ca2 ∧
      TraceCalleeSaved s2 s0)
    ?_ ?_
  · have h1 := v8_cleanup_vec1_11120_11144 hdealloc_fo st s0 s1 out ca1 pa1 ca2 ca3 pa5
      ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
       vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
       vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
      hfsp_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono h1 fun s2 P2 _ _ ⟨evs1, hevs1, hP2, hregs⟩ =>
        ⟨evs1, hevs1, Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)), hregs⟩)
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx21_2, hx26_2, hx28_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 11168#64)
      (P_evs := fun evs2 s3 =>
        memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim (M.stepEvents evs2 st1) s3 ∗
        ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
         vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest))
      (Q := fun s3 =>
        s3.sp = s0.sp - 2400#64 ∧ s3.readReg64 .x9 = pa5 ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x21 = pa5 ∧ s3.readReg64 .x26 = ca3 ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have h2 := v8_cleanup_vec2_11144_11168 hdealloc_fo st1 s0 s2 out ca2 pa2 ca3 pa5
        ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
         vecCapPtrDealloc A.repAlloc ca4 pa4 ∗ vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
        hfsp_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx26_2 hx28_2 htr2
      refine SepWP.mono h2 fun s3 P3 _ _ ⟨evs2, hevs2, hP3, hregs⟩ =>
        ⟨evs2, hevs2, Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl)), hregs⟩
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx9_3, hx19_3, hx21_3, hx26_3, htr3⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs
        (mid := lsmpl.base 333 + 11192#64)
        (P_evs := fun evs3 s4 =>
          memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
          A.pool lim (M.stepEvents evs3 st2) s4 ∗
          ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
           (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
           vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest))
        (Q := fun s4 =>
          s4.sp = s0.sp - 2400#64 ∧ s4.readReg64 .x9 = pa5 ∧ s4.readReg64 .x19 = out ∧
          s4.readReg64 .x21 = pa5 ∧ TraceCalleeSaved s4 s0)
        ?_ ?_
      · have h3 := v8_cleanup_vec3_11168_11192 hdealloc_fo st2 s0 s3 out ca3 pa3 pa5
          ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
           (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
           vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
          hfsp_align hpc3 hrun3 hsp3 hx9_3 hx19_3 hx21_3 hx26_3 htr3
        refine SepWP.mono h3 fun s4 P4 _ _ ⟨evs3, hevs3, hP4, hregs⟩ =>
          ⟨evs3, hevs3, Entails.trans hP4 (Entails.of_eq (by sep_ac_rfl)), hregs⟩
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨hsp4, hx9_4, hx19_4, hx21_4, htr4⟩
        let st3 := M.stepEvents evs3 st2
        refine seq_clean_evs
          (mid := lsmpl.base 333 + 11212#64)
          (P_evs := fun evs4 s5 =>
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
            vecCapPtrDealloc A.repAlloc ca5 pa5 ∗
            A.pool lim (M.stepEvents evs4 st3) s5 ∗
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest))
          (Q := fun s5 =>
            s5.sp = s0.sp - 2400#64 ∧ s5.readReg64 .x9 = pa5 ∧ s5.readReg64 .x19 = out ∧
            TraceCalleeSaved s5 s0)
          ?_ ?_
        · have h4 := v8_cleanup_vec4_11192_11212 hdealloc_fo st3 s0 s4 out ca4 pa4 pa5
            ((((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
             (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
             vecCapPtrDealloc A.repAlloc ca5 pa5 ∗ Rest)
            hfsp_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx21_4 htr4
          refine SepWP.mono h4 fun s5 P5 _ _ ⟨evs4, hevs4, hP5, hregs⟩ =>
            ⟨evs4, hevs4, Entails.trans hP5 (Entails.of_eq (by sep_ac_rfl)), hregs⟩
        · intro evs4 s5 hevs4 hpc5 hrun5 ⟨hsp5, hx9_5, hx19_5, htr5⟩
          let st4 := M.stepEvents evs4 st3
          have h5 := v8_cleanup_vec5_11212_of_sub_placed hdealloc_ok st4 s0 s5 out ca5 pa5
            ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
             (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ Rest)
            hsp0_align hpc5 hrun5 hsp5 hx9_5 hx19_5 htr5
          refine SepWP.mono h5 fun sf Pf _ _ ⟨evs5, hevs5, hPf, hregs⟩ => ?_
          refine ⟨evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5,
            FreeOnlyEvs.append (FreeOnlyEvs.append (FreeOnlyEvs.append
              (FreeOnlyEvs.append hevs1 hevs2) hevs3) hevs4) hevs5,
            ?_, hregs⟩
          have hst_eq : M.stepEvents evs5 st4 =
              M.stepEvents (evs1 ++ evs2 ++ evs3 ++ evs4 ++ evs5) st := by
            dsimp only [st4, st3, st2, st1]
            simp only [M.stepEvents_append, List.append_assoc]
          rw [hst_eq] at hPf
          rw [v8_stackAt_encoderFromPb_split_7552 s0.sp] at hPf
          exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-- 5-vector cleanup at `+11120 -> +4240` from a `__rust_dealloc` `HookSat` contract. -/
theorem v8_cleanup_5vecs_11120_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11120#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
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
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_11120_of_sub_placed (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 Rest hsp0_align
    hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

/-- 5-vector cleanup at `+11120 -> +4240` from `FromPbAllocHooksPlacedBudget`. -/
theorem v8_cleanup_5vecs_11120_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11120#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
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
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_11120_of_sub_placed (v1_dealloc_ok_of_placedHooks hA)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 Rest hsp0_align
    hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

/-- 5-vector cleanup at `+11120 -> +4240` from `FromPbAllocHooksBudget`. -/
theorem v8_cleanup_5vecs_11120_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 11120#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = pa5)
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
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v8_cleanup_5vecs_11120_of_sub_placed (v1_dealloc_ok_at_statesFromPb_placed hA)
    st s0 s1 out ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 Rest hsp0_align
    hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudget
