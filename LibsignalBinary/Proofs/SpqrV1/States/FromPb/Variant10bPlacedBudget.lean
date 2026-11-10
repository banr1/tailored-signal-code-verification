/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Variant 10 (`Ct2Sampled`, `+1632`) — Deallocation & `Authenticator` Cloning

Re-exports `+1632` early-error theorems from `Variant10bPlacedBudgetAux`, and proves `FreeOnlyEvs`
original-buffer deallocation (`+5688 -> +5728`) and total-correctness cloning of `rootKey`
(`+1720 -> +5540`) and `macKey` (`+5540 -> +5688`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved ofNat_beq_zero_false sp_sub_2400_align
   stackAt_encoderFromPb_split_allocHook v1_bv_add_add_lit v1_bv_sub_sub_lit
   v1_shl8_extract_0_8 vecU8Payload_of_nil vecU8Payload_pos vecU8Payload_pos_dealloc
   vecU8Payload_pos_unpack)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
  (v10_sub_ok_dealloc_125316_of_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget.toPlacedBudget blk333_noSvc0 entails_pre_st)

export Variant10bPlacedBudgetAux
  (v10_ct2Sent_expose_pre_uc_none_2304_placed v10_ct2Sent_expose_pre_uc_none_placed
   v10_ct2Sent_expose_pre_auth_none_2304_placed v10_ct2Sent_expose_pre_auth_none_placed)
export Variant10bPlacedBudgetAux
  (v10_ct2Sent_err_1632_uc_none_2304_of_sub_placed
   v10_ct2Sent_err_1632_uc_none_2304_of_dealloc_placed
   v10_ct2Sent_err_1632_uc_none_2304_placed
   v10_ct2Sent_err_1632_uc_none_of_sub_placed
   v10_ct2Sent_err_1632_uc_none_of_dealloc_placed
   v10_ct2Sent_err_1632_uc_none_placed)
export Variant10bPlacedBudgetAux
  (v10_ct2Sent_err_1632_auth_none_2304_of_sub_placed
   v10_ct2Sent_err_1632_auth_none_2304_of_dealloc_placed
   v10_ct2Sent_err_1632_auth_none_2304_placed
   v10_ct2Sent_err_1632_auth_none_of_sub_placed
   v10_ct2Sent_err_1632_auth_none_of_dealloc_placed
   v10_ct2Sent_err_1632_auth_none_placed)

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

/-! ## 1. Deallocation of Original `Authenticator` Buffers (`+5688 -> +5728`) -/

/-- Second deallocation step (`+5708 -> +5728`): deallocates `vecCapPtrDealloc A.repAlloc c2 p2`
    (`x25 = c2`, `[sp + 232] = p2`) emitting `FreeOnlyEvs`. -/
private theorem v10_ct2Sent_dealloc_5708_to_5728_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim))
    (st : M.σ) (s0 s2 : State) (out p1_new cap_enc c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 5708#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx21_2 : s2.readReg64 .x21 = p1_new)
    (hx22_2 : s2.readReg64 .x22 = cap_enc)
    (hx23_2 : s2.readReg64 .x23 = pbA + 8#64)
    (hx25_2 : s2.readReg64 .x25 = c2)
    (hx26_2 : s2.readReg64 .x26 = l2)
    (hx27_2 : s2.readReg64 .x27 = pbA)
    (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5728#64) s2
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s2 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = p1_new ∧
          sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x26 = l2 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0) := by
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
  change s2.pc = (blkPl_333).base + 5708#64 at hpc2
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5728#64) s2 _ _
  by_cases hc2 : (c2 == 0#64) = true
  · simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 ((blkPl_333).base + 5728#64)
    simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  · have hbeq : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    apply sepWP_evs_dealloc c2.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    wp_call hdealloc_fo (p2, c2.toNat, 1, st)
    have hacp2 : AllocCallPreserved s2 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s2.sp›.trans hsp2
    have htr_sf : sf.trace = s0.trace := hacp2.2.1.trans htr2.1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = calleeSavedVRegs s2›.trans htr2.2
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, hsp2]
      simp only [arm64_norm]
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done

/-- Deallocation of original `Authenticator` buffers at `+5688 -> +5728` from a Block-`333`
    `__rust_dealloc` contract: deallocates `vecCapPtrDealloc A.repAlloc c1 p1` (`x24 = c1`,
    `x20 = p1`) and `vecCapPtrDealloc A.repAlloc c2 p2` (`x25 = c2`, `[sp + 232] = p2`),
    emitting `FreeOnlyEvs`. -/
theorem v10_ct2Sent_dealloc_5688_to_5728_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5688#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = p1_new ∧
          sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x26 = l2 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 5708#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
      vecCapPtrDealloc A.repAlloc c2 p2 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = p1_new ∧
      sm.readReg64 .x22 = cap_enc ∧
      sm.readReg64 .x23 = pbA + 8#64 ∧
      sm.readReg64 .x25 = c2 ∧
      sm.readReg64 .x26 = l2 ∧
      sm.readReg64 .x27 = pbA ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · have hdealloc_fo1 := hdealloc_fo
    simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo1
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo1 hpc1 ⊢
    change s1.pc = (blkPl_333).base + 5688#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5708#64) s1 _ _
    by_cases hc1 : (c1 == 0#64) = true
    · simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [M.stepEvents_nil]
      wp_steps_sync_333 ((blkPl_333).base + 5708#64)
      simp only [State.setMem_setMem]
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
    · have hbeq : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc c1.toNat 1
      wp_steps_sync_333 (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      wp_call hdealloc_fo1 (p1, c1.toNat, 1, st)
      have hacp1 : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := ‹sf.sp = s1.sp›.trans hsp1
      have htr_sf : sf.trace = s0.trace := hacp1.2.1.trans htr1.1
      have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        ‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc, hsp1]
        simp only [arm64_norm]
        exact Entails.of_eq (by sep_ac_rfl)
      · wp_done
  ·
    intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx26_2, hx27_2, htr2⟩
    let st1 := M.stepEvents evs1 st
    have h5708 := v10_ct2Sent_dealloc_5708_to_5728_of_sub_placed hdealloc_fo
      st1 s0 s2 out p1_new cap_enc c2 p2 l2 pbA Rest
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2 htr2
    refine SepWP.mono h5708 fun sf Pf _ _ ⟨evs2, hevs2, hPf, hregs⟩ => ?_
    refine ⟨evs1 ++ evs2, FreeOnlyEvs.append hevs1 hevs2, ?_, hregs⟩
    have hst_eq : M.stepEvents evs2 st1 = M.stepEvents (evs1 ++ evs2) st := by
      dsimp only [st1]
      rw [M.stepEvents_append]
    rw [hst_eq] at hPf
    exact hPf

theorem v10_ct2Sent_dealloc_5688_to_5728_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5688#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_dealloc_5688_to_5728_of_sub_placed
    (v10_sub_ok_dealloc_125316_of_dealloc_placed hdealloc)
    st s0 s1 out p1 p1_new cap_enc c1 c2 p2 l2 pbA Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

theorem v10_ct2Sent_dealloc_5688_to_5728_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5688#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_dealloc_5688_to_5728_of_sub_placed hA.dealloc_ok
    st s0 s1 out p1 p1_new cap_enc c1 c2 p2 l2 pbA Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

theorem v10_ct2Sent_dealloc_5688_to_5728_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 l2 pbA : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5688#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗ A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_dealloc_5688_to_5728_of_dealloc_placed hA.dealloc
    st s0 s1 out p1 p1_new cap_enc c1 c2 p2 l2 pbA Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

/-! ## 2. Total-Correctness Cloning of `Authenticator` Buffers (`+1720 -> +5540` and `+5540 -> +5688`) -/

/-- Total-correctness (`SepWP`, zero OOM/panic branches) clone of `authPb.rootKey` at
    `+1720 -> +5540` from `FromPbAllocHooksPlacedBudget` under
    `FitsEvents M lim st (authKeyCloneEvents rootKey)`. -/
theorem v10_ct2Sent_clone_rootKey_1720_to_5540_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 cap_enc c1 c2 l2 pbA : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1)
    (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = BitVec.ofNat 64 rootKey.length)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5540#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A.repAlloc c1 p1 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧
          sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x24 = c1 ∧
          sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = l2 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hr_nil] at hx28_1 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx28_1 ⊢
    change s1.pc = (blkPl_333).base + 1720#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5540#64) s1 _ _
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim st sm ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x21 = 1#64 ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) ?_
      fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨1#64, hPm, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5540#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc c1 p1 []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc c1 p1 [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗
        A.pool lim st sc ∗ Rest by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : rootKey.isEmpty = false := by
      cases h : rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents rootKey = rustAllocEvents rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right
      (sepConj_mono_left
        (vecU8Payload_pos_unpack A.repAlloc c1 p1 rootKey hr_pos))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt fsp encoderFromPbStack ∗
          (⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64 ∧ c1 ≠ 0#64⌝ ∗
           (A.repAlloc.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
            memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length))) ∗
          A.pool lim st s1 ∗ Rest =
        ⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64 ∧ c1 ≠ 0#64⌝ ∗
        (memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
         A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
         memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length) ∗
         A.pool lim st s1 ∗ Rest) by
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk rootKey.length 1 := ⟨⟨hr_pos, hpow1, hr_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s1.pc = (blkPl_333).base + 1720#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5540#64) s1 _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (rootKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s1 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, p1, rootKey)
    have hacp_mc : AllocCallPreserved s1 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = fsp := ‹sf.sp = s1.sp›.trans hsp1
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr1.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length)
            (sf_1.readReg64 .x0) rootKey ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sm ∗
          Rest) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x21 = sf_1.readReg64 .x0 ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) ?_
      fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨sf_1.readReg64 .x0, hPm, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5540#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc c1 p1 rootKey hr_le hr_cap hptr0 hcap0_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) rootKey hr_pos hr_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, hsp_sf, stackAt_encoderFromPb_split_allocHook fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live (sf_1.readReg64 .x0) rootKey.length 1 ∗
         (sf_1.readReg64 .x0 ↦ₛ rootKey)) ∗
        (A.repAlloc.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
         memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
        memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sc ∗ Rest by
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hp (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v10_ct2Sent_clone_rootKey_1720_to_5540_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 cap_enc c1 c2 l2 pbA : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1720#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1) (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2) (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = BitVec.ofNat 64 rootKey.length)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5540#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ p1_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
          vecCapPtrDealloc A.repAlloc c1 p1 ∗
          A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = l2 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_clone_rootKey_1720_to_5540_of_placedHooks hA.toPlacedBudget
    st s0 s1 out p1 cap_enc c1 c2 l2 pbA rootKey Rest hfits hsp0_align
    hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1

/-- Total-correctness (`SepWP`, zero OOM/panic branches) clone of `authPb.macKey` at
    `+5540 -> +5688` from `FromPbAllocHooksPlacedBudget` under
    `FitsEvents M lim st (authKeyCloneEvents macKey)`. -/
theorem v10_ct2Sent_clone_macKey_5540_to_5688_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 v184 pbA : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5540#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx22_1 : s1.readReg64 .x22 = cap_enc)
    (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 macKey.length)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5688#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A.repAlloc c2 p2 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = p1 ∧
          sm.readReg64 .x21 = p1_new ∧
          sm.readReg64 .x22 = cap_enc ∧
          sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x24 = c1 ∧
          sm.readReg64 .x25 = c2 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 macKey.length ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0) := by
  have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
  have h232 : (s0.sp - 2400#64) + 232#64 = s0.sp - 2168#64 := by bv_omega
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hm_nil] at hx26_1 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx26_1 ⊢
    change s1.pc = (blkPl_333).base + 5540#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5688#64) s1 _ _
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ 1#64) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          vecCapPtrDealloc A.repAlloc c2 p2 ∗
          A.pool lim st sm ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = 0#64 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) ?_
      fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨1#64, hPm, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5688#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc c2 p2 []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, h184, h232]
      refine Entails.trans (Entails.of_eq (show _ =
        emp ∗ vecU8Payload A.repAlloc c2 p2 [] ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2216#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 2168#64) ↦₆₄ p2) ∗
        A.pool lim st sc ∗ Rest by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hn (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : macKey.isEmpty = false := by
      cases h : macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents macKey = rustAllocEvents macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (vecU8Payload_pos_unpack A.repAlloc c2 p2 macKey hm_pos))))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          (⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64 ∧ c2 ≠ 0#64⌝ ∗
           (A.repAlloc.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
            memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length))) ∗
          A.pool lim st s1 ∗ Rest =
        ⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64 ∧ c2 ≠ 0#64⌝ ∗
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
         ((s0.sp - 2216#64) ↦₆₄ v184) ∗ ((s0.sp - 2168#64) ↦₆₄ p2) ∗
         A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
         memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length) ∗
         A.pool lim st s1 ∗ Rest) by
      rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), h184, h232]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim
    rintro ⟨hm_le, hm_cap, hptr0, hcap0_ne⟩
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hrlay : RustLayoutOk macKey.length 1 := ⟨⟨hm_pos, hpow1, hm_lt63⟩, by decide⟩
    have hshim := hA.shim_ok
    dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec] at halloc
    have hmc := hA.memcpy_ok
    dsimp only [allocMemcpyVmSpec] at hmc
    clear hA
    change s1.pc = (blkPl_333).base + 5540#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5688#64) s1 _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
    simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym)
    simp only [State.setMem_setMem]
    wp_call halloc (macKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s1 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    wp_steps_sync_333 (lsρ spqrMemcpySym)
    simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, p2, macKey)
    have hacp_mc : AllocCallPreserved s1 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf2 : sf_2.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr1.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ sf_1.readReg64 .x0) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length)
            (sf_1.readReg64 .x0) macKey ∗
          vecCapPtrDealloc A.repAlloc c2 p2 ∗
          A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sm ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = BitVec.ofNat 64 macKey.length ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) ?_
      fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨sf_1.readReg64 .x0, hPm, hregs⟩
    wp_steps_sync_333 ((blkPl_333).base + 5688#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_pos_dealloc A.repAlloc c2 p2 macKey hm_le hm_cap hptr0 hcap0_ne
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) macKey hm_pos hm_lt63 hoom0
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [hsp_sf, hsp_sf1, hsp_sf2]
      rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), h184, h232]
      dsimp only [Reg.x0] at hp ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (A.repAlloc.live (sf_1.readReg64 (Reg.gpr 0#5)) macKey.length 1 ∗
         (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ macKey)) ∗
        (A.repAlloc.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
         memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
        memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
        ((s0.sp - 2216#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
        ((s0.sp - 2168#64) ↦₆₄ p2) ∗
        A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sc ∗ Rest by
          dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hp (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done

theorem v10_ct2Sent_clone_macKey_5540_to_5688_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p1_new cap_enc c1 c2 p2 v184 pbA : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5540#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = p1) (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx22_1 : s1.readReg64 .x22 = cap_enc) (hx23_1 : s1.readReg64 .x23 = pbA + 8#64)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = c2)
    (hx26_1 : s1.readReg64 .x26 = BitVec.ofNat 64 macKey.length)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5688#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ p2_new : BitVec 64,
        (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
          vecCapPtrDealloc A.repAlloc c2 p2 ∗
          A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x21 = p1_new ∧ sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧ sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = BitVec.ofNat 64 macKey.length ∧
        sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v10_ct2Sent_clone_macKey_5540_to_5688_of_placedHooks hA.toPlacedBudget
    st s0 s1 out p1 p1_new cap_enc c1 c2 p2 v184 pbA macKey Rest hfits hsp0_align
    hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlacedBudget
