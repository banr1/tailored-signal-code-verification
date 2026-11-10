/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part C

Proves `FreeOnlyEvs` deallocation helpers (`+9852 -> +9936`, `+10456 -> +10396`, `+10532 -> +10396`,
`+10416 -> +10396`, `+10492 -> +10396`) for Variant 6 and re-exports the total-correctness
`ProtoAuthenticator` buffer clone theorems from `Variant6cPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved stackAt_encoderFromPb_split_allocHook
   v1_bv_add_add_lit v1_bv_sub_sub_lit v1_shl8_extract_0_8)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs seq_clean_st subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
  (v6hr_sub_ok_dealloc_of_placedHooks v6hr_sub_ok_dealloc_placed)

export Variant6cPlacedBudgetAux
  (v6hr_oom_11596_entails_of_panic_placed v6hr_oom_11596_entails_of_placedHooks
   v6hr_oom_11596_entails_placed)
export Variant6cPlacedBudgetAux
  (v6hr_oom_11620_entails_of_panic_placed v6hr_oom_11620_entails_of_placedHooks
   v6hr_oom_11620_entails_placed)
export Variant6cPlacedBudgetAux
  (v6hr_clone_rootKey_3796_to_8812_of_placedHooks v6hr_clone_rootKey_3796_to_8812_placed
   v6hr_clone_macKey_8812_to_9852_of_placedHooks v6hr_clone_macKey_8812_to_9852_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_sub_sub_lit v1_shl8_extract_0_8 v1_bv_add_add_lit

/-! ## 3. `FreeOnlyEvs` Deallocation Helpers (`+9852 -> +9936`, `+10416 -> +10396`, `+10492 -> +10396`) -/

/-- Deallocate the input `ProtoAuthenticator` buffers `(c1, p1)` and `(c2, p2)` at `+9852 -> +9936`
    after cloning `rootKey` and `macKey`. -/
theorem v6hr_dealloc_auth_9852_to_9936_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State)
    (out c0 c1 p1 p1_new l1 c2 p2 c3 l3 : BitVec 64)
    (d112 d116 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9852#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = l3 ∧
          sm.readReg64 .x24 = p1_new >>> 8 ∧ sm.readReg64 .x25 = p1_new ∧
          sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  clear hfsp_eq hsp0_align
  have hw11 : (d112.zeroExtend 64).setWidth 32 = d112 := by bv_omega
  have hw12 : (d116.zeroExtend 64).setWidth 32 = d116 := by bv_omega
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 9892#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 192#64) ↦₆₄ p1_new) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
      vecCapPtrDealloc A.repAlloc c2 p2 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ Rest)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = l1 ∧
      sm.readReg64 .x23 = l3 ∧ sm.readReg64 .x25 = p1_new ∧ sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [show vecCapPtrDealloc A.repAlloc c1 p1 =
      if (c1 == 0#64) = true then emp else A.live p1 c1.toNat 1 ∗ memRegion p1 c1.toNat from rfl]
    by_cases hc1 : (c1 == 0#64) = true
    · simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      change s1.pc = (blkPl_333).base + 9852#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9892#64) s1 _ _
      wp_steps
      wp_done
    · have hbeq : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc c1.toNat 1
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      simp only [sepConj_assoc]
      change s1.pc = (blkPl_333).base + 9852#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9892#64) s1 _ _
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine align_pre_st
        (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2
      ⟨hsp2, hx11_2, hx12_2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
    rw [show vecCapPtrDealloc A.repAlloc c2 p2 =
      if (c2 == 0#64) = true then emp else A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat from rfl]
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      change s2.pc = (blkPl_333).base + 9892#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9936#64) s2 _ _
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 9936#64) s2
          (stackAt fsp encoderFromPbStack ∗
            ((fsp + 192#64) ↦₆₄ p1_new) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest)
          (fun sm Pm =>
            (Pm ⊢
              stackAt fsp encoderFromPbStack ∗
              ((fsp + 192#64) ↦₆₄ p1_new) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
              A.pool lim (M.stepEvents evs1 st) sm ∗ Rest) ∧
            sm.sp = fsp ∧
            sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
            sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = l3 ∧
            sm.readReg64 .x24 = p1_new >>> 8 ∧ sm.readReg64 .x25 = p1_new ∧
            sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = c0 ∧
            sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) := by
        wp_steps
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩
    · have hbeq : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      change s2.pc = (blkPl_333).base + 9892#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9936#64) s2 _ _
      have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 9936#64) s2
          (stackAt fsp encoderFromPbStack ∗
            ((fsp + 192#64) ↦₆₄ p1_new) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
            A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest)
          (fun sm Pm =>
            (Pm ⊢
              stackAt fsp encoderFromPbStack ∗
              ((fsp + 192#64) ↦₆₄ p1_new) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents c2.toNat 1) (M.stepEvents evs1 st)) sm ∗
              Rest) ∧
            sm.sp = fsp ∧
            sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
            sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = l3 ∧
            sm.readReg64 .x24 = p1_new >>> 8 ∧ sm.readReg64 .x25 = p1_new ∧
            sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = c0 ∧
            sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) := by
        rw [stackAt_encoderFromPb_split_allocHook fsp]
        simp only [sepConj_assoc]
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st
          (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents c2.toNat 1,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 c2.toNat), ?_, hq⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hp

theorem v6hr_dealloc_auth_9852_to_9936_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 c1 p1 p1_new l1 c2 p2 c3 l3 : BitVec 64)
    (d112 d116 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9852#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = l3 ∧
          sm.readReg64 .x24 = p1_new >>> 8 ∧ sm.readReg64 .x25 = p1_new ∧
          sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_auth_9852_to_9936_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 c1 p1 p1_new l1 c2 p2 c3 l3 d112 d116 Rest hsp0_align hpc1 hrun1 hsp1
    hx11_1 hx12_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

theorem v6hr_dealloc_auth_9852_to_9936_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 c1 p1 p1_new l1 c2 p2 c3 l3 : BitVec 64)
    (d112 d116 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9852#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d112.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d116.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = l3)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = c3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9936#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 192#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x11 = d112.zeroExtend 64 ∧ sm.readReg64 .x12 = d116.zeroExtend 64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x23 = l3 ∧
          sm.readReg64 .x24 = p1_new >>> 8 ∧ sm.readReg64 .x25 = p1_new ∧
          sm.readReg64 .x26 = l1 ∧ sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = c3 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_auth_9852_to_9936_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 c1 p1 p1_new l1 c2 p2 c3 l3 d112 d116 Rest hsp0_align hpc1 hrun1 hsp1
    hx11_1 hx12_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

/-- Deallocate `(c0, p0)` on the `decPb = none` error cleanup path (`+10456 -> +10396`). -/
theorem v6hr_dealloc_c0_10456_to_10396_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10456#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  clear hfsp_eq hsp0_align
  rw [show vecCapPtrDealloc A.repAlloc c0 p0 =
    if (c0 == 0#64) = true then emp else A.live p0 c0.toNat 1 ∗ memRegion p0 c0.toNat from rfl]
  by_cases hc0 : (c0 == 0#64) = true
  · simp only [hc0, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    refine seq_clean_st
      (mid := lsmpl.base 333 + 10536#64)
      (P_mid := fun sm =>
        stackAt fsp encoderFromPbStack ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
        A.pool lim st sm ∗ Rest)
      (Q := fun s2 =>
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ TraceCalleeSaved s2 s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 10456#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10536#64) s1 _ _
      wp_steps
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
      change s2.pc = (blkPl_333).base + 10536#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10396#64) s2 _ _
      wp_steps
      wp_done
  · have hbeq : (c0 == 0#64) = false := Bool.eq_false_iff.mpr hc0
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
    clear hdealloc_ok
    simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
    apply sepWP_evs_dealloc c0.toNat 1
    rw [stackAt_encoderFromPb_split_allocHook fsp]
    simp only [sepConj_assoc]
    change s1.pc = (blkPl_333).base + 10456#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10396#64) s1 _ _
    wp_steps
    wp_apply
    have hacp_sf : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
    wp_steps
    refine align_pre_st
      (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
    wp_done

theorem v6hr_dealloc_c0_10456_to_10396_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10456#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_c0_10456_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v6hr_dealloc_c0_10532_to_10396_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10532#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  clear hfsp_eq hsp0_align
  rw [show vecCapPtrDealloc A.repAlloc c0 p0 =
    if (c0 == 0#64) = true then emp else A.live p0 c0.toNat 1 ∗ memRegion p0 c0.toNat from rfl]
  by_cases hc0 : (c0 == 0#64) = true
  · simp only [hc0, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    change s1.pc = (blkPl_333).base + 10532#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10396#64) s1 _ _
    wp_steps
    wp_done
  · have hbeq : (c0 == 0#64) = false := Bool.eq_false_iff.mpr hc0
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
    clear hdealloc_ok
    simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
    apply sepWP_evs_dealloc c0.toNat 1
    refine seq_clean_st
      (mid := lsmpl.base 333 + 10460#64)
      (P_mid := fun sm =>
        stackAt fsp encoderFromPbStack ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
        A.live p0 c0.toNat 1 ∗ memRegion p0 c0.toNat ∗
        A.pool lim st sm ∗ Rest)
      (Q := fun s2 =>
        s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 10532#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10460#64) s1 _ _
      wp_steps
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, htr2⟩
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      simp only [sepConj_assoc]
      change s2.pc = (blkPl_333).base + 10460#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10396#64) s2 _ _
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s2 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine align_pre_st
        (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
      wp_done

theorem v6hr_dealloc_c0_10456_to_10396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10456#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_c0_10456_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v6hr_dealloc_c0_10532_to_10396_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10532#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_c0_10532_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

theorem v6hr_dealloc_c0_10532_to_10396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10532#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_c0_10532_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 Rest hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1

/-- Deallocate cloned `(l1, p1_new)`, `(l2, p2_new)`, and `hdr` `(c0, p0)` on the `decPb = none`
    error cleanup path (`+10416 -> +10396`). -/
theorem v6hr_dealloc_cloned_10416_to_10396_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10416#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗
        vecU8Payload A.repAlloc l2 p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdr ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hv1 := vecU8Payload_entails_dealloc A.repAlloc l1 p1_new rootKey
  have hv2 := vecU8Payload_entails_dealloc A.repAlloc l2 p2_new macKey
  have hv0 := vecU8Payload_entails_dealloc A.repAlloc c0 p0 hdr
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv0))))))) ?_
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 10436#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 136#64) ↦₆₄ p2_new) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
      ((fsp + 216#64) ↦₆₄ l2) ∗
      vecCapPtrDealloc A.repAlloc l2 p2_new ∗
      vecCapPtrDealloc A.repAlloc c0 p0 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ Rest)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · rw [show vecCapPtrDealloc A.repAlloc l1 p1_new =
      if (l1 == 0#64) = true then emp else A.live p1_new l1.toNat 1 ∗ memRegion p1_new l1.toNat from rfl]
    by_cases hl1 : (l1 == 0#64) = true
    · simp only [hl1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      change s1.pc = (blkPl_333).base + 10416#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10436#64) s1 _ _
      wp_steps
      wp_done
    · have hbeq : (l1 == 0#64) = false := Bool.eq_false_iff.mpr hl1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc l1.toNat 1
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      simp only [sepConj_assoc]
      change s1.pc = (blkPl_333).base + 10416#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10436#64) s1 _ _
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st
        (by sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, htr2⟩
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 10456#64)
      (P_evs := fun evs2 sm =>
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗
        (((fsp + 136#64) ↦₆₄ p2_new) ∗ ((fsp + 216#64) ↦₆₄ l2) ∗ Rest))
      (Q := fun s3 =>
        s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x27 = c0 ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · rw [show vecCapPtrDealloc A.repAlloc l2 p2_new =
        if (l2 == 0#64) = true then emp else A.live p2_new l2.toNat 1 ∗ memRegion p2_new l2.toNat from rfl]
      by_cases hl2 : (l2 == 0#64) = true
      · have hl2_eq : l2 = 0#64 := of_decide_eq_true hl2
        subst hl2_eq
        simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) ?_
        change s2.pc = (blkPl_333).base + 10436#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10456#64) s2 _ _
        wp_steps
        wp_done
      · have hbeq : (l2 == 0#64) = false := Bool.eq_false_iff.mpr hl2
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc l2.toNat 1
        rw [stackAt_encoderFromPb_split_allocHook fsp]
        simp only [sepConj_assoc]
        change s2.pc = (blkPl_333).base + 10436#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10456#64) s2 _ _
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st
          (by sep_ac_rfl) ?_
        wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx27_3, htr3⟩
      cases hfsp_eq
      have hc0_step := v6hr_dealloc_c0_10456_to_10396_of_sub_placed hdealloc_ok
        (M.stepEvents evs2 (M.stepEvents evs1 st)) s0 s3 out c0 p0
        ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗ Rest)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_3 htr3
      refine SepWP.mono hc0_step fun sm _Pm _ _ ⟨evs3, hevs3, hPm, hregs⟩ => ?_
      refine ⟨evs1 ++ evs2 ++ evs3, (hevs1.append hevs2).append hevs3, ?_, hregs⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
          LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v6hr_dealloc_cloned_10416_to_10396_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10416#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗
        vecU8Payload A.repAlloc l2 p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdr ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_cloned_10416_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 l1 p1_new l2 p2_new rootKey macKey hdr Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1

theorem v6hr_dealloc_cloned_10416_to_10396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10416#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗
        vecU8Payload A.repAlloc l2 p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdr ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_cloned_10416_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 l1 p1_new l2 p2_new rootKey macKey hdr Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1

/-- Deallocate cloned `(l1, p1_new)`, `(l2, p2_new)`, and `hdr` `(c0, p0)` on the
    `PolyDecoder::from_pb = Err(_)` error cleanup path (`+10492 -> +10396`). -/
theorem v6hr_dealloc_cloned_10492_to_10396_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10492#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗
        vecU8Payload A.repAlloc l2 p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdr ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hv1 := vecU8Payload_entails_dealloc A.repAlloc l1 p1_new rootKey
  have hv2 := vecU8Payload_entails_dealloc A.repAlloc l2 p2_new macKey
  have hv0 := vecU8Payload_entails_dealloc A.repAlloc c0 p0 hdr
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv0))))))) ?_
  generalize hfsp_eq : s0.sp - 2400#64 = fsp at hfsp_align hsp1 ⊢
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 10512#64)
    (P_evs := fun evs1 sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 136#64) ↦₆₄ p2_new) ∗ ((fsp + 144#64) ↦₆₄ p0) ∗
      ((fsp + 216#64) ↦₆₄ l2) ∗
      vecCapPtrDealloc A.repAlloc l2 p2_new ∗
      vecCapPtrDealloc A.repAlloc c0 p0 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗ Rest)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
      s2.readReg64 .x27 = c0 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · rw [show vecCapPtrDealloc A.repAlloc l1 p1_new =
      if (l1 == 0#64) = true then emp else A.live p1_new l1.toNat 1 ∗ memRegion p1_new l1.toNat from rfl]
    by_cases hl1 : (l1 == 0#64) = true
    · simp only [hl1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      change s1.pc = (blkPl_333).base + 10492#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10512#64) s1 _ _
      wp_steps
      wp_done
    · have hbeq : (l1 == 0#64) = false := Bool.eq_false_iff.mpr hl1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc l1.toNat 1
      rw [stackAt_encoderFromPb_split_allocHook fsp]
      simp only [sepConj_assoc]
      change s1.pc = (blkPl_333).base + 10492#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10512#64) s1 _ _
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st
        (by sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx19_2, hx27_2, htr2⟩
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 10532#64)
      (P_evs := fun evs2 sm =>
        stackAt fsp encoderFromPbStack ∗
        ((fsp + 144#64) ↦₆₄ p0) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) sm ∗
        (((fsp + 136#64) ↦₆₄ p2_new) ∗ ((fsp + 216#64) ↦₆₄ l2) ∗ Rest))
      (Q := fun s3 =>
        s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧
        s3.readReg64 .x27 = c0 ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · rw [show vecCapPtrDealloc A.repAlloc l2 p2_new =
        if (l2 == 0#64) = true then emp else A.live p2_new l2.toNat 1 ∗ memRegion p2_new l2.toNat from rfl]
      by_cases hl2 : (l2 == 0#64) = true
      · have hl2_eq : l2 = 0#64 := of_decide_eq_true hl2
        subst hl2_eq
        simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) ?_
        change s2.pc = (blkPl_333).base + 10512#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10532#64) s2 _ _
        wp_steps
        wp_done
      · have hbeq : (l2 == 0#64) = false := Bool.eq_false_iff.mpr hl2
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        apply sepWP_evs_dealloc l2.toNat 1
        rw [stackAt_encoderFromPb_split_allocHook fsp]
        simp only [sepConj_assoc]
        change s2.pc = (blkPl_333).base + 10512#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10532#64) s2 _ _
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st
          (by sep_ac_rfl) ?_
        wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨hsp3, hx19_3, hx27_3, htr3⟩
      cases hfsp_eq
      have hc0_step := v6hr_dealloc_c0_10532_to_10396_of_sub_placed hdealloc_ok
        (M.stepEvents evs2 (M.stepEvents evs1 st)) s0 s3 out c0 p0
        ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗ Rest)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_3 htr3
      refine SepWP.mono hc0_step fun sm _Pm _ _ ⟨evs3, hevs3, hPm, hregs⟩ => ?_
      refine ⟨evs1 ++ evs2 ++ evs3, (hevs1.append hevs2).append hevs3, ?_, hregs⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append,
          LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v6hr_dealloc_cloned_10492_to_10396_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10492#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗
        vecU8Payload A.repAlloc l2 p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdr ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_cloned_10492_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 l1 p1_new l2 p2_new rootKey macKey hdr Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1

theorem v6hr_dealloc_cloned_10492_to_10396_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out c0 p0 l1 p1_new l2 p2_new : BitVec 64)
    (rootKey macKey hdr : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10492#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
        (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗
        vecU8Payload A.repAlloc l2 p2_new macKey ∗
        vecU8Payload A.repAlloc c0 p0 hdr ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 144#64) ↦₆₄ p0) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x25 = 0#64 ∧ TraceCalleeSaved sm s0) :=
  v6hr_dealloc_cloned_10492_to_10396_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 l1 p1_new l2 p2_new rootKey macKey hdr Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6cPlacedBudget
