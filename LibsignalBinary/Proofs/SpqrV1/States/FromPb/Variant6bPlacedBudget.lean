/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part B

Proves `StateDecode` error deallocation paths from `+3760` (`+3760 -> +10316`) under `FreeOnlyEvs`
and the `VmPreserved`-strengthened `+3760 -> +3796` validation step, re-exporting early `MsgDecode`
cleanup helpers from `Variant6bPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false none2Cap_add_two_beq_zero noneCap_add_two_beq_zero vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v6hr_Regs1508 v6hr_Saved10324Preserved)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append)
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
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs seq_clean_st subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (blk333_noSvc0)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
  (v6hr_sub_ok_dealloc_of_placedHooks v6hr_sub_ok_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudgetAux
  (v6hr_Regs1508_of_stripS v6hr_Regs1508_to_stripS v6hr_Saved10324Preserved_of_stripS
   v6hr_rejoin_encoderStack v6hr_split_encoderStack)

export Variant6bPlacedBudgetAux
  (v6hr_sub_ok_decoder_from_pb_placed v6hr_sub_ok_decoder_from_pb_mem_placed
   v6hr_dealloc_hdr_1600_to_10324_of_sub_placed v6hr_dealloc_hdr_1600_to_10324_of_placedHooks
   v6hr_dealloc_hdr_1600_to_10324_placed
   v6hr_dealloc_auth_1536_to_1600_of_sub_placed v6hr_dealloc_auth_1536_to_1600_of_placedHooks
   v6hr_dealloc_auth_1536_to_1600_placed)
export Variant6bPlacedBudgetAux
  (v6hr_err_1520_uc_none_to_10324_placed v6hr_err_1520_uc_none_to_10324_placed_budget
   v6hr_err_1520_auth_none_to_10324_of_sub_placed v6hr_err_1520_auth_none_to_10324_of_placedHooks
   v6hr_err_1520_auth_none_to_10324_placed
   v6hr_err_1520_auth_some_to_10324_of_sub_placed v6hr_err_1520_auth_some_to_10324_of_placedHooks
   v6hr_err_1520_auth_some_to_10324_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

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

/-! ## 2. `StateDecode` Error Paths from `+3760` (`s.uc = none`, `hdr.length ≠ 64`, `auth = none`) -/

/-- `VmPreserved`-strengthened Variant 6 `StateDecode` error (`s.uc = none`, `+3760 -> +10316`). -/
theorem v6hr_err_3760_uc_none_to_10316_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ ((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 0#64 ∧
        sm.readReg64 .x23 = w104) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6bPlaced.v6hr_err_3760_uc_none_to_10316_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v224 Rest
      hsp0_align (by simpa using hpc1) (by simpa using hrun1)
      (v6hr_Regs1508_to_stripS hregs1))
    fun sm Pm hvm ⟨hPm, hpres, hx23⟩ =>
      ⟨hPm, hvm, v6hr_Saved10324Preserved_of_stripS hpres, by simpa using hx23⟩

theorem v6hr_err_3760_uc_none_to_10316_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 0#64 ∧
        sm.readReg64 .x23 = w104) := by
  have hwp := v6hr_err_3760_uc_none_to_10316_placed (ext := ext)
    s0 s1 out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v224
    (A.pool lim st s1 ∗ Rest) hsp0_align hpc1 hrun1 hregs1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

theorem v6hr_dealloc_hdr_4856_to_10316_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out c0 p0 cd pd ld v144 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4856#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2168#64) ↦₆₄ pd) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out pd cd (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = ld) := by
  rw [show vecCapPtrDealloc A.repAlloc c0 p0 =
    if (c0 == 0#64) = true then emp else A.live p0 c0.toNat 1 ∗ memRegion p0 c0.toNat from rfl]
  by_cases hc0 : (c0 == 0#64) = true
  · simp only [hc0, ↓reduceIte, sepConj_emp, emp_sepConj]
    apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    refine seq_clean_st
      (mid := lsmpl.base 333 + 6856#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        A.pool lim st sm ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 4856#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6856#64) s1 _ _
      wp_steps
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx25_2, hx28_2, htr2⟩
      refine seq_clean_st
        (mid := lsmpl.base 333 + 10308#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ v144) ∗
          ((s0.sp - 2168#64) ↦₆₄ pd) ∗
          A.pool lim st sm ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x25 = 0#64 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 6856#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10308#64) s2 _ _
        wp_steps
        wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx25_3, hx28_3, htr3⟩
        change s3.pc = (blkPl_333).base + 10308#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10316#64) s3 _ _
        wp_steps
        wp_done
  · have hbeq : (c0 == 0#64) = false := Bool.eq_false_iff.mpr hc0
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
    clear hdealloc_ok
    simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
    apply sepWP_evs_dealloc c0.toNat 1
    refine seq_clean_st
      (mid := lsmpl.base 333 + 9908#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ p0) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        A.live p0 c0.toNat 1 ∗
        memRegion p0 c0.toNat ∗
        A.pool lim st sm ∗
        Rest)
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = c0 ∧
        sm.readReg64 .x23 = ld ∧
        sm.readReg64 .x25 = 0#64 ∧
        sm.readReg64 .x26 = noneCap ∧
        sm.readReg64 .x28 = cd ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 4856#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9908#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 9908#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx21_2, hx23_2, hx25_2, hx26_2, hx28_2, htr2⟩
      dsimp only [noneCap] at hx26_2
      refine seq_clean_st
        (mid := lsmpl.base 333 + 10308#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ p0) ∗
          ((s0.sp - 2168#64) ↦₆₄ pd) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents c0.toNat 1) st) sm ∗
          Rest)
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x25 = 0#64 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · refine SepWP.weaken_pre (sepConj_mono_left (v6hr_split_encoderStack s0.sp)) ?_
        change s2.pc = (blkPl_333).base + 9908#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10308#64) s2 _ _
        have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
            ((blkPl_333).base + 10308#64) s2
            ((stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
              ((s0.sp - 2256#64) ↦₆₄ p0) ∗
              ((s0.sp - 2168#64) ↦₆₄ pd) ∗
              A.live p0 c0.toNat 1 ∗
              memRegion p0 c0.toNat ∗
              A.pool lim st s2 ∗
              Rest)
            (fun sm Pm =>
              (Pm ⊢
                (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
                ((s0.sp - 2256#64) ↦₆₄ p0) ∗
                ((s0.sp - 2168#64) ↦₆₄ pd) ∗
                A.pool lim (M.stepEvents (rustDeallocEvents c0.toNat 1) st) sm ∗
                Rest) ∧
              sm.sp = s0.sp - 2400#64 ∧
              sm.readReg64 .x19 = out ∧
              sm.readReg64 .x23 = ld ∧
              sm.readReg64 .x25 = 0#64 ∧
              sm.readReg64 .x28 = cd ∧
              TraceCalleeSaved sm s0) := by
          wp_steps
          wp_apply
          have hacp_sf : AllocCallPreserved s2 sf := by
            simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
          rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
          wp_steps
          refine align_pre_st (by rw [hsp2]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
          wp_done
        exact SepWP.mono hstep fun _ _ _ _ ⟨hp, hq⟩ =>
          ⟨Entails.trans hp (sepConj_mono_left (v6hr_rejoin_encoderStack s0.sp)), hq⟩
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx25_3, hx28_3, htr3⟩
        change s3.pc = (blkPl_333).base + 10308#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10316#64) s3 _ _
        wp_steps
        wp_done

theorem v6hr_dealloc_hdr_4856_to_10316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 cd pd ld v144 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4856#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2168#64) ↦₆₄ pd) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out pd cd (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = ld) :=
  v6hr_dealloc_hdr_4856_to_10316_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 cd pd ld v144 Rest hsp0_align hpc1 hrun1 hsp1
    hx9_1 hx19_1 hx23_1 hx27_1 hx28_1 htr1

theorem v6hr_dealloc_hdr_4856_to_10316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 cd pd ld v144 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4856#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ pd) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2168#64) ↦₆₄ pd) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out pd cd (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = ld) :=
  v6hr_dealloc_hdr_4856_to_10316_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 cd pd ld v144 Rest hsp0_align hpc1 hrun1 hsp1
    hx9_1 hx19_1 hx23_1 hx27_1 hx28_1 htr1

theorem v6hr_dealloc_auth_4760_to_4856_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out c0 p0 c1 p1 c2 p2 cd ld : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4856#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x9 = p0 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine seq_clean_evs
    (mid := lsmpl.base 333 + 4812#64)
    (P_evs := fun evs1 sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      vecCapPtrDealloc A.repAlloc c2 p2 ∗
      A.pool lim (M.stepEvents evs1 st) sm ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x14 = p2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x23 = ld ∧
      sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = cd ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [show vecCapPtrDealloc A.repAlloc c1 p1 =
      if (c1 == 0#64) = true then emp else A.live p1 c1.toNat 1 ∗ memRegion p1 c1.toNat from rfl]
    by_cases hc1 : (c1 == 0#64) = true
    · simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj]
      apply sepWP_evs_nil
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      change s1.pc = (blkPl_333).base + 4760#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4812#64) s1 _ _
      wp_steps
      wp_done
    · have hbeq : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply sepWP_evs_dealloc c1.toNat 1
      refine SepWP.weaken_pre (sepConj_mono_left (v6hr_split_encoderStack s0.sp)) ?_
      change s1.pc = (blkPl_333).base + 4760#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4812#64) s1 _ _
      have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4812#64) s1
          ((stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            A.live p1 c1.toNat 1 ∗
            memRegion p1 c1.toNat ∗
            vecCapPtrDealloc A.repAlloc c2 p2 ∗
            A.pool lim st s1 ∗
            Rest)
          (fun sm Pm =>
            (Pm ⊢
              (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
              vecCapPtrDealloc A.repAlloc c2 p2 ∗
              A.pool lim (M.stepEvents (rustDeallocEvents c1.toNat 1) st) sm ∗
              Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x9 = p0 ∧
            sm.readReg64 .x14 = p2 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x21 = c2 ∧
            sm.readReg64 .x23 = ld ∧
            sm.readReg64 .x27 = c0 ∧
            sm.readReg64 .x28 = cd ∧
            TraceCalleeSaved sm s0) := by
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp1]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      exact SepWP.mono hstep fun _ _ _ _ ⟨hp, hq⟩ =>
        ⟨Entails.trans hp (sepConj_mono_left (v6hr_rejoin_encoderStack s0.sp)), hq⟩
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx21_2, hx23_2, hx27_2, hx28_2, htr2⟩
    rw [show vecCapPtrDealloc A.repAlloc c2 p2 =
      if (c2 == 0#64) = true then emp else A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat from rfl]
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj]
      change s2.pc = (blkPl_333).base + 4812#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4856#64) s2 _ _
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4856#64) s2
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗
            Rest)
          (fun sm Pm =>
            (Pm ⊢
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              A.pool lim (M.stepEvents evs1 st) sm ∗
              Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x9 = p0 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x23 = ld ∧
            sm.readReg64 .x27 = c0 ∧
            sm.readReg64 .x28 = cd ∧
            TraceCalleeSaved sm s0) := by
        wp_steps
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs1, hevs1, hp, hq⟩
    · have hbeq : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre (sepConj_mono_left (v6hr_split_encoderStack s0.sp)) ?_
      change s2.pc = (blkPl_333).base + 4812#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4856#64) s2 _ _
      have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4856#64) s2
          ((stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
            A.live p2 c2.toNat 1 ∗
            memRegion p2 c2.toNat ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗
            Rest)
          (fun sm Pm =>
            (Pm ⊢
              (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 7552#64) 1056) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents c2.toNat 1) (M.stepEvents evs1 st)) sm ∗
              Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧
            sm.readReg64 .x9 = p0 ∧
            sm.readReg64 .x19 = out ∧
            sm.readReg64 .x23 = ld ∧
            sm.readReg64 .x27 = c0 ∧
            sm.readReg64 .x28 = cd ∧
            TraceCalleeSaved sm s0) := by
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp2]; simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents c2.toNat 1,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 c2.toNat), ?_, hq⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.trans hp (sepConj_mono_left (v6hr_rejoin_encoderStack s0.sp))

theorem v6hr_dealloc_auth_4760_to_4856_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 c1 p1 c2 p2 cd ld : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4856#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x9 = p0 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0) :=
  v6hr_dealloc_auth_4760_to_4856_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 c1 p1 c2 p2 cd ld Rest hsp0_align hpc1 hrun1 hsp1
    hx9_1 hx14_1 hx19_1 hx21_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

theorem v6hr_dealloc_auth_4760_to_4856_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 c1 p1 c2 p2 cd ld : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx9_1 : s1.readReg64 .x9 = p0)
    (hx14_1 : s1.readReg64 .x14 = p2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = c2)
    (hx23_1 : s1.readReg64 .x23 = ld)
    (hx24_1 : s1.readReg64 .x24 = c1)
    (hx26_1 : s1.readReg64 .x26 = p1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = cd)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4856#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x9 = p0 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = ld ∧
          sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = cd ∧
          TraceCalleeSaved sm s0) :=
  v6hr_dealloc_auth_4760_to_4856_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 c1 p1 c2 p2 cd ld Rest hsp0_align hpc1 hrun1 hsp1
    hx9_1 hx14_1 hx19_1 hx21_1 hx23_1 hx24_1 hx26_1 hx27_1 hx28_1 htr1

theorem v6hr_err_3760_auth_none_to_10316_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2320#64) ↦₆₄ w24) ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2176#64) ↦₆₄ w120) ∗
            ((s0.sp - 2168#64) ↦₆₄ w96) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  dsimp only [noneCap] at hx24_1
  refine seq_clean_st
    (mid := lsmpl.base 333 + 4856#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2256#64) ↦₆₄ v144) ∗
      ((s0.sp - 2168#64) ↦₆₄ w96) ∗
      vecCapPtrDealloc A.repAlloc c0 p0 ∗
      A.pool lim st sm ∗
      (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hw24 : (w24 == 64#64) = true
    · change s1.pc = (blkPl_333).base + 3760#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4856#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4856#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · refine seq_clean_st
        (mid := lsmpl.base 333 + 4752#64)
        (P_mid := fun sm =>
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2256#64) ↦₆₄ v144) ∗
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          vecCapPtrDealloc A.repAlloc c0 p0 ∗
          A.pool lim st sm ∗
          (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest))
        (Q := fun sm =>
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x9 = p0 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x23 = w104 ∧
          sm.readReg64 .x24 = noneCap ∧
          sm.readReg64 .x27 = c0 ∧
          sm.readReg64 .x28 = w88 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 3760#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4752#64) s1 _ _
        wp_steps_sync_333 ((blkPl_333).base + 4752#64)
        try simp only [State.setMem_setMem]
        refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx23_2, hx24_2, hx27_2, hx28_2, htr2⟩
        dsimp only [noneCap] at hx24_2
        change s2.pc = (blkPl_333).base + 4752#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4856#64) s2 _ _
        wp_steps
        wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx19_2, hx23_2, hx27_2, hx28_2, htr2⟩
    have h4856 := v6hr_dealloc_hdr_4856_to_10316_of_sub_placed hdealloc_ok st s0 s2
      out c0 p0 w88 w96 w104 v144
      (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx23_2 hx27_2 hx28_2 htr2
    refine SepWP.mono h4856 fun sm Pm _ _ ⟨evs, hevs, hent, hx25, hpres, hx23⟩ => ?_
    exact ⟨evs, hevs, Entails.trans hent (Entails.of_eq (by sep_ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_err_3760_auth_none_to_10316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2320#64) ↦₆₄ w24) ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2176#64) ↦₆₄ w120) ∗
            ((s0.sp - 2168#64) ↦₆₄ w96) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_err_3760_auth_none_to_10316_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v80 v144 v224
    Rest hsp0_align hc0 hpc1 hrun1 hregs1

theorem v6hr_err_3760_auth_none_to_10316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2320#64) ↦₆₄ w24) ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2176#64) ↦₆₄ w120) ∗
            ((s0.sp - 2168#64) ↦₆₄ w96) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_err_3760_auth_none_to_10316_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v80 v144 v224
    Rest hsp0_align hc0 hpc1 hrun1 hregs1

theorem v6hr_err_3760_hdr_ne64_auth_some_to_10316_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2320#64) ↦₆₄ w24) ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2176#64) ↦₆₄ w120) ∗
            ((s0.sp - 2168#64) ↦₆₄ w96) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) := by
  rcases hregs1 with ⟨hsp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx28_1, htr1⟩
  have hne_c0 := cap_add_one_beq_zero_false hc0
  have hne_c1 := cap_add_one_beq_zero_false hc1
  have hw24_ne : ¬((w24 == 64#64) = true) := by rw [hw24]; decide
  refine seq_clean_st
    (mid := lsmpl.base 333 + 4760#64)
    (P_mid := fun sm =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      vecCapPtrDealloc A.repAlloc c1 p1 ∗
      vecCapPtrDealloc A.repAlloc c2 p2 ∗
      A.pool lim st sm ∗
      (((s0.sp - 2256#64) ↦₆₄ v144) ∗
       ((s0.sp - 2168#64) ↦₆₄ w96) ∗
       vecCapPtrDealloc A.repAlloc c0 p0 ∗
       ((s0.sp - 2320#64) ↦₆₄ w24) ∗
       ((s0.sp - 2176#64) ↦₆₄ w120) ∗
       Rest))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x9 = p0 ∧
      sm.readReg64 .x14 = p2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x23 = w104 ∧
      sm.readReg64 .x24 = c1 ∧
      sm.readReg64 .x26 = p1 ∧
      sm.readReg64 .x27 = c0 ∧
      sm.readReg64 .x28 = w88 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine seq_clean_st
      (mid := lsmpl.base 333 + 4752#64)
      (P_mid := fun sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st sm ∗
        (((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2168#64) ↦₆₄ w96) ∗
         vecCapPtrDealloc A.repAlloc c0 p0 ∗
         ((s0.sp - 2320#64) ↦₆₄ w24) ∗
         ((s0.sp - 2176#64) ↦₆₄ w120) ∗
         Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x14 = p2 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = c2 ∧
        sm.readReg64 .x23 = w104 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x27 = c0 ∧
        sm.readReg64 .x28 = w88 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 3760#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4752#64) s1 _ _
      wp_steps_sync_333 ((blkPl_333).base + 4752#64)
      try simp only [State.setMem_setMem]
      refine align_pre_st (by (try simp only [wp_norm, arm64_norm]); try sep_ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx21_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
      change s2.pc = (blkPl_333).base + 4752#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4760#64) s2 _ _
      wp_steps
      wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hx14_2, hx19_2, hx21_2, hx23_2, hx24_2, hx26_2, hx27_2, hx28_2, htr2⟩
    refine seq_clean_evs
      (mid := lsmpl.base 333 + 4856#64)
      (P_evs := fun evs1 sm =>
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        A.pool lim (M.stepEvents evs1 st) sm ∗
        (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest))
      (Q := fun sm =>
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = p0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = w104 ∧
        sm.readReg64 .x27 = c0 ∧
        sm.readReg64 .x28 = w88 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · have h4760 := v6hr_dealloc_auth_4760_to_4856_of_sub_placed hdealloc_ok st s0 s2
        out c0 p0 c1 p1 c2 p2 w88 w104
        (((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2168#64) ↦₆₄ w96) ∗
         vecCapPtrDealloc A.repAlloc c0 p0 ∗
         ((s0.sp - 2320#64) ↦₆₄ w24) ∗
         ((s0.sp - 2176#64) ↦₆₄ w120) ∗
         Rest)
        hsp0_align hpc2 hrun2 hsp2 hx9_2 hx14_2 hx19_2 hx21_2 hx23_2 hx24_2 hx26_2 hx27_2 hx28_2 htr2
      refine SepWP.mono h4760 fun _ _ _ _ ⟨evs1, hevs1, hp, hq⟩ => ?_
      exact ⟨evs1, hevs1, Entails.trans hp (Entails.of_eq (by sep_ac_rfl)), hq⟩
    · intro evs1 s3 hevs1 hpc3 hrun3 ⟨hsp3, hx9_3, hx19_3, hx23_3, hx27_3, hx28_3, htr3⟩
      have h4856 := v6hr_dealloc_hdr_4856_to_10316_of_sub_placed hdealloc_ok
        (M.stepEvents evs1 st) s0 s3 out c0 p0 w88 w96 w104 v144
        (((s0.sp - 2320#64) ↦₆₄ w24) ∗ ((s0.sp - 2176#64) ↦₆₄ w120) ∗ Rest)
        hsp0_align hpc3 hrun3 hsp3 hx9_3 hx19_3 hx23_3 hx27_3 hx28_3 htr3
      refine SepWP.mono h4856 fun sm Pm _ _ ⟨evs2, hevs2, hent, hx25, hpres, hx23⟩ => ?_
      refine ⟨evs1 ++ evs2, hevs1.append hevs2, ?_, hx25, hpres, hx23⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact Entails.trans hent (Entails.of_eq (by sep_ac_rfl))

theorem v6hr_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2320#64) ↦₆₄ w24) ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2176#64) ↦₆₄ w120) ∗
            ((s0.sp - 2168#64) ↦₆₄ w96) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_err_3760_hdr_ne64_auth_some_to_10316_of_sub_placed (v6hr_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 d112 d116 w120 v80 v144 v224
    Rest hsp0_align hc0 hc1 hw24 hpc1 hrun1 hregs1

theorem v6hr_err_3760_hdr_ne64_auth_some_to_10316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v144 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2256#64) ↦₆₄ v144) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        ((s0.sp - 2168#64) ↦₆₄ w96) ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            ((s0.sp - 2320#64) ↦₆₄ w24) ∗
            ((s0.sp - 2256#64) ↦₆₄ if (c0 == 0#64) = true then v144 else p0) ∗
            ((s0.sp - 2176#64) ↦₆₄ w120) ∗
            ((s0.sp - 2168#64) ↦₆₄ w96) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_err_3760_hdr_ne64_auth_some_to_10316_of_sub_placed (v6hr_sub_ok_dealloc_placed hA)
    st s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 d112 d116 w120 v80 v144 v224
    Rest hsp0_align hc0 hc1 hw24 hpc1 hrun1 hregs1

/-- `VmPreserved`-strengthened Variant 6 validation step (`+3760 -> +3796`). -/
theorem v6hr_step_3760_to_3796_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p0 c1 p1 w48 c2 p2 w72 w80 w88 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3796#64) s1
      (((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2320#64) ↦₆₄ 64#64) ∗
          ((s0.sp - 2176#64) ↦₆₄ w120) ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out c0 p0 64#64 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120 ∧
        sm.readReg64 .x27 = c0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6bPlaced.v6hr_step_3760_to_3796_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out c0 p0 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120 v80 v224 Rest
      hsp0_align hc0 hc1 (by simpa using hpc1) (by simpa using hrun1)
      (v6hr_Regs1508_to_stripS hregs1))
    fun sm Pm hvm ⟨hPm, hregs, hx27⟩ =>
      ⟨hPm, hvm, v6hr_Regs1508_of_stripS hregs, by simpa using hx27⟩

theorem v6hr_step_3760_to_3796_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p0 c1 p1 w48 c2 p2 w72 w80 w88 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v80 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 64#64 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3796#64) s1
      (((s0.sp - 2320#64) ↦₆₄ v80) ∗
        ((s0.sp - 2176#64) ↦₆₄ v224) ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2320#64) ↦₆₄ 64#64) ∗
          ((s0.sp - 2176#64) ↦₆₄ w120) ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out c0 p0 64#64 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120 ∧
        sm.readReg64 .x27 = c0) := by
  have hwp := v6hr_step_3760_to_3796_placed (ext := ext)
    s0 s1 out c0 p0 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120 v80 v224
    (A.pool lim st s1 ∗ Rest) hsp0_align hc0 hc1 hpc1 hrun1 hregs1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudget
