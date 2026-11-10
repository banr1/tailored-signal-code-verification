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
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlaced
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
# Auxiliary `Authenticator` Clone Lemmas for `Variant8cPlacedBudget`

Lifts Variant 8 (`EkReceivedCt1Sampled`, Block `333`) validation steps (`+1872 -> +1972`,
`+1972 -> +10544 | +1984`, `+10836 -> +11120`) to `VmPreserved` and proves total-correctness
cloning of `Authenticator` `rootKey` and `macKey` (`+1984 -> +10680 -> +10740`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved ofNat_beq_zero_false sp_sub_2400_align
   stackAt_encoderFromPb_split_allocHook v1_bv_add_add_lit v1_bv_sub_sub_lit
   v1_shl8_extract_0_8 v8_ucWordsAt vecU8Payload_of_nil vecU8Payload_pos
   vecU8Payload_pos_dealloc vecU8Payload_pos_unpack)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FitsEvents
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status
   stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget FromPbAllocHooksBudget.toPlacedBudget blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

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

/-! ## 1. `VmPreserved` & Pool-Threading Pure Steps -/

/-- `VmPreserved`-strengthened combined step `+1872 -> +1972` when
    `u24 = 2080#64 ∧ u72 = 960#64 ∧ u48 = 1152#64`. -/
theorem v8_step_1872_to_1972_len_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1972#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8cPlaced.v8_step_1872_to_1972_len_ok_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx23_1) (by simpa using hx26_1)
      (by simpa using hx27_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx26_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_step_1872_to_1972_len_ok_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1872#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1972#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
        v8_ucWordsAt (pbA + 8#64)
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_step_1872_to_1972_len_ok_placed (ext := ext) s0 s1 out pbA
    u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u128 (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened check at `+1972` when `u80 = noneCap` (`u.auth = none`),
    branching to `+10544`. -/
theorem v8_check_auth_1972_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1972#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10544#64) s1
      (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8cPlaced.v8_check_auth_1972_none_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 u128 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_check_auth_1972_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1972#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10544#64) s1
      (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 noneCap u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_check_auth_1972_none_placed (ext := ext) s0 s1 out
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u88 u96 u104 u112 u120 u128 (A.pool lim st s1 ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened check at `+1972` when `u80.toNat < 2 ^ 63` (`u.auth = some authPb`),
    falling through to `+1984` with `x23 = u80`. -/
theorem v8_check_auth_1972_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hu80_lt : u80.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1972#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1984#64) s1
      (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8cPlaced.v8_check_auth_1972_some_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 Rest
      hu80_lt hsp0_align (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx23_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx23_m, by simpa using hx26_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_check_auth_1972_some_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp)
    (hu80_lt : u80.toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1972#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1984#64) s1
      (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          A.pool lim st sm ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_check_auth_1972_some_placed (ext := ext) s0 s1 out pbA
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 (A.pool lim st s1 ∗ Rest)
    hu80_lt hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened check at `+10836` when `[sp + 1520] = noneCap` (`sendingCt1 = none`),
    branching to `+11120`. -/
theorem v8_check_sendingCt1_10836_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa5 ca1 ca2 ca3 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10836#64)
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
      (lsmpl.base 333 + 11120#64) s1
      ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = pa5 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧
        sm.readReg64 .x22 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant8cPlaced.v8_check_sendingCt1_10836_none_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pa5 ca1 ca2 ca3 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx9_1) (by simpa using hx19_1) (by simpa using hx21_1)
      (by simpa using hx22_1) (by simpa using hx26_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx9_m, hx19_m, hx21_m, hx22_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx9_m, by simpa using hx19_m,
       by simpa using hx21_m, by simpa using hx22_m, by simpa using hx26_m,
       by simpa using hx28_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v8_check_sendingCt1_10836_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa5 ca1 ca2 ca3 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10836#64)
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
      (lsmpl.base 333 + 11120#64) s1
      ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x9 = pa5 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧
        sm.readReg64 .x22 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v8_check_sendingCt1_10836_none_placed (ext := ext) s0 s1 out pa5 ca1 ca2 ca3
    (A.pool lim st s1 ∗ Rest) hsp0_align hpc1 hrun1 hsp1 hx9_1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## 2. Total-Correctness Cloning of `Authenticator` Buffers (`+1984 -> +10680 -> +10740`) -/

/-- Total-correctness (`SepWP`, no OOM or panic) clone of `authPb.rootKey` at
    `+1984 -> +10680` from `FromPbAllocHooksPlacedBudget` under
    `FitsEvents M lim st (authKeyCloneEvents rootKey)`. -/
theorem v8_clone_rootKey_1984_to_10680_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA u8 u80 u88 u128 v120 v200 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1984#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10680#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
        (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
        vecU8Payload A.repAlloc u80 u88 rootKey ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
            (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
            (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A.repAlloc u80 u88 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧
          sm.readReg64 .x23 = u80 ∧
          sm.readReg64 .x24 = u88 ∧
          sm.readReg64 .x26 = u8 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0) := by
  have h120 : (s0.sp - 2400#64) + 120#64 = s0.sp - 2280#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h976 : (s0.sp - 2400#64) + 976#64 = s0.sp - 1424#64 := by bv_omega
  have h984 : (s0.sp - 2400#64) + 984#64 = s0.sp - 1416#64 := by bv_omega
  have h1016 : (s0.sp - 2400#64) + 1016#64 = s0.sp - 1384#64 := by bv_omega
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil, hr_nil]
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    rw [lsmpl_base_333_eq] at hpc1 ⊢
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ 1#64) ∗
          (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
          (((s0.sp - 2400#64) + 984#64) ↦₆₄ 0#64) ∗
          (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          vecCapPtrDealloc A.repAlloc u80 u88 ∗
          A.pool lim st sm ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) ?_
      fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨1#64, hPm, hregs⟩
    wp_steps_sync_333 (lsmpl.base 333 + 10680#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc u80 u88 []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, h120, h200, h976, h984, h1016]
      refine Entails.trans (Entails.of_eq (show _ =
        emp ∗ vecU8Payload A.repAlloc u80 u88 [] ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2280#64) ↦₆₄ u128) ∗
        ((s0.sp - 2200#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 1424#64) ↦₆₄ u88) ∗
        ((s0.sp - 1416#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 1384#64) ↦₆₄ u128) ∗
        A.pool lim st sc ∗ Rest by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hn (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : rootKey.isEmpty = false := by
      cases h : rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents rootKey = rustAllocEvents rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (P' :=
      ⌜rootKey.length ≤ u80.toNat ∧ u80.toNat < 2 ^ 63 ∧ u88 ≠ 0#64 ∧ u80 ≠ 0#64⌝ ∗
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
       ((s0.sp - 2280#64) ↦₆₄ v120) ∗ ((s0.sp - 2200#64) ↦₆₄ v200) ∗
       ((s0.sp - 1424#64) ↦₆₄ u88) ∗ ((s0.sp - 1416#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
       ((s0.sp - 1384#64) ↦₆₄ u128) ∗
       A.live u88 u80.toNat 1 ∗ (u88 ↦ₛ rootKey) ∗
       memRegion (u88 + BitVec.ofNat 64 rootKey.length) (u80.toNat - rootKey.length) ∗
       A.pool lim st s1 ∗ Rest)) ?_ ?_
    · have hunp := vecU8Payload_pos_unpack A.repAlloc u80 u88 rootKey hr_pos
      rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), h120, h200, h976, h984, h1016]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc u80 u88 rootKey ∗
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
         ((s0.sp - 2280#64) ↦₆₄ v120) ∗ ((s0.sp - 2200#64) ↦₆₄ v200) ∗
         ((s0.sp - 1424#64) ↦₆₄ u88) ∗ ((s0.sp - 1416#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
         ((s0.sp - 1384#64) ↦₆₄ u128) ∗ A.pool lim st s1 ∗ Rest) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hunp)
        (Entails.of_eq (by dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl))
    · apply SepWP.pure_elim
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
      rw [lsmpl_base_333_eq] at hpc1 ⊢
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
      wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym)
      simp only [State.setMem_setMem]
      wp_call hshim ()
      have hacp_shim : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
      wp_steps_sync_333 (lsρ spqrRustAllocSym)
      simp only [State.setMem_setMem]
      wp_call halloc (rootKey.length, 1, st)
      have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
      have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
      have hacp_alloc : AllocCallPreserved s1 sf_1 :=
        hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
      have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
      wp_steps_sync_333 (lsρ spqrMemcpySym)
      simp only [State.setMem_setMem]
      wp_call hmc (sf_1.readReg64 .x0, u88, rootKey)
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
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ sf_1.readReg64 .x0) ∗
            (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
            (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
            (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length)
              (sf_1.readReg64 .x0) rootKey ∗
            vecCapPtrDealloc A.repAlloc u80 u88 ∗
            A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧
          sm.readReg64 .x23 = u80 ∧
          sm.readReg64 .x24 = u88 ∧
          sm.readReg64 .x26 = u8 ∧
          sm.readReg64 .x27 = pbA ∧
          TraceCalleeSaved sm s0) ?_
        fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨sf_1.readReg64 .x0, hPm, hregs⟩
      wp_steps_sync_333 (lsmpl.base 333 + 10680#64)
      simp only [State.setMem_setMem]
      have hd := vecU8Payload_pos_dealloc A.repAlloc u80 u88 rootKey hr_le hr_cap hptr0 hcap0_ne
      have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) rootKey hr_pos hr_lt63 hoom0
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [hsp_sf, hsp_sf1, hsp_sf2]
        rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), h120, h200, h976, h984, h1016]
        dsimp only [Reg.x0] at hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.repAlloc.live (sf_1.readReg64 (Reg.gpr 0#5)) rootKey.length 1 ∗
           (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ rootKey)) ∗
          (A.repAlloc.live u88 u80.toNat 1 ∗ (u88 ↦ₛ rootKey) ∗
           memRegion (u88 + BitVec.ofNat 64 rootKey.length) (u80.toNat - rootKey.length)) ∗
          memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          ((s0.sp - 2280#64) ↦₆₄ u128) ∗
          ((s0.sp - 2200#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
          ((s0.sp - 1424#64) ↦₆₄ u88) ∗
          ((s0.sp - 1416#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
          ((s0.sp - 1384#64) ↦₆₄ u128) ∗
          A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sc ∗ Rest by
            dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hp (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
      · wp_done

/-- Total-correctness (`SepWP`, no OOM or panic) clone of `authPb.rootKey` at
    `+1984 -> +10680` from `FromPbAllocHooksBudget`. -/
theorem v8_clone_rootKey_1984_to_10680_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA u8 u80 u88 u128 v120 v200 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1984#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = u80) (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10680#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ v120) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
        (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
        (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
        vecU8Payload A.repAlloc u80 u88 rootKey ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ p1_new : BitVec 64,
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u128) ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1_new) ∗
          (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
          (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 rootKey.length) ∗
          (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u128) ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
          vecCapPtrDealloc A.repAlloc u80 u88 ∗
          A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 rootKey.length ∧
        sm.readReg64 .x23 = u80 ∧ sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) :=
  v8_clone_rootKey_1984_to_10680_of_placedHooks hA.toPlacedBudget
    st s0 s1 out pbA u8 u80 u88 u128 v120 v200 rootKey Rest hfits hsp0_align
    hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1

/-- Total-correctness (`SepWP`, no OOM or panic) clone of `authPb.macKey` at
    `+10680 -> +10740` from `FromPbAllocHooksPlacedBudget` under
    `FitsEvents M lim st (authKeyCloneEvents macKey)`. -/
theorem v8_clone_macKey_10680_to_10740_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA u8 l1 u80 u88 u104 u112 v184 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10680#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = l1)
    (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88)
    (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10740#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
        (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        vecU8Payload A.repAlloc u104 u112 macKey ∗
        A.pool lim st s1 ∗
        Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗
            (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
            (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A.repAlloc u104 u112 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = u112 ∧
          sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = u80 ∧
          sm.readReg64 .x24 = u88 ∧
          sm.readReg64 .x26 = u8 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 macKey.length ∧
          TraceCalleeSaved sm s0) := by
  have h184 : (s0.sp - 2400#64) + 184#64 = s0.sp - 2216#64 := by bv_omega
  have h1000 : (s0.sp - 2400#64) + 1000#64 = s0.sp - 1400#64 := by bv_omega
  have h1008 : (s0.sp - 2400#64) + 1008#64 = s0.sp - 1392#64 := by bv_omega
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil, hm_nil]
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    rw [lsmpl_base_333_eq] at hpc1 ⊢
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
    refine SepWP.mono
      (post := fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ 1#64) ∗
          (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
          (((s0.sp - 2400#64) + 1008#64) ↦₆₄ 0#64) ∗
          vecU8Payload A.repAlloc 0#64 1#64 [] ∗
          vecCapPtrDealloc A.repAlloc u104 u112 ∗
          A.pool lim st sm ∗
          Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = u112 ∧
        sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = u80 ∧
        sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) ?_
      fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨1#64, hPm, hregs⟩
    wp_steps_sync_333 (lsmpl.base 333 + 10740#64)
    simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc u104 u112 []
    have hn := vecU8Payload_of_nil A.repAlloc
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc, h184, h1000, h1008]
      refine Entails.trans (Entails.of_eq (show _ =
        emp ∗ vecU8Payload A.repAlloc u104 u112 [] ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2216#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 1400#64) ↦₆₄ u112) ∗
        ((s0.sp - 1392#64) ↦₆₄ 0#64) ∗
        A.pool lim st sc ∗ Rest by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hn (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · have hne_nil : macKey.isEmpty = false := by
      cases h : macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents macKey = rustAllocEvents macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (P' :=
      ⌜macKey.length ≤ u104.toNat ∧ u104.toNat < 2 ^ 63 ∧ u112 ≠ 0#64 ∧ u104 ≠ 0#64⌝ ∗
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
       ((s0.sp - 2216#64) ↦₆₄ v184) ∗ ((s0.sp - 1400#64) ↦₆₄ u112) ∗
       ((s0.sp - 1392#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
       A.live u112 u104.toNat 1 ∗ (u112 ↦ₛ macKey) ∗
       memRegion (u112 + BitVec.ofNat 64 macKey.length) (u104.toNat - macKey.length) ∗
       A.pool lim st s1 ∗ Rest)) ?_ ?_
    · have hunp := vecU8Payload_pos_unpack A.repAlloc u104 u112 macKey hm_pos
      rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), h184, h1000, h1008]
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A.repAlloc u104 u112 macKey ∗
        (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
         ((s0.sp - 2216#64) ↦₆₄ v184) ∗ ((s0.sp - 1400#64) ↦₆₄ u112) ∗
         ((s0.sp - 1392#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
         A.pool lim st s1 ∗ Rest) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hunp)
        (Entails.of_eq (by dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl))
    · apply SepWP.pure_elim
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
      rw [lsmpl_base_333_eq] at hpc1 ⊢
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) _ s1 _ _
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
      wp_call hmc (sf_1.readReg64 .x0, u112, macKey)
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
            (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
            (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length)
              (sf_1.readReg64 .x0) macKey ∗
            vecCapPtrDealloc A.repAlloc u104 u112 ∗
            A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sm ∗
            Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = u112 ∧
          sm.readReg64 .x22 = l1 ∧
          sm.readReg64 .x23 = u80 ∧
          sm.readReg64 .x24 = u88 ∧
          sm.readReg64 .x26 = u8 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 macKey.length ∧
          TraceCalleeSaved sm s0) ?_
        fun sm Pm _ _ ⟨hPm, hregs⟩ => ⟨sf_1.readReg64 .x0, hPm, hregs⟩
      wp_steps_sync_333 (lsmpl.base 333 + 10740#64)
      simp only [State.setMem_setMem]
      have hd := vecU8Payload_pos_dealloc A.repAlloc u104 u112 macKey hm_le hm_cap hptr0 hcap0_ne
      have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) macKey hm_pos hm_lt63 hoom0
      refine entails_pre_st ?_ ?_
      · intro sc hsc
        rw [← hsc]
        simp only [hsp_sf, hsp_sf1, hsp_sf2]
        rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64), h184, h1000, h1008]
        dsimp only [Reg.x0] at hp ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          (A.repAlloc.live (sf_1.readReg64 (Reg.gpr 0#5)) macKey.length 1 ∗
           (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ macKey)) ∗
          (A.repAlloc.live u112 u104.toNat 1 ∗ (u112 ↦ₛ macKey) ∗
           memRegion (u112 + BitVec.ofNat 64 macKey.length) (u104.toNat - macKey.length)) ∗
          memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          ((s0.sp - 2216#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
          ((s0.sp - 1400#64) ↦₆₄ u112) ∗
          ((s0.sp - 1392#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sc ∗ Rest by
            dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hp (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
      · wp_done

/-- Total-correctness (`SepWP`, no OOM or panic) clone of `authPb.macKey` at
    `+10680 -> +10740` from `FromPbAllocHooksBudget`. -/
theorem v8_clone_macKey_10680_to_10740_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out pbA u8 l1 u80 u88 u104 u112 v184 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10680#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = l1) (hx23_1 : s1.readReg64 .x23 = u80)
    (hx24_1 : s1.readReg64 .x24 = u88) (hx26_1 : s1.readReg64 .x26 = u8)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10740#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
        (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
        vecU8Payload A.repAlloc u104 u112 macKey ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm => ∃ p2_new : BitVec 64,
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          (((s0.sp - 2400#64) + 184#64) ↦₆₄ p2_new) ∗
          (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗
          (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
          vecCapPtrDealloc A.repAlloc u104 u112 ∗
          A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = u112 ∧ sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = u80 ∧ sm.readReg64 .x24 = u88 ∧
        sm.readReg64 .x26 = u8 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 macKey.length ∧ TraceCalleeSaved sm s0) :=
  v8_clone_macKey_10680_to_10740_of_placedHooks hA.toPlacedBudget
    st s0 s1 out pbA u8 l1 u80 u88 u104 u112 v184 macKey Rest hfits hsp0_align
    hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudgetAux
