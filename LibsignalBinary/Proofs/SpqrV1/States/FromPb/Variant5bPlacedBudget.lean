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
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 5 (`NoHeaderReceived`) — Part B

Relocatable Block-`333` header validation (`+1344`), `FreeOnlyEvs` early error paths, and
total-correctness `Authenticator` cloning and input deallocation (`+3744 -> +6064`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop
  (none2Cap none2Cap_add_two_beq_zero noneCap_add_two_beq_zero optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved cap_ne_zero_of_pos ofNat_beq_zero_false v5a_Saved6428Preserved v5a_pbAHeadersAt
   v5b_c1_add_two_uge_two v5b_cond_ls_none2Cap v5b_cond_ls_noneCap
   v5b_live_bytes_entails_vecCapPtrDealloc v5b_stackAt_encoderFromPb_split_7552
   vecU8Payload_pos vecU8Payload_zero)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil
   seq_clean_evs subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget
  (v5a_sub_ok_dealloc_of_placedHooks v5a_sub_ok_dealloc_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm] v5b_cond_ls_none2Cap v5b_cond_ls_noneCap

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip; wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm])) (hnext := ?_)))

private theorem sepWP_exists_post {P : Program} {tgt : BitVec 64} {s : State} {Pre : SepProp}
    {α : Type} (w : α) {post : α → State → SepProp → Prop} (h : SepWP P tgt s Pre (post w)) :
    SepWP P tgt s Pre (fun sm Pm => ∃ x : α, post x sm Pm) :=
  SepWP.mono h fun _ _ _ _ hp => ⟨w, hp⟩

private theorem vecU8Payload_pos_unpack (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (hpos : 0 < bs.length) :
    vecU8Payload A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8Payload; apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
  have hc : cap ≠ 0#64 := cap_ne_zero_of_pos hpos hle
  simp only [hc, ↓reduceIte]; exact Entails.pure_right ⟨hle, hlt, hptr, hc⟩ (Entails.refl _)

private theorem v5a_Saved6428Preserved_of_stripS {keep : BitVec 64 → Bool} {s0 sm : State}
    {fsp out ptsPtr ptsCap v : BitVec 64}
    (h : v5a_Saved6428Preserved s0 (ProofLib.stripS keep sm) fsp out ptsPtr ptsCap v) :
    v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap v := by
  rcases h with ⟨hsp, hx19, hx22, hx23, hx27, htr1, htr2⟩
  exact ⟨by simpa using hsp, by simpa using hx19, by simpa using hx22,
    by simpa using hx23, by simpa using hx27, by simpa using htr1, by simpa using htr2⟩

/-! ## Entry Header Check (`+1344 -> +3744 | +1396`) & Early Error Paths -/

theorem v5b_step_1344_to_3744_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s0 s : State)
    (fsp out pbA w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 z224 : BitVec 64) (z232 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1344#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 3744#64) s
      (v5a_pbAHeadersAt pbA noneCap w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗ ((fsp + 232#64) ↦₃₂ z232) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = w88 ∧ sm.readReg64 .x9 = w96 ∧ sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = w64 ∧ sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧ sm.readReg64 .x23 = noneCap ∧ sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x25 = d32.zeroExtend 64 ∧ sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = w24 ∧ TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_1344_to_3744_none_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232 Rest
      hfsp_align (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx27) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8, hx9, hx10, hx19_m, hx20, hx21, hx22, hx23, hx24,
      hx25, hx26, hx27_m, hx28, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx8, by simpa using hx9,
       by simpa using hx10, by simpa using hx19_m, by simpa using hx20, by simpa using hx21,
       by simpa using hx22, by simpa using hx23, by simpa using hx24, by simpa using hx25,
       by simpa using hx26, by simpa using hx27_m, by simpa using hx28,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v5b_step_1344_to_3744_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s0 s : State)
    (fsp out pbA w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 z224 : BitVec 64) (z232 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1344#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 3744#64) s
      (v5a_pbAHeadersAt pbA noneCap w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗ ((fsp + 232#64) ↦₃₂ z232) ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = w88 ∧ sm.readReg64 .x9 = w96 ∧ sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = w64 ∧ sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧ sm.readReg64 .x23 = noneCap ∧ sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x25 = d32.zeroExtend 64 ∧ sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = w24 ∧ TraceCalleeSaved sm s0) := by
  have hwp := v5b_step_1344_to_3744_none_placed (ext := ext)
    s0 s fsp out pbA w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
    (A.pool lim st s ∗ Rest) hfsp_align hpc hrun hsp hx19 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

theorem v5b_step_1344_to_3744_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s0 s : State)
    (fsp out pbA w8 w16 w24 : BitVec 64) (d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 z224 : BitVec 64) (z232 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw8_lt : w8.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1344#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 3744#64) s
      (v5a_pbAHeadersAt pbA w8 w16 w24 48#32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗ ((fsp + 232#64) ↦₃₂ z232) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = w88 ∧ sm.readReg64 .x9 = w96 ∧ sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = w64 ∧ sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧ sm.readReg64 .x23 = w8 ∧ sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x25 = (48#32).zeroExtend 64 ∧ sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = w24 ∧ TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_1344_to_3744_some_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA w8 w16 w24 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232 Rest
      hfsp_align hw8_lt (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx27) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8, hx9, hx10, hx19_m, hx20, hx21, hx22, hx23, hx24,
      hx25, hx26, hx27_m, hx28, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx8, by simpa using hx9,
       by simpa using hx10, by simpa using hx19_m, by simpa using hx20, by simpa using hx21,
       by simpa using hx22, by simpa using hx23, by simpa using hx24, by simpa using hx25,
       by simpa using hx26, by simpa using hx27_m, by simpa using hx28,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v5b_step_1344_to_3744_some_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s0 s : State)
    (fsp out pbA w8 w16 w24 : BitVec 64) (d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 z224 : BitVec 64) (z232 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw8_lt : w8.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1344#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 3744#64) s
      (v5a_pbAHeadersAt pbA w8 w16 w24 48#32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗ ((fsp + 232#64) ↦₃₂ z232) ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = w88 ∧ sm.readReg64 .x9 = w96 ∧ sm.readReg64 .x10 = w80 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = w64 ∧ sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧ sm.readReg64 .x23 = w8 ∧ sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x25 = (48#32).zeroExtend 64 ∧ sm.readReg64 .x26 = w56 ∧
        sm.readReg64 .x27 = pbA ∧ sm.readReg64 .x28 = w24 ∧ TraceCalleeSaved sm s0) := by
  have hwp := v5b_step_1344_to_3744_some_placed (ext := ext)
    s0 s fsp out pbA w8 w16 w24 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
    (A.pool lim st s ∗ Rest) hfsp_align hw8_lt hpc hrun hsp hx19 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

theorem v5b_step_1344_to_1396_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s0 s : State)
    (fsp out pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 z224 : BitVec 64) (z232 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw8_lt : w8.toNat < 2 ^ 63) (hd32_ne : d32 ≠ 48#32)
    (hpc : s.pc = lsmpl.base 333 + 1344#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 1396#64) s
      (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗ ((fsp + 232#64) ↦₃₂ z232) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x10 = w80 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧ sm.readReg64 .x23 = w8 ∧ sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x26 = w56 ∧ sm.readReg64 .x28 = w24 ∧ TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_1344_to_1396_err_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232 Rest
      hfsp_align hw8_lt hd32_ne (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx27) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx10, hx19_m, hx21, hx22, hx23, hx24, hx26, hx28, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx10, by simpa using hx19_m,
       by simpa using hx21, by simpa using hx22, by simpa using hx23, by simpa using hx24,
       by simpa using hx26, by simpa using hx28, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v5b_step_1344_to_1396_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)} (s0 s : State)
    (fsp out pbA w8 w16 w24 : BitVec 64) (d32 d36 : BitVec 32)
    (w40 w48 w56 w64 w72 w80 w88 w96 z224 : BitVec 64) (z232 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw8_lt : w8.toNat < 2 ^ 63) (hd32_ne : d32 ≠ 48#32)
    (hpc : s.pc = lsmpl.base 333 + 1344#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx27 : s.readReg64 .x27 = pbA)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 1396#64) s
      (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        ((fsp + 224#64) ↦₆₄ z224) ∗ ((fsp + 232#64) ↦₃₂ z232) ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion pbA optProtoInnerStateSize ∗
          ((fsp + 224#64) ↦₆₄ w40) ∗ ((fsp + 232#64) ↦₃₂ d36) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x10 = w80 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = w72 ∧
        sm.readReg64 .x22 = w16 ∧ sm.readReg64 .x23 = w8 ∧ sm.readReg64 .x24 = w48 ∧
        sm.readReg64 .x26 = w56 ∧ sm.readReg64 .x28 = w24 ∧ TraceCalleeSaved sm s0) := by
  have hwp := v5b_step_1344_to_1396_err_placed (ext := ext)
    s0 s fsp out pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
    (A.pool lim st s ∗ Rest) hfsp_align hw8_lt hd32_ne hpc hrun hsp hx19 hx27 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

theorem v5b_step_1396_uc_none_to_6428_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = none2Cap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_1396_uc_none_to_6428_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap ptsLen P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx22) (by simpa using hx23)
      (by simpa using hx24) (by simpa using hx28) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hpres, hx28_m⟩ =>
      ⟨hPm, hvm, v5a_Saved6428Preserved_of_stripS hpres, by simpa using hx28_m⟩

theorem v5b_step_1396_uc_none_to_6428_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = none2Cap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s
      (A.pool lim st s ∗ Frame)
      (fun sm Pm => (Pm ⊢ A.pool lim st sm ∗ Frame) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  have hwp := v5b_step_1396_uc_none_to_6428_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap ptsLen (A.pool lim st s ∗ Frame)
    hpc hrun hsp hx19 hx22 hx23 hx24 hx28 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

theorem v5b_step_1396_auth_none_to_6428_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = noneCap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_1396_auth_none_to_6428_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap ptsLen P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx22) (by simpa using hx23)
      (by simpa using hx24) (by simpa using hx28) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hpres, hx28_m⟩ =>
      ⟨hPm, hvm, v5a_Saved6428Preserved_of_stripS hpres, by simpa using hx28_m⟩

theorem v5b_step_1396_auth_none_to_6428_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = noneCap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s
      (A.pool lim st s ∗ Frame)
      (fun sm Pm => (Pm ⊢ A.pool lim st sm ∗ Frame) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  have hwp := v5b_step_1396_auth_none_to_6428_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap ptsLen (A.pool lim st s ∗ Frame)
    hpc hrun hsp hx19 hx22 hx23 hx24 hx28 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Early `MsgDecode` error path `+1396..+1460 -> +4256 -> +6428` when `auth = some authPb` (`c1 < 2^63`)
    under an explicit `__rust_dealloc` subroutine contract (`FreeOnlyEvs`). -/
theorem v5b_step_1396_auth_some_to_6428_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap ptsLen c1 p1 c2 p2 : BitVec 64)
    (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx10 : s.readReg64 .x10 = p2) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1) (hx26 : s.readReg64 .x26 = p1) (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s
      (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x28 = ptsLen ∧ AllocCallPreserved s sm) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok
  clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hult := v5b_c1_add_two_uge_two hc1_lt
  change s.pc = (blkPl_333).base + 1396#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6428#64) s _ _
  refine seq_clean_evs (mid := (blkPl_333).base + 1436#64)
    (P_evs := fun evs1 sm =>
      vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧ sm.readReg64 .x10 = p2 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = c2 ∧
      sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x28 = ptsLen ∧
      TraceCalleeSaved sm s0 ∧ AllocCallPreserved s sm)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc1 : (c1 == 0#64) = true
    · apply sepWP_evs_nil
      simp only [hc1, ↓reduceIte, emp_sepConj, sepConj_emp,
        LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      wp_done
    · have hc1_f : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      apply sepWP_evs_dealloc c1.toNat 1
      simp only [hc1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      have hacp_sf : AllocCallPreserved s sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      refine align_pre_st (by rw [hsp]; simp only [wp_norm, arm64_norm]; first | rfl | sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, hx10_1, hx19_1, hx21_1, hx22_1, hx23_1, hx28_1, htrace1, hacp1⟩
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, emp_sepConj, sepConj_emp]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6428#64) s1
          (A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim (M.stepEvents evs1 st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
            sm.readReg64 .x28 = ptsLen ∧ AllocCallPreserved s1 sm) := by
        wp_steps
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hpres_f, hx28_f, hacp_f⟩ =>
        ⟨evs1, hevs1, hp, hpres_f, hx28_f, hacp1.trans hacp_f⟩
    · have hc2_f : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hc2_f, Bool.false_eq_true, ↓reduceIte]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6428#64) s1
          ((A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat) ∗
            A.pool lim (M.stepEvents evs1 st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ A.pool lim (M.stepEvents (rustDeallocEvents c2.toNat 1) (M.stepEvents evs1 st))
                sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
            sm.readReg64 .x28 = ptsLen ∧ AllocCallPreserved s1 sm) := by
        simp only [sepConj_assoc]
        wp_steps
        wp_apply
        have hacp_sf : AllocCallPreserved s1 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp1]; simp only [wp_norm, arm64_norm]) ?_
        wp_done
      refine SepWP.mono hfin fun sm _Pm _ _ ⟨hp, hpres_f, hx28_f, hacp_f⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents c2.toNat 1,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 c2.toNat),
        ?_, hpres_f, hx28_f, hacp1.trans hacp_f⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hp

theorem v5b_step_1396_auth_some_to_6428_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap ptsLen c1 p1 c2 p2 : BitVec 64)
    (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx10 : s.readReg64 .x10 = p2) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1) (hx26 : s.readReg64 .x26 = p1) (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s
      (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x28 = ptsLen ∧ AllocCallPreserved s sm) :=
  v5b_step_1396_auth_some_to_6428_of_sub_placed (v5a_sub_ok_dealloc_of_placedHooks hA)
    st s0 s fsp out ptsPtr ptsCap ptsLen c1 p1 c2 p2 Frame
    hfsp_align hc1_lt hpc hrun hsp hx10 hx19 hx21 hx22 hx23 hx24 hx26 hx28 htrace

theorem v5b_step_1396_auth_some_to_6428_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out ptsPtr ptsCap ptsLen c1 p1 c2 p2 : BitVec 64)
    (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 1396#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx10 : s.readReg64 .x10 = p2) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1) (hx26 : s.readReg64 .x26 = p1) (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6428#64) s
      (vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x28 = ptsLen ∧ AllocCallPreserved s sm) :=
  v5b_step_1396_auth_some_to_6428_of_sub_placed (v5a_sub_ok_dealloc_placed hA)
    st s0 s fsp out ptsPtr ptsCap ptsLen c1 p1 c2 p2 Frame
    hfsp_align hc1_lt hpc hrun hsp hx10 hx19 hx21 hx22 hx23 hx24 hx26 hx28 htrace

theorem v5b_step_3744_uc_none_to_6420_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 3744#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = none2Cap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6420#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_3744_uc_none_to_6420_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap ptsLen P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx22) (by simpa using hx23)
      (by simpa using hx24) (by simpa using hx28) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hpres, hx28_m⟩ =>
      ⟨hPm, hvm, v5a_Saved6428Preserved_of_stripS hpres, by simpa using hx28_m⟩

theorem v5b_step_3744_uc_none_to_6420_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 3744#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = none2Cap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6420#64) s
      (A.pool lim st s ∗ Frame)
      (fun sm Pm => (Pm ⊢ A.pool lim st sm ∗ Frame) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  have hwp := v5b_step_3744_uc_none_to_6420_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap ptsLen (A.pool lim st s ∗ Frame)
    hpc hrun hsp hx19 hx22 hx23 hx24 hx28 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

theorem v5b_step_3744_auth_none_to_6420_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 3744#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = noneCap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6420#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_3744_auth_none_to_6420_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ptsPtr ptsCap ptsLen P
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx22) (by simpa using hx23)
      (by simpa using hx24) (by simpa using hx28) ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hpres, hx28_m⟩ =>
      ⟨hPm, hvm, v5a_Saved6428Preserved_of_stripS hpres, by simpa using hx28_m⟩

theorem v5b_step_3744_auth_none_to_6420_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap ptsLen : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 3744#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = ptsPtr)
    (hx23 : s.readReg64 .x23 = ptsCap) (hx24 : s.readReg64 .x24 = noneCap)
    (hx28 : s.readReg64 .x28 = ptsLen) (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6420#64) s
      (A.pool lim st s ∗ Frame)
      (fun sm Pm => (Pm ⊢ A.pool lim st sm ∗ Frame) ∧ VmPreserved s sm ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧ sm.readReg64 .x28 = ptsLen) := by
  have hwp := v5b_step_3744_auth_none_to_6420_placed (ext := ext)
    s0 s fsp out ptsPtr ptsCap ptsLen (A.pool lim st s ∗ Frame)
    hpc hrun hsp hx19 hx22 hx23 hx24 hx28 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## `Authenticator` Cloning & Original Buffer Deallocation (`+3744 -> +4264..+6064`) -/

theorem v5b_step_3744_to_4276_auth_some_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l2 ep p2 l1 c2 ptsPtr ptsCap c1 d32_64 p1 ptsLen : BitVec 64)
    (z152 z200 z216 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 3744#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = l2) (hx9 : s.readReg64 .x9 = ep) (hx10 : s.readReg64 .x10 = p2)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = l1) (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1) (hx25 : s.readReg64 .x25 = d32_64)
    (hx26 : s.readReg64 .x26 = p1) (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4276#64) s
      (((fsp + 152#64) ↦₆₄ z152) ∗ ((fsp + 200#64) ↦₆₄ z200) ∗
        ((fsp + 216#64) ↦₆₄ z216) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 152#64) ↦₆₄ ep) ∗ ((fsp + 200#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = l2 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
        sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
        sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant5bPlaced.v5b_step_3744_to_4276_auth_some_placed (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out l2 ep p2 l1 c2 ptsPtr ptsCap c1 d32_64 p1 ptsLen z152 z200 z216 Rest
      hfsp_align hc1_lt (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx8) (by simpa using hx9) (by simpa using hx10)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx23) (by simpa using hx24)
      (by simpa using hx25) (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htrace.1, by simpa using htrace.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m,
      hx24_m, hx25_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx8_m, by simpa using hx19_m,
       by simpa using hx20_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx24_m, by simpa using hx25_m,
       by simpa using hx26_m, by simpa using hx28_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v5b_step_3744_to_4276_auth_some_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out l2 ep p2 l1 c2 ptsPtr ptsCap c1 d32_64 p1 ptsLen : BitVec 64)
    (z152 z200 z216 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 3744#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = l2) (hx9 : s.readReg64 .x9 = ep) (hx10 : s.readReg64 .x10 = p2)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = l1) (hx21 : s.readReg64 .x21 = c2)
    (hx22 : s.readReg64 .x22 = ptsPtr) (hx23 : s.readReg64 .x23 = ptsCap)
    (hx24 : s.readReg64 .x24 = c1) (hx25 : s.readReg64 .x25 = d32_64)
    (hx26 : s.readReg64 .x26 = p1) (hx28 : s.readReg64 .x28 = ptsLen)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 4276#64) s
      (((fsp + 152#64) ↦₆₄ z152) ∗ ((fsp + 200#64) ↦₆₄ z200) ∗
        ((fsp + 216#64) ↦₆₄ z216) ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 152#64) ↦₆₄ ep) ∗ ((fsp + 200#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ l2) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = fsp ∧
        sm.readReg64 .x8 = l2 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
        sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
        sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x26 = p1 ∧
        sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) := by
  have hwp := v5b_step_3744_to_4276_auth_some_placed (ext := ext)
    s0 s fsp out l2 ep p2 l1 c2 ptsPtr ptsCap c1 d32_64 p1 ptsLen z152 z200 z216
    (A.pool lim st s ∗ Rest) hfsp_align hc1_lt hpc hrun hsp
    hx8 hx9 hx10 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 htrace
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- Clones `authPb.rootKey` at `+4276 -> +5964` under `FitsEvents M lim st (authKeyCloneEvents rootKey)`
    with zero OOM/panic branches (`FromPbAllocHooksPlacedBudget`). -/
theorem v5b_clone_rootKey_4276_to_5964_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 c1 c2 l2 ptsPtr ptsCap ptsLen d32_64 v208 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4276#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx8_1 : s1.readReg64 .x8 = l2)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 rootKey.length)
    (hx21_1 : s1.readReg64 .x21 = c2) (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5964#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A.repAlloc c1 p1 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x8 = l2 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x24 = c1 ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x26 = p1 ∧ sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0) := by
  have h208 : (s0.sp - 2400#64) + 208#64 = s0.sp - 2192#64 := by bv_omega
  have h216 : (s0.sp - 2400#64) + 216#64 = s0.sp - 2184#64 := by bv_omega
  simp only [h208, h216]
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · have hevs : authKeyCloneEvents rootKey = [] := by simp [authKeyCloneEvents, hr_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hr_nil] at hx20_1 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20_1 ⊢
    change s1.pc = (blkPl_333).base + 4276#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5964#64) s1 _ _
    refine sepWP_exists_post 1#64 ?_
    wp_steps_sync_333 ((blkPl_333).base + 5964#64); simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc c1 p1 []
    have hn := vecU8Payload_zero A.repAlloc
    refine entails_pre_st (fun sc hsc => ?_) (by wp_done)
    rw [← hsc]
    refine Entails.trans (Entails.of_eq (show _ =
      emp ∗ vecU8Payload A.repAlloc c1 p1 [] ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2192#64) ↦₆₄ 1#64) ∗ ((s0.sp - 2184#64) ↦₆₄ l2) ∗
      A.pool lim st sc ∗ Rest by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hn (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
  · have hne_nil : rootKey.isEmpty = false := by
      cases h : rootKey with | nil => simp [h] at hr_pos | cons => rfl
    have hevs : authKeyCloneEvents rootKey = rustAllocEvents rootKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A.repAlloc c1 p1 rootKey hr_pos))))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2192#64) ↦₆₄ v208) ∗ ((s0.sp - 2184#64) ↦₆₄ l2) ∗
          (⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64 ∧ c1 ≠ 0#64⌝ ∗
           (A.repAlloc.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
            memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length))) ∗
          A.pool lim st s1 ∗ Rest =
        ⌜rootKey.length ≤ c1.toNat ∧ c1.toNat < 2 ^ 63 ∧ p1 ≠ 0#64 ∧ c1 ≠ 0#64⌝ ∗
        (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
         ((s0.sp - 2192#64) ↦₆₄ v208) ∗ ((s0.sp - 2184#64) ↦₆₄ l2) ∗
         A.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
         memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length) ∗
         A.pool lim st s1 ∗ Rest) by
      rw [v5b_stackAt_encoderFromPb_split_7552 s0.sp]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim; rintro ⟨hr_le, hr_cap, hptr0, hc1_ne⟩
    have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim := hA.shim_ok; dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec, RustCliAllocBudget.live, ↓reduceIte] at halloc
    have hmc := hA.memcpy_ok; dsimp only [allocMemcpyVmSpec] at hmc; clear hA
    change s1.pc = (blkPl_333).base + 4276#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5964#64) s1 _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym); simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym); simp only [State.setMem_setMem]
    wp_call halloc (rootKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s1 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy"); simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, p1, rootKey)
    have hacp_mc : AllocCallPreserved s1 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr1.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine sepWP_exists_post (sf_1.readReg64 .x0) ?_
    wp_steps_sync_333 ((blkPl_333).base + 5964#64); simp only [State.setMem_setMem]
    have hd := v5b_live_bytes_entails_vecCapPtrDealloc A.repAlloc c1 p1 rootKey hc1_ne hr_le
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) rootKey hr_pos hr_lt63 hoom0
    refine entails_pre_st (fun sc hsc => ?_) (by wp_done)
    rw [← hsc, v5b_stackAt_encoderFromPb_split_7552 s0.sp]; simp only [hsp_sf, hsp_sf1]
    refine Entails.trans (Entails.of_eq (show _ =
      (A.repAlloc.live (sf_1.readReg64 .x0) rootKey.length 1 ∗ (sf_1.readReg64 .x0 ↦ₛ rootKey)) ∗
      (A.repAlloc.live p1 c1.toNat 1 ∗ (p1 ↦ₛ rootKey) ∗
       memRegion (p1 + BitVec.ofNat 64 rootKey.length) (c1.toNat - rootKey.length)) ∗
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2192#64) ↦₆₄ sf_1.readReg64 .x0) ∗ ((s0.sp - 2184#64) ↦₆₄ l2) ∗
      A.pool lim (M.stepEvents (rustAllocEvents rootKey.length 1) st) sc ∗ Rest by
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hp (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))

theorem v5b_clone_rootKey_4276_to_5964_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 c1 c2 l2 ptsPtr ptsCap ptsLen d32_64 v208 : BitVec 64)
    (rootKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents rootKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4276#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx8_1 : s1.readReg64 .x8 = l2)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 rootKey.length)
    (hx21_1 : s1.readReg64 .x21 = c2) (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 5964#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ v208) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        vecU8Payload A.repAlloc c1 p1 rootKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ p1_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 rootKey.length) p1_new rootKey ∗
            vecCapPtrDealloc A.repAlloc c1 p1 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents rootKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x8 = l2 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 rootKey.length ∧ sm.readReg64 .x21 = c2 ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x24 = c1 ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x26 = p1 ∧ sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0) :=
  v5b_clone_rootKey_4276_to_5964_of_placedHooks hA.toPlacedBudget st s0 s1
    out p1 c1 c2 l2 ptsPtr ptsCap ptsLen d32_64 v208 rootKey Rest
    hfits hsp0_align hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx28_1 htr1

/-- Clones `authPb.macKey` at `+5964 -> +6020` under `FitsEvents M lim st (authKeyCloneEvents macKey)`
    with zero OOM/panic branches (`FromPbAllocHooksPlacedBudget`). -/
theorem v5b_clone_macKey_5964_to_6020_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p2 c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 v136 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5964#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx8_1 : s1.readReg64 .x8 = BitVec.ofNat 64 macKey.length)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = l1)
    (hx21_1 : s1.readReg64 .x21 = c2) (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6020#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A.repAlloc c2 p2 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
          sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) := by
  have h136 : (s0.sp - 2400#64) + 136#64 = s0.sp - 2264#64 := by bv_omega
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  simp only [h136, h200]
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · have hevs : authKeyCloneEvents macKey = [] := by simp [authKeyCloneEvents, hm_nil]
    rw [hevs, M.stepEvents_nil]
    rw [hm_nil] at hx8_1 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx8_1 ⊢
    change s1.pc = (blkPl_333).base + 5964#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6020#64) s1 _ _
    refine sepWP_exists_post 1#64 ?_
    wp_steps_sync_333 ((blkPl_333).base + 6020#64); simp only [State.setMem_setMem]
    have hd := vecU8Payload_entails_dealloc A.repAlloc c2 p2 []
    have hn := vecU8Payload_zero A.repAlloc
    refine entails_pre_st (fun sc hsc => ?_) (by wp_done)
    rw [← hsc]
    refine Entails.trans (Entails.of_eq (show _ =
      emp ∗ vecU8Payload A.repAlloc c2 p2 [] ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2264#64) ↦₆₄ 1#64) ∗ ((s0.sp - 2200#64) ↦₆₄ p2) ∗
      A.pool lim st sc ∗ Rest by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hn (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))
  · have hne_nil : macKey.isEmpty = false := by
      cases h : macKey with | nil => simp [h] at hm_pos | cons => rfl
    have hevs : authKeyCloneEvents macKey = rustAllocEvents macKey.length 1 := by
      simp [authKeyCloneEvents, hne_nil]
    rw [hevs] at hfits ⊢
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A.repAlloc c2 p2 macKey hm_pos))))) ?_
    refine SepWP.weaken_pre (Entails.of_eq (show
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2200#64) ↦₆₄ p2) ∗
          (⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64 ∧ c2 ≠ 0#64⌝ ∗
           (A.repAlloc.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
            memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length))) ∗
          A.pool lim st s1 ∗ Rest =
        ⌜macKey.length ≤ c2.toNat ∧ c2.toNat < 2 ^ 63 ∧ p2 ≠ 0#64 ∧ c2 ≠ 0#64⌝ ∗
        (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2200#64) ↦₆₄ p2) ∗
         A.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
         memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length) ∗
         A.pool lim st s1 ∗ Rest) by
      rw [v5b_stackAt_encoderFromPb_split_7552 s0.sp]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    apply SepWP.pure_elim; rintro ⟨hm_le, hm_cap, hptr0, hc2_ne⟩
    have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
    have hshim := hA.shim_ok; dsimp only [rustAllocShimVmSpec] at hshim
    have halloc := subroutine_ok_allocNoOom_of_budget hA.alloc_ok
    dsimp only [rustCliAllocNoOomSpec, RustCliAllocBudget.live, ↓reduceIte] at halloc
    have hmc := hA.memcpy_ok; dsimp only [allocMemcpyVmSpec] at hmc; clear hA
    change s1.pc = (blkPl_333).base + 5964#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6020#64) s1 _ _
    wp_steps_sync_333 (lsρ spqrRustNoAllocShimSym); simp only [State.setMem_setMem]
    wp_call hshim ()
    have hacp_shim : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
    wp_steps_sync_333 (lsρ spqrRustAllocSym); simp only [State.setMem_setMem]
    wp_call halloc (macKey.length, 1, st)
    have hoom0 : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
    have hoom0_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_false_of_ne hoom0
    have hacp_alloc : AllocCallPreserved s1 sf_1 :=
      hacp_shim.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_1›)
    wp_steps_sync_333 (lsρ "memcpy"); simp only [State.setMem_setMem]
    wp_call hmc (sf_1.readReg64 .x0, p2, macKey)
    have hacp_mc : AllocCallPreserved s1 sf_2 :=
      hacp_alloc.trans (by simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf_2›)
    have hsp_sf : sf.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have hsp_sf1 : sf_1.sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
    have htr_sf2 : sf_2.trace = s0.trace := hacp_mc.2.1.trans htr1.1
    have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf_2 = calleeSavedVRegs sf_1›.trans
        (‹calleeSavedVRegs sf_1 = calleeSavedVRegs sf›.trans
          (‹calleeSavedVRegs sf = calleeSavedVRegs s1›.trans htr1.2))
    refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
    refine sepWP_exists_post (sf_1.readReg64 .x0) ?_
    wp_steps_sync_333 ((blkPl_333).base + 6020#64); simp only [State.setMem_setMem]
    have hd := v5b_live_bytes_entails_vecCapPtrDealloc A.repAlloc c2 p2 macKey hc2_ne hm_le
    have hp := vecU8Payload_pos A.repAlloc (sf_1.readReg64 .x0) macKey hm_pos hm_lt63 hoom0
    refine entails_pre_st (fun sc hsc => ?_) (by wp_done)
    rw [← hsc, v5b_stackAt_encoderFromPb_split_7552 s0.sp]; simp only [hsp_sf, hsp_sf1]
    refine Entails.trans (Entails.of_eq (show _ =
      (A.repAlloc.live (sf_1.readReg64 .x0) macKey.length 1 ∗ (sf_1.readReg64 .x0 ↦ₛ macKey)) ∗
      (A.repAlloc.live p2 c2.toNat 1 ∗ (p2 ↦ₛ macKey) ∗
       memRegion (p2 + BitVec.ofNat 64 macKey.length) (c2.toNat - macKey.length)) ∗
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2264#64) ↦₆₄ sf_1.readReg64 .x0) ∗ ((s0.sp - 2200#64) ↦₆₄ p2) ∗
      A.pool lim (M.stepEvents (rustAllocEvents macKey.length 1) st) sc ∗ Rest by
        dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]; sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hp (sepConj_mono_left hd)) (Entails.of_eq (by sep_ac_rfl))

theorem v5b_clone_macKey_5964_to_6020_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p2 c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 v136 : BitVec 64)
    (macKey : List (BitVec 8)) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authKeyCloneEvents macKey))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5964#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx8_1 : s1.readReg64 .x8 = BitVec.ofNat 64 macKey.length)
    (hx19_1 : s1.readReg64 .x19 = out) (hx20_1 : s1.readReg64 .x20 = l1)
    (hx21_1 : s1.readReg64 .x21 = c2) (hx22_1 : s1.readReg64 .x22 = ptsPtr)
    (hx23_1 : s1.readReg64 .x23 = ptsCap) (hx24_1 : s1.readReg64 .x24 = c1)
    (hx25_1 : s1.readReg64 .x25 = d32_64) (hx26_1 : s1.readReg64 .x26 = p1)
    (hx28_1 : s1.readReg64 .x28 = ptsLen) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6020#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 136#64) ↦₆₄ v136) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
        vecU8Payload A.repAlloc c2 p2 macKey ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ p2_new : BitVec 64,
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 macKey.length) p2_new macKey ∗
            vecCapPtrDealloc A.repAlloc c2 p2 ∗
            A.pool lim (M.stepEvents (authKeyCloneEvents macKey) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
          sm.readReg64 .x21 = c2 ∧ sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x24 = c1 ∧ sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x26 = p1 ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) :=
  v5b_clone_macKey_5964_to_6020_of_placedHooks hA.toPlacedBudget st s0 s1
    out p1 p2 c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 v136 macKey Rest
    hfits hsp0_align hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1
    hx24_1 hx25_1 hx26_1 hx28_1 htr1

/-- Deallocates the original `rootKey` (`c1, p1`) and `macKey` (`c2, p2`) buffers at
    `+6020 -> +6064` (`FreeOnlyEvs`), loading `x27 = [fsp + 208]` (`p1_new`). -/
theorem v5b_dealloc_old_auth_6020_to_6064_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out p1 p2 p1_new c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6020#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = l1) (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = p1) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6064#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x25 = d32_64 ∧
          sm.readReg64 .x27 = p1_new ∧ sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0 ∧ AllocCallPreserved s1 sm) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_ok; clear hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have h200 : (s0.sp - 2400#64) + 200#64 = s0.sp - 2200#64 := by bv_omega
  have h208 : (s0.sp - 2400#64) + 208#64 = s0.sp - 2192#64 := by bv_omega
  simp only [v5b_stackAt_encoderFromPb_split_7552 s0.sp, h200, h208, sepConj_assoc]
  change s1.pc = (blkPl_333).base + 6020#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6064#64) s1 _ _
  refine seq_clean_evs (mid := (blkPl_333).base + 6044#64)
    (P_evs := fun evs1 s2 =>
      memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
      ((s0.sp - 2200#64) ↦₆₄ p2) ∗ ((s0.sp - 2192#64) ↦₆₄ p1_new) ∗
      vecCapPtrDealloc A.repAlloc c2 p2 ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest)
    (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x20 = l1 ∧
      s2.readReg64 .x21 = c2 ∧ s2.readReg64 .x22 = ptsPtr ∧ s2.readReg64 .x23 = ptsCap ∧
      s2.readReg64 .x25 = d32_64 ∧ s2.readReg64 .x27 = p1_new ∧ s2.readReg64 .x28 = ptsLen ∧
      TraceCalleeSaved s2 s0 ∧ AllocCallPreserved s1 s2)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc1 ⊢
    by_cases hc1 : (c1 == 0#64) = true
    · apply sepWP_evs_nil
      simp only [hc1, ↓reduceIte, sepConj_emp, emp_sepConj, sepConj_assoc,
        LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      wp_steps
      refine align_pre_st (by first | rfl | sep_ac_rfl | (simp only [wp_norm, arm64_norm]; (try first | rfl | sep_ac_rfl))) ?_
      wp_done
    · have hc1_f : (c1 == 0#64) = false := Bool.eq_false_iff.mpr hc1
      apply sepWP_evs_dealloc c1.toNat 1
      simp only [hc1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps; wp_apply
      have hacp_sf : AllocCallPreserved s1 sf := by
        simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
      rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
      refine align_pre_st (by rw [hsp1]; sep_ac_rfl) ?_
      wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2
      ⟨hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2, hacp2⟩
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
      BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc2 ⊢
    by_cases hc2 : (c2 == 0#64) = true
    · simp only [hc2, ↓reduceIte, sepConj_emp, emp_sepConj, sepConj_assoc]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6064#64) s2
          (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            ((s0.sp - 2200#64) ↦₆₄ p2) ∗ ((s0.sp - 2192#64) ↦₆₄ p1_new) ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest)
          (fun sm Pm =>
            (Pm ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
              ((s0.sp - 2200#64) ↦₆₄ p2) ∗ ((s0.sp - 2192#64) ↦₆₄ p1_new) ∗
              A.pool lim (M.stepEvents evs1 st) sm ∗ Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
            sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x25 = d32_64 ∧
            sm.readReg64 .x27 = p1_new ∧ sm.readReg64 .x28 = ptsLen ∧
            TraceCalleeSaved sm s0 ∧ AllocCallPreserved s2 sm) := by
        wp_steps
        refine align_pre_st (by first | rfl | sep_ac_rfl | (simp only [wp_norm, arm64_norm]; (try first | rfl | sep_ac_rfl))) ?_
        wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m,
        hx25_m, hx27_m, hx28_m, htr_m, hacp_m⟩ =>
        ⟨evs1, hevs1, hp, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m,
          hx25_m, hx27_m, hx28_m, htr_m, hacp2.trans hacp_m⟩
    · have hc2_f : (c2 == 0#64) = false := Bool.eq_false_iff.mpr hc2
      simp only [hc2_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      have hfin : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6064#64) s2
          (memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
            ((s0.sp - 2200#64) ↦₆₄ p2) ∗ ((s0.sp - 2192#64) ↦₆₄ p1_new) ∗
            A.live p2 c2.toNat 1 ∗ memRegion p2 c2.toNat ∗
            A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest)
          (fun sm Pm =>
            (Pm ⊢ memRegion (s0.sp - 7552#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
              ((s0.sp - 2200#64) ↦₆₄ p2) ∗ ((s0.sp - 2192#64) ↦₆₄ p1_new) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents c2.toNat 1) (M.stepEvents evs1 st))
                sm ∗ Rest) ∧
            sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
            sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x25 = d32_64 ∧
            sm.readReg64 .x27 = p1_new ∧ sm.readReg64 .x28 = ptsLen ∧
            TraceCalleeSaved sm s0 ∧ AllocCallPreserved s2 sm) := by
        wp_steps; wp_apply
        have hacp_sf : AllocCallPreserved s2 sf := by
          simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
        rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by rw [hsp2]; sep_ac_rfl) ?_
        wp_done
      refine SepWP.mono hfin fun sm _Pm _ _ ⟨hp, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m,
        hx25_m, hx27_m, hx28_m, htr_m, hacp_m⟩ => ?_
      refine ⟨evs1 ++ rustDeallocEvents c2.toNat 1,
        hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 c2.toNat),
        ?_, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m, htr_m,
        hacp2.trans hacp_m⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      exact hp

theorem v5b_dealloc_old_auth_6020_to_6064_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p2 p1_new c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6020#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = l1) (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = p1) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6064#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x25 = d32_64 ∧
          sm.readReg64 .x27 = p1_new ∧ sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0 ∧ AllocCallPreserved s1 sm) :=
  v5b_dealloc_old_auth_6020_to_6064_of_sub_placed (v5a_sub_ok_dealloc_of_placedHooks hA)
    st s0 s1 out p1 p2 p1_new c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

theorem v5b_dealloc_old_auth_6020_to_6064_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1 p2 p1_new c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6020#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = l1) (hx21_1 : s1.readReg64 .x21 = c2)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = c1) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = p1) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6064#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
        vecCapPtrDealloc A.repAlloc c1 p1 ∗ vecCapPtrDealloc A.repAlloc c2 p2 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ p2) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = l1 ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧ sm.readReg64 .x25 = d32_64 ∧
          sm.readReg64 .x27 = p1_new ∧ sm.readReg64 .x28 = ptsLen ∧
          TraceCalleeSaved sm s0 ∧ AllocCallPreserved s1 sm) :=
  v5b_dealloc_old_auth_6020_to_6064_of_sub_placed (v5a_sub_ok_dealloc_placed hA)
    st s0 s1 out p1 p2 p1_new c1 c2 l1 ptsPtr ptsCap ptsLen d32_64 Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlacedBudget
