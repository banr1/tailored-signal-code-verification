/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part E

Relocatable Block-`333` `ek` deallocation (`+8908 -> +8932`), `Unchunked::EkSent` assembly,
`sendingEk = none` cleanup, and `ProtoPolynomialEncoder` staging (`+9036..+9096`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v2hsc_stackAt_allocHook_to_encoderFromPbStack
   v2hsc_stackAt_encoderFromPbStack_to_allocHook v2hse_bv_add_add_lit
   v2hse_protoPolyEncoderWordsAt v2hse_unchunkedEkSentWordsAt
   v2hse_unchunkedEkSentWordsAt_entails_80)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (align_pre_st deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_st
   subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget blk333_noSvc0 entails_pre_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
  (v2hsc_cleanup_9152_to_9212_of_sub_placed v2hsc_sub_ok_dealloc_of_dealloc_placed
   v2hsc_sub_ok_dealloc_of_placedHooks v2hsc_sub_ok_dealloc_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v2hse_bv_add_add_lit

private theorem blkPl_333_base [LibsignalPlacement] :
    (blkPl_333).base = lsmpl.base 333 := rfl

@[local simp] private theorem stripS_pstate (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).pstate = s.pstate := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem setMem_pstate (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := rfl

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  try rw [← blkPl_333_base]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## `+8908 .. +9032` Stepping & Cleanup -/

/-- Execution segment `+8908 -> +8932`: shifts `x26 = (pa1.extractLsb' 8 56).zeroExtend 64` and deallocates
    `(cap_ek, ptr_ek)` (`x24 = cap_ek`, `x25 = ptr_ek`) with `FreeOnlyEvs` budget accounting. -/
theorem v2hse_dealloc_8908_to_8932_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 pa1 cap_ek ptr_ek pbA epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx24_1 : s1.readReg64 .x24 = cap_ek)
    (hx25_1 : s1.readReg64 .x25 = ptr_ek)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8932#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt fsp encoderFromPbStack ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  rcases htr1 with ⟨htr_1, hvregs_1⟩
  have hdealloc_fo : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly hdealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat, lsProg_333] at hdealloc_fo hpc1 ⊢
  rw [← blkPl_333_base] at hpc1 ⊢
  by_cases hcap : (cap_ek == 0#64) = true <;>
    simp only [hcap, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [M.stepEvents_nil]
    wp_steps_sync_333 (lsmpl.base 333 + 8932#64)
    try simp only [State.setMem_setMem]
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (A.pool lim st sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done
  · apply sepWP_evs_dealloc cap_ek.toNat 1
    wp_steps_sync_333 (lsρ spqrRustDeallocSym)
    try simp only [State.setMem_setMem]
    wp_call hdealloc_fo (ptr_ek, cap_ek.toNat, 1, st)
    have hacp : AllocCallPreserved s1 sf := by
      simpa only [wp_norm, arm64_norm] using ‹AllocCallPreserved _ sf›
    have hsp_sf : sf.sp = fsp := ‹sf.sp = _›.trans (by simp [wp_norm, arm64_norm, hsp1])
    have htr_sf : sf.trace = s0.trace := hacp.2.1.trans htr_1
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
      ‹calleeSavedVRegs sf = _›.trans hvregs_1
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      simp only [wp_norm, arm64_norm, hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (A.pool lim (M.stepEvents (rustDeallocEvents cap_ek.toNat 1) st) sc ∗ Frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

theorem v2hse_dealloc_8908_to_8932_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 pa1 cap_ek ptr_ek pbA epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx24_1 : s1.readReg64 .x24 = cap_ek)
    (hx25_1 : s1.readReg64 .x25 = ptr_ek)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8932#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt fsp encoderFromPbStack ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) :=
  v2hse_dealloc_8908_to_8932_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0 pa1 cap_ek ptr_ek pbA epoch
    st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 htr1

theorem v2hse_dealloc_8908_to_8932_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 pa1 cap_ek ptr_ek pbA epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx24_1 : s1.readReg64 .x24 = cap_ek)
    (hx25_1 : s1.readReg64 .x25 = ptr_ek)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8932#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt fsp encoderFromPbStack ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) :=
  v2hse_dealloc_8908_to_8932_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0 pa1 cap_ek ptr_ek pbA epoch
    st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 htr1

theorem v2hse_dealloc_8908_to_8932_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 pa1 cap_ek ptr_ek pbA epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8908#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx24_1 : s1.readReg64 .x24 = cap_ek)
    (hx25_1 : s1.readReg64 .x25 = ptr_ek)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8932#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A.repAlloc cap_ek ptr_ek ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢ stackAt fsp encoderFromPbStack ∗ A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) :=
  v2hse_dealloc_8908_to_8932_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0 pa1 cap_ek ptr_ek pbA epoch
    st Frame hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 htr1

/-- `VmPreserved`-strengthened segment `+8932 -> +8960` when `ca1.toNat < 2 ^ 63`. -/
theorem v2hse_step_8932_to_8960_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca1 pa1 pbA epoch d1273_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8960#64) s1
      (((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1273#64) ↦₃₂ d1273_old.setWidth 32) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64 ∧
        sm.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = fsp + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hsePlaced.v2hse_step_8932_to_8960_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out d0 ca1 pa1 pbA epoch d1273_old Frame
      hfsp_align hca1 (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx26_1) (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8_m, hx9_m, hx10_m, hx19_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx8_m, hx9_m, hx10_m, hx19_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse_step_8932_to_8960_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca1 pa1 pbA epoch d1273_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8960#64) s1
      (((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1273#64) ↦₃₂ d1273_old.setWidth 32) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
          A.pool lim st sm ∗ Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64 ∧
        sm.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64 ∧
        sm.readReg64 .x10 = fsp + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse_step_8932_to_8960_placed (ext := ext) s0 s1 fsp out d0 ca1 pa1 pbA epoch
    d1273_old (A.pool lim st s1 ∗ Frame)
    hfsp_align hca1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened segment `+8960 -> +9032`. -/
theorem v2hse_step_8960_to_9032_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
     u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8960#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64)
    (hx9_1 : s1.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64)
    (hx10_1 : s1.readReg64 .x10 = fsp + 1264#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9032#64) s1
      (((fsp + 96#64) ↦₆₄ la3) ∗
        ((fsp + 152#64) ↦₆₄ ca3) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 976#64) ↦₆₄ cap_enc) ∗
        ((fsp + 1264#64) ↦₆₄ u0) ∗
        ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
        ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
        ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
        ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗
        ((fsp + 1280#64) ↦₆₄ u16) ∗
        ((fsp + 1288#64) ↦₆₄ u24) ∗
        ((fsp + 1296#64) ↦₆₄ u32) ∗
        ((fsp + 1304#64) ↦₆₄ u40) ∗
        ((fsp + 1312#64) ↦₆₄ u48) ∗
        ((fsp + 1320#64) ↦₆₄ u56) ∗
        ((fsp + 1328#64) ↦₆₄ u64) ∗
        ((fsp + 1336#64) ↦₆₄ u72) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 96#64) ↦₆₄ la3) ∗
          ((fsp + 152#64) ↦₆₄ ca3) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 976#64) ↦₆₄ cap_enc) ∗
          v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 ca1 ca2 pa2 ca2 ca3 pa3 la3 epoch ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        sm.pstate = addsPState64 cap_enc 1#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hsePlaced.v2hse_step_8960_to_9032_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 Frame
      hfsp_align (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx9_1) (by simpa using hx10_1)
      (by simpa using hx19_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx25_1) (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx8_m, hx19_m, hx22_m, hx23_m, hx25_m, hx26_m, hx27_m, hx28_m, hpstate_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx0_m, hx8_m, hx19_m, hx22_m, hx23_m, hx25_m, hx26_m, hx27_m, hx28_m,
       by simpa using hpstate_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse_step_8960_to_9032_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
     u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 8960#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 48 16).zeroExtend 64)
    (hx9_1 : s1.readReg64 .x9 = (((pa1.extractLsb' 8 56).zeroExtend 64).extractLsb' 32 32).zeroExtend 64)
    (hx10_1 : s1.readReg64 .x10 = fsp + 1264#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9032#64) s1
      (((fsp + 96#64) ↦₆₄ la3) ∗
        ((fsp + 152#64) ↦₆₄ ca3) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 976#64) ↦₆₄ cap_enc) ∗
        ((fsp + 1264#64) ↦₆₄ u0) ∗
        ((fsp + 1272#64) ↦₈ u8.extractLsb' 0 8) ∗
        ((fsp + 1273#64) ↦₃₂ pa1.extractLsb' 8 32) ∗
        ((fsp + 1277#64) ↦₁₆ u8.extractLsb' 40 16) ∗
        ((fsp + 1279#64) ↦₈ u8.extractLsb' 56 8) ∗
        ((fsp + 1280#64) ↦₆₄ u16) ∗
        ((fsp + 1288#64) ↦₆₄ u24) ∗
        ((fsp + 1296#64) ↦₆₄ u32) ∗
        ((fsp + 1304#64) ↦₆₄ u40) ∗
        ((fsp + 1312#64) ↦₆₄ u48) ∗
        ((fsp + 1320#64) ↦₆₄ u56) ∗
        ((fsp + 1328#64) ↦₆₄ u64) ∗
        ((fsp + 1336#64) ↦₆₄ u72) ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 96#64) ↦₆₄ la3) ∗
          ((fsp + 152#64) ↦₆₄ ca3) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 976#64) ↦₆₄ cap_enc) ∗
          v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 ca1 ca2 pa2 ca2 ca3 pa3 la3 epoch ∗
          A.pool lim st sm ∗ Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        sm.pstate = addsPState64 cap_enc 1#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse_step_8960_to_9032_placed (ext := ext) s0 s1
    fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 (A.pool lim st s1 ∗ Frame)
    hfsp_align hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened combined step `+8932 -> +9032`. -/
theorem v2hse_step_8932_to_9032_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9032#64) s1
      (((fsp + 96#64) ↦₆₄ la3) ∗
        ((fsp + 152#64) ↦₆₄ ca3) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 976#64) ↦₆₄ cap_enc) ∗
        memRegion (fsp + 1264#64) 80 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 96#64) ↦₆₄ la3) ∗
          ((fsp + 152#64) ↦₆₄ ca3) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 976#64) ↦₆₄ cap_enc) ∗
          v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 ca1 ca2 pa2 ca2 ca3 pa3 la3 epoch ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        sm.pstate = addsPState64 cap_enc 1#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hsePlaced.v2hse_step_8932_to_9032_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA Frame
      hfsp_align hca1 (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx26_1) (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx8_m, hx19_m, hx22_m, hx23_m, hx25_m, hx26_m, hx27_m, hx28_m, hpstate_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx0_m, hx8_m, hx19_m, hx22_m, hx23_m, hx25_m, hx26_m, hx27_m, hx28_m,
       by simpa using hpstate_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse_step_8932_to_9032_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State)
    (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hca1 : ca1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 8932#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx23_1 : s1.readReg64 .x23 = pa1)
    (hx26_1 : s1.readReg64 .x26 = (pa1.extractLsb' 8 56).zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = epoch)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9032#64) s1
      (((fsp + 96#64) ↦₆₄ la3) ∗
        ((fsp + 152#64) ↦₆₄ ca3) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 976#64) ↦₆₄ cap_enc) ∗
        memRegion (fsp + 1264#64) 80 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 96#64) ↦₆₄ la3) ∗
          ((fsp + 152#64) ↦₆₄ ca3) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 976#64) ↦₆₄ cap_enc) ∗
          v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 ca1 ca2 pa2 ca2 ca3 pa3 la3 epoch ∗
          A.pool lim st sm ∗ Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = cap_enc ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = ca1 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = epoch ∧
        sm.pstate = addsPState64 cap_enc 1#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse_step_8932_to_9032_placed (ext := ext) s0 s1
    fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch cap_enc pbA (A.pool lim st s1 ∗ Frame)
    hfsp_align hca1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- When `cap_enc = noneCap` at `+9032`, takes `b.eq +9152` and runs
    `v2hsc_cleanup_9152_to_9212_of_sub_placed` to deallocate `(ca1, pa1)`, `(ca2, pa2)`,
    `(ca3, pa3)` with `FreeOnlyEvs` budget accounting and reach `+9212`. -/
theorem v2hse_none_enc_9032_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1264#64) 80 ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine seq_clean_st
    (mid := lsmpl.base 333 + 9152#64)
    (P_mid := fun sm =>
      stackAt fsp encoderFromPbStack ∗
      v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim st sm ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = pa2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x25 = ca1 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rcases htr1 with ⟨htr_1, hvregs_1⟩
    dsimp only [noneCap, BitVec.ofNat_eq_ofNat, lsProg_333] at hpc1 hpstate1 ⊢
    rw [← blkPl_333_base] at hpc1
    wp_steps_sync_333 (lsmpl.base 333 + 9152#64)
    try simp only [State.setMem_setMem]
    refine align_pre_st (by sep_ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx25_2, hx26_2, htr2⟩
    unfold v2hse_unchunkedEkSentWordsAt
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    have h9152 := v2hsc_cleanup_9152_to_9212_of_sub_placed hdealloc_ok s0 s2 fsp out d0
      ca1 pa1 ca2 pa2 ca3 pa3 st
      (((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx25_2 hx26_2 htr2
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono h9152 fun sm Pm _ _ ⟨evs, hevs, hPm, hq⟩ => ?_)
    refine ⟨evs, hevs, Entails.trans hPm ?_, hq⟩
    have hm80 := v2hse_unchunkedEkSentWordsAt_entails_80
      (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch
    unfold v2hse_unchunkedEkSentWordsAt at hm80
    simp only [v2hse_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm80
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch)) ∗
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       A.pool lim (M.stepEvents evs st) sm ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm80) (Entails.of_eq (by sep_ac_rfl))

theorem v2hse_none_enc_9032_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1264#64) 80 ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hse_none_enc_9032_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc) s0 s1 fsp out d0
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch st Frame
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx25_1 hx26_1 hpstate1 htr1

theorem v2hse_none_enc_9032_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1264#64) 80 ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hse_none_enc_9032_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA) s0 s1 fsp out d0
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch st Frame
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx25_1 hx26_1 hpstate1 htr1

theorem v2hse_none_enc_9032_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9032#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        ∃ evs, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1264#64) 80 ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hse_none_enc_9032_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA) s0 s1 fsp out d0
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch st Frame
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx22_1 hx25_1 hx26_1 hpstate1 htr1

/-! ## Encoder Copy (`+9036 .. +9096`) -/

/-- `VmPreserved`-strengthened segment `+9036 -> +9096`: copies the 56-byte `ProtoPolynomialEncoder`
    words `(w0, w8, w16, w24, w32, w40, w48)` into `fsp + 1792..1848`. -/
theorem v2hse_copy_enc_9032_to_9096_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9036#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9096#64) s1
      (((fsp + 984#64) ↦₆₄ w8) ∗
        ((pbA + 96#64) ↦₆₄ w8) ∗
        ((pbA + 104#64) ↦₆₄ w16) ∗
        ((pbA + 112#64) ↦₆₄ w24) ∗
        ((pbA + 120#64) ↦₆₄ w32) ∗
        ((pbA + 128#64) ↦₆₄ w40) ∗
        ((pbA + 136#64) ↦₆₄ w48) ∗
        memRegion (fsp + 1792#64) 56 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 984#64) ↦₆₄ w8) ∗
          ((pbA + 96#64) ↦₆₄ w8) ∗
          ((pbA + 104#64) ↦₆₄ w16) ∗
          ((pbA + 112#64) ↦₆₄ w24) ∗
          ((pbA + 120#64) ↦₆₄ w32) ∗
          ((pbA + 128#64) ↦₆₄ w40) ∗
          ((pbA + 136#64) ↦₆₄ w48) ∗
          v2hse_protoPolyEncoderWordsAt (fsp + 1792#64) w0 w8 w16 w24 w32 w40 w48 ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = s1.readReg64 .x23 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hsePlaced.v2hse_copy_enc_9032_to_9096_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out d0 ca3 pbA w0 w8 w16 w24 w32 w40 w48 Frame
      hfsp_align (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx19_1) (by simpa using hx22_1)
      (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx0_m, hx1_m, hx19_m, by simpa using hx21_m, hx22_m,
       by simpa using hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, by simpa using hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse_copy_enc_9032_to_9096_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9036#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx8_1 : s1.readReg64 .x8 = w0)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9096#64) s1
      (((fsp + 984#64) ↦₆₄ w8) ∗
        ((pbA + 96#64) ↦₆₄ w8) ∗
        ((pbA + 104#64) ↦₆₄ w16) ∗
        ((pbA + 112#64) ↦₆₄ w24) ∗
        ((pbA + 120#64) ↦₆₄ w32) ∗
        ((pbA + 128#64) ↦₆₄ w40) ∗
        ((pbA + 136#64) ↦₆₄ w48) ∗
        memRegion (fsp + 1792#64) 56 ∗
        A.pool lim st s1 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 984#64) ↦₆₄ w8) ∗
          ((pbA + 96#64) ↦₆₄ w8) ∗
          ((pbA + 104#64) ↦₆₄ w16) ∗
          ((pbA + 112#64) ↦₆₄ w24) ∗
          ((pbA + 120#64) ↦₆₄ w32) ∗
          ((pbA + 128#64) ↦₆₄ w40) ∗
          ((pbA + 136#64) ↦₆₄ w48) ∗
          v2hse_protoPolyEncoderWordsAt (fsp + 1792#64) w0 w8 w16 w24 w32 w40 w48 ∗
          A.pool lim st sm ∗ Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = s1.readReg64 .x23 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse_copy_enc_9032_to_9096_placed (ext := ext) s0 s1
    fsp out d0 ca3 pbA w0 w8 w16 w24 w32 w40 w48 (A.pool lim st s1 ∗ Frame)
    hfsp_align hpc1 hrun1 hsp1 hx8_1 hx19_1 hx22_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsePlacedBudget
