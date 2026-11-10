/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget

/-!
# `FdsGe3Closed`-Threaded `drop_glue<SessionStructure> [local#2]` Seam (Block `139`)

Instantiates `Local2Budget.drop_session_structure_local2_placed_ok` at `withFds A` to lift
`dropSessionStructureLocal2Spec M A lim` under `withFdsGe3Closed` when `lim.enforced = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2BudgetFd

open Arm64
open CryptoVerification (
  IsLsBlockProg LibsignalPlacement LsBlockBound
  blkPC_139 blkPl_139 lsRustDeallocSym ls_subroutine_ok_of_block lsmpl withLsCodeLoaded
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  hookOk_deallocBudget_withFds withFds
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudgetFd (
  subroutine_ok_withFdsGe3Closed_withLsCodeLoaded_of_inner
  subroutine_ok_withLsCodeLoaded_dropSessionStructureLocal2_withFdsGe3Closed_of_withFds
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2Budget (
  drop_session_structure_local2_placed_ok
)

private theorem hookSat_deallocBudget_withFds [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits}
    {H : String → Option (State → State)} {sym : String}
    (hsat : HookSat H sym (rustCliDeallocBudgetSpec M A lim)) :
    HookSat H sym (rustCliDeallocBudgetSpec M (withFds A) lim) :=
  let ⟨f, hf, hok⟩ := hsat
  ⟨f, hf, hookOk_deallocBudget_withFds hok⟩

/-- Block `139` (`core::ptr::drop_glue::<SessionStructure> [local#2]`) meets
`withLsCodeLoaded lsmpl (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim))` when
`lim.enforced = true`. -/
theorem drop_session_structure_local2_placed_ok_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_139).rebase (blkPl_139).base H) (blkPl_139).base
      (withLsCodeLoaded lsmpl
        (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim))) :=
  subroutine_ok_withLsCodeLoaded_dropSessionStructureLocal2_withFdsGe3Closed_of_withFds henf
    (drop_session_structure_local2_placed_ok (hookSat_deallocBudget_withFds h_dealloc))

/-- Outer-`withFdsGe3Closed` variant of `drop_session_structure_local2_placed_ok_withFdsGe3Closed`. -/
theorem drop_session_structure_local2_placed_ok_outer_withFdsGe3Closed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_139).rebase (blkPl_139).base H) (blkPl_139).base
      (withFdsGe3Closed
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim))) :=
  subroutine_ok_withFdsGe3Closed_withLsCodeLoaded_of_inner
    (drop_session_structure_local2_placed_ok_withFdsGe3Closed henf h_dealloc)

/-- Caller-block transfer of `drop_session_structure_local2_placed_ok_withFdsGe3Closed` to any
`callerProg` with `[IsLsBlockProg callerProg i H]`. -/
theorem drop_session_structure_local2_placed_ok_withFdsGe3Closed_at [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {callerProg : Program} {i bi : Nat} [IsLsBlockProg callerProg i H] [LsBlockBound bi]
    (henf : lim.enforced = true)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 139)
      (withLsCodeLoaded lsmpl
        (withFdsGe3Closed (dropSessionStructureLocal2Spec M A lim))) :=
  ls_subroutine_ok_of_block
    (drop_session_structure_local2_placed_ok_withFdsGe3Closed henf h_dealloc) hi

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2BudgetFd
