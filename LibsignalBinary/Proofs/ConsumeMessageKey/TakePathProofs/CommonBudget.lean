/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Common

/-!
# Budget-Threaded Hook Helpers for the `consume_message_key` Take Path
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement blkPC_24 blkPl_24 lsρ)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkRustDeallocSym cmk_hook_ok_of_mem
)
open CryptoVerification.LibsignalSession.TakePath (cmkMemmoveSym)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkTakeState_placed FindIndexPlacedOk cmkPlacedSpec
)

def libcMemmoveBudgetSpec : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  withVmPreserved libcMemmoveSpec

def TakePathPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
    CmkAllocHooks A lim H → H cmkMemmoveSym = some hookMemmove → FindIndexPlacedOk H A →
      ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
        x.counter < x.ck.index →
        CmkTakeState_placed A lim x st_init st R s0 s →
        reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
          (cmkPlacedSpec F A lim) (x, st_init) R s0 s

set_option maxRecDepth 200000 in
theorem dealloc_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A lim H) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := by
  rcases hA with ⟨_, hdealloc, _, _, _, _⟩
  exact cmk_hook_ok_of_mem hdealloc

private theorem vmPreserved_hookMemmove (s : State) : VmPreserved s (hookMemmove s) := by
  dsimp only [hookMemmove, hookMemcpy, retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

set_option maxRecDepth 200000 in
theorem memmove_placed_ok_at [LibsignalPlacement]
    {H : String → Option (State → State)} (hmemmove : H cmkMemmoveSym = some hookMemmove) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkMemmoveSym)
      libcMemmoveBudgetSpec :=
  cmk_hook_ok_of_mem (hookSat_withVmPreserved ⟨hookMemmove, hmemmove, hookMemmove_ok⟩
    fun f hf s => by cases hmemmove.symm.trans hf; exact vmPreserved_hookMemmove s)

end LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.CommonBudget
