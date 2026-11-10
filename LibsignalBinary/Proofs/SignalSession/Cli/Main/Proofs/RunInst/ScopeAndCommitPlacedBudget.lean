/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
import Arm64.Trusted.Spec.Hoare

/-!
# Budget-Threaded `runNeed` Stack Bound for `signal_session::run`

Proves `runNeed cliRunBudgets (slotsOfPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) ≤ cliResStack`
under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget

open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.MainHops (cliResStack cliRunBudgets cliRunNeeds)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem)
open CryptoVerification.SignalSession.Cli.RunSkeleton (runNeed)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)

private theorem foldr_max_le {xs : List Nat} {acc b : Nat}
    (hacc : acc ≤ b) (hxs : ∀ x ∈ xs, x ≤ b) : xs.foldr max acc ≤ b := by
  induction xs with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldr_cons, Nat.max_le]
    exact ⟨hxs x (List.mem_cons_self ..), ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))⟩

theorem runNeed_cli_le_resStack_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (sEnvs : RunSlotEnvs)
    {S : RunSem} {decPkNeed : Nat} (hdec : decPkNeed ≤ 4194304) :
    runNeed cliRunBudgets (slotsOfPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) ≤ cliResStack := by
  have hcallee :
      CryptoVerification.SignalSession.Cli.RunSkeleton.runCalleeNeed cliRunBudgets
        (slotsOfPlaced A lim sEnvs S (cliRunNeeds decPkNeed)) ≤ 4194304 := by
    unfold CryptoVerification.SignalSession.Cli.RunSkeleton.runCalleeNeed
    refine foldr_max_le (by decide) fun x hx => ?_
    dsimp only [slotsOfPlaced, CryptoVerification.SignalSession.Cli.RunCompose.mkSlot, cliRunNeeds] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hdec | decide
  have hsum : CryptoVerification.SignalSession.Cli.RunSkeleton.runFrame + 4194304 ≤ cliResStack := by
    decide
  unfold runNeed
  omega

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
