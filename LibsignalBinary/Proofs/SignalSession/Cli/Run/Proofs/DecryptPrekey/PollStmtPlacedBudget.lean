/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.FramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Poll Closure Statements for `decrypt_prekey`

Defines the `RustCliAllocBudget M` poll closure contracts `CliDpPollOkStatePlacedAt` and
`CliDpPollOkStatePlacedStmt` on block `518` (`lsProg_518`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem dpPollNeed)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ decPkDef)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers (dpPollEntryPlaced dpPollProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget

open Arm64 Arm64.Process ProofLib
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollKStateBudget dpPollSpecStateBudget dpSlotPollKStatePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (readFileSpecPlaced sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

abbrev RunHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext

abbrev K₀_statePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) : DpPollKStateBudget M :=
  dpSlotPollKStatePlaced A lim DecPkEnv B S

/-- Pointwise budget-threaded `[LibsignalPlacement]` poll contract on block `518` at fixed
`(mmpl, g, W, X, B, S, Scope)` and allocation envelope `DecPkEnv`. -/
def CliDpPollOkStatePlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
    (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
  subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
    (sessDeserializeSpecPlaced CryptoVerification.SignalSession.Cli.Slots.scopeKit A lim DeserEnv) →
  CryptoVerification.SignalSession.Cli.Slots.EncodeInjOn CryptoVerification.SignalSession.Cli.Slots.scopeKit →
  (∀ r, Scope r → CryptoVerification.SignalSession.Cli.Slots.scopeIn r) →
  S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
  (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
    CryptoVerification.SignalSession.Cli.Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm) →
  ∀ stk' : Nat, (dpSlotPollKStatePlaced A lim DecPkEnv B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpPollEntryPlaced
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (dpPollSpecStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S) stk'))

/-- Quantified budget-threaded `[LibsignalPlacement]` poll contract on block `518` satisfying
`dpPollSpecStateBudget` at `K₀_statePlaced A lim (DecPkEnv W X B Scope) B S`. -/
def CliDpPollOkStatePlacedStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (DecPkEnv : CliHooks → UnreachedPqxdhPrimitives → RunBudgets →
      (SessionRecord (List (BitVec 8)) → Prop) → DecPkGhost → List AllocEvent → Prop) : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    CliDpPollOkStatePlacedAt A lim ReadEnv DeserEnv (DecPkEnv W X B Scope) mmpl g W X B S Scope

theorem dpSlotPollKStatePlaced_need [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) :
    (dpSlotPollKStatePlaced A lim DecPkEnv B S).need = dpPollNeed B := rfl

theorem dpSlotPollKStatePlaced_eq_K₀ [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop)
    (B : RunBudgets) (S : RunSem) :
    dpSlotPollKStatePlaced A lim DecPkEnv B S = K₀_statePlaced A lim DecPkEnv B S := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.PollStmtPlacedBudget
