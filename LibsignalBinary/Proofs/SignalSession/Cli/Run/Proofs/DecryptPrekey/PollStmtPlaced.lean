/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.FramePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Poll Closure Contract Statements for `decrypt_prekey`

Defines the `[LibsignalPlacement]` poll closure contract `CliDpPollOkStatePlacedStmt` and its
`LibsignalFrozen` variant on block `518` (`lsProg_518`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptPrekeyHelpers
open CryptoVerification.CliHandshake.RespClosurePlaced
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

/-- States that the `decrypt_prekey` poll closure (`cliDpPollName`, block `518`) satisfies
`dpPollSpecState` at `K₀_statePlaced B S` under `[LibsignalPlacement]`. -/
def CliDpPollOkStatePlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpPollEntryPlaced
        (StoreKit.withLsCodeRoLoaded lsmpl
          (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk'))

/-- `LibsignalFrozen`-guarded counterpart of `CliDpPollOkStatePlacedStmt`. -/
def CliDpPollOkStateFrozenPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop),
    RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns g (cliExternsPlaced mmpl W)) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
    subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Slots.scopeKit E2E.HooksE.A0) →
    Slots.EncodeInjOn Slots.scopeKit →
    (∀ r, Scope r → Slots.scopeIn r) →
    S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ Scope →
    (∀ F peer me pm, S.filesOk F peer me → S.decPkOk F peer me pm →
      Slots.FilesOkPeer Scope F peer ∧ DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm) →
    ∀ stk' : Nat, (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).need ≤ stk' → stk' ≤ 2 ^ 63 →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) dpPollEntryPlaced
        (withLsFrozen lsmpl
          (dpPollSpecState (dpSlotPollKStatePlaced E2E.HooksE.A0 B S) stk'))

example [LibsignalPlacement] (B : RunBudgets) (S : RunSem) :
    (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).need = dpPollNeed B := rfl

example [LibsignalPlacement] (B : RunBudgets) (S : RunSem) :
    dpSlotPollKStatePlaced E2E.HooksE.A0 B S = K₀_statePlaced B S := rfl

end CryptoVerification.SignalSession.Cli.RunProofs
