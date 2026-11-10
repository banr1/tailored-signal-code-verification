/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
import Arm64.Trusted.Spec.Hoare

/-!
# Budget-Threaded `dropSpeOwnedSpecPlaced` Aliases and `.proto` Projections (Placed)

Aliases the budget-threaded `[LibsignalPlacement]` `dropSpeOwnedSpecPlaced`, `DropSpeOwnedOkPlaced`,
`DropSpeOwnedOkAtBlock`, and `dropSpeSpecStkPlaced` definitions from `DropSpeOwnedPlacedBudget`, and
proves agreement on `.proto`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost)
open CryptoVerification.SignalSession.Cli.RunDrop (DropSpeOwnedGhost)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.ProofBudget (dropSpeSpecStk)

/-- Budget-threaded `[LibsignalPlacement]` `dropSpeOwnedSpecPlaced`. -/
abbrev dropSpeOwnedSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropSpeOwnedGhost × M.σ) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget.dropSpeOwnedSpecPlaced
    A lim stk

abbrev DropSpeOwnedOkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget.DropSpeOwnedOkPlaced
    A lim H

abbrev DropSpeOwnedOkAtBlock [LibsignalPlacement] {M : AllocCostModel}
    (callerProg : Program) (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget.DropSpeOwnedOkAtBlock
    callerProg A lim

abbrev dropSpeSpecStkPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    Spec (DropSpeGhost × M.σ) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget.dropSpeSpecStkPlaced
    A lim stk

theorem dropSpeOwnedSpecPlaced_proto_pre [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (a : BitVec 64) (fnName : List (BitVec 8))
    (e : SignalProtocolError) (st : M.σ) :
    (dropSpeOwnedSpecPlaced A lim stk).pre (⟨a, .proto fnName e⟩, st) =
      (withLsCodeRoLoaded lsmpl (dropSpeSpecStk A lim stk)).pre (⟨a, fnName, e⟩, st) := rfl

theorem dropSpeOwnedSpecPlaced_proto_post [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (a : BitVec 64) (fnName : List (BitVec 8))
    (e : SignalProtocolError) (st : M.σ) :
    (dropSpeOwnedSpecPlaced A lim stk).post (⟨a, .proto fnName e⟩, st) =
      (withLsCodeRoLoaded lsmpl (dropSpeSpecStk A lim stk)).post (⟨a, fnName, e⟩, st) := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Specs.SpeOwnedPlacedBudget
