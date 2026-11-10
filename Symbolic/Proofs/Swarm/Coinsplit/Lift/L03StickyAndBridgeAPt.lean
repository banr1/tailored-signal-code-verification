/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
import Symbolic.Proofs.Swarm.CREF.Sticky
import Symbolic.Proofs.Swarm.Coinsplit.Slots.S5PrefixGhostsPt

/-!
# Plaintext Collision Lift Across `CoinSplit`

Proves `bridgeA_pt : BridgeAPtSpec`, lifting a `.pt` `PrefixGhosts` memo collision on `τ₁` to
`CollisionAfterExplainedPrefixMoves` on `σ₁ ++ .pt b :: σ₂` under `NoAdjRng σ₁`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L03

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.Coinsplit.Lift

private theorem noAdjRng_to_s5 : ∀ {σ : List MachineEvent},
    Symbolic.Swarm.Coinsplit.S1.NoAdjRng σ → Symbolic.Swarm.Coinsplit.S5.NoAdjRngS5 σ
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: e₂ :: es, ⟨h12, htl⟩ => ⟨h12, noAdjRng_to_s5 (σ := e₂ :: es) htl⟩

/-- Lifts a `PrefixGhosts` memo collision on `τ₁` to `CollisionAfterExplainedPrefixMoves` on
`σ₁ ++ .pt b :: σ₂` under `NoAdjRng σ₁`. -/
theorem bridgeA_pt : BridgeAPtSpec := by
  intro interp r S who ok g ms σ₁ τ₁ σ₂ b hadj hex hmatch hmemo
  exact ⟨σ₁, .pt b, σ₂, τ₁, g, ms, rfl, hex, hmatch,
    Symbolic.Swarm.Coinsplit.S5.excusesLift_pt_of_noAdjRng
      (noAdjRng_to_s5 hadj) hex.1 hex.2.1 hmemo⟩

end Symbolic.Swarm.Coinsplit.Lift.L03
