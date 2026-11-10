/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Accept-Collision Predicate for Whisper Receive

Defines `TRRecvAllCollide`, stating that `body` has a receive representation and every
representation across `PrefixGhosts` exhibits `RecvCollision`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR.RecvCol

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Every valid representation `t` of `body` across all ghosts `g' ∈ PrefixGhosts` exhibits a
collision (`RecvCollision`) on `.recv`. -/
def TRRecvAllCollide (interpretation : ExternInterpretation) (r₀ : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (g : Ghost) (ms₁ : List Move) (τ₁ : List MachineEvent)
    (body : HwBytes) : Prop :=
  (∃ t, t ∈ recvRepresentations interpretation r₀ S g ms₁ body) ∧
  ∀ g' ∈ PrefixGhosts interpretation r₀ S who g ms₁ τ₁,
    ∀ t ∈ recvRepresentations interpretation r₀ S g' ms₁ body,
      RecvCollision interpretation r₀ S g' ms₁ t

end Symbolic.Swarm.CREF.TR.RecvCol
