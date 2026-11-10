/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation

/-!
# Move-Boundary Prefix Reachability

Every move-boundary prefix `ms₀` of a `MatchedPrefix` explanation `ms = ms₀ ++ δ` produces a
reachable composed trace `runTraceMoves r ms₀`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

theorem matchedPrefix_prefix_reachable {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent}
    (h : MatchedPrefix interpretation r S who g ms τ) :
    ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability := by
  intro ms₀ δ he
  have hreach := h.2.1.2.2.1.2.2 ms₀.length
  rwa [he, List.take_left] at hreach

end Symbolic.Swarm.CREF
