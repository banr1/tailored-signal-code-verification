/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1DecryptNoop
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs
def DecryptNoop (r : Records) (ms : List Move) : Prop := ∀ (k : Nat) (m : Move), ms[k]? = some m → m.decryptMsgIdx? ≠ none → m.vis (runTraceMoves r (ms.take k)) = [] ∧ m.next (runTraceMoves r (ms.take k)) = runTraceMoves r (ms.take k)
theorem not_readCollision_of_decryptNoop {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {τ : List MachineEvent} (h : DecryptNoop r ms) : ¬ ReadCollision i r S g ms τ := by
  rintro ⟨k, τ₁, e, τ₂, m, _, hget, _, _, hrc⟩
  unfold MoveReadsCollidingMsg at hrc
  cases m <;> try exact False.elim hrc
  all_goals
    rcases hrc with ⟨b, t, _, hsent, _⟩
    obtain ⟨hvis, -⟩ := h k _ hget (by simp [Move.decryptMsgIdx?])
    simp [Move.vis, decVis, hsent] at hvis
end Symbolic.BugInjection.Proofs.Common443.WsIdx1DecryptNoop
