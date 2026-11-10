/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.QuietTransferPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Current-Snapshot Premise and Quiet Extensions for Receive-Wire Steps

Defines `RcvCurrentRead`, stating that a `decrypt` or `decryptSkipped` move reads a current
session snapshot and a valid representation of `body`, and shows that `InvisibleNoEffect`
prefixes and suffixes induce `QuietExt` trace extensions.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure.RpkCli
open CryptoProofLib.Refinement (ExternInterpretation)

/-- Asserts that a `decrypt` or `decryptSkipped` move reads a current snapshot (`isCurrentSnapshot`)
and a message term in `recvRepresentations` for `body`; holds trivially for other moves. -/
def RcvCurrentRead (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (body : HwBytes) : Move → Prop
  | m@(.decrypt _ stateIdx ..) => TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
      ∀ t, rcvMoveTerm (runTraceMoves r ms) m = some t → t ∈ recvRepresentations interpretation r S g ms body
  | m@(.decryptSkipped _ stateIdx ..) =>
      TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) stateIdx = true ∧
      ∀ t, rcvMoveTerm (runTraceMoves r ms) m = some t → t ∈ recvRepresentations interpretation r S g ms body
  | _ => True

theorem a2b_quietPre {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
  rw [TR.runTrace_append]
  exact XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)

theorem a2b_quietPost {r : ProtocolSetup} {ms₀ pre post : List Move} {m : Move}
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r ms₀)).1) post) :
    XplQuiet.QuietExt (runTraceMoves r (ms₀ ++ pre ++ [m]))
      (runTraceMoves r (ms₀ ++ (pre ++ m :: post))) := by
  rw [show ms₀ ++ (pre ++ m :: post) = ms₀ ++ pre ++ [m] ++ post by simp,
    TR.runTrace_append (ms₁ := ms₀ ++ pre ++ [m]), TR.runTrace_snoc, TR.runTrace_append]
  exact XplQuiet.quietExt_of_movesFrom _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)

end Symbolic.Swarm.CREF.CliPure
