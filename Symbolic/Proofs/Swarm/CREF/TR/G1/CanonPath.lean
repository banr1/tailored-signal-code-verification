/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Bob Session-Start Exclusion under `PathFaithful`

Proves `not_bobStart_of_bobDone`: under `PathFaithful`, a call on a pre-key message whose base key
matches an earlier `BobDone` event cannot take Bob's session-start path.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1.Spine

cref_open
open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)

section Excl
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
  {ms : List Move} {τ₁ : List MachineEvent}

/-- Under `PathFaithful`, a call on pre-key bytes whose base key matches an earlier `BobDone` event
is not explained by Bob's session-start path. -/
theorem not_bobStart_of_bobDone (h : PathFaithful interpretation r S g ms τ₁) {i : Nat}
    {m : Move} {b : HwBytes} {p : PreKeyFields} (hi : ms[i]? = some m)
    (hcall : (callStarts τ₁)[callCount (runVis r (ms.take i))]? = some (.recv b))
    (hparse : parsePreKeyWire b = some p)
    (hdone : ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r (ms.take i)),
      ecKey (gamma interpretation S g ek) = p.baseKey.take 33) :
    m.prekeyPath? ≠ some false := by
  intro hpath
  have := (h i m false b p hi hpath hcall hparse).2 hdone
  cases this

end Excl

section Shape
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}

end Shape

section CanonStep
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}

end CanonStep

section CongrAndExtend
variable {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}

end CongrAndExtend

end Symbolic.Swarm.CREF.TR.G1.Spine
