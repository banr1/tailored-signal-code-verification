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
import Symbolic.Proofs.Swarm.Leaves.IC12_Stage1MatchedPrefixPure -- shake: keep

/-!
# Call-Count Agreement for Matched Events and Entries

Proves `prom_callCount_of_forall₂`, showing that `callCount` on visible entries equals
`(callStarts acc).length` under `List.Forall₂ EventMatchesEntry`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.Leaves.IC12Stage1MP
  (matchedPrefix_snoc_reject   runVis_append )

/-- Matched machine events and visible entries start the same number of calls. -/
theorem prom_callCount_of_forall₂ {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} :
    ∀ {acc : List MachineEvent} {vs : List VisEntry},
      List.Forall₂ (EventMatchesEntry interpretation r S g) acc vs →
        callCount vs = (callStarts acc).length
  | [], [], .nil => rfl
  | e :: acc, v :: vs, .cons hev h => by
    have ih := prom_callCount_of_forall₂ h
    have hk : v.kind = eventKind e := hev.1.symm
    unfold callCount callStarts at *
    simp only [List.filter_cons, hk]
    split <;> simp [ih]

end Symbolic.Swarm.CREF
