/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.Specifications.Security.Model

/-!
# Hardware Attacker and Explained-Trace Security Queries

**Trusted: definitions used by the statement.**

Defines the hardware-level Dolev-Yao attacker (`HwAttackerObserves`, `HwAttackerKnows`) and
instantiates `Security.AllSecurityQueriesHold` over explained CLI event traces
(`AllSecurityQueriesHoldOnHwTrace`).
-/

@[expose] public section

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (CliEvent)

section
variable (r : ProtocolSetup) (vis : List VisEntry)

/-- Terms observed by the hardware adversary under `vis`: public setup messages (`setupSent r`) and
terms in `.send`, `.recv`, or `.leak` entries (excluding `.pt`, `.rng`, and `.accept`). -/
def HwAttackerObserves (t : DY.Bytes) : Prop :=
  t ∈ setupSent r ∨
  ∃ v ∈ vis, t ∈ v.terms ∧
    match v.kind with
    | .send | .recv | .leak => True
    | .pt | .rng | .accept => False

/-- Dolev-Yao deduction closure of `HwAttackerObserves r vis`. -/
def HwAttackerKnows (t : DY.Bytes) : Prop :=
  Fixpoint.mkLeastFixpoint
    (fun known b => AttackerKnowledge.attackerKnowledge.pred known b ∨ HwAttackerObserves r vis b) t

end

/-- Under every explanation `(g, ss, vis)` of CLI trace `evs`, all ten security queries hold on
`runTrace r ss` against `HwAttackerKnows r vis`. -/
def AllSecurityQueriesHoldOnHwTrace (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs : List CliEvent) : Prop :=
  ∀ g ss vis, Explains interpretation r S g ss vis evs →
    Security.AllSecurityQueriesHold (runTrace r ss) (HwAttackerKnows r vis)

end DY.Libsignal.Composed.Refinement
