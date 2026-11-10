/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.AsmSecure
import Symbolic.Proofs.Tests.CliNonvacuity.HwAttackerKnows

/-!
# Non-Vacuity of `HwAttackerKnows` on Leaked Secrets

Shows that `HwAttackerKnows` holds on a CLI-explained trace (`Explains`) for a secret term
`t ∉ setupSent r` leaked via an environment `.leak` event matching a visible `.leak` entry.
Proofs live in `Symbolic.Proofs.Tests.CliNonvacuity.HwAttackerKnows`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.HwAttackerKnowsNonVacuity

open DY (Participant)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   setupSent BytesMatchEntry Explains HwAttackerKnows)

/-- Existence of a CLI-explained trace containing an environment leak `.env (.leak p bs)` of a
non-setup term `t ∉ setupSent r` such that `HwAttackerKnows r vis t` holds. -/
def HwAttackerKnowsLeakNonVacuous : Prop :=
  ∃ (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ss : List Step) (vis : List VisEntry) (evs : List CliEvent)
    (t : DY.Bytes) (p : Participant) (bs : HwBytes),
    Explains interp r S g ss vis evs ∧
    .env (.leak p bs) ∈ evs ∧
    (∃ v ∈ vis, v.kind = .leak ∧ t ∈ v.terms ∧ BytesMatchEntry interp r S g .leak bs v) ∧
    t ∉ setupSent r ∧
    HwAttackerKnows r vis t

/-- `HwAttackerKnowsLeakNonVacuous` holds, witnessed by Alice's leaked receiving chain key on the
exposed-session CLI trace. -/
theorem hwAttackerKnows_leak_nonvacuous : HwAttackerKnowsLeakNonVacuous :=
  Symbolic.Proofs.Tests.CliNonvacuity.HwAttackerKnows.hwAttackerKnows_leak_nonvacuous_proof

end Symbolic.Tests.HwAttackerKnowsNonVacuity
