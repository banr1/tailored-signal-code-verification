/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.NonVacuity.CliSatisfiable
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

/-!
# Pinned Witness Compatibility Predicate

Defines `TorsionShiftsRecorded` and the proof-layer compatibility predicate `compFitsPinned`,
which strengthens `compFits` by pinning the external interpretation to `compI0`, fixing
unrecorded setup randoms and participant names (`"alice"`, `"bob"`), and requiring X25519
8-torsion rejection and shift recording. Proofs establish `SpecHalf` and `ImplHalf` against
`compFitsPinned w` before eliminating `fits` via `not_refines_of_witness`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)

/-- Every recorded pair `(a, b)` in `shifts` equals `torsionShift i a t` for some `t : Fin 8`. -/
def TorsionShiftsRecorded (i : ExternInterpretation) (shifts : List (HwBytes × HwBytes)) : Prop :=
  ∀ ab ∈ shifts, ∃ t : Fin 8, DY.Libsignal.Refinement.torsionShift i ab.1 t = ab.2

section Comp
open DY.Libsignal.Composed.Refinement

/-- Strengthens `compFits w i r` by pinning `i = compI0`, setup randoms 3–5 to
`fillFresh 11/16/17 64`, participant names to `"alice"` and `"bob"`, X25519 torsion-shift
rejection, and `TorsionShiftsRecorded`. -/
def compFitsPinned (w : PQXDHSpqrSetup) (i : ExternInterpretation) (r : Records) : Prop :=
  compFits w i r ∧ i = Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compI0 ∧
    (secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧
      secretBytes r 5 = fillFresh 17 64) ∧ (r.alice = "alice" ∧ r.bob = "bob") ∧
    DY.Libsignal.PQXDH.Refinement.X25519PubTorsionShiftsRejected i ∧
    TorsionShiftsRecorded i w.torsionShifts

end Comp

end Symbolic.BugInjection
