/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.Model.RejKeyNonDerivability

/-!
# Non-Derivability of Kyber Implicit-Rejection Keys

States arbitrary-trace (`rejKey_attackerKnows_or_baseExposed`) and reachable-trace
(`rejKey_attackerKnows_iff_of_reachable`) non-derivability of `PQKem.kemRejKey sk ct` in the
composed symbolic model, together with `#guard_msgs` axiom checks. Proofs live in
`Symbolic.Proofs.Tests.Model.RejKeyNonDerivability`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.RejKeyNonDerivability

open DY
open DY.Libsignal.Composed

export Symbolic.Proofs.Tests.Model.RejKeyNonDerivability (ExposesSubterm)

/-- On any trace `tr`, attacker knowledge of `PQKem.kemRejKey sk ct` requires either attacker
knowledge of both `sk` and `ct` or a base-known entry exposing `PQKem.kemRejKey sk ct` via
projecting wrappers. -/
theorem rejKey_attackerKnows_or_baseExposed (tr : ExecTrace) (sk ct : Bytes) :
    (PQKem.kemRejKey sk ct).AttackerKnows tr →
      (sk.AttackerKnows tr ∧ ct.AttackerKnows tr) ∨
        ∃ m, tr.BaseAttackerKnows m ∧ ExposesSubterm (PQKem.kemRejKey sk ct) m :=
  Symbolic.Proofs.Tests.Model.RejKeyNonDerivability.rejKey_attackerKnows_or_baseExposed_proof tr sk ct

/-- On any reachable composed-protocol trace, `PQKem.kemRejKey sk ct` is attacker-known if and only
if both `sk` and `ct` are attacker-known. -/
theorem rejKey_attackerKnows_iff_of_reachable (tr : ExecTrace)
    (hreach : tr.Reachable reachability) (sk ct : Bytes) :
    (PQKem.kemRejKey sk ct).AttackerKnows tr ↔
      sk.AttackerKnows tr ∧ ct.AttackerKnows tr :=
  Symbolic.Proofs.Tests.Model.RejKeyNonDerivability.rejKey_attackerKnows_iff_of_reachable_proof tr hreach sk ct

/--
info: 'Symbolic.Tests.RejKeyNonDerivability.rejKey_attackerKnows_or_baseExposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejKey_attackerKnows_or_baseExposed

/--
info: 'Symbolic.Tests.RejKeyNonDerivability.rejKey_attackerKnows_iff_of_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rejKey_attackerKnows_iff_of_reachable

end Symbolic.Tests.RejKeyNonDerivability
