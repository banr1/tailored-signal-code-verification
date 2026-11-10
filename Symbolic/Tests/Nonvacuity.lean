/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Tests.Nonvacuity.SetupTrace
public import Symbolic.Tests.Nonvacuity.HonestHandshakeWithoutOpk
public import Symbolic.Tests.Nonvacuity.HonestHandshakeWithOpk
public import Symbolic.Tests.Nonvacuity.HonestSession
public import Symbolic.Tests.Nonvacuity.ExposedSession
import Symbolic.Proofs.Tests.Nonvacuity

/-!
# Model-Level Reachability of Example Protocol Traces

States `nonvacuity_examples_reachable`: the five example protocol traces in
`Symbolic/Tests/Nonvacuity/` and `Refinement.setupTrace r` are reachable under
`DY.Libsignal.Composed.reachability` (see `Symbolic.Tests.CliNonvacuity` for CLI-level
reachability). Proofs live in `Symbolic.Proofs.Tests.Nonvacuity`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.Nonvacuity

open DY.Libsignal.Composed

/-- Each of the five example protocol traces and every `Refinement.setupTrace r` is reachable under
`DY.Libsignal.Composed.reachability`. -/
theorem nonvacuity_examples_reachable :
    keySetupTrace.Reachable reachability ∧
    honestHandshakeWithoutOpkTrace.Reachable reachability ∧
    honestHandshakeWithOpkTrace.Reachable reachability ∧
    honestSessionTrace.Reachable reachability ∧
    exposedSessionTrace.Reachable reachability ∧
    (∀ r : Refinement.ProtocolSetup, (Refinement.setupTrace r).Reachable reachability) :=
  Symbolic.Proofs.Tests.Nonvacuity.nonvacuity_examples_reachable_proof

end Symbolic.Tests.Nonvacuity
