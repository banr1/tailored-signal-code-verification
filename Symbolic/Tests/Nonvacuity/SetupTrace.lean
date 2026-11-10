/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ModelTraces
import Symbolic.Proofs.Tests.SetupTrace

/-!
# Initial PKI and Prekey Provisioning Trace

Defines `keySetupTrace`, the 22-entry baseline trace registering Alice's and Bob's identities and
Bob's signed X25519 and Kyber-1024 prekeys (`withOpk = false`), and states `setupTrace_reachable`
for arbitrary `Refinement.ProtocolSetup`. Proofs live in `Symbolic.Proofs.Tests.SetupTrace`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.Nonvacuity

open DY
open DY.Libsignal.Composed

/-- Concrete 22-entry key-provisioning trace for `"alice"` and `"bob"` with `withOpk = false`,
equal to `Refinement.setupTrace r` whenever `r.alice = "alice"`, `r.bob = "bob"`, and
`r.withOpk = false`. -/
def keySetupTrace : ExecTrace :=
  ((Refinement.setupAct "alice" "bob" false).run Trace.nil).2.val

theorem setupTrace_reachable (r : Refinement.ProtocolSetup) :
    (Refinement.setupTrace r).Reachable reachability :=
  Symbolic.Proofs.Tests.SetupTrace.setupTrace_reachable_proof r

end Symbolic.Tests.Nonvacuity
