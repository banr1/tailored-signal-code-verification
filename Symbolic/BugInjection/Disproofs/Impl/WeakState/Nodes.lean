/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge
public import GeneratedLean.BugInjectionMutant
-- `#guard` evaluates at compile time, so it needs the mutant's constants at the meta stage too.
public meta import GeneratedLean.BugInjectionMutant

/-!
Machine-free specification half (`spec_half_pinned`) of the `cheval26-weak-state` security
disproof for the `Cheval26WeakStateIdx1Cli` witness. The placed implementation half is in
`Symbolic.BugInjection.Disproofs.Impl.WeakState.NodesPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.Nodes

open Symbolic.BugInjection (cliCompShape)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (cliCompFitsPinned)

#guard CryptoVerification.BugInjection.mutant == "cheval26-weak-state"

/-- No symbolic execution explains the `Cheval26WeakStateIdx1Cli` trace under any interpretation
and setup records admitted by `cliCompFitsPinned setup`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup)
      Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace :=
  Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge.spec_half_pinned

end Symbolic.BugInjection.Disproofs.Impl.WeakState.Nodes
