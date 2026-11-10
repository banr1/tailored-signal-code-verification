/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable

/-!
# Definitional Equality of Placed and Reference CLI Hooks

Proves by kernel reduction that `CompHooks0Placed.compHooks0` equals
`CompFitsSatisfiable.compHooks0`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq

open ProofLib.ProgramReflection in
theorem compHooks0_placed_eq :
    Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.compHooks0 =
      Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.compHooks0 := by
  rfl_kernel

end Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq
