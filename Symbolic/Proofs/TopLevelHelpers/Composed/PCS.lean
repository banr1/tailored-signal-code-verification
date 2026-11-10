/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import Symbolic.Proofs.Swarm.COMPOSED.CompPcsTop

/-!
# Whole-Protocol Post-Compromise Security

Re-exports whole-protocol post-compromise security (`Security.PostCompromiseSecurity`) for
`Symbolic.Theorems.Composed.ComposedPCS`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.PCS

open DY.Libsignal.Composed

/-- Post-compromise security of the whole protocol. -/
theorem post_compromise_security : Security.PostCompromiseSecurity :=
  Symbolic.Swarm.COMPOSED.CompRatchet.post_compromise_security

end Symbolic.Proofs.TopLevelHelpers.Composed.PCS
