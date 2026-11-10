/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Spec
import CaseStudies.Hashbrown

/-!
# `hashbrown` v0.17.1 End-to-End Theorems (`CaseStudies.Hashbrown.Theorems`)

Role: `Role::Theorems` (trusted end-to-end theorem layer). Discharges the top-level whole-binary
CLI statement from [`CaseStudies/Hashbrown/Spec/Top.lean`](../Spec/Top.lean):

- `hashbrownCliUniversal_ok` (proved in `CaseStudies.Hashbrown.Proofs.CliProof`): for every
  `inputs : ProcessInputs` satisfying `inputs.Valid` and `HashbrownStdinBudget inputs`, the static
  AArch64 safe-Rust `std` + stock `musl` `mallocng` binary `hashbrown_cli.elf` runs from `_start` to
  `SYS_exit_group` with zero hooks or overrides (`oom := fun _ _ => False`) and satisfies
  `HashbrownCliPost inputs.stdin`.
-/

namespace CaseStudies.Hashbrown.Theorems

/-- Headline whole-binary ELF process theorem for `hashbrown_cli.elf` (`CaseStudies/Hashbrown/Spec/Top.lean`). -/
theorem hashbrownCliUniversal_ok : _root_.CaseStudies.Hashbrown.HashbrownCliUniversalStmt :=
  _root_.CaseStudies.Hashbrown.hashbrownCliUniversal_ok

end CaseStudies.Hashbrown.Theorems
