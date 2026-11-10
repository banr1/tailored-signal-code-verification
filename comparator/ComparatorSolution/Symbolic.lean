/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Theorems.ModelSecurity
public import Symbolic.Theorems.RefinementPreservation
public import Symbolic.Theorems.Refinement
public import Symbolic.Theorems.Security

/-!
# Comparator solution module of the symbolic headlines

`solution_module` of `comparator/symbolic.json`: imports every theorem file in `Symbolic/Theorems/`
and declares nothing, so comparator checks the theorems (and their proofs) as they are. See
`comparator/README.md`.
-/
