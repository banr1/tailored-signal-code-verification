/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# Lookup-Tree Random-Oracle Step-Cost Budget Helpers

Step-cost multiplier and per-operation budget helper for persistent AVL random-oracle
lookup-or-insert tables, matching the `2 ^ 13 * (bits (...) + 4)` slice in
`SignalPqxdh.Security.stepCostBudgetSplit`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget

open _root_.ReductionDsl (bits)

/-- Per-level step-cost multiplier `2 ^ 13` matching the random-oracle lookup-tree slice in
`SignalPqxdh.Security.stepCostBudgetSplit`. -/
@[expose] def roTableKappa : ℕ := 2 ^ 13

/-- Step-cost budget `κ * (bits q + 4)` for a single persistent AVL random-oracle lookup-or-insert
on a table of capacity `q`. -/
@[expose] def roTableStepCost (κ q : ℕ) : ℕ :=
  κ * (bits q + 4)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget
