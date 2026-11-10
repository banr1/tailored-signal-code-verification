/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCost
public import Computational.Specifications.Pqxdh.Security.Auth.Headline

/-!
# Cost, Query, Block, and Per-Kind Bounds for One-Key Auth `gdh`

Exports the `gdh` cost, query (`sig`, `ddh`, `prim`), block-size, and per-query-kind step-cost
bounds for `(pqxdhAuth1KeyKindCostedSims S).gdh` at the `Auth1KeyCostedReductionBounds` field
signatures from `AuthGapDhKCost`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindGdhBounds

public section

set_option autoImplicit false

open _root_.SignalPqxdh (Setup QueryBudget)
open _root_.SignalPqxdh.Security (stepCostBudget stepCostBudgetSplit primQueryBudget
  GRedBlockBounded authQueryKind authKindCounts
  authChalIfaceSigQueryWeight authChalIfaceDdhQueryWeight authChalIfacePrimQueryWeight
  samplerZeroQueryWeight)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs (
  pqxdhAuth1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKCost (
  a1g2KindProg_totalCost_le_stepCostBudget a1g2KindProg_totalSigQueries_le
  a1g2KindProg_totalDdhQueries_le a1g2KindProg_totalPrimQueries_le
  a1g2KindProg_blockBounded a1g2KindProg_costBoundedByKind)

theorem auth1KeyKindGdh_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    ((pqxdhAuth1KeyKindCostedSims S).gdh b).totalCost b.q_total ≤ stepCostBudget S b :=
  a1g2KindProg_totalCost_le_stepCostBudget S b

theorem auth1KeyKindGdh_q_sig (S : Setup) (b : QueryBudget) :
    ((pqxdhAuth1KeyKindCostedSims S).gdh b).totalQueries
      authChalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total :=
  a1g2KindProg_totalSigQueries_le S b

theorem auth1KeyKindGdh_q_ddh (S : Setup) (b : QueryBudget) :
    ((pqxdhAuth1KeyKindCostedSims S).gdh b).totalQueries
      authChalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  a1g2KindProg_totalDdhQueries_le S b

theorem auth1KeyKindGdh_q_prim (S : Setup) (b : QueryBudget) :
    ((pqxdhAuth1KeyKindCostedSims S).gdh b).totalQueries
      authChalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b :=
  a1g2KindProg_totalPrimQueries_le S b

theorem auth1KeyKindGdh_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ ((pqxdhAuth1KeyKindCostedSims S).gdh b) :=
  a1g2KindProg_blockBounded S b ℓ

theorem auth1KeyKindGdh_costByKind (S : Setup) (b : QueryBudget) :
    ((pqxdhAuth1KeyKindCostedSims S).gdh b).CostBoundedByKind authQueryKind (authKindCounts b)
      (stepCostBudgetSplit S b (b.q_ro + b.q_roRoot)) :=
  a1g2KindProg_costBoundedByKind S b

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindGdhBounds
