/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.CostedBudgets

/-!
# Reduction bundles for the one-key PQXDH headline statement

**Trusted: the statement.** This file defines the one-key `KeyInd` reduction bundles and boundedness
predicates used by `PqxdhCorrectAndSecureδ` (`HeadlineDelta.lean`) and the CLI security statements
(`Computational/Specifications/LibsignalCli/StatementPqElf.lean`). Companion one-key first-message
`Auth` reduction bundles are in `Auth/Headline.lean`. See `Computational/docs/TRUSTED_BASE.md`.

For each query budget `b` and `b`-bounded game adversary `A`, a reduction family packages the
adversaries against `GapSigEufCma`, `KemShCr`, and `GapDhWithSign` constructed from `A` for the
one-key random-oracle PQXDH handshake game (`KeyInd1KeyRo.lean`). Each reduction is represented as a
first-order `ReductionDsl` syntax tree (`CostedReduction` or `TwoStageCostedReduction`) over the
pure operation table `pqAtomicOps` and coin-only sampler table `pqAtomicSamplers`, so step cost,
output block sizes, and worst-case query counts are checked syntactically.

The two-stage `KemShCr` reduction runs both stages with `fuel := b.q_total`; because a `b`-bounded
adversary makes at most `b.q_total` game queries in total, fuel is never exhausted and the fallback
return value is unreachable. Syntactic bounds (`KeyIndCostedReductionBounds`) check both the uniform
`stepCostBudget S b` over `b.q_total` handled queries and the online/random-oracle split budget
`stepCostBudgetSplit S b b.q_ro` via `CostBoundedByKind`, while semantic compliance
(`KeyIndReductionQueryBounds`) enforces the sharper dynamic caps
`q_sig = 2 * min S.N_spk_tot S.N_recv` and `q_ddh = gdhQueryBudget S b` declared by
`KeyIndCostedReductionFamily.eval`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

/-! ## Reduction bundles -/

/-- Shallow reduction family mapping each `b`-bounded `KeyIndAdversary S` to adversaries against
`GapSigEufCma` (`sig`), `KemShCr` (`shcr`), and `GapDhWithSign` (`gdh`). -/
structure KeyIndReductionFamily (S : Setup) where
  sig  : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapSigEufCmaAdv
  shcr : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → KemShCrAdv
  gdh  : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv

/-- Deep-embedded `ReductionDsl` syntax trees over `pqAtomicOps` and `pqKeyIndCodec S` for the
`GapSigEufCma` (`sig`), `KemShCr` (`shcr`), and `GapDhWithSign` (`gdh`) reductions. -/
structure KeyIndCostedReductionFamily (S : Setup) where
  sig  : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
           (PB 32) .unit .bool (.prod (PB 1569) (PB 64))
  shcr : QueryBudget → TwoStageCostedReduction pqAtomicOps pqPrimIface (keyIndSpec S) (pqKeyIndCodec S)
           (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
           (.prod (PB 32) (PB 1568)) (PB 1568)
  gdh  : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
           (.prod (PB 32) (PB 32)) .unit .bool (PB 32)

/-- Interpret a `KeyIndCostedReductionFamily` into a `KeyIndReductionFamily` at `fuel := b.q_total`
with fallback `false` for `shcr`. -/
def KeyIndCostedReductionFamily.eval {S : Setup} (R : KeyIndCostedReductionFamily S) :
    KeyIndReductionFamily S where
  sig b A :=
    { run := fun pk => (R.sig b).eval (fun _ => A.1.run) pk
      q_sig := 2 * min S.N_spk_tot S.N_recv
      q_ddh := gdhQueryBudget S b
      q_prim := gdhPrimQueryBudget S b }
  shcr b A :=
    { State := Mid (keyIndSpec S) Bool (R.shcr b).π.denote (R.shcr b).σ.denote (PB 1568).denote
      choosePk := fun pk sk =>
        (R.shcr b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
      findCollision := fun st ss ct =>
        (R.shcr b).eval2 st (ss, ct) b.q_total false
      q_prim := primQueryBudget S b }
  gdh b A :=
    { run := fun U V => (R.gdh b).eval (fun _ => A.1.run) (U, V)
      q_ddh := gdhQueryBudget S b
      q_sig := 2 * min S.N_spk_tot S.N_recv
      q_prim := gdhPrimQueryBudget S b }

/-! ## Cost, block-size, and query bounds -/

/-- Classifies `KeyIndQuery` into online queries (`0`, matching `isKeyIndOnlineQuery`) and offline
    `.roQuery` random-oracle queries (`1`) for per-kind step-cost accounting. -/
def keyIndQueryKind {S : Setup} : KeyIndQuery S → Fin 2
  | .roQuery _ => 1
  | _ => 0

/-- Per-kind query caps for a `b`-bounded `KeyIndAdversary`: `min b.q_on b.q_total` online queries
    (`0`) and `min b.q_ro b.q_total` random-oracle queries (`1`). -/
def keyIndKindCounts (b : QueryBudget) : Fin 2 → ℕ
  | 0 => min b.q_on b.q_total
  | 1 => min b.q_ro b.q_total

/-- Syntactic resource bounds for `R`: size-honesty of `pqAtomicOps` and `pqAtomicSamplers`, uniform
    (`stepCostBudget`) and online/random-oracle split (`stepCostBudgetSplit`) step-cost bounds,
    worst-case query bounds over `b.q_total` handled queries, and run-local output block-size bounds. -/
structure KeyIndCostedReductionBounds (S : Setup) (R : KeyIndCostedReductionFamily S) : Prop where
  ops_sizeHonest  : PqOpsSizeHonest pqAtomicOps
  samp_sizeHonest : PqSampSizeHonest pqAtomicSamplers
  sig_cost        : ∀ (b : QueryBudget), (R.sig b).totalCost b.q_total ≤ stepCostBudget S b
  shcr_cost       : ∀ (b : QueryBudget), (R.shcr b).totalCost b.q_total ≤ stepCostBudget S b
  gdh_cost        : ∀ (b : QueryBudget), (R.gdh b).totalCost b.q_total ≤ stepCostBudget S b
  sig_q_sig       : ∀ (b : QueryBudget),
    (R.sig b).totalQueries chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total
  sig_q_ddh       : ∀ (b : QueryBudget),
    (R.sig b).totalQueries chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  sig_q_prim      : ∀ (b : QueryBudget),
    (R.sig b).totalQueries chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  shcr_q_prim     : ∀ (b : QueryBudget),
    (R.shcr b).totalQueries primIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  gdh_q_sig       : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total
  gdh_q_ddh       : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
  gdh_q_prim      : ∀ (b : QueryBudget),
    (R.gdh b).totalQueries chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b
  sig_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.sig b)
  shcr_blocks     : ∀ (b : QueryBudget) (ℓ : Nat), GRed2BlockBounded S b ℓ (R.shcr b)
  gdh_blocks      : ∀ (b : QueryBudget) (ℓ : Nat), GRedBlockBounded S b ℓ (R.gdh b)
  sig_costByKind  : ∀ (b : QueryBudget),
    (R.sig b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
      (stepCostBudgetSplit S b b.q_ro)
  shcr_costByKind : ∀ (b : QueryBudget),
    (R.shcr b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
      (stepCostBudgetSplit S b b.q_ro)
  gdh_costByKind  : ∀ (b : QueryBudget),
    (R.gdh b).CostBoundedByKind keyIndQueryKind (keyIndKindCounts b)
      (stepCostBudgetSplit S b b.q_ro)

/-- Semantic query compliance of `R`: for every budget `b` and `b`-bounded adversary `A`, the
evaluated `sig`, `shcr`, and `gdh` adversaries satisfy their `.Bounded` query predicates. -/
structure KeyIndReductionQueryBounds (S : Setup) (R : KeyIndReductionFamily S) : Prop where
  sig_bounded  : ∀ b A, (R.sig b A).Bounded
  shcr_bounded : ∀ b A, (R.shcr b A).Bounded
  gdh_bounded  : ∀ b A, (R.gdh b A).Bounded

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (
  KeyIndReductionFamily KeyIndCostedReductionFamily KeyIndCostedReductionBounds
  KeyIndReductionQueryBounds stepCostBudget outputSizeBudget
)

end SignalPqxdh

namespace SignalPqxdh.Costed

export SignalPqxdh.Security (
  KeyIndReductionFamily KeyIndCostedReductionFamily KeyIndReductionQueryBounds
  KeyIndCostedReductionBounds
)

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

export SignalPqxdh.Security (
  KeyIndReductionFamily KeyIndCostedReductionFamily KeyIndReductionQueryBounds
  KeyIndCostedReductionBounds
)

end SignalPqxdh.Security.Costed
