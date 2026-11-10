/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

/-!
# Step-cost and block-size budgets for the PQXDH reductions

**Trusted: definitions used by the statement.**

Explicit polynomial resource budgets, size-honesty predicates, and oracle query weights for the
deep-embedded `ReductionDsl` PQXDH reductions (`KeyInd` and `Auth`) over `pqAtomicOps` and
`pqAtomicSamplers`.

In `stepCostBudget S b`, dynamic DH-key and session tables start empty and grow by at most one
entry per game query, so their sizes are bounded by `M_dh = min q_total N_dh` and
`M_sess = min q_total N_sess_tot`. Each of the at most `q_total` game queries incurs `O(q_total)`
work for random-oracle and adversarial-key scans, `O(M_dh + M_sess)` for key and session scans,
and `O(⌊log₂ N_dh⌋ + ⌊log₂ N_sess_tot⌋)` for `Ty.tbl` index arithmetic; final extraction adds a
one-shot `O(M_dh² + M_dh · M_sess)` pass.

In `stepCostBudgetSplit S b q_off`, online queries (`M_on = min q_on q_total`) and offline
random-oracle queries (`M_off = min q_off q_total`) are accounted separately via
`CostBoundedByKind`: only online queries allocate keys and sessions (clamping `M_dh` and `M_sess`
against `M_on`), while random-oracle lookups and bilinear random-oracle-by-session consistency
checks (`O(M_off · M_on)`) are charged on their own terms. Because neither budget dominates the
other across all `b`, the headline reduction bundles state both bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open _root_.ReductionDsl
open OracleSpec OracleComp
open SignalPqxdh.Costed

/-- Polynomial syntactic step-cost budget for `CostedReduction.totalCost` and
    `TwoStageCostedReduction.totalCost` across all PQXDH reductions. -/
def stepCostBudget (S : Setup) (b : QueryBudget) : Nat :=
  let M_dh := min b.q_total S.N_dh
  let M_sess := min b.q_total S.N_sess_tot
  2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
    2 ^ 15 * (b.q_total + 1) * (M_dh + M_sess) +
    2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
    2 ^ 11 * M_dh ^ 2 + 2 ^ 8 * M_dh * M_sess

/-- Polynomial block-, bit-, and list-size budget for reduction outputs when challenge inputs,
    encoded game queries, and target answers fit in `ℓ` blocks. -/
def outputSizeBudget (S : Setup) (b : QueryBudget) (ℓ : Nat) : Nat :=
  2 * stepCostBudget S b * (ℓ + 1) + 2 * (b.q_total + 1) * ℓ

/-- Per-kind syntactic step-cost budget for `totalCostByKind` when the adversary makes at most
    `M_on = min b.q_on b.q_total` online queries and `M_off = min q_off b.q_total` offline
    random-oracle queries (`q_off = b.q_ro` for `KeyInd`, `b.q_ro + b.q_roRoot` for `Auth`).
    Because only online queries create keys and sessions, `M_dh` and `M_sess` clamp against `M_on`,
    while random-oracle lookups over at most `M_off + 2 * M_on + 1` entries and bilinear
    random-oracle-by-session consistency checks (`2 ^ 13 * M_off * M_on`) are charged separately.
    The lookup term is sized for a balanced lookup tree with `O(bits K)` lookup plus insert,
    `K = M_off + 2 * M_on + 1`. The current proofs use an AVL table (proof side, ported from #1283);
    in the `Auth` CPA, PRF and SHCR reductions each offline query costs at most
    `4420 * bits K + 1750`, and `avl_split_budget_le` (`avl_split_budget_twoStage_le` for SHCR)
    bounds the offline steps plus the online table syncs by the lookup term up to an `O(M_on ^ 2)`
    remainder (`Proofs/SignalPqxdh/Security/ReductionDsl/KindSplit/AuthCoreKCostBase.lean`). -/
def stepCostBudgetSplit (S : Setup) (b : QueryBudget) (q_off : Nat) : Nat :=
  let M_on := min b.q_on b.q_total
  let M_off := min q_off b.q_total
  let M_dh := min M_on S.N_dh
  let M_sess := min M_on S.N_sess_tot
  2 ^ 16 * (M_on + 1) * (M_on + 1) +
    2 ^ 15 * (M_on + 1) * (M_dh + M_sess) +
    2 ^ 10 * (M_on + M_off + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
    2 ^ 13 * (M_off + M_on) * (bits (M_off + 2 * M_on + 1) + 4) +
    2 ^ 13 * M_off * M_on +
    2 ^ 11 * M_dh ^ 2 + 2 ^ 8 * M_dh * M_sess

export _root_.ReductionDsl (ValFits)

/-- Operator size-honesty: every operator `o` in `O` increases the `ValFits` size bound by at most
    its declared cost `O.cost o`. -/
abbrev PqOpsSizeHonest {S : Sig}
    (O : Ops S) : Prop :=
  ∀ (o : O.Op) (x : (O.dom o).denote) (B : ℕ),
    ValFits B (O.dom o) x → ValFits (B + O.cost o) (O.cod o) (O.eval o x)

/-- Sampler size-honesty: every output in the support of `X.samp s x` increases the `ValFits` size
    bound by at most `X.sCost s`. -/
abbrev PqSampSizeHonest {S : Sig} (X : Samplers S) : Prop :=
  ∀ (s : X.Samp) (x : (X.sDom s).denote) (B : ℕ),
    ValFits B (X.sDom s) x →
    ∀ y ∈ support (X.samp s x), ValFits (B + X.sCost s) (X.sTy s) y

/-- Program-size and run-local output-size bound for a one-stage reduction `R`: bounds `R.size`
    and requires every output to fit in `outputSizeBudget S b ℓ` whenever the challenge input, all
    at most `b.q_total` adversary game queries, and all target answers on the run fit in `ℓ`. -/
def GRedBlockBounded {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ} {C : GameCodec pqAtomicSig G}
    {rIn out : Ty pqAtomicSig}
    (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqAtomicOps I G C rIn .unit .bool out) : Prop :=
  R.size ≤ reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) ∧ (
  ∀ (A : Unit → OracleComp (unifSpec + G) Bool),
    (∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total) →
    (∀ u, AllGameQueriesFit ℓ C (A u)) →
    ∀ (x : rIn.denote), ValFits ℓ rIn x →
      ∀ y ∈ supportWhen (I.AnswerFits ℓ) (R.eval A x), ValFits (outputSizeBudget S b ℓ) out y)

/-- Program-size and run-local output-size bound for a two-stage reduction `R`: bounds `R.size`
    and requires both the first-stage challenge request and the second-stage output to fit in
    `outputSizeBudget S b ℓ` whenever inputs, adversary game queries, and target answers on the run
    fit in `ℓ`. -/
def GRed2BlockBounded {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ} {C : GameCodec pqAtomicSig G}
    {rIn ch rIn2 out : Ty pqAtomicSig}
    (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : TwoStageCostedReduction pqAtomicOps I G C rIn .unit .bool ch rIn2 out) : Prop :=
  R.size ≤ reductionSizeBudget + 2 ^ 12 * bits (stepCostBudget S b) ∧ (
  ∀ (A : Unit → OracleComp (unifSpec + G) Bool),
    (∀ u, AllGameQueriesFit ℓ C (A u)) →
    ∀ (x : rIn.denote), ValFits ℓ rIn x →
    ∀ cm ∈ supportWhen (I.AnswerFits ℓ) (R.eval1 A x b.q_total false),
      ValFits (outputSizeBudget S b ℓ) ch cm.1 ∧
      ∀ (y : rIn2.denote), ValFits ℓ rIn2 y →
        ∀ z ∈ supportWhen (I.AnswerFits ℓ) (R.eval2 cm.2 y b.q_total false),
          ValFits (outputSizeBudget S b ℓ) out z)

/-- Unit primitive-query weight on `pqPrimIface`. -/
def primIfacePrimQueryWeight : PTag → ℕ := fun _ => 1

/-- Primitive-query weight on `PTag ⊕ ChalTag` (1 on `PTag`, 0 on `ChalTag`). -/
def chalIfacePrimQueryWeight {ChalTag : Type} : PTag ⊕ ChalTag → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Signing-query weight on `pqSigAndDdhIface` (1 on `.inr (.inl _)`, 0 otherwise). -/
def chalIfaceSigQueryWeight : PTag ⊕ (ℕ+ ⊕ Unit) → ℕ
  | .inr (.inl _) => 1
  | _ => 0

/-- DDH-query weight on `pqSigAndDdhIface` (1 on `.inr (.inr ())`, 0 otherwise). -/
def chalIfaceDdhQueryWeight : PTag ⊕ (ℕ+ ⊕ Unit) → ℕ
  | .inr (.inr ()) => 1
  | _ => 0

/-- Zero query weight on pure coin samplers. -/
def samplerZeroQueryWeight {Samp : Type} : Samp → ℕ := fun _ => 0

end SignalPqxdh.Security

namespace SignalPqxdh.Costed

export SignalPqxdh.Security (
  stepCostBudget outputSizeBudget stepCostBudgetSplit ValFits PqOpsSizeHonest PqSampSizeHonest
  GRedBlockBounded GRed2BlockBounded
  primIfacePrimQueryWeight chalIfacePrimQueryWeight chalIfaceSigQueryWeight
  chalIfaceDdhQueryWeight samplerZeroQueryWeight
)

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

export SignalPqxdh.Security (
  stepCostBudget outputSizeBudget stepCostBudgetSplit ValFits PqOpsSizeHonest PqSampSizeHonest
  GRedBlockBounded GRed2BlockBounded
  primIfacePrimQueryWeight chalIfacePrimQueryWeight chalIfaceSigQueryWeight
  chalIfaceDdhQueryWeight samplerZeroQueryWeight
)

end SignalPqxdh.Security.Costed
