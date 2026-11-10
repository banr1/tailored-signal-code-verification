/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Specifications.Pqxdh.Security.CostedBudgets

/-!
# Program-Size Bounds in Headline Reduction Predicates

**Checked by Lean.** Step cost charges a branch only its costlier arm, so step cost alone does not
bound the size of an existentially quantified reduction. This module checks that
`ReductionDsl.reductionSizeBudget = 2 ^ 24` and that `GRedBounded`, `GRed2Bounded`,
`GRedBlockBounded`, and `GRed2BlockBounded` each bound `R.size` by `reductionSizeBudget` plus a
logarithmic term in the step-cost budget.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.SizeBudget

open OracleSpec OracleComp

theorem reductionSizeBudget_eq : ReductionDsl.reductionSizeBudget = 2 ^ 24 := rfl

theorem size_le_of_GRedBounded {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut out : ReductionDsl.Ty S}
    (R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) (q qOut costBudget : ℕ)
    (h : CryptoVerification.LibsignalSession.GRedBounded R wTag wSamp q qOut costBudget) :
    R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget :=
  h.2.1

theorem size_le_of_GRed2Bounded {S : ReductionDsl.Sig}
    {O : ReductionDsl.Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec S G} {rIn aIn aOut ch rIn2 out : ReductionDsl.Ty S}
    (R : ReductionDsl.TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) (q qOut costBudget : ℕ) (dflt : aOut.denote)
    (h : CryptoVerification.E2E.GRed2Bounded R wTag wSamp q qOut costBudget dflt) :
    R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget :=
  h.2.1

theorem size_le_of_GRedBlockBounded {ι κ : Type} {T : OracleSpec ι}
    {I : ReductionDsl.Iface SignalPqxdh.Costed.pqAtomicSig T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec SignalPqxdh.Costed.pqAtomicSig G}
    {rIn out : ReductionDsl.Ty SignalPqxdh.Costed.pqAtomicSig}
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (ℓ : ℕ)
    (R : ReductionDsl.CostedReduction SignalPqxdh.Costed.pqAtomicOps I G C rIn .unit .bool out)
    (h : SignalPqxdh.Security.GRedBlockBounded S b ℓ R) :
    R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits (SignalPqxdh.Security.stepCostBudget S b) :=
  h.1

theorem size_le_of_GRed2BlockBounded {ι κ : Type} {T : OracleSpec ι}
    {I : ReductionDsl.Iface SignalPqxdh.Costed.pqAtomicSig T} {G : OracleSpec κ}
    {C : ReductionDsl.GameCodec SignalPqxdh.Costed.pqAtomicSig G}
    {rIn ch rIn2 out : ReductionDsl.Ty SignalPqxdh.Costed.pqAtomicSig}
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (ℓ : ℕ)
    (R : ReductionDsl.TwoStageCostedReduction SignalPqxdh.Costed.pqAtomicOps I G C rIn .unit .bool
      ch rIn2 out)
    (h : SignalPqxdh.Security.GRed2BlockBounded S b ℓ R) :
    R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits (SignalPqxdh.Security.stepCostBudget S b) :=
  h.1

end CryptoVerification.E2E.Guards.SizeBudget
