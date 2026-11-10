/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs

/-!
# Closed-Form Cost Budgets for E2E Reductions

Defines concrete step-cost budgets for the binary-harness adapter (`e2eAdapterCostBudget`) and
end-to-end composition reductions (`e2eCompositionCostBudget`, `bhE2ECostBudgetHonest`), proves
dominance relations and modular `totalCost` / `GRed2Bounded` constructors, and checks numerical
bounds at `SignalPqxdh.deploymentSetup`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.LeafCostBounds

open Nat
open OracleSpec OracleComp
open ReductionDsl (Sig Ty Ops Samplers Iface GameCodec CostedReduction TwoStageCostedReduction
  OpsSizeHonest SampSizeHonest bits reductionSizeBudget)
open CryptoVerification.LibsignalSession (CostedFits CostedOpsSizeHonest CostedSampSizeHonest
  GRedBounded)
open CryptoGames.LibsignalSession (maxForwardJumps)
open CryptoVerification.E2E (GRed2Bounded)
open CryptoVerification.E2E.Costed (e2eSig prefixCtxT costedFits_iff_fits
  costedOpsSizeHonest_of_opsSizeHonest costedSampSizeHonest_of_sampSizeHonest
  gRedBounded_of_bounds)

/-! ## Closed-form step-cost budgets -/

/-- Closed-form step-cost budget for the binary-harness to model-state adapter. -/
def e2eAdapterCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 8 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

abbrev bhAdapterCostBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  e2eAdapterCostBudget S b qStart qDR ℓ

/-- Pre-block-cost adapter step-cost budget covering `E2EPureOp.pbytesEq 1568 1568` unconditionally. -/
def e2eAdapterCostBudgetPreBlock (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 8 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

/-- Uniform-coefficient adapter step-cost budget with leading factor `2 ^ 12`. -/
def e2eAdapterCostBudgetUniform12 (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 12 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 8)

/-- Conservative upper adapter step-cost envelope with leading factor `2 ^ 17`. -/
def m0AdapterCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 17 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 16)

/-- Closed-form step-cost budget for the end-to-end composition reductions (`kindRed` and `prefixRed`). -/
def e2eCompositionCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 12 * (b.q_total + qStart + qDR + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Honest end-to-end composition step-cost budget covering multi-arm handshake, session-start, and
one-shot `finishPrefixCost` overhead. -/
def bhE2ECostBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 15 * (b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Linear-in-`qDR` variant of `e2eCompositionCostBudget` for `O(1)` per-epoch table lookup. -/
def e2eCompositionCostBudgetLinearSm (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 12 * (b.q_total + qStart + qDR + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + qDR + qep + ℓ + 2 ^ 12)

/-- Conservative upper composition step-cost envelope with leading factor `2 ^ 24`. -/
def m0CompositionCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 24 * (b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-! ## Budget monotonicity and dominance -/

theorem e2eAdapterCostBudget_le_m0AdapterCostBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    e2eAdapterCostBudget S b qStart qDR ℓ ≤ m0AdapterCostBudget S b qStart qDR ℓ := by
  unfold e2eAdapterCostBudget m0AdapterCostBudget
  refine Nat.mul_le_mul ?_ (by omega)
  exact Nat.mul_le_mul_right _ (by decide)

theorem e2eAdapterCostBudgetPreBlock_le_uniform12 (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ ≤
      e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ := by
  unfold e2eAdapterCostBudgetPreBlock e2eAdapterCostBudgetUniform12
  have hEq :
      2 ^ 12 * (b.q_total + qStart + qDR + 1) *
        (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 8) =
      2 ^ 8 * (b.q_total + qStart + qDR + 1) *
        (16 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 8)) := by
    ring
  rw [hEq]
  exact Nat.mul_le_mul_left _ (by omega)

theorem e2eAdapterCostBudgetUniform12_le_m0AdapterCostBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ ≤ m0AdapterCostBudget S b qStart qDR ℓ := by
  unfold e2eAdapterCostBudgetUniform12 m0AdapterCostBudget
  refine Nat.mul_le_mul ?_ (by omega)
  exact Nat.mul_le_mul_right _ (by decide)

theorem e2eCompositionCostBudget_le_bhE2ECostBudgetHonest (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ) :
    e2eCompositionCostBudget S b qStart qDR qep ℓ ≤
      bhE2ECostBudgetHonest S b qStart qDR qep ℓ := by
  unfold e2eCompositionCostBudget bhE2ECostBudgetHonest
  refine Nat.mul_le_mul ?_ le_rfl
  exact Nat.mul_le_mul (by decide) (by omega)

theorem bhE2ECostBudgetHonest_le_m0CompositionCostBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ) :
    bhE2ECostBudgetHonest S b qStart qDR qep ℓ ≤
      m0CompositionCostBudget S b qStart qDR qep ℓ := by
  unfold bhE2ECostBudgetHonest m0CompositionCostBudget
  refine Nat.mul_le_mul ?_ le_rfl
  exact Nat.mul_le_mul_right _ (by decide)

theorem e2eCompositionCostBudget_le_m0CompositionCostBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ) :
    e2eCompositionCostBudget S b qStart qDR qep ℓ ≤
      m0CompositionCostBudget S b qStart qDR qep ℓ :=
  le_trans (e2eCompositionCostBudget_le_bhE2ECostBudgetHonest S b qStart qDR qep ℓ)
    (bhE2ECostBudgetHonest_le_m0CompositionCostBudget S b qStart qDR qep ℓ)

theorem e2eAdapterCostBudget_mono (S : SignalPqxdh.Setup)
    {b₁ b₂ : SignalPqxdh.QueryBudget} {qStart₁ qStart₂ qDR₁ qDR₂ ℓ₁ ℓ₂ : ℕ}
    (hq : b₁.q_total ≤ b₂.q_total) (hs : qStart₁ ≤ qStart₂)
    (hd : qDR₁ ≤ qDR₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    e2eAdapterCostBudget S b₁ qStart₁ qDR₁ ℓ₁ ≤
      e2eAdapterCostBudget S b₂ qStart₂ qDR₂ ℓ₂ := by
  unfold e2eAdapterCostBudget
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

theorem e2eCompositionCostBudget_mono (S : SignalPqxdh.Setup)
    {b₁ b₂ : SignalPqxdh.QueryBudget}
    {qStart₁ qStart₂ qDR₁ qDR₂ qep₁ qep₂ ℓ₁ ℓ₂ : ℕ}
    (hq : b₁.q_total ≤ b₂.q_total) (hs : qStart₁ ≤ qStart₂)
    (hd : qDR₁ ≤ qDR₂) (hep : qep₁ ≤ qep₂) (hℓ : ℓ₁ ≤ ℓ₂) :
    e2eCompositionCostBudget S b₁ qStart₁ qDR₁ qep₁ ℓ₁ ≤
      e2eCompositionCostBudget S b₂ qStart₂ qDR₂ qep₂ ℓ₂ := by
  unfold e2eCompositionCostBudget
  have hprod : (qDR₁ + 1) * (qDR₁ + qep₁ + ℓ₁ + 1) ≤ (qDR₂ + 1) * (qDR₂ + qep₂ + ℓ₂ + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-! ## Modular `totalCost` and `GRed2Bounded` constructors -/

/-- Upper-bounds `CostedReduction.totalCost` from component bounds on `init`, `uCost`, `handle`, and `finish`. -/
theorem totalCost_le_of_parts {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    {q initB stepB finB : ℕ}
    (hInit : R.init.cost ≤ initB)
    (hU : I.uCost ≤ stepB)
    (hStep : R.handle.cost + C.codecCost ≤ stepB)
    (hFin : R.finish.cost ≤ finB) :
    R.totalCost q ≤ initB + q * stepB + finB := by
  dsimp only [CostedReduction.totalCost]
  have hMax : max I.uCost (R.handle.cost + C.codecCost) ≤ stepB := max_le hU hStep
  have hMul : q * max I.uCost (R.handle.cost + C.codecCost) ≤ q * stepB :=
    Nat.mul_le_mul_left q hMax
  omega

/-- Upper-bounds `TwoStageCostedReduction.totalCost` from separate bounds on each stage component. -/
theorem twoStage_totalCost_le_of_parts {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {q initB stepB midB finB : ℕ}
    (hInit : R.init.cost ≤ initB)
    (hU : I.uCost ≤ stepB)
    (hPre : R.handlePre.cost + C.codecCost ≤ stepB)
    (hPost : R.handlePost.cost + C.codecCost ≤ stepB)
    (hCh : R.chDone.cost ≤ midB)
    (hRes : R.resume.cost ≤ midB)
    (hFin : R.finish.cost ≤ finB) :
    R.totalCost q ≤ initB + q * stepB + midB + finB := by
  dsimp only [TwoStageCostedReduction.totalCost]
  have hMaxH : max R.handlePre.cost R.handlePost.cost + C.codecCost ≤ stepB := by omega
  have hMaxU : max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) ≤ stepB :=
    max_le hU hMaxH
  have hMul : q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) ≤ q * stepB :=
    Nat.mul_le_mul_left q hMaxU
  have hMid : max R.chDone.cost R.resume.cost ≤ midB := max_le hCh hRes
  omega

theorem fits_prefixCtxT_two {ℓ : ℕ} (c : (prefixCtxT (ℓ := ℓ)).denote) :
    CostedFits 2 (prefixCtxT (ℓ := ℓ)) c := by
  rw [costedFits_iff_fits]
  simp [Ty.Fits, CryptoVerification.E2E.Costed.E2ESort.blocks]

theorem fits_bool_two {S0 : Sig} (b : (Ty.bool (S := S0)).denote) :
    CostedFits 2 (Ty.bool (S := S0)) b := by
  rw [costedFits_iff_fits]
  simp [Ty.Fits]

/-- Constructs `GRed2Bounded` when challenge `ch` and output `out` have fixed block width at most `2`. -/
theorem gRed2Bounded_of_fixed_ch_out {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ) (dflt : aOut.denote)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hStage1Q :
      R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp + R.chDone.queries wTag wSamp = 0)
    (hQueries : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp)
    (hCh : ∀ c : ch.denote, CostedFits 2 ch c)
    (hOut : ∀ z : out.denote, CostedFits 2 out z) :
    GRed2Bounded R wTag wSamp q qOut costBudget dflt := by
  refine ⟨hCost, hSize, hStage1Q, hQueries, costedOpsSizeHonest_of_opsSizeHonest hO,
    costedSampSizeHonest_of_sampSizeHonest hS, fun B _ A _ x _ => ?_⟩
  intro widthB cm _
  have hTwoLe : 2 ≤ widthB := by
    dsimp only [widthB]
    have h1 : 2 ≤ 2 * (costBudget + q + 1) := by omega
    have h2 : 1 ≤ B + 1 := by omega
    exact Nat.mul_le_mul h1 h2
  refine ⟨?_, fun _ _ z _ => ?_⟩
  · exact (costedFits_iff_fits widthB ch cm.1).2
      (Ty.fits_mono hTwoLe ch cm.1 ((costedFits_iff_fits 2 ch cm.1).1 (hCh cm.1)))
  · exact (costedFits_iff_fits widthB out z).2
      (Ty.fits_mono hTwoLe out z ((costedFits_iff_fits 2 out z).1 (hOut z)))

/-! ## Leaf-sum inequalities -/

/-- Per-step linear capacity of `e2eAdapterCostBudget`. -/
def adapterPerStepBudget (S : SignalPqxdh.Setup) (qStart ℓ : ℕ) : ℕ :=
  2 ^ 8 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

def adapterPerStepBudgetPreBlock (S : SignalPqxdh.Setup) (qStart ℓ : ℕ) : ℕ :=
  2 ^ 8 * (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

theorem totalCost_le_e2eAdapterCostBudgetPreBlock_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ)
    (hInitFin : R.init.cost + R.finish.cost ≤ adapterPerStepBudgetPreBlock S qStart ℓ)
    (hU : I.uCost ≤ adapterPerStepBudgetPreBlock S qStart ℓ)
    (hStep : R.handle.cost + C.codecCost ≤ adapterPerStepBudgetPreBlock S qStart ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ := by
  have hParts := totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := adapterPerStepBudgetPreBlock S qStart ℓ)
    (finB := R.finish.cost) le_rfl hU hStep le_rfl
  unfold e2eAdapterCostBudgetPreBlock adapterPerStepBudgetPreBlock at *
  have hEq :
      2 ^ 8 * (b.q_total + qStart + qDR + 1) *
        (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) =
      (b.q_total + qStart + qDR) *
        (2 ^ 8 * (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)) +
      2 ^ 8 * (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) := by
    ring
  omega

theorem totalCost_le_e2eAdapterCostBudget_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ)
    (hInitFin : R.init.cost + R.finish.cost ≤ adapterPerStepBudget S qStart ℓ)
    (hU : I.uCost ≤ adapterPerStepBudget S qStart ℓ)
    (hStep : R.handle.cost + C.codecCost ≤ adapterPerStepBudget S qStart ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ e2eAdapterCostBudget S b qStart qDR ℓ := by
  have hParts := totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := adapterPerStepBudget S qStart ℓ) (finB := R.finish.cost)
    le_rfl hU hStep le_rfl
  unfold e2eAdapterCostBudget adapterPerStepBudget at *
  have hEq :
      2 ^ 8 * (b.q_total + qStart + qDR + 1) *
        (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) =
      (b.q_total + qStart + qDR) *
        (2 ^ 8 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)) +
      2 ^ 8 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) := by
    ring
  omega

/-- Per-step capacity of `e2eCompositionCostBudget`. -/
def compositionPerStepBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 12 *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Aggregates PQXDH, session-start, SPQR, Double Ratchet, and codec step costs inside
`compositionPerStepBudget`. -/
theorem e2eLeafSum_le_compositionPerStepBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    {pqxdhCost startCost spqrCost drCost codecCost : ℕ}
    (hPqxdh :
      pqxdhCost ≤ 1024 *
        (b.q_total + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot) + 65536)
    (hStart :
      startCost ≤ 1024 *
        (qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) + 131072)
    (hSpqr : spqrCost ≤ 2000000)
    (hDr : drCost ≤ 1024 * (qDR + 1) * (qDR + qep + ℓ + 1) + 4000000)
    (hCodec : codecCost ≤ 1024) :
    pqxdhCost + startCost + spqrCost + drCost + codecCost ≤
      compositionPerStepBudget S b qStart qDR qep ℓ := by
  have hJumps : maxForwardJumps = 25000 := rfl
  rw [Nat.mul_assoc 1024 (qDR + 1) _] at hDr
  unfold compositionPerStepBudget
  rw [hJumps]
  omega

theorem totalCost_le_e2eCompositionCostBudget_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    (hInitFin : R.init.cost + R.finish.cost ≤ compositionPerStepBudget S b qStart qDR qep ℓ)
    (hU : I.uCost ≤ compositionPerStepBudget S b qStart qDR qep ℓ)
    (hStep : R.handle.cost + C.codecCost ≤ compositionPerStepBudget S b qStart qDR qep ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ e2eCompositionCostBudget S b qStart qDR qep ℓ := by
  have hParts := totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := compositionPerStepBudget S b qStart qDR qep ℓ)
    (finB := R.finish.cost) le_rfl hU hStep le_rfl
  unfold e2eCompositionCostBudget compositionPerStepBudget at *
  have hEq :
      2 ^ 12 * (b.q_total + qStart + qDR + 1) *
        (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
          maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1)) =
      (b.q_total + qStart + qDR) *
        (2 ^ 12 *
          (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
            maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))) +
      2 ^ 12 *
        (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
          maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1)) := by
    ring
  omega

/-- Per-step capacity of `bhE2ECostBudgetHonest`. -/
def compositionPerStepBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 15 *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Aggregates multi-arm PQXDH, session-start, SPQR, Double Ratchet, and codec step costs inside
`compositionPerStepBudgetHonest`. -/
theorem e2eLeafSumM3_le_compositionPerStepBudgetHonest (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    {pqxdhCost startCost spqrCost drCost codecCost : ℕ}
    (hPqxdh :
      pqxdhCost ≤ 16384 *
        (b.q_total + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot) + 524288)
    (hStart :
      startCost ≤ 8192 *
        (qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot) + 524288)
    (hSpqr : spqrCost ≤ 4000000)
    (hDr : drCost ≤ 8192 * (qDR + 1) * (qDR + qep + ℓ + 1) + 8000000)
    (hCodec : codecCost ≤ 8192) :
    pqxdhCost + startCost + spqrCost + drCost + codecCost ≤
      compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
  have hJumps : maxForwardJumps = 25000 := rfl
  rw [Nat.mul_assoc 8192 (qDR + 1) _] at hDr
  unfold compositionPerStepBudgetHonest
  rw [hJumps]
  omega

private theorem finish_pair_le_honest_slack (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ) :
    2 ^ 15 * S.N_send_tot * S.N_recv_tot ≤
      (S.N_send_tot + S.N_recv_tot) * compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
  have hRecv : 2 ^ 15 * S.N_recv_tot ≤ compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
    unfold compositionPerStepBudgetHonest
    exact Nat.mul_le_mul_left _ (by omega)
  calc
    2 ^ 15 * S.N_send_tot * S.N_recv_tot
        = S.N_send_tot * (2 ^ 15 * S.N_recv_tot) := by ring
    _ ≤ (S.N_send_tot + S.N_recv_tot) * compositionPerStepBudgetHonest S b qStart qDR qep ℓ :=
        Nat.mul_le_mul (by omega) hRecv

/-- Bounds `CostedReduction.totalCost` by `bhE2ECostBudgetHonest` from per-step and endpoint bounds. -/
theorem totalCost_le_bhE2ECostBudgetHonest_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    (hInitFin : R.init.cost + R.finish.cost ≤
      2 ^ 15 * S.N_send_tot * S.N_recv_tot +
        compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (hU : I.uCost ≤ compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (hStep : R.handle.cost + C.codecCost ≤ compositionPerStepBudgetHonest S b qStart qDR qep ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ := by
  have hParts := totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (finB := R.finish.cost) le_rfl hU hStep le_rfl
  have hSlack := finish_pair_le_honest_slack S b qStart qDR qep ℓ
  have hSplit :
      bhE2ECostBudgetHonest S b qStart qDR qep ℓ =
      (b.q_total + qStart + qDR) * compositionPerStepBudgetHonest S b qStart qDR qep ℓ +
        (S.N_send_tot + S.N_recv_tot) * compositionPerStepBudgetHonest S b qStart qDR qep ℓ +
        compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
    unfold bhE2ECostBudgetHonest compositionPerStepBudgetHonest
    ring
  omega

/-- Bounds `TwoStageCostedReduction.totalCost` by `bhE2ECostBudgetHonest` from per-step and endpoint bounds. -/
theorem twoStage_totalCost_le_bhE2ECostBudgetHonest_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    {midB : ℕ}
    (hCh : R.chDone.cost ≤ midB)
    (hRes : R.resume.cost ≤ midB)
    (hOverhead : R.init.cost + midB + R.finish.cost ≤
      2 ^ 15 * S.N_send_tot * S.N_recv_tot +
        compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (hU : I.uCost ≤ compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (hPre : R.handlePre.cost + C.codecCost ≤ compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (hPost : R.handlePost.cost + C.codecCost ≤ compositionPerStepBudgetHonest S b qStart qDR qep ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ bhE2ECostBudgetHonest S b qStart qDR qep ℓ := by
  have hParts := twoStage_totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := compositionPerStepBudgetHonest S b qStart qDR qep ℓ)
    (midB := midB) (finB := R.finish.cost)
    le_rfl hU hPre hPost hCh hRes le_rfl
  have hSlack := finish_pair_le_honest_slack S b qStart qDR qep ℓ
  have hSplit :
      bhE2ECostBudgetHonest S b qStart qDR qep ℓ =
      (b.q_total + qStart + qDR) * compositionPerStepBudgetHonest S b qStart qDR qep ℓ +
        (S.N_send_tot + S.N_recv_tot) * compositionPerStepBudgetHonest S b qStart qDR qep ℓ +
        compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
    unfold bhE2ECostBudgetHonest compositionPerStepBudgetHonest
    ring
  omega

theorem twoStage_totalCost_le_e2eCompositionCostBudget_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    {midB : ℕ}
    (hCh : R.chDone.cost ≤ midB)
    (hRes : R.resume.cost ≤ midB)
    (hOverhead : R.init.cost + midB + R.finish.cost ≤ compositionPerStepBudget S b qStart qDR qep ℓ)
    (hU : I.uCost ≤ compositionPerStepBudget S b qStart qDR qep ℓ)
    (hPre : R.handlePre.cost + C.codecCost ≤ compositionPerStepBudget S b qStart qDR qep ℓ)
    (hPost : R.handlePost.cost + C.codecCost ≤ compositionPerStepBudget S b qStart qDR qep ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ e2eCompositionCostBudget S b qStart qDR qep ℓ := by
  have hParts := twoStage_totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := compositionPerStepBudget S b qStart qDR qep ℓ)
    (midB := midB) (finB := R.finish.cost)
    le_rfl hU hPre hPost hCh hRes le_rfl
  unfold e2eCompositionCostBudget compositionPerStepBudget at *
  have hEq :
      2 ^ 12 * (b.q_total + qStart + qDR + 1) *
        (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
          maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1)) =
      (b.q_total + qStart + qDR) *
        (2 ^ 12 *
          (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
            maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))) +
      2 ^ 12 *
        (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
          maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1)) := by
    ring
  omega

/-! ## Numerical bounds at `SignalPqxdh.deploymentSetup` -/

def deploymentQueryBudget40 : SignalPqxdh.QueryBudget :=
  { q_ro := 2 ^ 40, q_roRoot := 2 ^ 40, q_total := 2 ^ 40, q_on := 2 ^ 40 }

theorem e2eAdapterCostBudget_deployment_lt :
    e2eAdapterCostBudget SignalPqxdh.deploymentSetup deploymentQueryBudget40 (2 ^ 20) (2 ^ 40) 1024 <
      2 ^ 90 := by
  unfold e2eAdapterCostBudget SignalPqxdh.deploymentSetup deploymentQueryBudget40
    SignalPqxdh.Setup.N_spk_tot SignalPqxdh.Setup.N_opk_tot SignalPqxdh.Setup.N_send_tot
  decide

theorem e2eAdapterCostBudgetPreBlock_deployment_lt :
    e2eAdapterCostBudgetPreBlock SignalPqxdh.deploymentSetup deploymentQueryBudget40
      (2 ^ 20) (2 ^ 40) 1024 < 2 ^ 90 := by
  unfold e2eAdapterCostBudgetPreBlock SignalPqxdh.deploymentSetup deploymentQueryBudget40
    SignalPqxdh.Setup.N_spk_tot SignalPqxdh.Setup.N_opk_tot SignalPqxdh.Setup.N_send_tot
  decide

theorem e2eCompositionCostBudget_deployment_qDR30_lt :
    e2eCompositionCostBudget SignalPqxdh.deploymentSetup deploymentQueryBudget40
      (2 ^ 20) (2 ^ 30) (2 ^ 20) 1024 < 2 ^ 113 := by
  unfold e2eCompositionCostBudget SignalPqxdh.deploymentSetup deploymentQueryBudget40
    SignalPqxdh.Setup.N_spk_tot SignalPqxdh.Setup.N_opk_tot SignalPqxdh.Setup.N_send_tot
    SignalPqxdh.Setup.N_recv_tot maxForwardJumps
  decide

theorem e2eCompositionCostBudgetLinearSm_deployment_lt :
    e2eCompositionCostBudgetLinearSm SignalPqxdh.deploymentSetup deploymentQueryBudget40
      (2 ^ 20) (2 ^ 40) (2 ^ 20) 1024 < 2 ^ 96 := by
  unfold e2eCompositionCostBudgetLinearSm SignalPqxdh.deploymentSetup deploymentQueryBudget40
    SignalPqxdh.Setup.N_spk_tot SignalPqxdh.Setup.N_opk_tot SignalPqxdh.Setup.N_send_tot
    SignalPqxdh.Setup.N_recv_tot maxForwardJumps
  decide

theorem bhE2ECostBudgetHonest_deployment_qDR30_lt :
    bhE2ECostBudgetHonest SignalPqxdh.deploymentSetup deploymentQueryBudget40
      (2 ^ 20) (2 ^ 30) (2 ^ 20) 1024 < 2 ^ 116 := by
  unfold bhE2ECostBudgetHonest SignalPqxdh.deploymentSetup deploymentQueryBudget40
    SignalPqxdh.Setup.N_spk_tot SignalPqxdh.Setup.N_opk_tot SignalPqxdh.Setup.N_send_tot
    SignalPqxdh.Setup.N_recv_tot maxForwardJumps
  decide

end Computational.Proofs.E2E.Dsl.LeafCostBounds
