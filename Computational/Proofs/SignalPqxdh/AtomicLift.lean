/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.CostedTablesCompat
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
public import Computational.Proofs.ReductionDsl.AtomicSizeHonest
public import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Lifting Legacy PQXDH `ReductionDsl` Programs to Atomic Tables

**Checked by Lean.** Translates `SignalPqxdh.LegacyCosted` expressions, computations, and one- and
two-stage reductions onto `pqAtomicSig`, `pqAtomicOps`, and `pqAtomicSamplers`. Preserves
`OracleComp` evaluation semantics along with query, polynomial step-cost, syntax-size, and output
block-size bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.SignalPqxdh.AtomicLift

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Sig Ty Var Env Ops Expr Comp Samplers Iface GameCodec
  CostedReduction TwoStageCostedReduction Mid
  AtomicSort AtomicBaseUnif AtomicPureOp
  atomicSig atomicBaseSamplers atomicPureOps unifSamplers UniformSamplerTag
  pqAtomicSig pqAtomicOps pqAtomicSamplers pqPrimIface pqSigAndDdhIface pqKeyIndCodec
  PB PU32 BV128 BV256 FinT bundleT hdrT drKeyT dhSecretsT sidT keyIndQT keyIndRT
  bundleV bundleOfV hdrV hdrOfV drKeyV drKeyOfV sidV sidOfV keyIndQenc keyIndRdec
  PTag bits sampleIndex iterM findML anyML mapML consumeFirstML foldML runFuel
  OpsSizeHonest SampSizeHonest ValFits
)

/-! ## Block-size bounds -/

theorem one_le_pqAtomicSamplers_sCost (s : pqAtomicSamplers.Samp) :
    1 ≤ pqAtomicSamplers.sCost s := by
  cases s with
  | bool => simp
  | index N => simp
  | base b =>
    cases b <;> simp [AtomicBaseUnif.cost]

theorem one_le_ptag_qCost (t : PTag) : 1 ≤ t.qCost := by
  cases t <;> simp [PTag.qCost] <;> omega

theorem one_le_firstMsgPTag_qCost (t : SignalPqxdh.Costed.FirstMsgPTag) : 1 ≤ t.qCost := by
  cases t <;> simp [SignalPqxdh.Costed.FirstMsgPTag.qCost] <;> omega

theorem one_le_authPTag_qCost (t : SignalPqxdh.Costed.AuthPTag) :
    1 ≤ SignalPqxdh.Costed.AuthPTag.qCost t := by
  cases t with
  | inl t => exact one_le_ptag_qCost t
  | inr t => exact one_le_firstMsgPTag_qCost t

theorem one_le_pqPrimIface_qCost (g : pqPrimIface.Tag) : 1 ≤ pqPrimIface.qCost g :=
  one_le_ptag_qCost g

theorem one_le_pqSigAndDdhIface_qCost (g : pqSigAndDdhIface.Tag) :
    1 ≤ pqSigAndDdhIface.qCost g := by
  rcases g with t | (m | ⟨⟩)
  · exact one_le_ptag_qCost t
  · simp; omega
  · simp

theorem one_le_pqChalIface_qCost {C : SignalPqxdh.Costed.ChallengerOracle}
    (hC : ∀ t, 1 ≤ C.qCost t) (g : (SignalPqxdh.Costed.pqChalIface C).Tag) :
    1 ≤ (SignalPqxdh.Costed.pqChalIface C).qCost g := by
  cases g with
  | inl t => exact one_le_ptag_qCost t
  | inr t => exact hC t

theorem one_le_pqAuthPrimIface_qCost (g : SignalPqxdh.Costed.pqAuthPrimIface.Tag) :
    1 ≤ SignalPqxdh.Costed.pqAuthPrimIface.qCost g :=
  one_le_authPTag_qCost g

theorem one_le_pqAuthChalIface_qCost {C : SignalPqxdh.Costed.ChallengerOracle}
    (hC : ∀ t, 1 ≤ C.qCost t) (g : (SignalPqxdh.Costed.pqAuthChalIface C).Tag) :
    1 ≤ (SignalPqxdh.Costed.pqAuthChalIface C).qCost g := by
  cases g with
  | inl t => exact one_le_authPTag_qCost t
  | inr t => exact hC t

theorem one_le_eufCmaSignOracle_qCost (t : SignalPqxdh.Costed.eufCmaSignOracle.Tag) :
    1 ≤ SignalPqxdh.Costed.eufCmaSignOracle.qCost t := by
  simp [SignalPqxdh.Costed.eufCmaSignOracle]; omega

theorem one_le_gapDhDdhOracle_qCost (t : SignalPqxdh.Costed.gapDhDdhOracle.Tag) :
    1 ≤ SignalPqxdh.Costed.gapDhDdhOracle.qCost t := by
  simp [SignalPqxdh.Costed.gapDhDdhOracle]

theorem one_le_msgKeyPrfOracle_qCost (t : SignalPqxdh.Costed.msgKeyPrfOracle.Tag) :
    1 ≤ SignalPqxdh.Costed.msgKeyPrfOracle.qCost t := by
  simp [SignalPqxdh.Costed.msgKeyPrfOracle]; omega

theorem one_le_hmacPrfOracle_qCost (t : SignalPqxdh.Costed.hmacPrfOracle.Tag) :
    1 ≤ SignalPqxdh.Costed.hmacPrfOracle.qCost t := by
  simp [SignalPqxdh.Costed.hmacPrfOracle]; omega

theorem one_le_sigAndDdhOracle_qCost (t : SignalPqxdh.Costed.sigAndDdhOracle.Tag) :
    1 ≤ SignalPqxdh.Costed.sigAndDdhOracle.qCost t := by
  rcases t with m | ⟨⟩
  · simp [SignalPqxdh.Costed.sigAndDdhOracle]; omega
  · simp [SignalPqxdh.Costed.sigAndDdhOracle]

theorem comp_nq_le_cost_atomic {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig} (c : Comp pqAtomicOps I Γ t) :
    c.nq ≤ c.cost := by
  induction c with
  | ret _ => simp [Comp.nq, Comp.queries, Comp.cost]
  | bind c k ihc ihk => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | ite _ c d ihc ihd => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseOpt _ n s ihn ihs => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | caseSum _ l r ihl ihr => dsimp only [Comp.nq, Comp.queries, Comp.cost] at *; omega
  | sample s _ => have := hs s; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | query g _ => have := hq g; dsimp only [Comp.nq, Comp.queries, Comp.cost]; omega
  | iter n _ body ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) body ≤ body.cost + 1 := by omega
    have := Nat.mul_le_mul_left n h1
    omega
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | foldM K _ _ p ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega
  | consumeFirstM K _ p mk ih =>
    dsimp only [Comp.nq] at ih ⊢
    dsimp only [Comp.queries, Comp.cost]
    have h1 : Comp.queries (fun _ => 1) (fun _ => 1) p ≤ p.cost + mk.cost + 1 := by omega
    have := Nat.mul_le_mul_left K h1
    omega

theorem gred_nq_le_totalCost_atomic {ι κ : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {G : OracleSpec κ} {C : GameCodec pqAtomicSig G} {rIn aIn aOut out : Ty pqAtomicSig}
    (hq : ∀ g, 1 ≤ I.qCost g) (hs : ∀ s, 1 ≤ I.smp.sCost s)
    (R : CostedReduction pqAtomicOps I G C rIn aIn aOut out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hI := comp_nq_le_cost_atomic hq hs R.init
  have hH := comp_nq_le_cost_atomic hq hs R.handle
  have hF := comp_nq_le_cost_atomic hq hs R.finish
  have hMax : R.handle.nq ≤ max I.uCost (R.handle.cost + C.codecCost) :=
    le_trans hH (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left q hMax
  dsimp only [CostedReduction.nq, CostedReduction.totalQueries, CostedReduction.totalCost,
    Comp.nq] at *
  omega

theorem gredBlockBounded_atomic_of_totalCost_le {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ} {C : GameCodec pqAtomicSig G}
    {rIn out : Ty pqAtomicSig}
    (hS : SampSizeHonest I.smp) (hqCost : ∀ g, 1 ≤ I.qCost g) (hsCost : ∀ s, 1 ≤ I.smp.sCost s)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqAtomicOps I G C rIn .unit .bool out)
    (hCost : R.totalCost b.q_total ≤ SignalPqxdh.Security.stepCostBudget S b)
    (hSize : R.size ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (SignalPqxdh.Security.stepCostBudget S b)) :
    SignalPqxdh.Security.GRedBlockBounded S b ℓ R := by
  refine ⟨hSize, fun A hA hfit x hx y hy => ?_⟩
  have hA' : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := G)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [_root_.ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := R.fits_eval_when
    Computational.Proofs.ReductionDsl.AtomicSizeHonest.pqAtomicOps_sizeHonest hS
    ℓ ℓ 0 (fun _ => trivial) A b.q_total ℓ hA' hfit x hx y hy
  have hNq := le_trans (gred_nq_le_totalCost_atomic hqCost hsCost R b.q_total) hCost
  refine Ty.fits_mono ?_ out y hEval
  unfold SignalPqxdh.Security.outputSizeBudget
  nlinarith

theorem gred2BlockBounded_atomic_of_totalCost_le {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ} {C : GameCodec pqAtomicSig G}
    {rIn ch rIn2 out : Ty pqAtomicSig}
    (hS : SampSizeHonest I.smp) (hqCost : ∀ g, 1 ≤ I.qCost g) (hsCost : ∀ s, 1 ≤ I.smp.sCost s)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (ℓ : Nat)
    (R : TwoStageCostedReduction pqAtomicOps I G C rIn .unit .bool ch rIn2 out)
    (hCost : R.totalCost b.q_total ≤ SignalPqxdh.Security.stepCostBudget S b)
    (hSize : R.size ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (SignalPqxdh.Security.stepCostBudget S b)) :
    SignalPqxdh.Security.GRed2BlockBounded S b ℓ R := by
  refine ⟨hSize, fun A hfit x hx cm hcm => ?_⟩
  have ⟨hc1, hm1⟩ := R.fits_eval1_when
    Computational.Proofs.ReductionDsl.AtomicSizeHonest.pqAtomicOps_sizeHonest hS
    ℓ ℓ 0 (fun _ => trivial) A hfit b.q_total ℓ x hx false cm hcm
  have hI := comp_nq_le_cost_atomic hqCost hsCost R.init
  have hPre := comp_nq_le_cost_atomic hqCost hsCost R.handlePre
  have hPost := comp_nq_le_cost_atomic hqCost hsCost R.handlePost
  have hDone := comp_nq_le_cost_atomic hqCost hsCost R.chDone
  have hRes := comp_nq_le_cost_atomic hqCost hsCost R.resume
  have hFin := comp_nq_le_cost_atomic hqCost hsCost R.finish
  have hPreC : R.handlePre.cost ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    le_trans (le_max_left _ _) (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hPostC : R.handlePost.cost ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    le_trans (le_max_right _ _) (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMaxH : max R.handlePre.nq R.handlePost.nq ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    max_le (le_trans hPre hPreC) (le_trans hPost hPostC)
  have hMaxCR : max R.chDone.nq R.resume.nq ≤ max R.chDone.cost R.resume.cost :=
    max_le (le_trans hDone (le_max_left _ _)) (le_trans hRes (le_max_right _ _))
  have hMulH := Nat.mul_le_mul_left b.q_total hMaxH
  have hMulPreC := Nat.mul_le_mul_left b.q_total hPreC
  have hMulPostC := Nat.mul_le_mul_left b.q_total hPostC
  have hMulPreN := Nat.mul_le_mul_left b.q_total (le_trans hPre hPreC)
  have hMulPostN := Nat.mul_le_mul_left b.q_total (le_trans hPost hPostC)
  have hNqLe : R.nq b.q_total ≤ SignalPqxdh.Security.stepCostBudget S b := by
    dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries,
      TwoStageCostedReduction.totalCost, Comp.nq] at *
    omega
  have hB1Le : R.init.cost + b.q_total * R.handlePre.cost ≤
      SignalPqxdh.Security.stepCostBudget S b := by
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  have hN1Le : R.init.nq + b.q_total * R.handlePre.nq ≤
      SignalPqxdh.Security.stepCostBudget S b := by
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  have hB2Le : R.resume.cost + b.q_total * R.handlePost.cost + R.finish.cost ≤
      SignalPqxdh.Security.stepCostBudget S b := by
    have : R.resume.cost ≤ max R.chDone.cost R.resume.cost := le_max_right _ _
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  have hN2Le : R.resume.nq + b.q_total * R.handlePost.nq + R.finish.nq ≤
      SignalPqxdh.Security.stepCostBudget S b := by
    have : R.resume.nq ≤ max R.chDone.cost R.resume.cost := le_trans hRes (le_max_right _ _)
    dsimp only [TwoStageCostedReduction.totalCost] at hCost; omega
  refine ⟨?_, fun y hy z hz => ?_⟩
  · refine Ty.fits_mono ?_ ch cm.1 hc1
    unfold SignalPqxdh.Security.outputSizeBudget
    nlinarith
  · have hz' := R.fits_eval2_when
      Computational.Proofs.ReductionDsl.AtomicSizeHonest.pqAtomicOps_sizeHonest hS
      ℓ ℓ 0 (fun _ => trivial) cm.2 _ hm1 y ℓ hy b.q_total false z hz
    refine Ty.fits_mono ?_ out z hz'
    unfold SignalPqxdh.Security.outputSizeBudget
    nlinarith

/-! ## Sort, type, and value embedding -/

@[reducible] def embedSort : SignalPqxdh.LegacyCosted.PSort → AtomicSort
  | .bytes w => .pbytes w
  | .u32 => .pu32

@[reducible] def embedTy : Ty SignalPqxdh.LegacyCosted.pqSig → Ty pqAtomicSig
  | .base s => .base (embedSort s)
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .opt t => .opt (embedTy t)
  | .prod t u => .prod (embedTy t) (embedTy u)
  | .sum t u => .sum (embedTy t) (embedTy u)
  | .list t => .list (embedTy t)
  | .tbl t => .tbl (embedTy t)

@[reducible] def embedBase :
    (s : SignalPqxdh.LegacyCosted.PSort) →
      SignalPqxdh.LegacyCosted.pqSig.den s → pqAtomicSig.den (embedSort s)
  | .bytes _, x => x
  | .u32, x => x

@[reducible] def projBase :
    (s : SignalPqxdh.LegacyCosted.PSort) →
      pqAtomicSig.den (embedSort s) → SignalPqxdh.LegacyCosted.pqSig.den s
  | .bytes _, x => x
  | .u32, x => x

def embedVal : (t : Ty SignalPqxdh.LegacyCosted.pqSig) → t.denote → (embedTy t).denote
  | .base s, x => embedBase s x
  | .unit, () => ()
  | .bool, b => b
  | .nat, n => n
  | .opt _, none => none
  | .opt t, some x => some (embedVal t x)
  | .prod t u, (a, b) => (embedVal t a, embedVal u b)
  | .sum t _, .inl a => .inl (embedVal t a)
  | .sum _ u, .inr b => .inr (embedVal u b)
  | .list t, l => l.map (embedVal t)
  | .tbl t, f => fun i => embedVal t (f i)

def projVal : (t : Ty SignalPqxdh.LegacyCosted.pqSig) → (embedTy t).denote → t.denote
  | .base s, x => projBase s x
  | .unit, () => ()
  | .bool, b => b
  | .nat, n => n
  | .opt _, none => none
  | .opt t, some x => some (projVal t x)
  | .prod t u, (a, b) => (projVal t a, projVal u b)
  | .sum t _, .inl a => .inl (projVal t a)
  | .sum _ u, .inr b => .inr (projVal u b)
  | .list t, l => l.map (projVal t)
  | .tbl t, f => fun i => projVal t (f i)

@[simp] theorem projVal_embedVal :
    ∀ (t : Ty SignalPqxdh.LegacyCosted.pqSig) (x : t.denote), projVal t (embedVal t x) = x
  | .base (.bytes _), _ => rfl
  | .base .u32, _ => rfl
  | .unit, () => rfl
  | .bool, _ => rfl
  | .nat, _ => rfl
  | .opt _, none => rfl
  | .opt t, some x => congrArg some (projVal_embedVal t x)
  | .prod t u, (a, b) => Prod.ext (projVal_embedVal t a) (projVal_embedVal u b)
  | .sum t _, .inl a => congrArg Sum.inl (projVal_embedVal t a)
  | .sum _ u, .inr b => congrArg Sum.inr (projVal_embedVal u b)
  | .list t, l => by
    simp only [embedVal, projVal, List.map_map]
    have h : projVal t ∘ embedVal t = id := funext (projVal_embedVal t)
    simp [h]
  | .tbl t, f => funext fun i => projVal_embedVal t (f i)

@[simp] theorem embedVal_projVal :
    ∀ (t : Ty SignalPqxdh.LegacyCosted.pqSig) (y : (embedTy t).denote), embedVal t (projVal t y) = y
  | .base (.bytes _), _ => rfl
  | .base .u32, _ => rfl
  | .unit, () => rfl
  | .bool, _ => rfl
  | .nat, _ => rfl
  | .opt _, none => rfl
  | .opt t, some y => congrArg some (embedVal_projVal t y)
  | .prod t u, (a, b) => Prod.ext (embedVal_projVal t a) (embedVal_projVal u b)
  | .sum t _, .inl a => congrArg Sum.inl (embedVal_projVal t a)
  | .sum _ u, .inr b => congrArg Sum.inr (embedVal_projVal u b)
  | .list t, l => by
    simp only [embedVal, projVal, List.map_map]
    have h : embedVal t ∘ projVal t = id := funext (embedVal_projVal t)
    simp [h]
  | .tbl t, f => funext fun i => embedVal_projVal t (f i)

@[reducible] def embedCtx : List (Ty SignalPqxdh.LegacyCosted.pqSig) → List (Ty pqAtomicSig)
  | [] => []
  | t :: Γ => embedTy t :: embedCtx Γ

def embedVar :
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} → {t : Ty SignalPqxdh.LegacyCosted.pqSig} →
      Var Γ t → Var (embedCtx Γ) (embedTy t)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (embedVar v)

@[reducible] def embedEnv : {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} → Env Γ → Env (embedCtx Γ)
  | _, .nil => .nil
  | _, .cons x ρ => .cons (embedVal _ x) (embedEnv ρ)

theorem embedEnv_get :
    ∀ {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
      (ρ : Env Γ) (v : Var Γ t),
      (embedEnv ρ).get (embedVar v) = embedVal t (ρ.get v)
  | _, _, .cons _ _, .zero => rfl
  | _, _, .cons _ ρ, .succ v => embedEnv_get ρ v

/-! ## Context renaming -/

def liftRen {S : Sig} {Γ Δ : List (Ty S)} {u : Ty S}
    (ξ : ∀ {t}, Var Γ t → Var Δ t) : ∀ {t}, Var (u :: Γ) t → Var (u :: Δ) t
  | _, .zero => .zero
  | _, .succ v => .succ (ξ v)

def exprRename {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ξ : ∀ {a}, Var Γ a → Var Δ a) : Expr O Γ t → Expr O Δ t
  | .var v => .var (ξ v)
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .add a b => .add (exprRename ξ a) (exprRename ξ b)
  | .sub a b => .sub (exprRename ξ a) (exprRename ξ b)
  | .mulK k a => .mulK k (exprRename ξ a)
  | .divK k a => .divK k (exprRename ξ a)
  | .modK k a => .modK k (exprRename ξ a)
  | .lt a b => .lt (exprRename ξ a) (exprRename ξ b)
  | .eqN a b => .eqN (exprRename ξ a) (exprRename ξ b)
  | .not a => .not (exprRename ξ a)
  | .and a b => .and (exprRename ξ a) (exprRename ξ b)
  | .ite c a b => .ite (exprRename ξ c) (exprRename ξ a) (exprRename ξ b)
  | .pair a b => .pair (exprRename ξ a) (exprRename ξ b)
  | .fst a => .fst (exprRename ξ a)
  | .snd a => .snd (exprRename ξ a)
  | .inl a => .inl (exprRename ξ a)
  | .inr a => .inr (exprRename ξ a)
  | .none => .none
  | .some a => .some (exprRename ξ a)
  | .caseOpt e n s => .caseOpt (exprRename ξ e) (exprRename ξ n) (exprRename (liftRen ξ) s)
  | .caseSum e l r => .caseSum (exprRename ξ e) (exprRename (liftRen ξ) l) (exprRename (liftRen ξ) r)
  | .letE e b => .letE (exprRename ξ e) (exprRename (liftRen ξ) b)
  | .op o a => .op o (exprRename ξ a)
  | .nil => .nil
  | .cons x l => .cons (exprRename ξ x) (exprRename ξ l)
  | .len l => .len (exprRename ξ l)
  | .take n l => .take (exprRename ξ n) (exprRename ξ l)
  | .appendL K a b => .appendL K (exprRename ξ a) (exprRename ξ b)
  | .findB K l p => .findB K (exprRename ξ l) (exprRename (liftRen ξ) p)
  | .anyB K l p => .anyB K (exprRename ξ l) (exprRename (liftRen ξ) p)
  | .mapB K l f => .mapB K (exprRename ξ l) (exprRename (liftRen ξ) f)
  | .foldrB K l z f =>
    .foldrB K (exprRename ξ l) (exprRename ξ z) (exprRename (liftRen (liftRen ξ)) f)
  | .tconst a => .tconst (exprRename ξ a)
  | .tget m i => .tget (exprRename ξ m) (exprRename ξ i)
  | .tset m i a => .tset (exprRename ξ m) (exprRename ξ i) (exprRename ξ a)

@[simp] theorem exprRename_cost {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (ξ : ∀ {a}, Var Γ a → Var Δ a) (e : Expr O Γ t) :
    (exprRename ξ e).cost = e.cost := by
  induction e generalizing Δ <;> simp [exprRename, Expr.cost, *]

theorem exprRename_eval {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) (ξ : ∀ {a}, Var Γ a → Var Δ a) (ρ : Env Γ) (ρ' : Env Δ)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    (exprRename ξ e).eval ρ' = e.eval ρ := by
  induction e generalizing Δ with
  | var v => exact hρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | take a b iha ihb
  | appendL _ a b iha ihb | tget a b iha ihb =>
    simp [exprRename, Expr.eval, iha ξ ρ ρ' hρ, ihb ξ ρ ρ' hρ]
  | mulK _ a iha | divK _ a iha | modK _ a iha | not a iha | fst a iha | snd a iha
  | inl a iha | inr a iha | some a iha | op _ a iha | len a iha | tconst a iha =>
    simp [exprRename, Expr.eval, iha ξ ρ ρ' hρ]
  | ite c a b ihc iha ihb | tset c a b ihc iha ihb =>
    simp [exprRename, Expr.eval, ihc ξ ρ ρ' hρ, iha ξ ρ ρ' hρ, ihb ξ ρ ρ' hρ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [exprRename, Expr.eval, ihe ξ ρ ρ' hρ]
    cases e.eval ρ with
    | none => exact ihn ξ ρ ρ' hρ
    | some x =>
      refine ihs (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | caseSum e l r ihe ihl ihr =>
    simp only [exprRename, Expr.eval, ihe ξ ρ ρ' hρ]
    cases e.eval ρ with
    | inl x =>
      refine ihl (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
    | inr y =>
      refine ihr (liftRen ξ) (.cons y ρ) (.cons y ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | letE e b ihe ihb =>
    simp only [exprRename, Expr.eval, ihe ξ ρ ρ' hρ]
    refine ihb (liftRen ξ) (.cons (e.eval ρ) ρ) (.cons (e.eval ρ) ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | findB K l p ihl ihp =>
    simp only [exprRename, Expr.eval, ihl ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihp (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | anyB K l p ihl ihp =>
    simp only [exprRename, Expr.eval, ihl ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihp (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | mapB K l f ihl ihf =>
    simp only [exprRename, Expr.eval, ihl ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihf (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | foldrB K l z f ihl ihz ihf =>
    simp only [exprRename, Expr.eval, ihl ξ ρ ρ' hρ, ihz ξ ρ ρ' hρ]
    congr 1; ext x acc
    refine ihf (liftRen (liftRen ξ)) (.cons x (.cons acc ρ)) (.cons x (.cons acc ρ')) ?_
    intro a v; cases v with
    | zero => rfl
    | succ v => cases v <;> simp [liftRen, Env.get, hρ]

def compRename {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ {a}, Var Γ a → Var Δ a) :
    Comp O I Γ t → Comp O I Δ t
  | .ret e => .ret (exprRename ξ e)
  | .bind c k => .bind (compRename ξ c) (compRename (liftRen ξ) k)
  | .ite b c d => .ite (exprRename ξ b) (compRename ξ c) (compRename ξ d)
  | .caseOpt e n s => .caseOpt (exprRename ξ e) (compRename ξ n) (compRename (liftRen ξ) s)
  | .caseSum e l r => .caseSum (exprRename ξ e) (compRename (liftRen ξ) l) (compRename (liftRen ξ) r)
  | .sample s e => .sample s (exprRename ξ e)
  | .query g e => .query g (exprRename ξ e)
  | .iter n e body => .iter n (exprRename ξ e) (compRename (liftRen ξ) body)
  | .findM K l p => .findM K (exprRename ξ l) (compRename (liftRen ξ) p)
  | .anyM K l p => .anyM K (exprRename ξ l) (compRename (liftRen ξ) p)
  | .mapM K l f => .mapM K (exprRename ξ l) (compRename (liftRen ξ) f)
  | .consumeFirstM K l p mk =>
    .consumeFirstM K (exprRename ξ l) (compRename (liftRen ξ) p) (exprRename (liftRen ξ) mk)
  | .foldM K l z f =>
    .foldM K (exprRename ξ l) (exprRename ξ z) (compRename (liftRen (liftRen ξ)) f)

@[simp] theorem compRename_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp O I Γ t) :
    (compRename ξ c).cost = c.cost := by
  induction c generalizing Δ <;> simp [compRename, Comp.cost, exprRename_cost, *]

@[simp] theorem compRename_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {t : Ty S}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp O I Γ t) :
    (compRename ξ c).queries w ws = c.queries w ws := by
  induction c generalizing Δ <;> simp [compRename, Comp.queries, *]

theorem compRename_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} {t : Ty S}
    (c : Comp O I Γ t) (ξ : ∀ {a}, Var Γ a → Var Δ a) (ρ : Env Γ) (ρ' : Env Δ)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    (compRename ξ c).eval ρ' = c.eval ρ := by
  induction c generalizing Δ with
  | ret e => simp [compRename, Comp.eval, exprRename_eval e ξ ρ ρ' hρ]
  | bind c k ihc ihk =>
    simp only [compRename, Comp.eval, ihc ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihk (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | ite b c d ihc ihd =>
    simp [compRename, Comp.eval, exprRename_eval b ξ ρ ρ' hρ, ihc ξ ρ ρ' hρ, ihd ξ ρ ρ' hρ]
  | caseOpt e n s ihn ihs =>
    simp only [compRename, Comp.eval, exprRename_eval e ξ ρ ρ' hρ]
    cases e.eval ρ with
    | none => exact ihn ξ ρ ρ' hρ
    | some x =>
      refine ihs (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | caseSum e l r ihl ihr =>
    simp only [compRename, Comp.eval, exprRename_eval e ξ ρ ρ' hρ]
    cases e.eval ρ with
    | inl x =>
      refine ihl (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
    | inr y =>
      refine ihr (liftRen ξ) (.cons y ρ) (.cons y ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | sample s e => dsimp [compRename, Comp.eval]; rw [exprRename_eval e ξ ρ ρ' hρ]
  | query g e => dsimp [compRename, Comp.eval]; rw [exprRename_eval e ξ ρ ρ' hρ]
  | iter n e body ihb =>
    simp only [compRename, Comp.eval, exprRename_eval e ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihb (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | findM K l p ihp =>
    simp only [compRename, Comp.eval, exprRename_eval l ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihp (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | anyM K l p ihp =>
    simp only [compRename, Comp.eval, exprRename_eval l ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihp (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | mapM K l f ihf =>
    simp only [compRename, Comp.eval, exprRename_eval l ξ ρ ρ' hρ]
    congr 1; ext x
    refine ihf (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
    intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | consumeFirstM K l p mk ihp =>
    simp only [compRename, Comp.eval, exprRename_eval l ξ ρ ρ' hρ]
    congr 1
    · ext x
      refine ihp (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
    · ext x
      refine exprRename_eval mk (liftRen ξ) (.cons x ρ) (.cons x ρ') ?_
      intro a v; cases v <;> simp [liftRen, Env.get, hρ]
  | foldM K l z f ihf =>
    simp only [compRename, Comp.eval, exprRename_eval l ξ ρ ρ' hρ, exprRename_eval z ξ ρ ρ' hρ]
    congr 1; ext x acc
    refine ihf (liftRen (liftRen ξ)) (.cons x (.cons acc ρ)) (.cons x (.cons acc ρ')) ?_
    intro a v; cases v with
    | zero => rfl
    | succ v => cases v <;> simp [liftRen, Env.get, hρ]

def swapHandlerVar {σ' Q_nat Q_fin : Ty pqAtomicSig} :
    ∀ {t}, Var [σ', Q_nat] t → Var [Q_nat, σ', Q_fin] t
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero

/-! ## Pure expression translation -/

theorem one_le_expr_cost {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : 1 ≤ e.cost := by
  induction e with
  | nat n => exact _root_.ReductionDsl.one_le_bits n
  | mulK k _ ih | divK k _ ih | modK k _ ih | op _ _ ih => simp only [Expr.cost]; omega
  | _ => simp only [Expr.cost]; omega

def nonNat : Ty SignalPqxdh.LegacyCosted.pqSig → ℕ
  | .nat => 0
  | _ => 1

theorem nonNat_le_one (t : Ty SignalPqxdh.LegacyCosted.pqSig) : nonNat t ≤ 1 := by
  cases t <;> simp [nonNat]

theorem add_nonNat_le {t : Ty SignalPqxdh.LegacyCosted.pqSig} (m n : ℕ) (h : m + 1 ≤ n) :
    m + nonNat t ≤ n := by
  have := nonNat_le_one t
  omega

abbrev aop {Γ : List (Ty pqAtomicSig)} (o : AtomicPureOp)
    (a : Expr pqAtomicOps Γ (o.dom 0 Empty)) : Expr pqAtomicOps Γ (o.cod 0 Empty) :=
  Expr.op (O := pqAtomicOps) o a

def mapOpExpr {Γ : List (Ty pqAtomicSig)} :
    (o : SignalPqxdh.LegacyCosted.pqxdhOps.Op) →
      Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhOps.dom o)) →
      Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhOps.cod o))
  | .inl (.lit w v), a => aop (.pbytesLit w v) a
  | .inl (.cat m n), a => aop (.pbytesCat m n) a
  | .inl (.cons b w), a => aop (.pbytesCons b w) a
  | .inl (.widen w d), a => aop (.pbytesWiden w d) a
  | .inl (.takeK w k), a => aop (.pbytesTakeK w k) a
  | .inl (.take w), a => aop (.pbytesTake w) a
  | .inl (.drop w), a => aop (.pbytesDrop w) a
  | .inl (.len w), a => aop (.pbytesLen w) a
  | .inl (.eq m n), a => aop (.pbytesEq m n) a
  | .inl .varint, a => aop .pbVarint a
  | .inr (.lit k), a => aop (.pu32Lit k) a
  | .inr .ofNat, a => aop .pu32OfNat a
  | .inr .toNat, a => aop .pu32ToNat a
  | .inr .eq, a => aop .pu32Eq a

def mapExpr {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig} :
    Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ t → Expr pqAtomicOps (embedCtx Γ) (embedTy t)
  | .var v => .var (embedVar v)
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .add a b => .add (mapExpr a) (mapExpr b)
  | .sub a b => .sub (mapExpr a) (mapExpr b)
  | .mulK k a => .mulK k (mapExpr a)
  | .divK k a => .divK k (mapExpr a)
  | .modK k a => .modK k (mapExpr a)
  | .lt a b => .lt (mapExpr a) (mapExpr b)
  | .eqN a b => .eqN (mapExpr a) (mapExpr b)
  | .not a => .not (mapExpr a)
  | .and a b => .and (mapExpr a) (mapExpr b)
  | .ite c a b => .ite (mapExpr c) (mapExpr a) (mapExpr b)
  | .pair a b => .pair (mapExpr a) (mapExpr b)
  | .fst a => .fst (mapExpr a)
  | .snd a => .snd (mapExpr a)
  | .inl a => .inl (mapExpr a)
  | .inr a => .inr (mapExpr a)
  | .none => .none
  | .some a => .some (mapExpr a)
  | .caseOpt e n s => .caseOpt (mapExpr e) (mapExpr n) (mapExpr s)
  | .caseSum e l r => .caseSum (mapExpr e) (mapExpr l) (mapExpr r)
  | .letE e b => .letE (mapExpr e) (mapExpr b)
  | .op o a => mapOpExpr o (mapExpr a)
  | .nil => .nil
  | .cons x l => .cons (mapExpr x) (mapExpr l)
  | .len l => .len (mapExpr l)
  | .take n l => .take (mapExpr n) (mapExpr l)
  | .appendL K a b => .appendL K (mapExpr a) (mapExpr b)
  | .findB K l p => .findB K (mapExpr l) (mapExpr p)
  | .anyB K l p => .anyB K (mapExpr l) (mapExpr p)
  | .mapB K l f => .mapB K (mapExpr l) (mapExpr f)
  | .foldrB K l z f => .foldrB K (mapExpr l) (mapExpr z) (mapExpr f)
  | .tconst a => .tconst (mapExpr a)
  | .tget m i => .tget (mapExpr m) (mapExpr i)
  | .tset m i a => .tset (mapExpr m) (mapExpr i) (mapExpr a)

private theorem find?_embed {α α' : Type} (ea : α → α') (p' : α' → Bool) (p : α → Bool)
    (hp : ∀ x, p' (ea x) = p x) :
    ∀ xs : List α, (xs.map ea).find? p' = (xs.find? p).map ea
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons, hp x]
    cases p x <;> simp [find?_embed ea p' p hp xs]

private theorem any_embed {α α' : Type} (ea : α → α') (p' : α' → Bool) (p : α → Bool)
    (hp : ∀ x, p' (ea x) = p x) :
    ∀ xs : List α, (xs.map ea).any p' = xs.any p
  | [] => rfl
  | x :: xs => by simp [List.map_cons, hp x, any_embed ea p' p hp xs]

private theorem map_embed {α β α' β' : Type} (ea : α → α') (eb : β → β')
    (f' : α' → β') (f : α → β) (hf : ∀ x, f' (ea x) = eb (f x)) :
    ∀ xs : List α, (xs.map ea).map f' = (xs.map f).map eb
  | [] => rfl
  | x :: xs => by simp [List.map_cons, hf x, map_embed ea eb f' f hf xs]

private theorem foldr_embed {α β α' β' : Type} (ea : α → α') (eb : β → β')
    (g : α' → β' → β') (f : α → β → β)
    (h : ∀ x acc, g (ea x) (eb acc) = eb (f x acc)) (z : β) :
    ∀ xs : List α, (xs.map ea).foldr g (eb z) = eb (xs.foldr f z)
  | [] => rfl
  | x :: xs => by simp [List.foldr_cons, foldr_embed ea eb g f h z xs, h]

theorem mapOpExpr_eval {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (o : SignalPqxdh.LegacyCosted.pqxdhOps.Op)
    (a : Expr pqAtomicOps (embedCtx Γ) (embedTy (SignalPqxdh.LegacyCosted.pqxdhOps.dom o)))
    (x : (SignalPqxdh.LegacyCosted.pqxdhOps.dom o).denote) (ρ : Env Γ)
    (ha : a.eval (embedEnv ρ) = embedVal (SignalPqxdh.LegacyCosted.pqxdhOps.dom o) x) :
    (mapOpExpr o a).eval (embedEnv ρ) =
      embedVal (SignalPqxdh.LegacyCosted.pqxdhOps.cod o)
        (SignalPqxdh.LegacyCosted.pqxdhOps.eval o x) := by
  rcases o with o | o
  · cases o with
    | lit w v => rfl
    | cat m n => rcases x with ⟨_, _⟩; exact congrArg (pqAtomicOps.eval (.pbytesCat m n)) ha
    | cons b w => exact congrArg (pqAtomicOps.eval (.pbytesCons b w)) ha
    | widen w d => exact congrArg (pqAtomicOps.eval (.pbytesWiden w d)) ha
    | takeK w k => exact congrArg (pqAtomicOps.eval (.pbytesTakeK w k)) ha
    | take w => rcases x with ⟨_, _⟩; exact congrArg (pqAtomicOps.eval (.pbytesTake w)) ha
    | drop w => rcases x with ⟨_, _⟩; exact congrArg (pqAtomicOps.eval (.pbytesDrop w)) ha
    | len w => exact congrArg (pqAtomicOps.eval (.pbytesLen w)) ha
    | eq m n => rcases x with ⟨_, _⟩; exact congrArg (pqAtomicOps.eval (.pbytesEq m n)) ha
    | varint => exact congrArg (pqAtomicOps.eval .pbVarint) ha
  · cases o with
    | lit k => rfl
    | ofNat => exact congrArg (pqAtomicOps.eval .pu32OfNat) ha
    | toNat => exact congrArg (pqAtomicOps.eval .pu32ToNat) ha
    | eq => rcases x with ⟨_, _⟩; exact congrArg (pqAtomicOps.eval .pu32Eq) ha

theorem mapExpr_eval {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ t) (ρ : Env Γ) :
    (mapExpr e).eval (embedEnv ρ) = embedVal t (e.eval ρ) := by
  induction e with
  | var v => exact embedEnv_get ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | tget a b iha ihb =>
    simp [mapExpr, Expr.eval, embedVal, iha ρ, ihb ρ]
  | mulK _ a iha | divK _ a iha | modK _ a iha | not a iha | fst a iha | snd a iha
  | inl a iha | inr a iha | some a iha | len a iha | tconst a iha =>
    simp [mapExpr, Expr.eval, embedVal, iha ρ]
  | ite c a b ihc iha ihb =>
    simp only [mapExpr, Expr.eval, ihc ρ, embedVal]
    split <;> [exact iha ρ; exact ihb ρ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [mapExpr, Expr.eval, ihe ρ]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihe ihl ihr =>
    simp only [mapExpr, Expr.eval, ihe ρ]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | letE e b ihe ihb =>
    simp only [mapExpr, Expr.eval, ihe ρ]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha => exact mapOpExpr_eval o (mapExpr a) (a.eval ρ) ρ (iha ρ)
  | take n l ihn ihl =>
    simp only [mapExpr, Expr.eval, ihn ρ, ihl ρ, embedVal, List.map_take]
  | appendL K a b iha ihb =>
    simp only [mapExpr, Expr.eval, iha ρ, ihb ρ, embedVal, List.map_take, List.map_append]
  | findB K l p ihl ihp =>
    simp only [mapExpr, Expr.eval, ihl ρ, embedVal, ← List.map_take]
    rw [find?_embed (embedVal _)
      (fun x => (mapExpr p).eval (.cons x (embedEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => ihp (.cons x ρ))
      ((l.eval ρ).take K)]
    cases ((l.eval ρ).take K).find? (fun x => p.eval (.cons x ρ)) <;> rfl
  | anyB K l p ihl ihp =>
    simp only [mapExpr, Expr.eval, ihl ρ, embedVal, ← List.map_take]
    exact any_embed (embedVal _)
      (fun x => (mapExpr p).eval (.cons x (embedEnv ρ)))
      (fun x => p.eval (.cons x ρ))
      (fun x => ihp (.cons x ρ))
      ((l.eval ρ).take K)
  | mapB K l f ihl ihf =>
    simp only [mapExpr, Expr.eval, ihl ρ, embedVal, ← List.map_take]
    exact map_embed (embedVal _) (embedVal _)
      (fun x => (mapExpr f).eval (.cons x (embedEnv ρ)))
      (fun x => f.eval (.cons x ρ))
      (fun x => ihf (.cons x ρ))
      ((l.eval ρ).take K)
  | foldrB K l z f ihl ihz ihf =>
    simp only [mapExpr, Expr.eval, ihl ρ, ihz ρ, embedVal, ← List.map_take]
    exact foldr_embed (embedVal _) (embedVal _)
      (fun x acc => (mapExpr f).eval (.cons x (.cons acc (embedEnv ρ))))
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => ihf (.cons x (.cons acc ρ)))
      (z.eval ρ) ((l.eval ρ).take K)
  | tset m i a ihm ihi iha =>
    simp only [mapExpr, Expr.eval, ihm ρ, ihi ρ, iha ρ, embedVal]
    funext j; split <;> rfl

theorem expr_cost_le_three_halves {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ t) :
    2 * (mapExpr e).cost + nonNat t ≤ 3 * e.cost := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost]; omega
  | nat n => simp only [mapExpr, Expr.cost, nonNat]; omega
  | add a b iha ihb | sub a b iha ihb =>
    simp only [mapExpr, Expr.cost, nonNat] at *; omega
  | mulK k a iha | divK k a iha | modK k a iha =>
    simp only [mapExpr, Expr.cost, nonNat] at *; omega
  | lt a b iha ihb | eqN a b iha ihb | and a b iha ihb | pair a b iha ihb
  | letE a b iha ihb | cons a b iha ihb | take a b iha ihb =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost] at *; omega
  | not a iha | fst a iha | snd a iha | inl a iha | inr a iha | some a iha
  | len a iha | tconst a iha =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost] at *; omega
  | ite c a b ihc iha ihb | caseOpt c a b ihc iha ihb | caseSum c a b ihc iha ihb =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost] at *; omega
  | appendL K a b iha ihb =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost] at *; omega
  | tget m i ihm ihi =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost] at *; omega
  | tset m i a ihm ihi iha =>
    refine add_nonNat_le _ _ ?_; simp only [mapExpr, Expr.cost] at *; omega
  | findB K l p ihl ihp | anyB K l p ihl ihp | mapB K l p ihl ihp =>
    refine add_nonNat_le _ _ ?_
    simp only [mapExpr, Expr.cost] at ihl ihp ⊢
    have hp : 2 * ((mapExpr p).cost + 1) ≤ 3 * (p.cost + 1) := by omega
    have hK := Nat.mul_le_mul_left K hp
    have hK1 : 2 * (K * ((mapExpr p).cost + 1)) = K * (2 * ((mapExpr p).cost + 1)) := by ring
    have hK2 : 3 * (K * (p.cost + 1)) = K * (3 * (p.cost + 1)) := by ring
    omega
  | foldrB K l z f ihl ihz ihf =>
    refine add_nonNat_le _ _ ?_
    simp only [mapExpr, Expr.cost] at ihl ihz ihf ⊢
    have hf : 2 * ((mapExpr f).cost + 1) ≤ 3 * (f.cost + 1) := by omega
    have hK := Nat.mul_le_mul_left K hf
    have hK1 : 2 * (K * ((mapExpr f).cost + 1)) = K * (2 * ((mapExpr f).cost + 1)) := by ring
    have hK2 : 3 * (K * (f.cost + 1)) = K * (3 * (f.cost + 1)) := by ring
    omega
  | op o a iha =>
    rcases o with o | o
    · cases o with
      | len w =>
        have hw := _root_.ReductionDsl.one_le_bits w.val
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
      | lit w v =>
        have hw := w.2
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
      | cat m n | eq m n =>
        have hm := m.2; have hn := n.2
        refine add_nonNat_le _ _ ?_
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
      | cons b w | take w | drop w =>
        have hw := w.2
        refine add_nonNat_le _ _ ?_
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
      | widen w d =>
        have hw := w.2; have hd := d.2
        refine add_nonNat_le _ _ ?_
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
      | takeK w k =>
        have hw := w.2; have hk := k.2
        refine add_nonNat_le _ _ ?_
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
      | varint =>
        refine add_nonNat_le _ _ ?_
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inl,
          SignalPqxdh.LegacyCosted.pqBytesOps, SignalPqxdh.LegacyCosted.B, nonNat] at iha ⊢
        omega
    · cases o <;>
      · refine add_nonNat_le _ _ ?_
        simp only [mapExpr, mapOpExpr, Expr.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
          SignalPqxdh.LegacyCosted.pqxdhOps, Ops.sum, Sum.elim_inr,
          SignalPqxdh.LegacyCosted.pqU32Ops, SignalPqxdh.LegacyCosted.U32, nonNat] at iha ⊢
        omega

theorem expr_cost_two_mul_le {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ t) :
    2 * (mapExpr e).cost ≤ 3 * e.cost := by
  have := expr_cost_le_three_halves e
  omega

/-! ## Samplers and target interfaces -/

theorem toU8_toLEBytes_16 (w : BitVec 128) :
    CryptoVerification.E2E.toU8 (_root_.ReductionDsl.toLEBytes 16 w) = SignalPqxdh.word128ToBytes w := by
  simp only [CryptoVerification.E2E.toU8, _root_.ReductionDsl.toLEBytes, SignalPqxdh.word128ToBytes,
    List.map_ofFn]
  congr 1; funext i
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [UInt8.ofNat, BitVec.extractLsb'_toNat]

structure AtomicIface {ι : Type} (T : OracleSpec ι) where
  fwdU : (n : ℕ) → OracleComp T (Fin (n + 1))
  Tag : Type
  dom : Tag → Ty pqAtomicSig
  cod : Tag → Ty pqAtomicSig
  enc : (g : Tag) → (dom g).denote → ι
  dec : (g : Tag) → (x : (dom g).denote) → T (enc g x) → (cod g).denote
  qCost : Tag → ℕ

@[reducible] def AtomicIface.toIface {ι : Type} {T : OracleSpec ι} (A : AtomicIface T) :
    Iface pqAtomicSig T where
  fwdU := A.fwdU
  uCost := 1
  Tag := A.Tag
  dom := A.dom
  cod := A.cod
  enc := A.enc
  dec := A.dec
  qCost := A.qCost
  smp := pqAtomicSamplers

@[reducible] def aiOfIface {ι : Type} {T : OracleSpec ι} (I : Iface pqAtomicSig T) :
    AtomicIface T where
  fwdU := I.fwdU
  Tag := I.Tag
  dom := I.dom
  cod := I.cod
  enc := I.enc
  dec := I.dec
  qCost := I.qCost

@[reducible] def aiPrim : AtomicIface SignalPqxdh.PrimBaseSpec := aiOfIface pqPrimIface
@[reducible] def aiSigDdh : AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigAndDdhSpec) :=
  aiOfIface pqSigAndDdhIface
@[reducible] def aiEufCma : AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigOracleSpec) :=
  aiOfIface SignalPqxdh.Costed.pqxdhEufCmaIface
@[reducible] def aiGapDh : AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.gapDhOracleSpec) :=
  aiOfIface SignalPqxdh.Costed.pqGapDhIface
@[reducible] def aiAuthPrim : AtomicIface SignalPqxdh.PrimBaseSpec :=
  aiOfIface SignalPqxdh.Costed.pqAuthPrimIface
@[reducible] def aiAuthEufCma :
    AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigOracleSpec) :=
  aiOfIface SignalPqxdh.Costed.pqAuthEufCmaIface
@[reducible] def aiAuthGapDh :
    AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.gapDhOracleSpec) :=
  aiOfIface SignalPqxdh.Costed.pqAuthGapDhIface
@[reducible] def aiPrfMk :
    AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.prfMsgKeysSpec) :=
  aiOfIface SignalPqxdh.Costed.pqPrfMkIface
@[reducible] def aiPrfHmac :
    AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.prfHmacSpec) :=
  aiOfIface SignalPqxdh.Costed.pqPrfHmacIface
@[reducible] def aiAuthSigDdh :
    AtomicIface (SignalPqxdh.PrimBaseSpec + SignalPqxdh.sigAndDdhSpec) :=
  aiOfIface SignalPqxdh.Costed.pqAuthSigAndDdhIface

def r64W : SignalPqxdh.LegacyCosted.PSamp → ℕ
  | .random64 => 1
  | _ => 0

def mapSamp {ι : Type} {T : OracleSpec ι} (A : AtomicIface T) {Γ : List (Ty pqAtomicSig)} :
    (s : SignalPqxdh.LegacyCosted.PSamp) → Comp pqAtomicOps A.toIface Γ (embedTy s.ty)
  | .bool => Comp.sample (I := A.toIface) UniformSamplerTag.bool .unit
  | .index N => Comp.sample (I := A.toIface) (UniformSamplerTag.index N) .unit
  | .bytes32 =>
    .bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
      (.ret (aop .bv256ToPbytes32 .v0))
  | .random64 =>
    .bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
        (.ret (aop (.pbytesCat 32 32)
          (.pair (aop .bv256ToPbytes32 .v1) (aop .bv256ToPbytes32 .v0)))))
  | .drKey96 =>
    .bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
        (.bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
          (.ret (.pair (aop .bv256ToPbytes32 .v2)
            (.pair (aop .bv256ToPbytes32 .v1) (aop .bv256ToPbytes32 .v0))))))
  | .msgKeys80 =>
    .bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv256) .unit)
        (.bind (Comp.sample (I := A.toIface) (UniformSamplerTag.base .bv128) .unit)
          (.ret (.pair (aop .bv256ToPbytes32 .v2)
            (.pair (aop .bv256ToPbytes32 .v1)
              (aop (.bytesToPbytes 16) (aop .bv128ToBytes16 .v0)))))))

@[simp] theorem mapSamp_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w' : A.Tag → ℕ) {Γ : List (Ty pqAtomicSig)} (s : SignalPqxdh.LegacyCosted.PSamp) :
    (mapSamp A (Γ := Γ) s).queries w' (fun _ => 0) = 0 := by
  cases s <;> simp [mapSamp, Comp.queries]

theorem mapSamp_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    {Γ : List (Ty pqAtomicSig)} (s : SignalPqxdh.LegacyCosted.PSamp) :
    2 * (mapSamp A (Γ := Γ) s).cost ≤ 3 * (1 + s.cost) + 78 * r64W s := by
  cases s <;>
    simp only [mapSamp, r64W, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
      AtomicIface.toIface, pqAtomicSamplers, atomicBaseSamplers, unifSamplers,
      AtomicBaseUnif.cost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
      SignalPqxdh.LegacyCosted.PSamp.cost, SignalPqxdh.LegacyCosted.PSamp.ty,
      SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
      SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
    omega

theorem mapSamp_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (hfwd : A.fwdU = I.fwdU) {Γ : List (Ty pqAtomicSig)}
    (s : SignalPqxdh.LegacyCosted.PSamp) (ρ : Env Γ) :
    (mapSamp A s).eval ρ = embedVal s.ty <$> I.liftP s.run := by
  have hLift : ∀ {α} (p : ProbComp α), A.toIface.liftP p = I.liftP p := by
    intro α p; simp [Iface.liftP, AtomicIface.toIface, hfwd]
  cases s with
  | bool =>
    simp [mapSamp, Comp.eval, hLift, SignalPqxdh.LegacyCosted.PSamp.run, embedVal]
  | index N =>
    have hIdx : SignalPqxdh.LegacyCosted.sampleIndex N = sampleIndex N := rfl
    simp [mapSamp, Comp.eval, hLift, SignalPqxdh.LegacyCosted.PSamp.run, hIdx, embedVal]
  | bytes32 =>
    simp [mapSamp, Comp.eval, Expr.eval, Expr.v0, Env.get, pqAtomicOps, atomicPureOps,
      AtomicPureOp.eval, hLift, hfwd, Iface.liftP, SignalPqxdh.LegacyCosted.PSamp.run,
      SignalPqxdh.sampleBytes32, simulateQ_map, map_eq_bind_pure_comp, embedVal, embedBase]
    rfl
  | random64 =>
    simp [mapSamp, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get, pqAtomicOps, atomicPureOps,
      AtomicPureOp.eval, hLift, hfwd, Iface.liftP, SignalPqxdh.LegacyCosted.PSamp.run,
      SignalPqxdh.sampleRandom64, SignalPqxdh.sampleBytes32, simulateQ_bind, simulateQ_map,
      simulateQ_pure, bind_assoc, embedVal, embedBase]
    rfl
  | drKey96 =>
    simp [mapSamp, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, pqAtomicOps,
      atomicPureOps, AtomicPureOp.eval, hLift, hfwd, Iface.liftP, SignalPqxdh.LegacyCosted.PSamp.run,
      SignalPqxdh.sampleDRKey96, SignalPqxdh.sampleBytes32, SignalPqxdh.LegacyCosted.drKeyV,
      simulateQ_bind, simulateQ_map, simulateQ_pure, bind_assoc, embedVal, embedBase]
    rfl
  | msgKeys80 =>
    simp [mapSamp, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, pqAtomicOps,
      atomicPureOps, AtomicPureOp.eval, hLift, hfwd, Iface.liftP, SignalPqxdh.LegacyCosted.PSamp.run,
      SignalPqxdh.sampleMessageKeys80, SignalPqxdh.sampleBytes32,
      SignalPqxdh.LegacyCosted.msgKeysV, toU8_toLEBytes_16,
      simulateQ_bind, simulateQ_map, simulateQ_pure, bind_assoc, embedVal, embedBase]
    rfl

structure TagLift {ι : Type} {T : OracleSpec ι}
    (I : Iface SignalPqxdh.LegacyCosted.pqSig T) (A : AtomicIface T) where
  hfwd : A.fwdU = I.fwdU
  hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers
  unsupportedW : I.Tag → ℕ
  mapQuery : ∀ {Γ : List (Ty pqAtomicSig)} (g : I.Tag),
    Expr pqAtomicOps Γ (embedTy (I.dom g)) → Comp pqAtomicOps A.toIface Γ (embedTy (I.cod g))
  cost_le : ∀ {Γ} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
    (mapQuery g e).cost ≤ e.cost + I.qCost g
  eval_eq : ∀ {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} (g : I.Tag),
    unsupportedW g = 0 →
    ∀ (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (I.dom g)) (ρ : Env Γ),
      (mapQuery g (mapExpr e)).eval (embedEnv ρ) =
        embedVal (I.cod g) <$>
          (I.dec g (e.eval ρ) <$> (liftM (T.query (I.enc g (e.eval ρ))) : OracleComp T _))

def keyIndUnsupportedPrimW : SignalPqxdh.LegacyCosted.PTag → ℕ
  | .x25519 | .x25519Base | .isCanonical | .pow8 | .sigPkGen
  | .sigSign _ | .sigVerify _ | .kemKeyGen | .kemEncaps | .kemDecaps | .hkdfDerive96 _ => 0
  | _ => 1

def mapKeyIndPrimTag {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {Γ : List (Ty pqAtomicSig)}
    (inj : ∀ (t : PTag),
      Expr pqAtomicOps Γ (t.dom (ℓ := 0) (Pt := Empty)) →
      Comp pqAtomicOps A.toIface Γ (t.cod (ℓ := 0) (Pt := Empty))) :
    (g : SignalPqxdh.LegacyCosted.PTag) →
      Expr pqAtomicOps Γ (embedTy g.dom) → Comp pqAtomicOps A.toIface Γ (embedTy g.cod)
  | .x25519, e => inj .x25519 e
  | .x25519Base, e => inj .x25519Base e
  | .isCanonical, e => inj .isCanonical e
  | .pow8, e => inj .pow8 e
  | .sigPkGen, e => inj .sigPkGen e
  | .sigSign m, e => inj (.sigSign m) e
  | .sigVerify m, e => inj (.sigVerify m) e
  | .kemKeyGen, e => inj .kemKeyGen e
  | .kemEncaps, e => inj .kemEncaps e
  | .kemDecaps, e => inj .kemDecaps e
  | .hkdfDerive96 w, e => inj (.hkdfDerive96 w) e
  | .rootCreateChain, _ =>
    .ret (.pair (aop (.pbytesLit 32 []) .unit)
      (aop (.pbytesLit 32 []) .unit))
  | .chainKdfSeed, _ => .ret (aop (.pbytesLit 32 []) .unit)
  | .chainKdfNext, _ => .ret (aop (.pbytesLit 32 []) .unit)
  | .spqrInitSend _ _, _ => .ret .none
  | .spqrInitRecv _ _, _ => .ret .none
  | .deriveMsgKeys _, _ =>
    .ret (.pair (aop (.pbytesLit 32 []) .unit)
      (.pair (aop (.pbytesLit 32 []) .unit)
        (aop (.pbytesLit 16 []) .unit)))
  | .aeadEnc _ _ c, _ => .ret (aop (.pbytesLit c []) .unit)
  | .aeadDec _ _ _, _ => .ret .none

def mapAuthPrimTag : SignalPqxdh.LegacyCosted.PTag → SignalPqxdh.Costed.AuthPTag
  | .x25519 => .inl .x25519
  | .x25519Base => .inl .x25519Base
  | .isCanonical => .inl .isCanonical
  | .pow8 => .inl .pow8
  | .sigPkGen => .inl .sigPkGen
  | .sigSign m => .inl (.sigSign m)
  | .sigVerify m => .inl (.sigVerify m)
  | .kemKeyGen => .inl .kemKeyGen
  | .kemEncaps => .inl .kemEncaps
  | .kemDecaps => .inl .kemDecaps
  | .hkdfDerive96 w => .inl (.hkdfDerive96 w)
  | .rootCreateChain => .inr .rootCreateChain
  | .chainKdfSeed => .inr .chainKdfSeed
  | .chainKdfNext => .inr .chainKdfNext
  | .spqrInitSend p c => .inr (.spqrInitSend p c)
  | .spqrInitRecv p c => .inr (.spqrInitRecv p c)
  | .deriveMsgKeys s => .inr (.deriveMsgKeys s)
  | .aeadEnc a m c => .inr (.aeadEnc a m c)
  | .aeadDec a c m => .inr (.aeadDec a c m)

def mapAuthPrimQuery {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {Γ : List (Ty pqAtomicSig)}
    (inj : ∀ (t : SignalPqxdh.Costed.AuthPTag),
      Expr pqAtomicOps Γ t.dom → Comp pqAtomicOps A.toIface Γ t.cod) :
    (g : SignalPqxdh.LegacyCosted.PTag) →
      Expr pqAtomicOps Γ (embedTy g.dom) → Comp pqAtomicOps A.toIface Γ (embedTy g.cod)
  | .x25519, e => inj (.inl .x25519) e
  | .x25519Base, e => inj (.inl .x25519Base) e
  | .isCanonical, e => inj (.inl .isCanonical) e
  | .pow8, e => inj (.inl .pow8) e
  | .sigPkGen, e => inj (.inl .sigPkGen) e
  | .sigSign m, e => inj (.inl (.sigSign m)) e
  | .sigVerify m, e => inj (.inl (.sigVerify m)) e
  | .kemKeyGen, e => inj (.inl .kemKeyGen) e
  | .kemEncaps, e => inj (.inl .kemEncaps) e
  | .kemDecaps, e => inj (.inl .kemDecaps) e
  | .hkdfDerive96 w, e => inj (.inl (.hkdfDerive96 w)) e
  | .rootCreateChain, e => inj (.inr .rootCreateChain) e
  | .chainKdfSeed, e => inj (.inr .chainKdfSeed) e
  | .chainKdfNext, e => inj (.inr .chainKdfNext) e
  | .spqrInitSend p c, e => inj (.inr (.spqrInitSend p c)) e
  | .spqrInitRecv p c, e => inj (.inr (.spqrInitRecv p c)) e
  | .deriveMsgKeys s, e => inj (.inr (.deriveMsgKeys s)) e
  | .aeadEnc a m c, e => inj (.inr (.aeadEnc a m c)) e
  | .aeadDec a c m, e => inj (.inr (.aeadDec a c m)) e

private theorem eval_query_of_defeq {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    {Γ : List (Ty pqAtomicSig)} (t' : A.Tag) (e' : Expr pqAtomicOps Γ (A.dom t'))
    (ρ' : Env Γ) (v : (A.dom t').denote) (hv : e'.eval ρ' = v) :
    (Comp.query (I := A.toIface) t' e').eval ρ' =
      A.dec t' v <$> (liftM (T.query (A.enc t' v)) : OracleComp T _) := by
  cases hv; rfl

def tlPrimKeyInd : TagLift SignalPqxdh.LegacyCosted.pqPrimIface aiPrim where
  hfwd := rfl
  hsmp := rfl
  unsupportedW := keyIndUnsupportedPrimW
  mapQuery g e := mapKeyIndPrimTag (fun t e' => Comp.query (I := aiPrim.toIface) t e') g e
  cost_le g e := by
    cases g <;>
      simp only [mapKeyIndPrimTag, Comp.cost, Expr.cost, aiPrim, aiOfIface, pqPrimIface,
        PTag.qCost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost, List.length_nil,
        SignalPqxdh.LegacyCosted.pqPrimIface, SignalPqxdh.LegacyCosted.PTag.dom,
        SignalPqxdh.LegacyCosted.PTag.cod, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, SignalPqxdh.LegacyCosted.drKeyT,
        SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
      omega
  eval_eq g hOk e ρ := by
    cases g <;> simp only [keyIndUnsupportedPrimW] at hOk
    all_goals try contradiction
    all_goals (
      dsimp only [mapKeyIndPrimTag]
      refine Eq.trans (eval_query_of_defeq aiPrim _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]
      first
        | rfl
        | (refine congrArg (· <$> _) (funext fun r => ?_); cases r <;> rfl))

def tlSigDdhKeyInd : TagLift SignalPqxdh.LegacyCosted.pqSigAndDdhIface aiSigDdh where
  hfwd := rfl
  hsmp := rfl
  unsupportedW | .inl t => keyIndUnsupportedPrimW t | .inr _ => 0
  mapQuery
    | .inl t, e =>
      mapKeyIndPrimTag (fun t' e' => Comp.query (I := aiSigDdh.toIface) (Sum.inl t') e') t e
    | .inr (.inl m), e => Comp.query (I := aiSigDdh.toIface) (Sum.inr (Sum.inl m)) e
    | .inr (.inr _), e => Comp.query (I := aiSigDdh.toIface) (Sum.inr (Sum.inr ())) e
  cost_le g e := by
    rcases g with t | (m | u)
    · cases t <;>
        simp only [mapKeyIndPrimTag, Comp.cost, Expr.cost, aiSigDdh, aiOfIface, pqSigAndDdhIface,
          PTag.qCost, pqAtomicOps, atomicPureOps, AtomicPureOp.cost, List.length_nil,
          SignalPqxdh.LegacyCosted.pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiSigDdh, aiOfIface, pqSigAndDdhIface,
        SignalPqxdh.LegacyCosted.pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.sigAndDdhOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
    · cases u
      simp only [Comp.cost, aiSigDdh, aiOfIface, pqSigAndDdhIface,
        SignalPqxdh.LegacyCosted.pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.sigAndDdhOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g hOk e ρ := by
    rcases g with t | (m | u)
    · cases t <;> simp only [keyIndUnsupportedPrimW] at hOk
      all_goals try contradiction
      all_goals (
        dsimp only [mapKeyIndPrimTag]
        refine Eq.trans (eval_query_of_defeq aiSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]
        first
          | rfl
          | (refine congrArg (· <$> _) (funext fun r => ?_); cases r <;> rfl))
    · refine Eq.trans (eval_query_of_defeq aiSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl
    · cases u
      refine Eq.trans (eval_query_of_defeq aiSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlEufCmaKeyInd : TagLift SignalPqxdh.LegacyCosted.pqxdhEufCmaIface aiEufCma where
  hfwd := rfl
  hsmp := rfl
  unsupportedW | .inl t => keyIndUnsupportedPrimW t | .inr _ => 0
  mapQuery
    | .inl t, e =>
      mapKeyIndPrimTag (fun t' e' => Comp.query (I := aiEufCma.toIface) (Sum.inl t') e') t e
    | .inr m, e => Comp.query (I := aiEufCma.toIface) (Sum.inr m) e
  cost_le g e := by
    rcases g with t | m
    · cases t <;>
        simp only [mapKeyIndPrimTag, Comp.cost, Expr.cost, aiEufCma, aiOfIface,
          SignalPqxdh.Costed.pqxdhEufCmaIface, SignalPqxdh.Costed.pqChalIface, PTag.qCost,
          pqAtomicOps, atomicPureOps, AtomicPureOp.cost, List.length_nil,
          SignalPqxdh.LegacyCosted.pqxdhEufCmaIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiEufCma, aiOfIface, SignalPqxdh.Costed.pqxdhEufCmaIface,
        SignalPqxdh.Costed.pqChalIface, SignalPqxdh.Costed.eufCmaSignOracle,
        SignalPqxdh.LegacyCosted.pqxdhEufCmaIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.eufCmaSignOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g hOk e ρ := by
    rcases g with t | m
    · cases t <;> simp only [keyIndUnsupportedPrimW] at hOk
      all_goals try contradiction
      all_goals (
        dsimp only [mapKeyIndPrimTag]
        refine Eq.trans (eval_query_of_defeq aiEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]
        first
          | rfl
          | (refine congrArg (· <$> _) (funext fun r => ?_); cases r <;> rfl))
    · refine Eq.trans (eval_query_of_defeq aiEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlGapDhKeyInd : TagLift SignalPqxdh.LegacyCosted.pqGapDhIface aiGapDh where
  hfwd := rfl
  hsmp := rfl
  unsupportedW | .inl t => keyIndUnsupportedPrimW t | .inr _ => 0
  mapQuery
    | .inl t, e =>
      mapKeyIndPrimTag (fun t' e' => Comp.query (I := aiGapDh.toIface) (Sum.inl t') e') t e
    | .inr _, e => Comp.query (I := aiGapDh.toIface) (Sum.inr ()) e
  cost_le g e := by
    rcases g with t | u
    · cases t <;>
        simp only [mapKeyIndPrimTag, Comp.cost, Expr.cost, aiGapDh, aiOfIface,
          SignalPqxdh.Costed.pqGapDhIface, SignalPqxdh.Costed.pqChalIface, PTag.qCost,
          pqAtomicOps, atomicPureOps, AtomicPureOp.cost, List.length_nil,
          SignalPqxdh.LegacyCosted.pqGapDhIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiGapDh, aiOfIface, SignalPqxdh.Costed.pqGapDhIface,
        SignalPqxdh.Costed.pqChalIface, SignalPqxdh.Costed.gapDhDdhOracle,
        SignalPqxdh.LegacyCosted.pqGapDhIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.gapDhDdhOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g hOk e ρ := by
    rcases g with t | u
    · cases t <;> simp only [keyIndUnsupportedPrimW] at hOk
      all_goals try contradiction
      all_goals (
        dsimp only [mapKeyIndPrimTag]
        refine Eq.trans (eval_query_of_defeq aiGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]
        first
          | rfl
          | (refine congrArg (· <$> _) (funext fun r => ?_); cases r <;> rfl))
    · cases u
      refine Eq.trans (eval_query_of_defeq aiGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlAuthPrim : TagLift SignalPqxdh.LegacyCosted.pqPrimIface aiAuthPrim where
  hfwd := rfl
  hsmp := rfl
  unsupportedW _ := 0
  mapQuery g e := mapAuthPrimQuery (fun t e' => Comp.query (I := aiAuthPrim.toIface) t e') g e
  cost_le g e := by
    cases g <;>
      simp only [mapAuthPrimQuery, Comp.cost, aiAuthPrim, aiOfIface,
        SignalPqxdh.Costed.pqAuthPrimIface, SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost,
        SignalPqxdh.Costed.FirstMsgPTag.qCost, SignalPqxdh.LegacyCosted.pqPrimIface,
        SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
        SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
        SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
      omega
  eval_eq g _ e ρ := by
    cases g with
    | deriveMsgKeys s =>
      dsimp only [mapAuthPrimQuery]
      refine Eq.trans (eval_query_of_defeq aiAuthPrim _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rcases e.eval ρ with ⟨k, _ | bs⟩ <;> rfl
    | spqrInitSend p c =>
      dsimp only [mapAuthPrimQuery]
      refine Eq.trans (eval_query_of_defeq aiAuthPrim _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
      rcases r with _ | ⟨_, _ | _, _⟩ <;> rfl
    | spqrInitRecv p c =>
      dsimp only [mapAuthPrimQuery]
      refine Eq.trans (eval_query_of_defeq aiAuthPrim _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
      rcases r with _ | ⟨_, _ | _⟩ <;> rfl
    | kemEncaps | kemDecaps | aeadDec _ _ _ =>
      dsimp only [mapAuthPrimQuery]
      refine Eq.trans (eval_query_of_defeq aiAuthPrim _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
      cases r <;> rfl
    | _ =>
      dsimp only [mapAuthPrimQuery]
      refine Eq.trans (eval_query_of_defeq aiAuthPrim _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlAuthEufCma : TagLift SignalPqxdh.LegacyCosted.pqxdhEufCmaIface aiAuthEufCma where
  hfwd := rfl
  hsmp := rfl
  unsupportedW _ := 0
  mapQuery
    | .inl t, e =>
      mapAuthPrimQuery (fun t' e' => Comp.query (I := aiAuthEufCma.toIface) (Sum.inl t') e') t e
    | .inr m, e => Comp.query (I := aiAuthEufCma.toIface) (Sum.inr m) e
  cost_le g e := by
    rcases g with t | m
    · cases t <;>
        simp only [mapAuthPrimQuery, Comp.cost, aiAuthEufCma, aiOfIface,
          SignalPqxdh.Costed.pqAuthEufCmaIface, SignalPqxdh.Costed.pqAuthChalIface,
          SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost, SignalPqxdh.Costed.FirstMsgPTag.qCost,
          SignalPqxdh.LegacyCosted.pqxdhEufCmaIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiAuthEufCma, aiOfIface, SignalPqxdh.Costed.pqAuthEufCmaIface,
        SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.eufCmaSignOracle,
        SignalPqxdh.LegacyCosted.pqxdhEufCmaIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.eufCmaSignOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g _ e ρ := by
    rcases g with t | m
    · cases t with
      | deriveMsgKeys s =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rcases e.eval ρ with ⟨k, _ | bs⟩ <;> rfl
      | spqrInitSend p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _, _⟩ <;> rfl
      | spqrInitRecv p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _⟩ <;> rfl
      | kemEncaps | kemDecaps | aeadDec _ _ _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        cases r <;> rfl
      | _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rfl
    · refine Eq.trans (eval_query_of_defeq aiAuthEufCma _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlAuthSigDdh : TagLift SignalPqxdh.LegacyCosted.pqSigAndDdhIface aiAuthSigDdh where
  hfwd := rfl
  hsmp := rfl
  unsupportedW _ := 0
  mapQuery
    | .inl t, e =>
      mapAuthPrimQuery (fun t' e' => Comp.query (I := aiAuthSigDdh.toIface) (Sum.inl t') e') t e
    | .inr (.inl m), e => Comp.query (I := aiAuthSigDdh.toIface) (Sum.inr (Sum.inl m)) e
    | .inr (.inr _), e => Comp.query (I := aiAuthSigDdh.toIface) (Sum.inr (Sum.inr ())) e
  cost_le g e := by
    rcases g with t | (m | u)
    · cases t <;>
        simp only [mapAuthPrimQuery, Comp.cost, aiAuthSigDdh, aiOfIface,
          SignalPqxdh.Costed.pqAuthSigAndDdhIface, SignalPqxdh.Costed.pqAuthChalIface,
          SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost, SignalPqxdh.Costed.FirstMsgPTag.qCost,
          SignalPqxdh.LegacyCosted.pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiAuthSigDdh, aiOfIface, SignalPqxdh.Costed.pqAuthSigAndDdhIface,
        SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.sigAndDdhOracle,
        SignalPqxdh.LegacyCosted.pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.sigAndDdhOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
    · simp only [Comp.cost, aiAuthSigDdh, aiOfIface, SignalPqxdh.Costed.pqAuthSigAndDdhIface,
        SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.sigAndDdhOracle,
        SignalPqxdh.LegacyCosted.pqSigAndDdhIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.sigAndDdhOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g _ e ρ := by
    rcases g with t | (m | ⟨⟩)
    · cases t with
      | deriveMsgKeys s =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rcases e.eval ρ with ⟨k, _ | bs⟩ <;> rfl
      | spqrInitSend p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _, _⟩ <;> rfl
      | spqrInitRecv p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _⟩ <;> rfl
      | kemEncaps | kemDecaps | aeadDec _ _ _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        cases r <;> rfl
      | _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rfl
    · refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl
    · refine Eq.trans (eval_query_of_defeq aiAuthSigDdh _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlAuthGapDh : TagLift SignalPqxdh.LegacyCosted.pqGapDhIface aiAuthGapDh where
  hfwd := rfl
  hsmp := rfl
  unsupportedW _ := 0
  mapQuery
    | .inl t, e =>
      mapAuthPrimQuery (fun t' e' => Comp.query (I := aiAuthGapDh.toIface) (Sum.inl t') e') t e
    | .inr _, e => Comp.query (I := aiAuthGapDh.toIface) (Sum.inr ()) e
  cost_le g e := by
    rcases g with t | u
    · cases t <;>
        simp only [mapAuthPrimQuery, Comp.cost, aiAuthGapDh, aiOfIface,
          SignalPqxdh.Costed.pqAuthGapDhIface, SignalPqxdh.Costed.pqAuthChalIface,
          SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost, SignalPqxdh.Costed.FirstMsgPTag.qCost,
          SignalPqxdh.LegacyCosted.pqGapDhIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiAuthGapDh, aiOfIface, SignalPqxdh.Costed.pqAuthGapDhIface,
        SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.gapDhDdhOracle,
        SignalPqxdh.LegacyCosted.pqGapDhIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.gapDhDdhOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g _ e ρ := by
    rcases g with t | u
    · cases t with
      | deriveMsgKeys s =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rcases e.eval ρ with ⟨k, _ | bs⟩ <;> rfl
      | spqrInitSend p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _, _⟩ <;> rfl
      | spqrInitRecv p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _⟩ <;> rfl
      | kemEncaps | kemDecaps | aeadDec _ _ _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        cases r <;> rfl
      | _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiAuthGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rfl
    · cases u
      refine Eq.trans (eval_query_of_defeq aiAuthGapDh _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

def tlPrfMk : TagLift SignalPqxdh.LegacyCosted.pqPrfMkIface aiPrfMk where
  hfwd := rfl
  hsmp := rfl
  unsupportedW _ := 0
  mapQuery
    | .inl t, e =>
      mapAuthPrimQuery (fun t' e' => Comp.query (I := aiPrfMk.toIface) (Sum.inl t') e') t e
    | .inr s, e => Comp.query (I := aiPrfMk.toIface) (Sum.inr s) e
  cost_le g e := by
    rcases g with t | s
    · cases t <;>
        simp only [mapAuthPrimQuery, Comp.cost, aiPrfMk, aiOfIface,
          SignalPqxdh.Costed.pqPrfMkIface, SignalPqxdh.Costed.pqAuthChalIface,
          SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost, SignalPqxdh.Costed.FirstMsgPTag.qCost,
          SignalPqxdh.LegacyCosted.pqPrfMkIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiPrfMk, aiOfIface, SignalPqxdh.Costed.pqPrfMkIface,
        SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.msgKeyPrfOracle,
        SignalPqxdh.LegacyCosted.pqPrfMkIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.msgKeyPrfOracle, SignalPqxdh.LegacyCosted.saltKeyEncCost,
        SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
        SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat]; omega
  eval_eq g _ e ρ := by
    rcases g with t | s
    · cases t with
      | deriveMsgKeys s =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfMk _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rcases e.eval ρ with ⟨k, _ | bs⟩ <;> rfl
      | spqrInitSend p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfMk _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _, _⟩ <;> rfl
      | spqrInitRecv p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfMk _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _⟩ <;> rfl
      | kemEncaps | kemDecaps | aeadDec _ _ _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfMk _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        cases r <;> rfl
      | _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfMk _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rfl
    · refine Eq.trans (eval_query_of_defeq aiPrfMk _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; cases e.eval ρ <;> rfl

def tlPrfHmac : TagLift SignalPqxdh.LegacyCosted.pqPrfHmacIface aiPrfHmac where
  hfwd := rfl
  hsmp := rfl
  unsupportedW _ := 0
  mapQuery
    | .inl t, e =>
      mapAuthPrimQuery (fun t' e' => Comp.query (I := aiPrfHmac.toIface) (Sum.inl t') e') t e
    | .inr m, e => Comp.query (I := aiPrfHmac.toIface) (Sum.inr m) e
  cost_le g e := by
    rcases g with t | m
    · cases t <;>
        simp only [mapAuthPrimQuery, Comp.cost, aiPrfHmac, aiOfIface,
          SignalPqxdh.Costed.pqPrfHmacIface, SignalPqxdh.Costed.pqAuthChalIface,
          SignalPqxdh.Costed.AuthPTag.qCost, PTag.qCost, SignalPqxdh.Costed.FirstMsgPTag.qCost,
          SignalPqxdh.LegacyCosted.pqPrfHmacIface, SignalPqxdh.LegacyCosted.pqChalIface,
          SignalPqxdh.LegacyCosted.PTag.dom, SignalPqxdh.LegacyCosted.PTag.cod,
          SignalPqxdh.LegacyCosted.Ty.wd, SignalPqxdh.LegacyCosted.B,
          SignalPqxdh.LegacyCosted.drKeyT, SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
        omega
    · simp only [Comp.cost, aiPrfHmac, aiOfIface, SignalPqxdh.Costed.pqPrfHmacIface,
        SignalPqxdh.Costed.pqAuthChalIface, SignalPqxdh.Costed.hmacPrfOracle,
        SignalPqxdh.LegacyCosted.pqPrfHmacIface, SignalPqxdh.LegacyCosted.pqChalIface,
        SignalPqxdh.LegacyCosted.ChallengerOracle.qCost,
        SignalPqxdh.LegacyCosted.hmacPrfOracle, SignalPqxdh.LegacyCosted.Ty.wd,
        SignalPqxdh.LegacyCosted.B, PNat.val_ofNat]; omega
  eval_eq g _ e ρ := by
    rcases g with t | m
    · cases t with
      | deriveMsgKeys s =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfHmac _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rcases e.eval ρ with ⟨k, _ | bs⟩ <;> rfl
      | spqrInitSend p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfHmac _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _, _⟩ <;> rfl
      | spqrInitRecv p c =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfHmac _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        rcases r with _ | ⟨_, _ | _⟩ <;> rfl
      | kemEncaps | kemDecaps | aeadDec _ _ _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfHmac _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; refine congrArg (· <$> _) (funext fun r => ?_)
        cases r <;> rfl
      | _ =>
        dsimp only [mapAuthPrimQuery]
        refine Eq.trans (eval_query_of_defeq aiPrfHmac _ _ _ _ (mapExpr_eval e ρ)) ?_
        rw [Functor.map_map]; rfl
    · refine Eq.trans (eval_query_of_defeq aiPrfHmac _ _ _ _ (mapExpr_eval e ρ)) ?_
      rw [Functor.map_map]; rfl

/-! ## Monadic program translation -/

def castLegacySamp {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers) (s : I.smp.Samp) :
    SignalPqxdh.LegacyCosted.PSamp :=
  cast (congrArg Samplers.Samp hsmp) s

@[simp] theorem castLegacySamp_ty {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers) (s : I.smp.Samp) :
    (castLegacySamp hsmp s).ty = I.smp.sTy s := by
  revert hsmp s
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  rintro (rfl : smp = SignalPqxdh.LegacyCosted.pqSamplers) s
  rfl

def mapSampH {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} (A : AtomicIface T)
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers)
    {Γ : List (Ty pqAtomicSig)} (s : I.smp.Samp) :
    Comp pqAtomicOps A.toIface Γ (embedTy (I.smp.sTy s)) :=
  castLegacySamp_ty hsmp s ▸ mapSamp A (castLegacySamp hsmp s)

theorem mapSampH_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (hfwd : A.fwdU = I.fwdU) (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers)
    {Γ : List (Ty pqAtomicSig)} (s : I.smp.Samp) (ρ : Env Γ) (eVal : (I.smp.sDom s).denote) :
    (mapSampH A hsmp s).eval ρ = embedVal (I.smp.sTy s) <$> I.liftP (I.smp.samp s eVal) := by
  revert hfwd hsmp s eVal
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  intro hfwd hsmp
  dsimp only at hfwd hsmp ⊢
  cases hsmp
  intro s eVal
  exact mapSamp_eval (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost,
    SignalPqxdh.LegacyCosted.pqSamplers⟩) hfwd s ρ

@[simp] theorem mapSampH_queries_zero {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} (A : AtomicIface T)
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers) (w' : A.Tag → ℕ)
    {Γ : List (Ty pqAtomicSig)} (s : I.smp.Samp) :
    (mapSampH A hsmp (Γ := Γ) s).queries w' (fun _ => 0) = 0 := by
  revert hsmp s
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hsmp
  dsimp only at hsmp ⊢
  cases hsmp
  intro s
  exact mapSamp_queries_zero A w' s

def mapSampCast {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) {Γ : List (Ty pqAtomicSig)} (s : I.smp.Samp) :
    Comp pqAtomicOps A.toIface Γ (embedTy (I.smp.sTy s)) :=
  mapSampH A tl.hsmp s

def mapComp {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig} :
    Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t →
      Comp pqAtomicOps A.toIface (embedCtx Γ) (embedTy t)
  | .ret e => .ret (mapExpr e)
  | .bind c k => .bind (mapComp tl c) (mapComp tl k)
  | .ite b c d => .ite (mapExpr b) (mapComp tl c) (mapComp tl d)
  | .caseOpt e n s => .caseOpt (mapExpr e) (mapComp tl n) (mapComp tl s)
  | .caseSum e l r => .caseSum (mapExpr e) (mapComp tl l) (mapComp tl r)
  | .sample s _ => mapSampCast tl s
  | .query g e => tl.mapQuery g (mapExpr e)
  | .iter n e body => .iter n (mapExpr e) (mapComp tl body)
  | .findM K l p => .findM K (mapExpr l) (mapComp tl p)
  | .anyM K l p => .anyM K (mapExpr l) (mapComp tl p)
  | .mapM K l f => .mapM K (mapExpr l) (mapComp tl f)
  | .consumeFirstM K l p mk => .consumeFirstM K (mapExpr l) (mapComp tl p) (mapExpr mk)
  | .foldM K l z f => .foldM K (mapExpr l) (mapExpr z) (mapComp tl f)

private theorem iterM_embed {m : Type → Type} [Monad m] [LawfulMonad m]
    {α α' : Type} (ea : α → α') (f' : α' → m α') (f : α → m α)
    (hf : ∀ a, f' (ea a) = ea <$> f a) :
    ∀ (n : ℕ) (z : α), iterM f' n (ea z) = ea <$> iterM f n z
  | 0, z => by simp [iterM]
  | n + 1, z => by
    simp only [iterM]
    rw [hf z, bind_map_left, map_bind]
    congr 1; funext a
    exact iterM_embed ea f' f hf n a

private theorem findML_embed {m : Type → Type} [Monad m] [LawfulMonad m]
    {α α' : Type} (ea : α → α') (p' : α' → m Bool) (p : α → m Bool)
    (hp : ∀ x, p' (ea x) = p x) :
    ∀ xs : List α, findML p' (xs.map ea) = Option.map ea <$> findML p xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML]
    rw [hp x, findML_embed ea p' p hp xs, map_bind]
    congr 1; funext b; cases b <;> simp

private theorem anyML_embed {m : Type → Type} [Monad m] [LawfulMonad m]
    {α α' : Type} (ea : α → α') (p' : α' → m Bool) (p : α → m Bool)
    (hp : ∀ x, p' (ea x) = p x) :
    ∀ xs : List α, anyML p' (xs.map ea) = anyML p xs
  | [] => by simp [anyML]
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x, anyML_embed ea p' p hp xs]

private theorem mapML_embed {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β α' β' : Type} (ea : α → α') (eb : β → β') (f' : α' → m β') (f : α → m β)
    (hf : ∀ x, f' (ea x) = eb <$> f x) :
    ∀ xs : List α, mapML f' (xs.map ea) = List.map eb <$> mapML f xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML]
    rw [hf x, bind_map_left, map_bind]
    congr 1; funext y
    rw [mapML_embed ea eb f' f hf xs, bind_map_left, map_bind]
    congr 1; funext ys; simp

private theorem consumeFirstML_embed {m : Type → Type} [Monad m] [LawfulMonad m]
    {α α' : Type} (ea : α → α') (p' : α' → m Bool) (p : α → m Bool)
    (mk' : α' → α') (mk : α → α)
    (hp : ∀ x, p' (ea x) = p x) (hmk : ∀ x, mk' (ea x) = ea (mk x)) :
    ∀ xs : List α,
      consumeFirstML p' mk' (xs.map ea) = Prod.map id (List.map ea) <$> consumeFirstML p mk xs
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML]
    rw [hp x, hmk x, map_bind]
    congr 1; funext b
    cases b with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [consumeFirstML_embed ea p' p mk' mk hp hmk xs, bind_map_left, map_bind]
      congr 1; funext r; simp

private theorem foldML_embed {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β α' β' : Type} (ea : α → α') (eb : β → β')
    (f' : α' → β' → m β') (f : α → β → m β)
    (hf : ∀ x acc, f' (ea x) (eb acc) = eb <$> f x acc) :
    ∀ (xs : List α) (z : β), foldML f' (eb z) (xs.map ea) = eb <$> foldML f z xs
  | [], z => by simp [foldML]
  | x :: xs, z => by
    simp only [List.map_cons, foldML]
    rw [hf x z, bind_map_left, map_bind]
    congr 1; funext b'
    exact foldML_embed ea eb f' f hf xs b'

theorem mapComp_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t)
    (hOk : c.queries tl.unsupportedW (fun _ => 0) = 0) (ρ : Env Γ) :
    (mapComp tl c).eval (embedEnv ρ) = embedVal t <$> c.eval ρ := by
  revert hOk ρ
  induction c with
  | ret e => intro _ ρ; simp [mapComp, Comp.eval, mapExpr_eval]
  | bind c k ihc ihk =>
    intro hOk ρ
    simp only [Comp.queries, Nat.add_eq_zero_iff] at hOk
    simp only [mapComp, Comp.eval]
    rw [ihc hOk.1 ρ, bind_map_left, map_bind]
    congr 1; funext x
    exact ihk hOk.2 (.cons x ρ)
  | ite b c d ihc ihd =>
    intro hOk ρ
    simp only [Comp.queries, Nat.max_eq_zero_iff] at hOk
    simp only [mapComp, Comp.eval, mapExpr_eval, embedVal]
    split <;> [exact ihc hOk.1 ρ; exact ihd hOk.2 ρ]
  | caseOpt e n s ihn ihs =>
    intro hOk ρ
    simp only [Comp.queries, Nat.max_eq_zero_iff] at hOk
    simp only [mapComp, Comp.eval, mapExpr_eval]
    cases e.eval ρ with
    | none => exact ihn hOk.1 ρ
    | some x => exact ihs hOk.2 (.cons x ρ)
  | caseSum e l r ihl ihr =>
    intro hOk ρ
    simp only [Comp.queries, Nat.max_eq_zero_iff] at hOk
    simp only [mapComp, Comp.eval, mapExpr_eval]
    cases e.eval ρ with
    | inl x => exact ihl hOk.1 (.cons x ρ)
    | inr y => exact ihr hOk.2 (.cons y ρ)
  | sample s e =>
    intro _ ρ
    exact mapSampH_eval tl.hfwd tl.hsmp s (embedEnv ρ) (e.eval ρ)
  | query g e =>
    intro hOk ρ
    simp only [Comp.queries] at hOk
    simpa [mapComp, Comp.eval] using tl.eval_eq g hOk e ρ
  | iter n e body ihb =>
    intro hOk ρ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [mapComp, Comp.eval, iterM, mapExpr_eval]
    · simp only [Comp.queries, Nat.mul_eq_zero] at hOk
      have hbOk : body.queries tl.unsupportedW (fun _ => 0) = 0 :=
        hOk.resolve_left (Nat.ne_of_gt hn)
      simp only [mapComp, Comp.eval, mapExpr_eval]
      exact iterM_embed (embedVal _)
        (fun a => (mapComp tl body).eval (.cons a (embedEnv ρ)))
        (fun a => body.eval (.cons a ρ))
        (fun a => ihb hbOk (.cons a ρ)) n (e.eval ρ)
  | findM K l p ihp =>
    intro hOk ρ
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [mapComp, Comp.eval, findML, embedVal]
    · simp only [Comp.queries, Nat.mul_eq_zero] at hOk
      have hpOk : p.queries tl.unsupportedW (fun _ => 0) = 0 :=
        hOk.resolve_left (Nat.ne_of_gt hK)
      simp only [mapComp, Comp.eval, mapExpr_eval, embedVal, ← List.map_take]
      have hc := findML_embed (embedVal _)
        (fun x => (mapComp tl p).eval (.cons x (embedEnv ρ)))
        (fun x => p.eval (.cons x ρ))
        (fun x => by simpa [embedVal] using ihp hpOk (.cons x ρ))
        ((l.eval ρ).take K)
      rw [hc]
      congr 1; funext o; cases o <;> rfl
  | anyM K l p ihp =>
    intro hOk ρ
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [mapComp, Comp.eval, anyML, embedVal]
    · simp only [Comp.queries, Nat.mul_eq_zero] at hOk
      have hpOk : p.queries tl.unsupportedW (fun _ => 0) = 0 :=
        hOk.resolve_left (Nat.ne_of_gt hK)
      simp only [mapComp, Comp.eval, mapExpr_eval, embedVal, ← List.map_take]
      simpa [embedVal] using anyML_embed (embedVal _)
        (fun x => (mapComp tl p).eval (.cons x (embedEnv ρ)))
        (fun x => p.eval (.cons x ρ))
        (fun x => by simpa [embedVal] using ihp hpOk (.cons x ρ))
        ((l.eval ρ).take K)
  | mapM K l f ihf =>
    intro hOk ρ
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [mapComp, Comp.eval, mapML, embedVal]
    · simp only [Comp.queries, Nat.mul_eq_zero] at hOk
      have hfOk : f.queries tl.unsupportedW (fun _ => 0) = 0 :=
        hOk.resolve_left (Nat.ne_of_gt hK)
      simp only [mapComp, Comp.eval, mapExpr_eval, embedVal, ← List.map_take]
      exact mapML_embed (embedVal _) (embedVal _)
        (fun x => (mapComp tl f).eval (.cons x (embedEnv ρ)))
        (fun x => f.eval (.cons x ρ))
        (fun x => ihf hfOk (.cons x ρ))
        ((l.eval ρ).take K)
  | consumeFirstM K l p mk ihp =>
    intro hOk ρ
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [mapComp, Comp.eval, consumeFirstML, embedVal]
    · simp only [Comp.queries, Nat.mul_eq_zero] at hOk
      have hpOk : p.queries tl.unsupportedW (fun _ => 0) = 0 :=
        hOk.resolve_left (Nat.ne_of_gt hK)
      simp only [mapComp, Comp.eval, mapExpr_eval, embedVal, ← List.map_take]
      have hc := consumeFirstML_embed (embedVal _)
        (fun x => (mapComp tl p).eval (.cons x (embedEnv ρ)))
        (fun x => p.eval (.cons x ρ))
        (fun x => (mapExpr mk).eval (.cons x (embedEnv ρ)))
        (fun x => mk.eval (.cons x ρ))
        (fun x => by simpa [embedVal] using ihp hpOk (.cons x ρ))
        (fun x => mapExpr_eval mk (.cons x ρ))
        ((l.eval ρ).take K)
      rw [hc]
      rfl
  | foldM K l z f ihf =>
    intro hOk ρ
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [mapComp, Comp.eval, foldML, mapExpr_eval]
    · simp only [Comp.queries, Nat.mul_eq_zero] at hOk
      have hfOk : f.queries tl.unsupportedW (fun _ => 0) = 0 :=
        hOk.resolve_left (Nat.ne_of_gt hK)
      simp only [mapComp, Comp.eval, mapExpr_eval, embedVal, ← List.map_take]
      exact foldML_embed (embedVal _) (embedVal _)
        (fun x acc =>
          (mapComp tl f).eval (.cons x (.cons acc (embedEnv ρ))))
        (fun x acc => f.eval (.cons x (.cons acc ρ)))
        (fun x acc => ihf hfOk (.cons x (.cons acc ρ)))
        ((l.eval ρ).take K) (z.eval ρ)

theorem mapComp_queries_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (w' : A.Tag → ℕ)
    (hw : ∀ {Γ} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
      (tl.mapQuery g e).queries w' (fun _ => 0) ≤ w g)
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t) :
    (mapComp tl c).queries w' (fun _ => 0) ≤ c.queries w ws := by
  induction c with
  | ret _ => simp [mapComp, Comp.queries]
  | bind c k ihc ihk => simp only [mapComp, Comp.queries] at *; omega
  | ite _ c d ihc ihd => simp only [mapComp, Comp.queries] at *; omega
  | caseOpt _ n s ihn ihs => simp only [mapComp, Comp.queries] at *; omega
  | caseSum _ l r ihl ihr => simp only [mapComp, Comp.queries] at *; omega
  | sample s _ => simp [mapComp, mapSampCast]
  | query g e => exact hw g (mapExpr e)
  | iter n _ body ih =>
    simp only [mapComp, Comp.queries]
    exact Nat.mul_le_mul_left n ih
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | consumeFirstM K _ p _ ih
  | foldM K _ _ p ih =>
    simp only [mapComp, Comp.queries]
    exact Nat.mul_le_mul_left K ih

def sampR64W {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers) : I.smp.Samp → ℕ :=
  fun s => r64W (castLegacySamp hsmp s)

theorem sampR64W_le_one {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers) (s : I.smp.Samp) :
    sampR64W hsmp s ≤ 1 := by
  revert hsmp s
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  intro hsmp
  dsimp only at hsmp ⊢
  cases hsmp
  intro s
  have hEq : sampR64W (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost,
      SignalPqxdh.LegacyCosted.pqSamplers⟩) rfl s = r64W s := rfl
  rw [hEq]
  cases s <;> simp [r64W]

theorem sampR64W_le_sCost {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers) (s : I.smp.Samp) :
    65 * sampR64W hsmp s ≤ I.smp.sCost s := by
  revert hsmp s
  rcases I with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  intro hsmp
  dsimp only at hsmp ⊢
  cases hsmp
  intro s
  have hEq : sampR64W (I := ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost,
      SignalPqxdh.LegacyCosted.pqSamplers⟩) rfl s = r64W s := rfl
  rw [hEq]
  cases s <;>
    simp only [r64W, SignalPqxdh.LegacyCosted.pqSamplers, SignalPqxdh.LegacyCosted.PSamp.cost,
      SignalPqxdh.LegacyCosted.PSamp.ty, SignalPqxdh.LegacyCosted.Ty.wd,
      SignalPqxdh.LegacyCosted.B, SignalPqxdh.LegacyCosted.drKeyT,
      SignalPqxdh.LegacyCosted.msgKeysT, PNat.val_ofNat] <;>
    omega

theorem mapSampH_cost_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} (A : AtomicIface T)
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers)
    {Γ : List (Ty pqAtomicSig)} (s : I.smp.Samp) :
    2 * (mapSampH A hsmp (Γ := Γ) s).cost ≤
      3 * (1 + I.smp.sCost s) + 78 * sampR64W hsmp s := by
  revert hsmp s
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hsmp
  dsimp only at hsmp ⊢
  cases hsmp
  intro s
  exact mapSamp_cost_le A s

theorem comp_r64_cost_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers)
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t) :
    66 * c.queries (fun _ => 0) (sampR64W hsmp) ≤ c.cost := by
  induction c with
  | ret _ | query _ _ => simp [Comp.queries, Comp.cost]
  | bind c k ihc ihk => simp only [Comp.queries, Comp.cost] at *; omega
  | ite _ c d ihc ihd => simp only [Comp.queries, Comp.cost] at *; omega
  | caseOpt _ n s ihn ihs => simp only [Comp.queries, Comp.cost] at *; omega
  | caseSum _ l r ihl ihr => simp only [Comp.queries, Comp.cost] at *; omega
  | sample s e =>
    have h1 := sampR64W_le_one hsmp s
    have he := one_le_expr_cost e
    have hs := sampR64W_le_sCost hsmp s
    simp only [Comp.queries, Comp.cost]
    omega
  | iter n _ body ih =>
    simp only [Comp.queries, Comp.cost]
    have hb : 66 * body.queries (fun _ => 0) (sampR64W hsmp) ≤ body.cost + 1 := by omega
    have hMul := Nat.mul_le_mul_left n hb
    have hRing : 66 * (n * body.queries (fun _ => 0) (sampR64W hsmp)) =
        n * (66 * body.queries (fun _ => 0) (sampR64W hsmp)) := by ring
    omega
  | findM K _ p ih | anyM K _ p ih | mapM K _ p ih | foldM K _ _ p ih =>
    simp only [Comp.queries, Comp.cost]
    have hp : 66 * p.queries (fun _ => 0) (sampR64W hsmp) ≤ p.cost + 1 := by omega
    have hMul := Nat.mul_le_mul_left K hp
    have hRing : 66 * (K * p.queries (fun _ => 0) (sampR64W hsmp)) =
        K * (66 * p.queries (fun _ => 0) (sampR64W hsmp)) := by ring
    omega
  | consumeFirstM K _ p mk ih =>
    simp only [Comp.queries, Comp.cost]
    have hp : 66 * p.queries (fun _ => 0) (sampR64W hsmp) ≤ p.cost + mk.cost + 1 := by omega
    have hMul := Nat.mul_le_mul_left K hp
    have hRing : 66 * (K * p.queries (fun _ => 0) (sampR64W hsmp)) =
        K * (66 * p.queries (fun _ => 0) (sampR64W hsmp)) := by ring
    omega

theorem mapComp_cost_two_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t) :
    2 * (mapComp tl c).cost ≤ 3 * c.cost + 78 * c.queries (fun _ => 0) (sampR64W tl.hsmp) := by
  induction c with
  | ret e =>
    have := expr_cost_two_mul_le e
    simp only [mapComp, Comp.cost, Comp.queries]
    omega
  | bind c k ihc ihk =>
    simp only [mapComp, Comp.cost, Comp.queries] at *; omega
  | ite b c d ihc ihd | caseOpt b c d ihc ihd | caseSum b c d ihc ihd =>
    have := expr_cost_two_mul_le b
    simp only [mapComp, Comp.cost, Comp.queries] at *; omega
  | @sample Γ' s e =>
    have he := one_le_expr_cost e
    have hs := mapSampH_cost_le A tl.hsmp (Γ := embedCtx Γ') s
    simp only [mapComp, mapSampCast, Comp.cost, Comp.queries]
    omega
  | query g e =>
    have he := expr_cost_two_mul_le e
    have hq := tl.cost_le g (mapExpr e)
    simp only [mapComp, Comp.cost, Comp.queries]
    omega
  | iter n e body ih =>
    have he := expr_cost_two_mul_le e
    simp only [mapComp, Comp.cost, Comp.queries] at ih ⊢
    have hb : 2 * ((mapComp tl body).cost + 1) ≤
        3 * (body.cost + 1) + 78 * body.queries (fun _ => 0) (sampR64W tl.hsmp) := by omega
    have hMul := Nat.mul_le_mul_left n hb
    have hR1 : 2 * (n * ((mapComp tl body).cost + 1)) =
        n * (2 * ((mapComp tl body).cost + 1)) := by ring
    have hR2 : n * (3 * (body.cost + 1) + 78 * body.queries (fun _ => 0) (sampR64W tl.hsmp)) =
        3 * (n * (body.cost + 1)) + 78 * (n * body.queries (fun _ => 0) (sampR64W tl.hsmp)) := by
      ring
    omega
  | findM K l p ih | anyM K l p ih | mapM K l p ih =>
    have hl := expr_cost_two_mul_le l
    simp only [mapComp, Comp.cost, Comp.queries] at ih ⊢
    have hp : 2 * ((mapComp tl p).cost + 1) ≤
        3 * (p.cost + 1) + 78 * p.queries (fun _ => 0) (sampR64W tl.hsmp) := by omega
    have hMul := Nat.mul_le_mul_left K hp
    have hR1 : 2 * (K * ((mapComp tl p).cost + 1)) =
        K * (2 * ((mapComp tl p).cost + 1)) := by ring
    have hR2 : K * (3 * (p.cost + 1) + 78 * p.queries (fun _ => 0) (sampR64W tl.hsmp)) =
        3 * (K * (p.cost + 1)) + 78 * (K * p.queries (fun _ => 0) (sampR64W tl.hsmp)) := by
      ring
    omega
  | consumeFirstM K l p mk ih =>
    have hl := expr_cost_two_mul_le l
    have hmk := expr_cost_two_mul_le mk
    simp only [mapComp, Comp.cost, Comp.queries] at ih ⊢
    have hp : 2 * ((mapComp tl p).cost + (mapExpr mk).cost + 1) ≤
        3 * (p.cost + mk.cost + 1) + 78 * p.queries (fun _ => 0) (sampR64W tl.hsmp) := by omega
    have hMul := Nat.mul_le_mul_left K hp
    have hR1 :
        2 * (K * ((mapComp tl p).cost + (mapExpr mk).cost + 1)) =
        K * (2 * ((mapComp tl p).cost + (mapExpr mk).cost + 1)) := by
      ring
    have hR2 :
        K * (3 * (p.cost + mk.cost + 1) + 78 * p.queries (fun _ => 0) (sampR64W tl.hsmp)) =
        3 * (K * (p.cost + mk.cost + 1)) +
          78 * (K * p.queries (fun _ => 0) (sampR64W tl.hsmp)) := by ring
    omega
  | foldM K l z f ih =>
    have hl := expr_cost_two_mul_le l
    have hz := expr_cost_two_mul_le z
    simp only [mapComp, Comp.cost, Comp.queries] at ih ⊢
    have hf : 2 * ((mapComp tl f).cost + 1) ≤
        3 * (f.cost + 1) + 78 * f.queries (fun _ => 0) (sampR64W tl.hsmp) := by omega
    have hMul := Nat.mul_le_mul_left K hf
    have hR1 : 2 * (K * ((mapComp tl f).cost + 1)) =
        K * (2 * ((mapComp tl f).cost + 1)) := by ring
    have hR2 : K * (3 * (f.cost + 1) + 78 * f.queries (fun _ => 0) (sampR64W tl.hsmp)) =
        3 * (K * (f.cost + 1)) + 78 * (K * f.queries (fun _ => 0) (sampR64W tl.hsmp)) := by
      ring
    omega

theorem mapComp_cost_eleven_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t) :
    11 * (mapComp tl c).cost ≤ 23 * c.cost := by
  have h1 := mapComp_cost_two_mul_le tl c
  have h2 := comp_r64_cost_le tl.hsmp c
  omega

/-! ## Game codec adapters and reduction lifters -/

def finSidToNatExpr (S : SignalPqxdh.Setup) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ (sidT (ℓ := 0) (Pt := Empty) S)) :
    Expr pqAtomicOps Γ (embedTy SignalPqxdh.LegacyCosted.sidT) :=
  .caseSum e
    (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
      (aop (.finVal S.N_send_opk) (.snd .v0))))
    (.caseSum .v0
      (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
        (aop (.finVal S.N_send_no_opk) (.snd .v0)))))
      (.caseSum .v0
        (.inr (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
          (.pair (aop (.finVal S.N_recv) (.fst (.snd .v0)))
                 (aop (.finVal S.N_opk) (.snd (.snd .v0))))))))
        (.inr (.inr (.inr (.pair (aop (.finVal S.N_id) (.fst .v0))
          (.pair (aop (.finVal S.N_recv) (.fst (.snd .v0)))
                 (aop (.finVal S.N_no_opk) (.snd (.snd .v0))))))))))

def finKeyIndQToNatExpr (S : SignalPqxdh.Setup) {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ ((pqKeyIndCodec S).Q)) :
    Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.keyIndCodec S).Q) :=
  .caseSum e
    (.inl (aop (.finVal S.N_id) .v0))
    (.caseSum .v0
      (.inr (.inl (aop (.finVal S.N_id) .v0)))
      (.caseSum .v0
        (.inr (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
          (aop (.finVal S.N_recv) (.snd .v0))))))
        (.caseSum .v0
          (.inr (.inr (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
            (.pair (aop (.finVal S.N_recv) (.fst (.snd .v0)))
              (aop (.finVal S.N_opk) (.snd (.snd .v0)))))))))
          (.caseSum .v0
            (.inr (.inr (.inr (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
              (.pair (aop (.finVal S.N_send_opk) (.fst (.snd .v0)))
                (.snd (.snd .v0)))))))))
            (.caseSum .v0
              (.inr (.inr (.inr (.inr (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
                (.pair (aop (.finVal S.N_send_no_opk) (.fst (.snd .v0)))
                  (.snd (.snd .v0))))))))))
              (.caseSum .v0
                (.inr (.inr (.inr (.inr (.inr (.inr (.inl (.pair (aop (.finVal S.N_id) (.fst .v0))
                  (.pair (aop (.finVal S.N_recv) (.fst (.snd .v0)))
                    (.pair (aop (.finVal S.N_opk) (.fst (.snd (.snd .v0))))
                      (.snd (.snd (.snd .v0)))))))))))))
                (.caseSum .v0
                  (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
                    (.pair (aop (.finVal S.N_id) (.fst .v0))
                      (.pair (aop (.finVal S.N_recv) (.fst (.snd .v0)))
                        (.pair (aop (.finVal S.N_no_opk) (.fst (.snd (.snd .v0))))
                          (.snd (.snd (.snd .v0))))))))))))))
                  (.caseSum .v0
                    (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
                      (finSidToNatExpr S .v0))))))))))
                    (.caseSum .v0
                      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl .v0))))))))))
                      (.caseSum .v0
                        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
                          (.inl .unit)))))))))))
                        (.caseSum .v0
                          (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
                            (.inl (finSidToNatExpr S .v0)))))))))))))
                          (.caseSum .v0
                            (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
                              (.inr (.inl .v0)))))))))))))
                            (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
                              (.inr (.inr (.pair (aop (.finVal S.N_id) (.fst .v0))
                                (aop (.finVal S.N_recv) (.snd .v0))))))))))))))))))))))))))))

theorem finKeyIndQToNatExpr_v1_cost_le (S : SignalPqxdh.Setup) {σ' : Ty pqAtomicSig} :
    (finKeyIndQToNatExpr S (Γ := [σ', (pqKeyIndCodec S).Q]) .v1).cost ≤ 64 := by
  simp only [finKeyIndQToNatExpr, finSidToNatExpr, Expr.cost, Expr.v0, Expr.v1,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost]
  omega

theorem finKeyIndQToNatExpr_eval (S : SignalPqxdh.Setup) {σ' : Ty pqAtomicSig}
    (s : σ'.denote) (t : SignalPqxdh.KeyIndQuery S) :
    (finKeyIndQToNatExpr S (Γ := [σ', (pqKeyIndCodec S).Q]) .v1).eval
      (.cons s (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
    embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).Q
      ((SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) := by
  cases t with
  | initiateOPK u i b | initiateNoOPK u i b =>
    rcases b with ⟨ikB, spkId, spkB, spkSig, _ | ⟨opkId, opkPk⟩, pqspkId, pqspkB, pqspkSig⟩ <;> rfl
  | acceptOPK k j o h | acceptNoOPK k j o h =>
    rcases h with ⟨ikAPk, ekAPk, spkId, _ | opkId, pqspkId, kemCt⟩ <;> rfl
  | testSession sid | revealSessionKey sid =>
    cases sid <;> rfl
  | _ => rfl

theorem keyIndRdec_embedVal (S : SignalPqxdh.Setup) (t : SignalPqxdh.KeyIndQuery S)
    (v : (SignalPqxdh.LegacyCosted.keyIndCodec S).R.denote) :
    (pqKeyIndCodec S).rdec t (embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).R v) =
      (SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t v := by
  change keyIndRdec (ℓ := 0) (Pt := Empty) (embedVal SignalPqxdh.LegacyCosted.keyIndRT v) =
    SignalPqxdh.LegacyCosted.keyIndRdec v
  rcases v with ⟨⟩ | ⟨ik, s⟩ | pk | ⟨ik, s⟩ | b | h | ⟨dk, h⟩ | ⟨⟩ | dk | ⟨l1, l2, l3, l4⟩ | sk
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases b with ⟨b1, b2, b3, b4, _ | ⟨id5, pk5⟩, b6, b7, b8⟩ <;> rfl
  · rcases h with ⟨h1, h2, h3, _ | id4, h5, h6⟩ <;> rfl
  · rcases h with ⟨h1, h2, h3, _ | id4, h5, h6⟩ <;> rfl
  · rfl
  · rfl
  · simp [embedVal, embedBase, keyIndRdec, SignalPqxdh.LegacyCosted.keyIndRdec]
  · rfl

theorem authQenc_eq {S : SignalPqxdh.Setup} (t : SignalPqxdh.AuthQuery S) :
    (SignalPqxdh.Costed.authCodec S).qenc t =
      embedVal (SignalPqxdh.LegacyCosted.authCodec S).Q
        ((SignalPqxdh.LegacyCosted.authCodec S).qenc t) := by
  cases t with
  | sendOPK u i b m0 m1 | sendNoOPK u i b m0 m1 =>
    rcases b with ⟨ikB, spkId, spkB, spkSig, _ | ⟨opkId, opkPk⟩, pqspkId, pqspkB, pqspkSig⟩ <;> rfl
  | recvOPK k j o msg | recvNoOPK k j o msg =>
    rcases msg with ⟨⟨ikAPk, ekAPk, spkId, _ | opkId, pqspkId, kemCt⟩, eph, pqr, ct⟩ <;> rfl
  | _ => rfl

theorem authRdec_embedVal (S : SignalPqxdh.Setup) (t : SignalPqxdh.AuthQuery S)
    (v : (SignalPqxdh.LegacyCosted.authCodec S).R.denote) :
    (SignalPqxdh.Costed.authCodec S).rdec t
      (embedVal (SignalPqxdh.LegacyCosted.authCodec S).R v) =
    (SignalPqxdh.LegacyCosted.authCodec S).rdec t v := by
  change SignalPqxdh.Costed.authRdec (embedVal SignalPqxdh.LegacyCosted.authRT v) =
    SignalPqxdh.LegacyCosted.authRdec v
  rcases v with
    ⟨⟩ | ⟨ik, s⟩ | pk | ⟨ik, s⟩ | b | m | ⟨dk, rk, ck, m⟩ | ⟨⟩ |
      ⟨dk, rk, ck, pt⟩ | dk | ⟨rk, ck⟩ | ⟨l1, l2, l3, l4⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases b with ⟨b1, b2, b3, b4, _ | ⟨id5, pk5⟩, b6, b7, b8⟩ <;> rfl
  · rcases m with ⟨⟨h1, h2, h3, _ | id4, h5, h6⟩, e1, e2, e3⟩ <;> rfl
  · rcases m with ⟨⟨h1, h2, h3, _ | id4, h5, h6⟩, e1, e2, e3⟩ <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [embedVal, embedBase, SignalPqxdh.Costed.authRdec, SignalPqxdh.LegacyCosted.authRdec]

/-! ### One-stage reduction lifters -/

theorem comp_queries_zero_of_zero {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    {w : I.Tag → ℕ} (hZero : ∀ g, w g = 0)
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t) :
    c.queries w (fun _ => 0) = 0 := by
  induction c <;> simp [Comp.queries, hZero, *]

def liftKeyIndHandle {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.keyIndCodec S).Q] outH) :
    Comp pqAtomicOps A.toIface [embedTy σ, (pqKeyIndCodec S).Q] (embedTy outH) :=
  .bind (.ret (finKeyIndQToNatExpr S .v1))
    (compRename swapHandlerVar (mapComp tl h))

theorem liftKeyIndHandle_cost_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.keyIndCodec S).Q] outH) :
    (liftKeyIndHandle tl S h).cost ≤ (mapComp tl h).cost + 66 := by
  have hc := finKeyIndQToNatExpr_v1_cost_le S (σ' := embedTy σ)
  simp only [liftKeyIndHandle, Comp.cost, compRename_cost]
  omega

theorem liftKeyIndHandle_queries {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup) (w' : A.Tag → ℕ)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.keyIndCodec S).Q] outH) :
    (liftKeyIndHandle tl S h).queries w' (fun _ => 0) =
      (mapComp tl h).queries w' (fun _ => 0) := by
  simp [liftKeyIndHandle, Comp.queries, compRename_queries]

theorem liftKeyIndHandle_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.keyIndCodec S).Q] outH)
    (hOk : h.queries tl.unsupportedW (fun _ => 0) = 0)
    (s : σ.denote) (t : SignalPqxdh.KeyIndQuery S) :
    (liftKeyIndHandle tl S h).eval
      (.cons (embedVal σ s) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
    embedVal outH <$>
      h.eval (.cons s (.cons ((SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) := by
  unfold liftKeyIndHandle
  simp only [Comp.eval, pure_bind]
  have hQ :
      (finKeyIndQToNatExpr S (Γ := [embedTy σ, (pqKeyIndCodec S).Q]) .v1).eval
        (.cons (embedVal σ s) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).Q
        ((SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) :=
    finKeyIndQToNatExpr_eval S (embedVal σ s) t
  rw [hQ]
  rw [compRename_eval (mapComp tl h) swapHandlerVar
    (embedEnv (.cons s (.cons ((SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)))]
  · exact mapComp_eval tl h hOk _
  · intro a v
    dsimp only [embedCtx] at v
    cases v with
    | zero => rfl
    | succ v => cases v with
      | zero => rfl
      | succ v => nomatch v

private theorem env_cons2_eq {S₀ : Sig} {a b : Ty S₀} {x : a.denote} {y y' : b.denote}
    (hy : y = y') :
    (Env.cons x (.cons y .nil) : Env [a, b]) = .cons x (.cons y' .nil) := by
  cases hy; rfl

def liftAuthHandle {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.authCodec S).Q] outH) :
    Comp pqAtomicOps A.toIface
      [embedTy σ, (SignalPqxdh.Costed.authCodec S).Q] (embedTy outH) :=
  mapComp tl h

@[simp] theorem liftAuthHandle_cost {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.authCodec S).Q] outH) :
    (liftAuthHandle tl S h).cost = (mapComp tl h).cost := rfl

@[simp] theorem liftAuthHandle_queries {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup) (w' : A.Tag → ℕ)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.authCodec S).Q] outH) :
    (liftAuthHandle tl S h).queries w' (fun _ => 0) =
      (mapComp tl h).queries w' (fun _ => 0) := rfl

theorem liftAuthHandle_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (hZero : ∀ g, tl.unsupportedW g = 0)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.authCodec S).Q] outH)
    (s : σ.denote) (t : SignalPqxdh.AuthQuery S) :
    (liftAuthHandle tl S h).eval
      (.cons (embedVal σ s) (.cons ((SignalPqxdh.Costed.authCodec S).qenc t) .nil)) =
    embedVal outH <$>
      h.eval (.cons s (.cons ((SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)) :=
  (congrArg (mapComp tl h).eval (env_cons2_eq (authQenc_eq t))).trans
    (mapComp_eval tl h (comp_queries_zero_of_zero hZero h)
      (.cons s (.cons ((SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil)))

@[reducible] def liftKeyInd1Stage {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool out) :
    CostedReduction pqAtomicOps A.toIface (SignalPqxdh.keyIndSpec S) (pqKeyIndCodec S)
      (embedTy rIn) .unit .bool (embedTy out) where
  σ := embedTy R.σ
  init := mapComp tl R.init
  handle := liftKeyIndHandle tl S R.handle
  finish := mapComp tl R.finish

@[reducible] def liftAuth1Stage {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool out) :
    CostedReduction pqAtomicOps A.toIface (SignalPqxdh.authSpec S)
      (SignalPqxdh.Costed.authCodec S) (embedTy rIn) .unit .bool (embedTy out) where
  σ := embedTy R.σ
  init := mapComp tl R.init
  handle := liftAuthHandle tl S R.handle
  finish := mapComp tl R.finish

private theorem simulateQ_stateT_embed {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
    {σ σ' : Type} (es : σ → σ')
    (impl' : QueryImpl (unifSpec + G) (StateT σ' (OracleComp T)))
    (impl : QueryImpl (unifSpec + G) (StateT σ (OracleComp T)))
    (hStep : ∀ q s, (impl' q).run (es s) = Prod.map id es <$> (impl q).run s)
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ s, (simulateQ impl' oa).run (es s) = Prod.map id es <$> (simulateQ impl oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure]
  | query_bind q mx ih =>
    intro s
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, hStep q s, bind_map_left, map_bind]
    congr 1; funext p
    exact ih p.1 p.2

theorem liftKeyInd1Stage_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool out)
    (hInit : R.init.queries tl.unsupportedW (fun _ => 0) = 0)
    (hHandle : R.handle.queries tl.unsupportedW (fun _ => 0) = 0)
    (hFin : R.finish.queries tl.unsupportedW (fun _ => 0) = 0)
    (adv : Unit → OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) Bool) (x : rIn.denote) :
    (liftKeyInd1Stage tl S R).eval adv (embedVal rIn x) = embedVal out <$> R.eval adv x := by
  unfold CostedReduction.eval
  have hI : (mapComp tl R.init).eval (.cons (embedVal rIn x) .nil) =
      embedVal (.prod .unit R.σ) <$> R.init.eval (.cons x .nil) :=
    mapComp_eval tl R.init hInit (.cons x .nil)
  have hStep : ∀ q s,
      ((liftKeyInd1Stage tl S R).impl q).run (embedVal R.σ s) =
        Prod.map id (embedVal R.σ) <$> (R.impl q).run s := by
    intro q s; cases q with
    | inl n =>
      simp [CostedReduction.impl, _root_.ReductionDsl.handlerImpl, liftKeyInd1Stage,
        AtomicIface.toIface, tl.hfwd, StateT.run_lift, map_bind, map_pure]
    | inr t =>
      change (do
        let p ← (liftKeyIndHandle tl S R.handle).eval
          (.cons (embedVal R.σ s) (.cons ((pqKeyIndCodec S).qenc t) .nil))
        pure ((pqKeyIndCodec S).rdec t p.1, p.2)) =
        Prod.map id (embedVal R.σ) <$> (do
          let p ← R.handle.eval
            (.cons s (.cons ((SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))
          pure ((SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t p.1, p.2))
      rw [liftKeyIndHandle_eval tl S R.handle hHandle s t, bind_map_left, map_bind]
      congr 1; funext ⟨v, s'⟩
      have hR : keyIndRdec (ℓ := 0) (Pt := Empty)
          (embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).R v) =
          (SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t v :=
        keyIndRdec_embedVal S t v
      dsimp only [embedVal, pqKeyIndCodec, _root_.ReductionDsl.keyIndCodec]
      rw [hR]
      rfl
  dsimp only [liftKeyInd1Stage]
  rw [hI, bind_map_left, map_bind]
  congr 1; funext ⟨a, s⟩
  dsimp only [embedVal]
  rw [simulateQ_stateT_embed (embedVal R.σ) (liftKeyInd1Stage tl S R).impl R.impl hStep (adv a) s,
    bind_map_left, map_bind]
  congr 1; funext ⟨b, s'⟩
  exact mapComp_eval tl R.finish hFin (.cons s' (.cons b .nil))

theorem liftAuth1Stage_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (hZero : ∀ g, tl.unsupportedW g = 0)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool out)
    (adv : Unit → OracleComp (unifSpec + SignalPqxdh.authSpec S) Bool) (x : rIn.denote) :
    (liftAuth1Stage tl S R).eval adv (embedVal rIn x) = embedVal out <$> R.eval adv x := by
  unfold CostedReduction.eval
  have hI : (mapComp tl R.init).eval (.cons (embedVal rIn x) .nil) =
      embedVal (.prod .unit R.σ) <$> R.init.eval (.cons x .nil) :=
    mapComp_eval tl R.init (comp_queries_zero_of_zero hZero R.init) (.cons x .nil)
  have hStep : ∀ q s,
      ((liftAuth1Stage tl S R).impl q).run (embedVal R.σ s) =
        Prod.map id (embedVal R.σ) <$> (R.impl q).run s := by
    intro q s; cases q with
    | inl n =>
      simp [CostedReduction.impl, _root_.ReductionDsl.handlerImpl, liftAuth1Stage,
        AtomicIface.toIface, tl.hfwd, StateT.run_lift, map_bind, map_pure]
    | inr t =>
      change (do
        let p ← (liftAuthHandle tl S R.handle).eval
          (.cons (embedVal R.σ s) (.cons ((SignalPqxdh.Costed.authCodec S).qenc t) .nil))
        pure ((SignalPqxdh.Costed.authCodec S).rdec t p.1, p.2)) =
        Prod.map id (embedVal R.σ) <$> (do
          let p ← R.handle.eval
            (.cons s (.cons ((SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil))
          pure ((SignalPqxdh.LegacyCosted.authCodec S).rdec t p.1, p.2))
      rw [liftAuthHandle_eval tl S hZero R.handle s t, bind_map_left, map_bind]
      congr 1; funext ⟨v, s'⟩
      have hR := authRdec_embedVal S t v
      dsimp only [embedVal]
      rw [hR]
      rfl
  dsimp only [liftAuth1Stage]
  rw [hI, bind_map_left, map_bind]
  congr 1; funext ⟨a, s⟩
  dsimp only [embedVal]
  rw [simulateQ_stateT_embed (embedVal R.σ) (liftAuth1Stage tl S R).impl R.impl hStep (adv a) s,
    bind_map_left, map_bind]
  congr 1; funext ⟨b, s'⟩
  exact mapComp_eval tl R.finish (comp_queries_zero_of_zero hZero R.finish)
    (.cons s' (.cons b .nil))

/-! ### Two-stage reduction lifters -/

@[reducible] def liftKeyInd2Stage {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out) :
    TwoStageCostedReduction pqAtomicOps A.toIface (SignalPqxdh.keyIndSpec S) (pqKeyIndCodec S)
      (embedTy rIn) .unit .bool (embedTy ch) (embedTy rIn2) (embedTy out) where
  σ := embedTy R.σ
  π := embedTy R.π
  init := mapComp tl R.init
  handlePre := liftKeyIndHandle tl S R.handlePre
  chDone := mapComp tl R.chDone
  resume := mapComp tl R.resume
  handlePost := liftKeyIndHandle tl S R.handlePost
  finish := mapComp tl R.finish

@[reducible] def liftAuth2Stage {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out) :
    TwoStageCostedReduction pqAtomicOps A.toIface (SignalPqxdh.authSpec S)
      (SignalPqxdh.Costed.authCodec S)
      (embedTy rIn) .unit .bool (embedTy ch) (embedTy rIn2) (embedTy out) where
  σ := embedTy R.σ
  π := embedTy R.π
  init := mapComp tl R.init
  handlePre := liftAuthHandle tl S R.handlePre
  chDone := mapComp tl R.chDone
  resume := mapComp tl R.resume
  handlePost := liftAuthHandle tl S R.handlePost
  finish := mapComp tl R.finish

def embedMid {κ : Type} {G : OracleSpec κ} {α : Type}
    {π σ ch : Ty SignalPqxdh.LegacyCosted.pqSig} :
    Mid G α π.denote σ.denote ch.denote →
      Mid G α (embedTy π).denote (embedTy σ).denote (embedTy ch).denote
  | .done a s => .done a (embedVal σ s)
  | .paused t c p s k => .paused t (embedVal ch c) (embedVal π p) (embedVal σ s) k

def projMid {κ : Type} {G : OracleSpec κ} {α : Type}
    {π σ ch : Ty SignalPqxdh.LegacyCosted.pqSig} :
    Mid G α (embedTy π).denote (embedTy σ).denote (embedTy ch).denote →
      Mid G α π.denote σ.denote ch.denote
  | .done a s => .done a (projVal σ s)
  | .paused t c p s k => .paused t (projVal ch c) (projVal π p) (projVal σ s) k

@[simp] theorem embedMid_projMid {κ : Type} {G : OracleSpec κ} {α : Type}
    {π σ ch : Ty SignalPqxdh.LegacyCosted.pqSig}
    (m : Mid G α (embedTy π).denote (embedTy σ).denote (embedTy ch).denote) :
    embedMid (projMid m) = m := by
  cases m <;> simp [embedMid, projMid]

private theorem bind_eval_eq {ι : Type} {T : OracleSpec ι} {α α' β γ : Type}
    (f : α → α') (g : β → γ)
    (m1 : OracleComp T α') (m2 : OracleComp T α)
    (h1 : m1 = f <$> m2)
    (k1 : α' → OracleComp T γ) (k2 : α → OracleComp T β)
    (hk : ∀ x, k1 (f x) = g <$> k2 x) :
    (m1 >>= k1) = g <$> (m2 >>= k2) := by
  subst h1
  rw [bind_map_left, map_bind]
  congr 1; funext x
  exact hk x

theorem run1_keyInd_embed {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out)
    (hPre : R.handlePre.queries tl.unsupportedW (fun _ => 0) = 0)
    {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α) :
    ∀ (f : ℕ) (s : R.σ.denote),
      (liftKeyInd2Stage tl S R).run1 dflt oa f (embedVal R.σ s) =
        embedMid <$> R.run1 dflt oa f s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro f s
    simp [TwoStageCostedReduction.run1, construct_pure, embedMid]
  | query_bind q mx ih =>
    intro f s
    cases q with
    | inl n =>
      unfold TwoStageCostedReduction.run1
      rw [construct_query_bind, construct_query_bind]
      change (A.fwdU n >>= fun u =>
          (liftKeyInd2Stage tl S R).run1 dflt (mx u) f (embedVal R.σ s)) =
        embedMid <$> (I.fwdU n >>= fun u => R.run1 dflt (mx u) f s)
      rw [tl.hfwd, map_bind]
      congr 1; funext u
      exact ih u f s
    | inr t =>
      cases f with
      | zero =>
        simp [TwoStageCostedReduction.run1, construct_query_bind, embedMid]
      | succ f =>
        unfold TwoStageCostedReduction.run1
        rw [construct_query_bind, construct_query_bind]
        dsimp only
        refine bind_eval_eq
          (embedVal (((SignalPqxdh.LegacyCosted.keyIndCodec S).R.prod R.σ).sum
            (ch.prod (R.π.prod R.σ))))
          embedMid _ _ (liftKeyIndHandle_eval tl S R.handlePre hPre s t) _ _ fun x => ?_
        rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · have hR : keyIndRdec (ℓ := 0) (Pt := Empty)
              (embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).R v) =
              (SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t v :=
            keyIndRdec_embedVal S t v
          dsimp only [embedVal, pqKeyIndCodec, _root_.ReductionDsl.keyIndCodec]
          rw [hR]
          exact ih _ f s'
        · simp [embedVal, embedMid]

theorem runFuel_keyInd_embed {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {σ : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.keyIndCodec S).Q]
      (.prod (SignalPqxdh.LegacyCosted.keyIndCodec S).R σ))
    (hOk : h.queries tl.unsupportedW (fun _ => 0) = 0)
    {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) α) :
    ∀ (f : ℕ) (s : σ.denote),
      runFuel (C := pqKeyIndCodec S) (liftKeyIndHandle tl S h) dflt oa f (embedVal σ s) =
        Prod.map id (embedVal σ) <$>
          runFuel (C := SignalPqxdh.LegacyCosted.keyIndCodec S) h dflt oa f s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro f s
    simp [runFuel, construct_pure]
  | query_bind q mx ih =>
    intro f s
    cases q with
    | inl n =>
      unfold runFuel
      rw [construct_query_bind, construct_query_bind]
      change (A.fwdU n >>= fun u =>
          runFuel (C := pqKeyIndCodec S) (liftKeyIndHandle tl S h) dflt (mx u) f (embedVal σ s)) =
        Prod.map id (embedVal σ) <$>
          (I.fwdU n >>= fun u =>
            runFuel (C := SignalPqxdh.LegacyCosted.keyIndCodec S) h dflt (mx u) f s)
      rw [tl.hfwd, map_bind]
      congr 1; funext u
      exact ih u f s
    | inr t =>
      cases f with
      | zero =>
        simp [runFuel, construct_query_bind]
      | succ f =>
        unfold runFuel
        rw [construct_query_bind, construct_query_bind]
        change (do
          let p ← (liftKeyIndHandle tl S h).eval
            (.cons (embedVal σ s) (.cons ((pqKeyIndCodec S).qenc t) .nil))
          runFuel (C := pqKeyIndCodec S) (liftKeyIndHandle tl S h) dflt
            (mx ((pqKeyIndCodec S).rdec t p.1)) f p.2) =
          Prod.map id (embedVal σ) <$> (do
            let p ← h.eval (.cons s (.cons ((SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))
            runFuel (C := SignalPqxdh.LegacyCosted.keyIndCodec S) h dflt
              (mx ((SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t p.1)) f p.2)
        rw [liftKeyIndHandle_eval tl S h hOk s t, bind_map_left, map_bind]
        congr 1; funext ⟨v, s'⟩
        have hR : keyIndRdec (ℓ := 0) (Pt := Empty)
            (embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).R v) =
            (SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t v :=
          keyIndRdec_embedVal S t v
        dsimp only [embedVal, pqKeyIndCodec, _root_.ReductionDsl.keyIndCodec]
        rw [hR]
        exact ih _ f s'

theorem liftKeyInd2Stage_eval1 {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out)
    (hInit : R.init.queries tl.unsupportedW (fun _ => 0) = 0)
    (hPre : R.handlePre.queries tl.unsupportedW (fun _ => 0) = 0)
    (hDone : R.chDone.queries tl.unsupportedW (fun _ => 0) = 0)
    (adv : Unit → OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) Bool)
    (x : rIn.denote) (fuel : ℕ) (dflt : Bool) :
    (liftKeyInd2Stage tl S R).eval1 adv (embedVal rIn x) fuel dflt =
      Prod.map (embedVal ch) embedMid <$> R.eval1 adv x fuel dflt := by
  unfold TwoStageCostedReduction.eval1
  have hI : (mapComp tl R.init).eval (.cons (embedVal rIn x) .nil) =
      embedVal (.prod .unit R.σ) <$> R.init.eval (.cons x .nil) :=
    mapComp_eval tl R.init hInit (.cons x .nil)
  dsimp only [liftKeyInd2Stage]
  rw [hI, bind_map_left, map_bind]
  congr 1; funext ⟨a, s⟩
  dsimp only [embedVal]
  rw [run1_keyInd_embed tl S R hPre dflt (adv a) fuel s, bind_map_left, map_bind]
  congr 1; funext m
  cases m with
  | done b s' =>
    dsimp only [embedMid]
    have hD : (mapComp tl R.chDone).eval (.cons (embedVal R.σ s') (.cons b .nil)) =
        embedVal ch <$> R.chDone.eval (.cons s' (.cons b .nil)) :=
      mapComp_eval tl R.chDone hDone (.cons s' (.cons b .nil))
    rw [hD, bind_map_left, map_bind]
    congr 1
  | paused t c p s' k =>
    simp [embedMid]

theorem liftKeyInd2Stage_eval2 {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out)
    (hRes : R.resume.queries tl.unsupportedW (fun _ => 0) = 0)
    (hPost : R.handlePost.queries tl.unsupportedW (fun _ => 0) = 0)
    (hFin : R.finish.queries tl.unsupportedW (fun _ => 0) = 0)
    (m : Mid (SignalPqxdh.keyIndSpec S) Bool R.π.denote R.σ.denote ch.denote)
    (y : rIn2.denote) (fuel : ℕ) (dflt : Bool) :
    (liftKeyInd2Stage tl S R).eval2 (embedMid m) (embedVal rIn2 y) fuel dflt =
      embedVal out <$> R.eval2 m y fuel dflt := by
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2, embedMid, pure_bind, liftKeyInd2Stage]
    exact mapComp_eval tl R.finish hFin (.cons s (.cons b (.cons y .nil)))
  | paused t c p s k =>
    change (do
      let r1 ← (mapComp tl R.resume).eval
        (.cons (embedVal R.σ s) (.cons (embedVal R.π p) (.cons (embedVal rIn2 y) .nil)))
      let r2 ← runFuel (C := pqKeyIndCodec S) (liftKeyIndHandle tl S R.handlePost) dflt
        (k ((pqKeyIndCodec S).rdec t r1.1)) fuel r1.2
      (mapComp tl R.finish).eval (.cons r2.2 (.cons r2.1 (.cons (embedVal rIn2 y) .nil)))) =
      embedVal out <$> (do
        let r1 ← R.resume.eval (.cons s (.cons p (.cons y .nil)))
        let r2 ← runFuel (C := SignalPqxdh.LegacyCosted.keyIndCodec S) R.handlePost dflt
          (k ((SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t r1.1)) fuel r1.2
        R.finish.eval (.cons r2.2 (.cons r2.1 (.cons y .nil))))
    have hR : (mapComp tl R.resume).eval
        (.cons (embedVal R.σ s) (.cons (embedVal R.π p) (.cons (embedVal rIn2 y) .nil))) =
        embedVal (.prod (SignalPqxdh.LegacyCosted.keyIndCodec S).R R.σ) <$>
          R.resume.eval (.cons s (.cons p (.cons y .nil))) :=
      mapComp_eval tl R.resume hRes (.cons s (.cons p (.cons y .nil)))
    rw [hR, bind_map_left, map_bind]
    congr 1; funext ⟨v, s'⟩
    have hRdec : keyIndRdec (ℓ := 0) (Pt := Empty)
        (embedVal (SignalPqxdh.LegacyCosted.keyIndCodec S).R v) =
        (SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t v :=
      keyIndRdec_embedVal S t v
    have hFuel := runFuel_keyInd_embed tl S R.handlePost hPost dflt
      (k ((SignalPqxdh.LegacyCosted.keyIndCodec S).rdec t v)) fuel s'
    dsimp only [embedVal, pqKeyIndCodec, _root_.ReductionDsl.keyIndCodec] at hFuel ⊢
    rw [hRdec, hFuel, bind_map_left, map_bind]
    congr 1; funext ⟨b, s''⟩
    exact mapComp_eval tl R.finish hFin (.cons s'' (.cons b (.cons y .nil)))

theorem run1_auth_embed {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (hZero : ∀ g, tl.unsupportedW g = 0)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out)
    {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + SignalPqxdh.authSpec S) α) :
    ∀ (f : ℕ) (s : R.σ.denote),
      (liftAuth2Stage tl S R).run1 dflt oa f (embedVal R.σ s) =
        embedMid <$> R.run1 dflt oa f s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro f s
    simp [TwoStageCostedReduction.run1, construct_pure, embedMid]
  | query_bind q mx ih =>
    intro f s
    cases q with
    | inl n =>
      unfold TwoStageCostedReduction.run1
      rw [construct_query_bind, construct_query_bind]
      change (A.fwdU n >>= fun u =>
          (liftAuth2Stage tl S R).run1 dflt (mx u) f (embedVal R.σ s)) =
        embedMid <$> (I.fwdU n >>= fun u => R.run1 dflt (mx u) f s)
      rw [tl.hfwd, map_bind]
      congr 1; funext u
      exact ih u f s
    | inr t =>
      cases f with
      | zero =>
        simp [TwoStageCostedReduction.run1, construct_query_bind, embedMid]
      | succ f =>
        unfold TwoStageCostedReduction.run1
        rw [construct_query_bind, construct_query_bind]
        dsimp only
        refine bind_eval_eq
          (embedVal (((SignalPqxdh.LegacyCosted.authCodec S).R.prod R.σ).sum
            (ch.prod (R.π.prod R.σ))))
          embedMid _ _ (liftAuthHandle_eval tl S hZero R.handlePre s t) _ _ fun x => ?_
        rcases x with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · have hR := authRdec_embedVal S t v
          dsimp only [embedVal]
          rw [hR]
          exact ih _ f s'
        · simp [embedVal, embedMid]

theorem runFuel_auth_embed {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (hZero : ∀ g, tl.unsupportedW g = 0)
    {σ : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.authCodec S).Q]
      (.prod (SignalPqxdh.LegacyCosted.authCodec S).R σ))
    {α : Type} (dflt : α)
    (oa : OracleComp (unifSpec + SignalPqxdh.authSpec S) α) :
    ∀ (f : ℕ) (s : σ.denote),
      runFuel (C := SignalPqxdh.Costed.authCodec S) (liftAuthHandle tl S h) dflt oa f
        (embedVal σ s) =
        Prod.map id (embedVal σ) <$>
          runFuel (C := SignalPqxdh.LegacyCosted.authCodec S) h dflt oa f s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro f s
    simp [runFuel, construct_pure]
  | query_bind q mx ih =>
    intro f s
    cases q with
    | inl n =>
      unfold runFuel
      rw [construct_query_bind, construct_query_bind]
      change (A.fwdU n >>= fun u =>
          runFuel (C := SignalPqxdh.Costed.authCodec S) (liftAuthHandle tl S h) dflt (mx u) f
            (embedVal σ s)) =
        Prod.map id (embedVal σ) <$>
          (I.fwdU n >>= fun u =>
            runFuel (C := SignalPqxdh.LegacyCosted.authCodec S) h dflt (mx u) f s)
      rw [tl.hfwd, map_bind]
      congr 1; funext u
      exact ih u f s
    | inr t =>
      cases f with
      | zero =>
        simp [runFuel, construct_query_bind]
      | succ f =>
        unfold runFuel
        rw [construct_query_bind, construct_query_bind]
        change (do
          let p ← (liftAuthHandle tl S h).eval
            (.cons (embedVal σ s) (.cons ((SignalPqxdh.Costed.authCodec S).qenc t) .nil))
          runFuel (C := SignalPqxdh.Costed.authCodec S) (liftAuthHandle tl S h) dflt
            (mx ((SignalPqxdh.Costed.authCodec S).rdec t p.1)) f p.2) =
          Prod.map id (embedVal σ) <$> (do
            let p ← h.eval (.cons s (.cons ((SignalPqxdh.LegacyCosted.authCodec S).qenc t) .nil))
            runFuel (C := SignalPqxdh.LegacyCosted.authCodec S) h dflt
              (mx ((SignalPqxdh.LegacyCosted.authCodec S).rdec t p.1)) f p.2)
        rw [liftAuthHandle_eval tl S hZero h s t, bind_map_left, map_bind]
        congr 1; funext ⟨v, s'⟩
        have hR := authRdec_embedVal S t v
        dsimp only [embedVal]
        rw [hR]
        exact ih _ f s'

theorem liftAuth2Stage_eval1 {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (hZero : ∀ g, tl.unsupportedW g = 0)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out)
    (adv : Unit → OracleComp (unifSpec + SignalPqxdh.authSpec S) Bool)
    (x : rIn.denote) (fuel : ℕ) (dflt : Bool) :
    (liftAuth2Stage tl S R).eval1 adv (embedVal rIn x) fuel dflt =
      Prod.map (embedVal ch) embedMid <$> R.eval1 adv x fuel dflt := by
  unfold TwoStageCostedReduction.eval1
  have hI : (mapComp tl R.init).eval (.cons (embedVal rIn x) .nil) =
      embedVal (.prod .unit R.σ) <$> R.init.eval (.cons x .nil) :=
    mapComp_eval tl R.init (comp_queries_zero_of_zero hZero R.init) (.cons x .nil)
  dsimp only [liftAuth2Stage]
  rw [hI, bind_map_left, map_bind]
  congr 1; funext ⟨a, s⟩
  dsimp only [embedVal]
  rw [run1_auth_embed tl S hZero R dflt (adv a) fuel s, bind_map_left, map_bind]
  congr 1; funext m
  cases m with
  | done b s' =>
    dsimp only [embedMid]
    have hD : (mapComp tl R.chDone).eval (.cons (embedVal R.σ s') (.cons b .nil)) =
        embedVal ch <$> R.chDone.eval (.cons s' (.cons b .nil)) :=
      mapComp_eval tl R.chDone (comp_queries_zero_of_zero hZero R.chDone)
        (.cons s' (.cons b .nil))
    rw [hD, bind_map_left, map_bind]
    congr 1
  | paused t c p s' k =>
    simp [embedMid]

theorem liftAuth2Stage_eval2 {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (hZero : ∀ g, tl.unsupportedW g = 0)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out)
    (m : Mid (SignalPqxdh.authSpec S) Bool R.π.denote R.σ.denote ch.denote)
    (y : rIn2.denote) (fuel : ℕ) (dflt : Bool) :
    (liftAuth2Stage tl S R).eval2 (embedMid m) (embedVal rIn2 y) fuel dflt =
      embedVal out <$> R.eval2 m y fuel dflt := by
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2, embedMid, pure_bind, liftAuth2Stage]
    exact mapComp_eval tl R.finish (comp_queries_zero_of_zero hZero R.finish)
      (.cons s (.cons b (.cons y .nil)))
  | paused t c p s k =>
    change (do
      let r1 ← (mapComp tl R.resume).eval
        (.cons (embedVal R.σ s) (.cons (embedVal R.π p) (.cons (embedVal rIn2 y) .nil)))
      let r2 ← runFuel (C := SignalPqxdh.Costed.authCodec S) (liftAuthHandle tl S R.handlePost) dflt
        (k ((SignalPqxdh.Costed.authCodec S).rdec t r1.1)) fuel r1.2
      (mapComp tl R.finish).eval (.cons r2.2 (.cons r2.1 (.cons (embedVal rIn2 y) .nil)))) =
      embedVal out <$> (do
        let r1 ← R.resume.eval (.cons s (.cons p (.cons y .nil)))
        let r2 ← runFuel (C := SignalPqxdh.LegacyCosted.authCodec S) R.handlePost dflt
          (k ((SignalPqxdh.LegacyCosted.authCodec S).rdec t r1.1)) fuel r1.2
        R.finish.eval (.cons r2.2 (.cons r2.1 (.cons y .nil))))
    have hR : (mapComp tl R.resume).eval
        (.cons (embedVal R.σ s) (.cons (embedVal R.π p) (.cons (embedVal rIn2 y) .nil))) =
        embedVal (.prod (SignalPqxdh.LegacyCosted.authCodec S).R R.σ) <$>
          R.resume.eval (.cons s (.cons p (.cons y .nil))) :=
      mapComp_eval tl R.resume (comp_queries_zero_of_zero hZero R.resume)
        (.cons s (.cons p (.cons y .nil)))
    rw [hR, bind_map_left, map_bind]
    congr 1; funext ⟨v, s'⟩
    have hRdec := authRdec_embedVal S t v
    have hFuel := runFuel_auth_embed tl S hZero R.handlePost dflt
      (k ((SignalPqxdh.LegacyCosted.authCodec S).rdec t v)) fuel s'
    dsimp only [embedVal] at hFuel ⊢
    rw [hRdec, hFuel, bind_map_left, map_bind]
    congr 1; funext ⟨b, s''⟩
    exact mapComp_eval tl R.finish (comp_queries_zero_of_zero hZero R.finish)
      (.cons s'' (.cons b (.cons y .nil)))

/-! ### Two-stage advantage and query transfer -/

theorem kemShCrExp_eq_of_state_map (P : SignalPqxdh.Primitives)
    (A A' : SignalPqxdh.KemShCrAdv)
    (f : A.State → A'.State)
    (h1 : ∀ pk sk, A'.choosePk pk sk = Prod.map id f <$> A.choosePk pk sk)
    (h2 : ∀ st ss ct, A'.findCollision (f st) ss ct = A.findCollision st ss ct) :
    SignalPqxdh.kemShCrExp P A' = SignalPqxdh.kemShCrExp P A := by
  unfold SignalPqxdh.kemShCrExp
  congr 1; funext ⟨pk, sk⟩
  simp only [h1 pk sk, simulateQ_map, bind_map_left]
  congr 1; funext ⟨pk', st⟩
  congr 1; funext r
  dsimp only [Prod.map, id]
  cases P.kemEncaps pk' r with
  | none => rfl
  | some p => simp only [h2 st p.1 p.2]

theorem kemShCr_eq_of_state_map (P : SignalPqxdh.Primitives)
    (A A' : SignalPqxdh.KemShCrAdv)
    (f : A.State → A'.State)
    (h1 : ∀ pk sk, A'.choosePk pk sk = Prod.map id f <$> A.choosePk pk sk)
    (h2 : ∀ st ss ct, A'.findCollision (f st) ss ct = A.findCollision st ss ct) :
    SignalPqxdh.KemShCr P A' = SignalPqxdh.KemShCr P A := by
  unfold SignalPqxdh.KemShCr
  rw [kemShCrExp_eq_of_state_map P A A' f h1 h2]

theorem kemShCrAdv_bounded_of_state_retract
    {A A' : SignalPqxdh.KemShCrAdv}
    (hq : A'.q_prim = A.q_prim)
    (f : A.State → A'.State) (g : A'.State → A.State)
    (h1 : ∀ pk sk, A'.choosePk pk sk = Prod.map id f <$> A.choosePk pk sk)
    (h2 : ∀ st' ss ct, A'.findCollision st' ss ct = A.findCollision (g st') ss ct)
    (hB : A.Bounded) : A'.Bounded := by
  refine ⟨fun pk sk => ?_, fun st' ss ct => ?_⟩
  · rw [h1 pk sk, hq, isQueryBoundP_map_iff]
    exact hB.1 pk sk
  · rw [h2 st' ss ct, hq]
    exact hB.2 (g st') ss ct

theorem aeadIndCpaExp_eq_of_state_map (P : SignalPqxdh.Primitives)
    (A A' : SignalPqxdh.AeadIndCpaAdv)
    (f : A.State → A'.State)
    (h1 : A'.choose = (fun (ad, m0, m1, st) => (ad, m0, m1, f st)) <$> A.choose)
    (h2 : ∀ st c, A'.dist (f st) c = A.dist st c) :
    SignalPqxdh.aeadIndCpaExp P A' = SignalPqxdh.aeadIndCpaExp P A := by
  unfold SignalPqxdh.aeadIndCpaExp
  congr 1; funext b
  congr 1; funext mk
  simp only [h1, simulateQ_map, bind_map_left]
  congr 1; funext ⟨ad, m0, m1, st⟩
  split
  · rfl
  · simp only [h2 st _]

theorem aeadIndCpa_eq_of_state_map (P : SignalPqxdh.Primitives)
    (A A' : SignalPqxdh.AeadIndCpaAdv)
    (f : A.State → A'.State)
    (h1 : A'.choose = (fun (ad, m0, m1, st) => (ad, m0, m1, f st)) <$> A.choose)
    (h2 : ∀ st c, A'.dist (f st) c = A.dist st c) :
    SignalPqxdh.AeadIndCpa P A' = SignalPqxdh.AeadIndCpa P A := by
  unfold SignalPqxdh.AeadIndCpa
  rw [aeadIndCpaExp_eq_of_state_map P A A' f h1 h2]

theorem aeadIndCpaAdv_bounded_of_state_retract
    {A A' : SignalPqxdh.AeadIndCpaAdv}
    (hq : A'.q_prim = A.q_prim)
    (f : A.State → A'.State) (g : A'.State → A.State)
    (h1 : A'.choose = (fun (ad, m0, m1, st) => (ad, m0, m1, f st)) <$> A.choose)
    (h2 : ∀ st' c, A'.dist st' c = A.dist (g st') c)
    (hB : A.Bounded) : A'.Bounded := by
  refine ⟨?_, fun st' c => ?_⟩
  · rw [h1, hq, isQueryBoundP_map_iff]
    exact hB.1
  · rw [h2 st' c, hq]
    exact hB.2 (g st') c

/-! ## Query-count preservation and `totalCost` bounds -/

theorem tlPrimKeyInd_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqPrimIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqPrimIface.dom g))) :
    (tlPrimKeyInd.mapQuery g e).queries SignalPqxdh.Security.primIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight g := by
  cases g <;>
    simp [tlPrimKeyInd, mapKeyIndPrimTag, Comp.queries,
      SignalPqxdh.Security.primIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight]

theorem tlSigDdhKeyInd_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))) :
    (tlSigDdhKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | (m | u)
  · cases t <;>
      simp [tlSigDdhKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlSigDdhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · cases u
    simp [tlSigDdhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlSigDdhKeyInd_sigW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))) :
    (tlSigDdhKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfaceSigQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight g := by
  rcases g with t | (m | u)
  · cases t <;>
      simp [tlSigDdhKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfaceSigQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
  · simp [tlSigDdhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfaceSigQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
  · cases u
    simp [tlSigDdhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfaceSigQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]

theorem tlSigDdhKeyInd_ddhW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))) :
    (tlSigDdhKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfaceDdhQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight g := by
  rcases g with t | (m | u)
  · cases t <;>
      simp [tlSigDdhKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfaceDdhQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · simp [tlSigDdhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfaceDdhQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · cases u
    simp [tlSigDdhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfaceDdhQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]

theorem tlEufCmaKeyInd_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.dom g))) :
    (tlEufCmaKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | m
  · cases t <;>
      simp [tlEufCmaKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlEufCmaKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlEufCmaKeyInd_chalW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.dom g))) :
    (tlEufCmaKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfaceChalQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight g := by
  rcases g with t | m
  · cases t <;>
      simp [tlEufCmaKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfaceChalQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]
  · simp [tlEufCmaKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfaceChalQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]

theorem tlGapDhKeyInd_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqGapDhIface.dom g))) :
    (tlGapDhKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | u
  · cases t <;>
      simp [tlGapDhKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlGapDhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlGapDhKeyInd_chalW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqGapDhIface.dom g))) :
    (tlGapDhKeyInd.mapQuery g e).queries SignalPqxdh.Security.chalIfaceChalQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight g := by
  rcases g with t | u
  · cases t <;>
      simp [tlGapDhKeyInd, mapKeyIndPrimTag, Comp.queries,
        SignalPqxdh.Security.chalIfaceChalQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]
  · simp [tlGapDhKeyInd, Comp.queries,
      SignalPqxdh.Security.chalIfaceChalQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]

theorem tlAuthPrim_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqPrimIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqPrimIface.dom g))) :
    (tlAuthPrim.mapQuery g e).queries SignalPqxdh.Security.authPrimIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight g := by
  cases g <;>
    simp [tlAuthPrim, mapAuthPrimQuery, Comp.queries,
      SignalPqxdh.Security.authPrimIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight]

theorem tlAuthEufCma_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.dom g))) :
    (tlAuthEufCma.mapQuery g e).queries SignalPqxdh.Security.authChalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | m
  · cases t <;>
      simp [tlAuthEufCma, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlAuthEufCma, Comp.queries,
      SignalPqxdh.Security.authChalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlAuthEufCma_chalW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.dom g))) :
    (tlAuthEufCma.mapQuery g e).queries SignalPqxdh.Security.chalIfaceChalQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight g := by
  rcases g with t | m
  · cases t <;>
      simp [tlAuthEufCma, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.chalIfaceChalQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]
  · simp [tlAuthEufCma, Comp.queries,
      SignalPqxdh.Security.chalIfaceChalQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]

theorem tlAuthSigDdh_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))) :
    (tlAuthSigDdh.mapQuery g e).queries SignalPqxdh.Security.authChalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | (m | ⟨⟩)
  · cases t <;>
      simp [tlAuthSigDdh, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlAuthSigDdh, Comp.queries,
      SignalPqxdh.Security.authChalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlAuthSigDdh, Comp.queries,
      SignalPqxdh.Security.authChalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlAuthSigDdh_sigW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))) :
    (tlAuthSigDdh.mapQuery g e).queries SignalPqxdh.Security.authChalIfaceSigQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight g := by
  rcases g with t | (m | ⟨⟩)
  · cases t <;>
      simp [tlAuthSigDdh, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfaceSigQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
  · simp [tlAuthSigDdh, Comp.queries,
      SignalPqxdh.Security.authChalIfaceSigQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
  · simp [tlAuthSigDdh, Comp.queries,
      SignalPqxdh.Security.authChalIfaceSigQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]

theorem tlAuthSigDdh_ddhW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqSigAndDdhIface.dom g))) :
    (tlAuthSigDdh.mapQuery g e).queries SignalPqxdh.Security.authChalIfaceDdhQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight g := by
  rcases g with t | (m | ⟨⟩)
  · cases t <;>
      simp [tlAuthSigDdh, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfaceDdhQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · simp [tlAuthSigDdh, Comp.queries,
      SignalPqxdh.Security.authChalIfaceDdhQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · simp [tlAuthSigDdh, Comp.queries,
      SignalPqxdh.Security.authChalIfaceDdhQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]

theorem tlAuthGapDh_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqGapDhIface.dom g))) :
    (tlAuthGapDh.mapQuery g e).queries SignalPqxdh.Security.authChalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | u
  · cases t <;>
      simp [tlAuthGapDh, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlAuthGapDh, Comp.queries,
      SignalPqxdh.Security.authChalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlAuthGapDh_chalW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqGapDhIface.dom g))) :
    (tlAuthGapDh.mapQuery g e).queries SignalPqxdh.Security.chalIfaceChalQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight g := by
  rcases g with t | u
  · cases t <;>
      simp [tlAuthGapDh, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.chalIfaceChalQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]
  · simp [tlAuthGapDh, Comp.queries,
      SignalPqxdh.Security.chalIfaceChalQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]

theorem tlPrfMk_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqPrfMkIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqPrfMkIface.dom g))) :
    (tlPrfMk.mapQuery g e).queries SignalPqxdh.Security.authChalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | s
  · cases t <;>
      simp [tlPrfMk, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlPrfMk, Comp.queries,
      SignalPqxdh.Security.authChalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlPrfMk_chalW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqPrfMkIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqPrfMkIface.dom g))) :
    (tlPrfMk.mapQuery g e).queries SignalPqxdh.Security.chalIfaceChalQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight g := by
  rcases g with t | s
  · cases t <;>
      simp [tlPrfMk, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.chalIfaceChalQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]
  · simp [tlPrfMk, Comp.queries,
      SignalPqxdh.Security.chalIfaceChalQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]

theorem tlPrfHmac_primW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqPrfHmacIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqPrfHmacIface.dom g))) :
    (tlPrfHmac.mapQuery g e).queries SignalPqxdh.Security.authChalIfacePrimQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight g := by
  rcases g with t | m
  · cases t <;>
      simp [tlPrfHmac, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.authChalIfacePrimQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
  · simp [tlPrfHmac, Comp.queries,
      SignalPqxdh.Security.authChalIfacePrimQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]

theorem tlPrfHmac_chalW {Γ : List (Ty pqAtomicSig)}
    (g : SignalPqxdh.LegacyCosted.pqPrfHmacIface.Tag)
    (e : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqPrfHmacIface.dom g))) :
    (tlPrfHmac.mapQuery g e).queries SignalPqxdh.Security.chalIfaceChalQueryWeight
      (fun _ => 0) ≤ SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight g := by
  rcases g with t | m
  · cases t <;>
      simp [tlPrfHmac, mapAuthPrimQuery, Comp.queries,
        SignalPqxdh.Security.chalIfaceChalQueryWeight,
        SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]
  · simp [tlPrfHmac, Comp.queries,
      SignalPqxdh.Security.chalIfaceChalQueryWeight,
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight]

@[simp] theorem samplerZeroQueryWeight_eq {Samp : Type} :
    (SignalPqxdh.Security.samplerZeroQueryWeight : Samp → ℕ) = (fun _ => 0) :=
  rfl

theorem liftKeyInd1Stage_totalQueries_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (w' : A.Tag → ℕ)
    (hw : ∀ {Γ} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
      (tl.mapQuery g e).queries w' (fun _ => 0) ≤ w g)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool out) (q : ℕ) :
    (liftKeyInd1Stage tl S R).totalQueries w' SignalPqxdh.Security.samplerZeroQueryWeight q ≤
      R.totalQueries w ws q := by
  have hH : (liftKeyInd1Stage tl S R).handle.queries w'
      SignalPqxdh.Security.samplerZeroQueryWeight ≤ R.handle.queries w ws :=
    (liftKeyIndHandle_queries tl S w' R.handle).le.trans (mapComp_queries_le tl w ws w' hw R.handle)
  exact Nat.add_le_add (Nat.add_le_add (mapComp_queries_le tl w ws w' hw R.init)
    (Nat.mul_le_mul_left q hH))
    (mapComp_queries_le tl w ws w' hw R.finish)

theorem liftKeyInd2Stage_totalQueries_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (w' : A.Tag → ℕ)
    (hw : ∀ {Γ} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
      (tl.mapQuery g e).queries w' (fun _ => 0) ≤ w g)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out) (q : ℕ) :
    (liftKeyInd2Stage tl S R).totalQueries w' SignalPqxdh.Security.samplerZeroQueryWeight q ≤
      R.totalQueries w ws q := by
  have hPre : (liftKeyInd2Stage tl S R).handlePre.queries w'
      SignalPqxdh.Security.samplerZeroQueryWeight ≤ R.handlePre.queries w ws :=
    (liftKeyIndHandle_queries tl S w' R.handlePre).le.trans
      (mapComp_queries_le tl w ws w' hw R.handlePre)
  have hPost : (liftKeyInd2Stage tl S R).handlePost.queries w'
      SignalPqxdh.Security.samplerZeroQueryWeight ≤ R.handlePost.queries w ws :=
    (liftKeyIndHandle_queries tl S w' R.handlePost).le.trans
      (mapComp_queries_le tl w ws w' hw R.handlePost)
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (mapComp_queries_le tl w ws w' hw R.init)
    (Nat.mul_le_mul_left q (max_le_max hPre hPost)))
    (max_le_max
      (mapComp_queries_le tl w ws w' hw R.chDone)
      (mapComp_queries_le tl w ws w' hw R.resume)))
    (mapComp_queries_le tl w ws w' hw R.finish)

theorem liftAuth1Stage_totalQueries_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (w' : A.Tag → ℕ)
    (hw : ∀ {Γ} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
      (tl.mapQuery g e).queries w' (fun _ => 0) ≤ w g)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool out) (q : ℕ) :
    (liftAuth1Stage tl S R).totalQueries w' SignalPqxdh.Security.samplerZeroQueryWeight q ≤
      R.totalQueries w ws q := by
  unfold CostedReduction.totalQueries liftAuth1Stage SignalPqxdh.Security.samplerZeroQueryWeight
  dsimp only
  exact Nat.add_le_add (Nat.add_le_add (mapComp_queries_le tl w ws w' hw R.init)
    (Nat.mul_le_mul_left q (mapComp_queries_le tl w ws w' hw R.handle)))
    (mapComp_queries_le tl w ws w' hw R.finish)

theorem liftAuth2Stage_totalQueries_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : SignalPqxdh.Setup)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (w' : A.Tag → ℕ)
    (hw : ∀ {Γ} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
      (tl.mapQuery g e).queries w' (fun _ => 0) ≤ w g)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out) (q : ℕ) :
    (liftAuth2Stage tl S R).totalQueries w' SignalPqxdh.Security.samplerZeroQueryWeight q ≤
      R.totalQueries w ws q := by
  unfold TwoStageCostedReduction.totalQueries liftAuth2Stage
    SignalPqxdh.Security.samplerZeroQueryWeight
  dsimp only
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (mapComp_queries_le tl w ws w' hw R.init)
    (Nat.mul_le_mul_left q (max_le_max
      (mapComp_queries_le tl w ws w' hw R.handlePre)
      (mapComp_queries_le tl w ws w' hw R.handlePost))))
    (max_le_max
      (mapComp_queries_le tl w ws w' hw R.chDone)
      (mapComp_queries_le tl w ws w' hw R.resume)))
    (mapComp_queries_le tl w ws w' hw R.finish)

theorem liftKeyInd1Stage_totalCost_eleven_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool out) (q : ℕ) :
    11 * (liftKeyInd1Stage tl S R).totalCost q ≤ 23 * R.totalCost q + 694 * q := by
  have hI := mapComp_cost_eleven_mul_le tl R.init
  have hH := mapComp_cost_eleven_mul_le tl R.handle
  have hF := mapComp_cost_eleven_mul_le tl R.finish
  have hHC := liftKeyIndHandle_cost_le tl S R.handle
  have hPer : 11 * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64) ≤
      23 * max 1 (R.handle.cost + 32) + 694 := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 11 * (q * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64)) =
      q * (11 * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64)) := by ring
  have hR2 : q * (23 * max 1 (R.handle.cost + 32) + 694) =
      23 * (q * max 1 (R.handle.cost + 32)) + 694 * q := by ring
  rw [← hR1, hR2] at hMul
  change 11 * ((mapComp tl R.init).cost +
      q * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64) +
      (mapComp tl R.finish).cost) ≤
    23 * (R.init.cost + q * max I.uCost (R.handle.cost + 32) + R.finish.cost) + 694 * q
  rw [hu]
  omega

theorem liftKeyInd1Stage_totalCost_two_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool out) (q : ℕ) :
    2 * (liftKeyInd1Stage tl S R).totalCost q ≤
      3 * R.totalCost q + 78 * R.totalQueries (fun _ => 0) (sampR64W tl.hsmp) q + 164 * q := by
  have hI := mapComp_cost_two_mul_le tl R.init
  have hH := mapComp_cost_two_mul_le tl R.handle
  have hF := mapComp_cost_two_mul_le tl R.finish
  have hHC := liftKeyIndHandle_cost_le tl S R.handle
  have hPer : 2 * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64) ≤
      3 * max 1 (R.handle.cost + 32) +
        78 * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp) + 164 := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 2 * (q * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64)) =
      q * (2 * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64)) := by ring
  have hR2 : q * (3 * max 1 (R.handle.cost + 32) +
        78 * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp) + 164) =
      3 * (q * max 1 (R.handle.cost + 32)) +
        78 * (q * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp)) + 164 * q := by ring
  rw [← hR1, hR2] at hMul
  change 2 * ((mapComp tl R.init).cost +
      q * max 1 ((liftKeyIndHandle tl S R.handle).cost + 64) +
      (mapComp tl R.finish).cost) ≤
    3 * (R.init.cost + q * max I.uCost (R.handle.cost + 32) + R.finish.cost) +
      78 * (R.init.queries (fun _ => 0) (sampR64W tl.hsmp) +
        q * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp) +
        R.finish.queries (fun _ => 0) (sampR64W tl.hsmp)) + 164 * q
  rw [hu]
  omega

theorem liftKeyInd2Stage_totalCost_eleven_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out) (q : ℕ) :
    11 * (liftKeyInd2Stage tl S R).totalCost q ≤ 23 * R.totalCost q + 694 * q := by
  have hI := mapComp_cost_eleven_mul_le tl R.init
  have hPre := mapComp_cost_eleven_mul_le tl R.handlePre
  have hPost := mapComp_cost_eleven_mul_le tl R.handlePost
  have hDone := mapComp_cost_eleven_mul_le tl R.chDone
  have hRes := mapComp_cost_eleven_mul_le tl R.resume
  have hFin := mapComp_cost_eleven_mul_le tl R.finish
  have hPreC := liftKeyIndHandle_cost_le tl S R.handlePre
  have hPostC := liftKeyIndHandle_cost_le tl S R.handlePost
  have hCR : 11 * max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost ≤
      23 * max R.chDone.cost R.resume.cost := by omega
  have hPer : 11 * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64) ≤
      23 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) + 694 := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 11 * (q * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64)) =
      q * (11 * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64)) := by ring
  have hR2 : q * (23 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) + 694) =
      23 * (q * max 1 (max R.handlePre.cost R.handlePost.cost + 32)) + 694 * q := by ring
  rw [← hR1, hR2] at hMul
  change 11 * ((mapComp tl R.init).cost +
      q * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64) +
      max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost +
      (mapComp tl R.finish).cost) ≤
    23 * (R.init.cost + q * max I.uCost (max R.handlePre.cost R.handlePost.cost + 32) +
      max R.chDone.cost R.resume.cost + R.finish.cost) + 694 * q
  rw [hu]
  omega

theorem liftAuth1Stage_totalCost_eleven_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool out) (q : ℕ) :
    11 * (liftAuth1Stage tl S R).totalCost q ≤ 23 * R.totalCost q := by
  have hI := mapComp_cost_eleven_mul_le tl R.init
  have hH := mapComp_cost_eleven_mul_le tl R.handle
  have hF := mapComp_cost_eleven_mul_le tl R.finish
  have hPer : 11 * max 1 ((mapComp tl R.handle).cost + 32) ≤
      23 * max 1 (R.handle.cost + 32) := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 11 * (q * max 1 ((mapComp tl R.handle).cost + 32)) =
      q * (11 * max 1 ((mapComp tl R.handle).cost + 32)) := by ring
  have hR2 : q * (23 * max 1 (R.handle.cost + 32)) =
      23 * (q * max 1 (R.handle.cost + 32)) := by ring
  rw [← hR1, hR2] at hMul
  change 11 * ((mapComp tl R.init).cost +
      q * max 1 ((mapComp tl R.handle).cost + 32) +
      (mapComp tl R.finish).cost) ≤
    23 * (R.init.cost + q * max I.uCost (R.handle.cost + 32) + R.finish.cost)
  rw [hu]
  omega

theorem liftAuth2Stage_totalCost_eleven_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out) (q : ℕ) :
    11 * (liftAuth2Stage tl S R).totalCost q ≤ 23 * R.totalCost q := by
  have hI := mapComp_cost_eleven_mul_le tl R.init
  have hPre := mapComp_cost_eleven_mul_le tl R.handlePre
  have hPost := mapComp_cost_eleven_mul_le tl R.handlePost
  have hDone := mapComp_cost_eleven_mul_le tl R.chDone
  have hRes := mapComp_cost_eleven_mul_le tl R.resume
  have hFin := mapComp_cost_eleven_mul_le tl R.finish
  have hCR : 11 * max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost ≤
      23 * max R.chDone.cost R.resume.cost := by omega
  have hPer : 11 * max 1 (max (mapComp tl R.handlePre).cost
        (mapComp tl R.handlePost).cost + 32) ≤
      23 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 11 * (q * max 1 (max (mapComp tl R.handlePre).cost
        (mapComp tl R.handlePost).cost + 32)) =
      q * (11 * max 1 (max (mapComp tl R.handlePre).cost
        (mapComp tl R.handlePost).cost + 32)) := by ring
  have hR2 : q * (23 * max 1 (max R.handlePre.cost R.handlePost.cost + 32)) =
      23 * (q * max 1 (max R.handlePre.cost R.handlePost.cost + 32)) := by ring
  rw [← hR1, hR2] at hMul
  change 11 * ((mapComp tl R.init).cost +
      q * max 1 (max (mapComp tl R.handlePre).cost (mapComp tl R.handlePost).cost + 32) +
      max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost +
      (mapComp tl R.finish).cost) ≤
    23 * (R.init.cost + q * max I.uCost (max R.handlePre.cost R.handlePost.cost + 32) +
      max R.chDone.cost R.resume.cost + R.finish.cost)
  rw [hu]
  omega

theorem liftAuth2Stage_totalCost_two_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out) (q : ℕ) :
    2 * (liftAuth2Stage tl S R).totalCost q ≤
      3 * R.totalCost q + 78 * R.totalQueries (fun _ => 0) (sampR64W tl.hsmp) q := by
  have hI := mapComp_cost_two_mul_le tl R.init
  have hPre := mapComp_cost_two_mul_le tl R.handlePre
  have hPost := mapComp_cost_two_mul_le tl R.handlePost
  have hDone := mapComp_cost_two_mul_le tl R.chDone
  have hRes := mapComp_cost_two_mul_le tl R.resume
  have hFin := mapComp_cost_two_mul_le tl R.finish
  have hCR : 2 * max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost ≤
      3 * max R.chDone.cost R.resume.cost +
        78 * max (R.chDone.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.resume.queries (fun _ => 0) (sampR64W tl.hsmp)) := by omega
  have hPer : 2 * max 1 (max (mapComp tl R.handlePre).cost
        (mapComp tl R.handlePost).cost + 32) ≤
      3 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) +
        78 * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp)) := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 2 * (q * max 1 (max (mapComp tl R.handlePre).cost
        (mapComp tl R.handlePost).cost + 32)) =
      q * (2 * max 1 (max (mapComp tl R.handlePre).cost
        (mapComp tl R.handlePost).cost + 32)) := by ring
  have hR2 : q * (3 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) +
        78 * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp))) =
      3 * (q * max 1 (max R.handlePre.cost R.handlePost.cost + 32)) +
        78 * (q * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp))) := by ring
  rw [← hR1, hR2] at hMul
  change 2 * ((mapComp tl R.init).cost +
      q * max 1 (max (mapComp tl R.handlePre).cost (mapComp tl R.handlePost).cost + 32) +
      max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost +
      (mapComp tl R.finish).cost) ≤
    3 * (R.init.cost + q * max I.uCost (max R.handlePre.cost R.handlePost.cost + 32) +
      max R.chDone.cost R.resume.cost + R.finish.cost) +
      78 * (R.init.queries (fun _ => 0) (sampR64W tl.hsmp) +
        q * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp)) +
        max (R.chDone.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.resume.queries (fun _ => 0) (sampR64W tl.hsmp)) +
        R.finish.queries (fun _ => 0) (sampR64W tl.hsmp))
  rw [hu]
  omega

theorem liftAuth1Stage_totalCost_two_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool out) (q : ℕ) :
    2 * (liftAuth1Stage tl S R).totalCost q ≤
      3 * R.totalCost q + 78 * R.totalQueries (fun _ => 0) (sampR64W tl.hsmp) q := by
  have hI := mapComp_cost_two_mul_le tl R.init
  have hH := mapComp_cost_two_mul_le tl R.handle
  have hF := mapComp_cost_two_mul_le tl R.finish
  have hPer : 2 * max 1 ((mapComp tl R.handle).cost + 32) ≤
      3 * max 1 (R.handle.cost + 32) +
        78 * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp) := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 2 * (q * max 1 ((mapComp tl R.handle).cost + 32)) =
      q * (2 * max 1 ((mapComp tl R.handle).cost + 32)) := by ring
  have hR2 : q * (3 * max 1 (R.handle.cost + 32) +
        78 * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp)) =
      3 * (q * max 1 (R.handle.cost + 32)) +
        78 * (q * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp)) := by ring
  rw [← hR1, hR2] at hMul
  change 2 * ((mapComp tl R.init).cost +
      q * max 1 ((mapComp tl R.handle).cost + 32) +
      (mapComp tl R.finish).cost) ≤
    3 * (R.init.cost + q * max I.uCost (R.handle.cost + 32) + R.finish.cost) +
      78 * (R.init.queries (fun _ => 0) (sampR64W tl.hsmp) +
        q * R.handle.queries (fun _ => 0) (sampR64W tl.hsmp) +
        R.finish.queries (fun _ => 0) (sampR64W tl.hsmp))
  rw [hu]
  omega

/-! ## Syntactic program-size bounds -/

@[simp] theorem exprRename_size {S : Sig} {O : Ops S} :
    ∀ {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ {a}, Var Γ a → Var Δ a) (e : Expr O Γ t),
      (exprRename ξ e).size = e.size
  | _, _, _, _, .var _ | _, _, _, _, .unit | _, _, _, _, .bool _
  | _, _, _, _, .nat _ | _, _, _, _, .none | _, _, _, _, .nil => rfl
  | _, _, _, ξ, .add a b | _, _, _, ξ, .sub a b | _, _, _, ξ, .lt a b
  | _, _, _, ξ, .eqN a b | _, _, _, ξ, .and a b | _, _, _, ξ, .pair a b
  | _, _, _, ξ, .cons a b | _, _, _, ξ, .take a b | _, _, _, ξ, .appendL _ a b
  | _, _, _, ξ, .tget a b | _, _, _, ξ, .letE a b
  | _, _, _, ξ, .findB _ a b | _, _, _, ξ, .anyB _ a b | _, _, _, ξ, .mapB _ a b => by
    simp only [exprRename, Expr.size, exprRename_size _ a, exprRename_size _ b]
  | _, _, _, ξ, .mulK _ a | _, _, _, ξ, .divK _ a | _, _, _, ξ, .modK _ a
  | _, _, _, ξ, .not a | _, _, _, ξ, .fst a | _, _, _, ξ, .snd a
  | _, _, _, ξ, .inl a | _, _, _, ξ, .inr a | _, _, _, ξ, .some a
  | _, _, _, ξ, .op _ a | _, _, _, ξ, .len a | _, _, _, ξ, .tconst a => by
    simp only [exprRename, Expr.size, exprRename_size _ a]
  | _, _, _, ξ, .ite c a b | _, _, _, ξ, .tset c a b
  | _, _, _, ξ, .caseOpt c a b | _, _, _, ξ, .caseSum c a b
  | _, _, _, ξ, .foldrB _ c a b => by
    simp only [exprRename, Expr.size, exprRename_size _ c, exprRename_size _ a, exprRename_size _ b]

@[simp] theorem compRename_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    ∀ {Γ Δ : List (Ty S)} {t : Ty S} (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp O I Γ t),
      (compRename ξ c).size = c.size
  | _, _, _, _, .ret _ | _, _, _, _, .sample _ _ | _, _, _, _, .query _ _ => by
    simp only [compRename, Comp.size, exprRename_size]
  | _, _, _, ξ, .bind c k => by
    simp only [compRename, Comp.size, compRename_size _ c, compRename_size _ k]
  | _, _, _, ξ, .ite b c d | _, _, _, ξ, .caseOpt b c d | _, _, _, ξ, .caseSum b c d => by
    simp only [compRename, Comp.size, exprRename_size, compRename_size _ c, compRename_size _ d]
  | _, _, _, ξ, .iter _ e body
  | _, _, _, ξ, .findM _ e body | _, _, _, ξ, .anyM _ e body | _, _, _, ξ, .mapM _ e body => by
    simp only [compRename, Comp.size, exprRename_size, compRename_size _ body]
  | _, _, _, ξ, .consumeFirstM _ l p mk => by
    simp only [compRename, Comp.size, exprRename_size, compRename_size _ p]
  | _, _, _, ξ, .foldM _ l z f => by
    simp only [compRename, Comp.size, exprRename_size, compRename_size _ f]

def pqOpLitSize : SignalPqxdh.LegacyCosted.pqxdhOps.Op → ℕ
  | .inl (.lit _ v) => v.length
  | .inl (.cons _ _) => 1
  | .inr (.lit _) => 4
  | _ => 0

@[simp] theorem pqxdhOps_opSize (o : SignalPqxdh.LegacyCosted.pqxdhOps.Op) :
    SignalPqxdh.LegacyCosted.pqxdhOps.opSize o = 0 := by
  cases o <;> rfl

@[simp] theorem mapOpExpr_size {Γ : List (Ty pqAtomicSig)}
    (o : SignalPqxdh.LegacyCosted.pqxdhOps.Op)
    (a : Expr pqAtomicOps Γ (embedTy (SignalPqxdh.LegacyCosted.pqxdhOps.dom o))) :
    (mapOpExpr o a).size = a.size + pqOpLitSize o + 1 := by
  rcases o with o | o <;> cases o <;> rfl

def exprLitSize : {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} →
    {t : Ty SignalPqxdh.LegacyCosted.pqSig} →
    Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _
  | _, _, .nat _ | _, _, .none | _, _, .nil => 0
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b
  | _, _, .eqN a b | _, _, .and a b | _, _, .pair a b
  | _, _, .cons a b | _, _, .take a b | _, _, .appendL _ a b
  | _, _, .tget a b | _, _, .letE a b
  | _, _, .findB _ a b | _, _, .anyB _ a b | _, _, .mapB _ a b =>
    exprLitSize a + exprLitSize b
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a
  | _, _, .not a | _, _, .fst a | _, _, .snd a
  | _, _, .inl a | _, _, .inr a | _, _, .some a
  | _, _, .len a | _, _, .tconst a =>
    exprLitSize a
  | _, _, .op o a => exprLitSize a + pqOpLitSize o
  | _, _, .ite c a b | _, _, .tset c a b
  | _, _, .caseOpt c a b | _, _, .caseSum c a b
  | _, _, .foldrB _ c a b =>
    exprLitSize c + exprLitSize a + exprLitSize b

@[simp] theorem mapExpr_size :
    ∀ {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
      (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ t),
      (mapExpr e).size = e.size + exprLitSize e
  | _, _, .var _ | _, _, .unit | _, _, .bool _
  | _, _, .nat _ | _, _, .none | _, _, .nil => rfl
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b
  | _, _, .eqN a b | _, _, .and a b | _, _, .pair a b
  | _, _, .cons a b | _, _, .take a b | _, _, .appendL _ a b
  | _, _, .tget a b | _, _, .letE a b
  | _, _, .findB _ a b | _, _, .anyB _ a b | _, _, .mapB _ a b => by
    simp only [mapExpr, Expr.size, exprLitSize, mapExpr_size a, mapExpr_size b]; omega
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a
  | _, _, .not a | _, _, .fst a | _, _, .snd a
  | _, _, .inl a | _, _, .inr a | _, _, .some a
  | _, _, .len a | _, _, .tconst a => by
    simp only [mapExpr, Expr.size, exprLitSize, mapExpr_size a]; omega
  | _, _, .op o a => by
    simp only [mapExpr, Expr.size, exprLitSize, pqxdhOps_opSize, mapOpExpr_size, mapExpr_size a]
    omega
  | _, _, .ite c a b | _, _, .tset c a b
  | _, _, .caseOpt c a b | _, _, .caseSum c a b
  | _, _, .foldrB _ c a b => by
    simp only [mapExpr, Expr.size, exprLitSize, mapExpr_size c, mapExpr_size a, mapExpr_size b]
    omega

theorem one_le_expr_size {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : 1 ≤ e.size := by
  cases e <;> simp only [Expr.size, bits] <;> omega

theorem mapSamp_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    {Γ : List (Ty pqAtomicSig)} (s : SignalPqxdh.LegacyCosted.PSamp) :
    (mapSamp A (Γ := Γ) s).size ≤ 19 := by
  cases s <;>
    simp only [mapSamp, Comp.size, Expr.size, aop, pqAtomicOps, atomicPureOps,
      AtomicPureOp.opSize, Expr.v0, Expr.v1, Expr.v2] <;>
    omega

theorem mapSampH_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} (A : AtomicIface T)
    (hsmp : I.smp = SignalPqxdh.LegacyCosted.pqSamplers)
    {Γ : List (Ty pqAtomicSig)} (s : I.smp.Samp) :
    (mapSampH A hsmp (Γ := Γ) s).size ≤ 19 := by
  revert hsmp s
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hsmp
  dsimp only at hsmp ⊢
  cases hsmp
  intro s
  exact mapSamp_size_le A s

def TagLift.QuerySizeLe {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) : Prop :=
  ∀ {Γ : List (Ty pqAtomicSig)} (g : I.Tag) (e : Expr pqAtomicOps Γ (embedTy (I.dom g))),
    (tl.mapQuery g e).size ≤ e.size + 9

private theorem mapKeyIndPrimTag_size_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {Γ : List (Ty pqAtomicSig)}
    (inj : ∀ (t : PTag),
      Expr pqAtomicOps Γ (t.dom (ℓ := 0) (Pt := Empty)) →
      Comp pqAtomicOps A.toIface Γ (t.cod (ℓ := 0) (Pt := Empty)))
    (hinj : ∀ t e', (inj t e').size = e'.size + 1)
    (g : SignalPqxdh.LegacyCosted.PTag) (e : Expr pqAtomicOps Γ (embedTy g.dom)) :
    (mapKeyIndPrimTag inj g e).size ≤ e.size + 9 := by
  cases g <;>
    simp only [mapKeyIndPrimTag, hinj, Comp.size, Expr.size, aop, pqAtomicOps, atomicPureOps,
      AtomicPureOp.opSize, List.length_nil] <;>
    omega

private theorem mapAuthPrimQuery_size_le {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {Γ : List (Ty pqAtomicSig)}
    (inj : ∀ (t : SignalPqxdh.Costed.AuthPTag),
      Expr pqAtomicOps Γ t.dom → Comp pqAtomicOps A.toIface Γ t.cod)
    (hinj : ∀ t e', (inj t e').size = e'.size + 1)
    (g : SignalPqxdh.LegacyCosted.PTag) (e : Expr pqAtomicOps Γ (embedTy g.dom)) :
    (mapAuthPrimQuery inj g e).size ≤ e.size + 9 := by
  cases g <;> simp only [mapAuthPrimQuery, hinj] <;> omega

theorem tlPrimKeyInd_sizeLe : tlPrimKeyInd.QuerySizeLe := fun g e =>
  mapKeyIndPrimTag_size_le _ (fun _ _ => rfl) g e

theorem tlSigDdhKeyInd_sizeLe : tlSigDdhKeyInd.QuerySizeLe := by
  intro Γ g e
  rcases g with t | (m | u)
  · dsimp only [tlSigDdhKeyInd]
    exact mapKeyIndPrimTag_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlEufCmaKeyInd_sizeLe : tlEufCmaKeyInd.QuerySizeLe := by
  intro Γ g e
  rcases g with t | m
  · dsimp only [tlEufCmaKeyInd]
    exact mapKeyIndPrimTag_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlGapDhKeyInd_sizeLe : tlGapDhKeyInd.QuerySizeLe := by
  intro Γ g e
  rcases g with t | u
  · dsimp only [tlGapDhKeyInd]
    exact mapKeyIndPrimTag_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlAuthPrim_sizeLe : tlAuthPrim.QuerySizeLe := fun g e =>
  mapAuthPrimQuery_size_le _ (fun _ _ => rfl) g e

theorem tlAuthEufCma_sizeLe : tlAuthEufCma.QuerySizeLe := by
  intro Γ g e
  rcases g with t | m
  · dsimp only [tlAuthEufCma]
    exact mapAuthPrimQuery_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlAuthSigDdh_sizeLe : tlAuthSigDdh.QuerySizeLe := by
  intro Γ g e
  rcases g with t | (m | u)
  · dsimp only [tlAuthSigDdh]
    exact mapAuthPrimQuery_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlAuthGapDh_sizeLe : tlAuthGapDh.QuerySizeLe := by
  intro Γ g e
  rcases g with t | u
  · dsimp only [tlAuthGapDh]
    exact mapAuthPrimQuery_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlPrfMk_sizeLe : tlPrfMk.QuerySizeLe := by
  intro Γ g e
  rcases g with t | s
  · dsimp only [tlPrfMk]
    exact mapAuthPrimQuery_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

theorem tlPrfHmac_sizeLe : tlPrfHmac.QuerySizeLe := by
  intro Γ g e
  rcases g with t | m
  · dsimp only [tlPrfHmac]
    exact mapAuthPrimQuery_size_le _ (fun _ _ => rfl) t e
  · exact Nat.add_le_add_left (by decide : 1 ≤ 9) e.size

def compLitSize {ι : Type} {T : OracleSpec ι} {I : Iface SignalPqxdh.LegacyCosted.pqSig T} :
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} → {t : Ty SignalPqxdh.LegacyCosted.pqSig} →
    Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t → ℕ
  | _, _, .ret e | _, _, .query _ e => exprLitSize e
  | _, _, .sample _ _ => 0
  | _, _, .bind c k => compLitSize c + compLitSize k
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprLitSize b + compLitSize c + compLitSize d
  | _, _, .iter _ e body | _, _, .findM _ e body | _, _, .anyM _ e body | _, _, .mapM _ e body =>
    exprLitSize e + compLitSize body
  | _, _, .consumeFirstM _ l p mk => exprLitSize l + compLitSize p + exprLitSize mk
  | _, _, .foldM _ l z f => exprLitSize l + exprLitSize z + compLitSize f

def red1LitSize {ι κ : Type} {T : OracleSpec ι} {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    {G : OracleSpec κ} {C : GameCodec SignalPqxdh.LegacyCosted.pqSig G}
    {rIn gIn gOut out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I G C rIn gIn gOut out) : ℕ :=
  compLitSize R.init + compLitSize R.handle + compLitSize R.finish

def red2LitSize {ι κ : Type} {T : OracleSpec ι} {I : Iface SignalPqxdh.LegacyCosted.pqSig T}
    {G : OracleSpec κ} {C : GameCodec SignalPqxdh.LegacyCosted.pqSig G}
    {rIn gIn gOut ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I G C rIn gIn gOut ch rIn2 out) : ℕ :=
  compLitSize R.init + compLitSize R.handlePre + compLitSize R.chDone +
    compLitSize R.resume + compLitSize R.handlePost + compLitSize R.finish

theorem mapComp_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) :
    ∀ {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {t : Ty SignalPqxdh.LegacyCosted.pqSig}
      (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps I Γ t),
      (mapComp tl c).size ≤ 10 * c.size + compLitSize c
  | _, _, .ret e => by
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .bind c k => by
    have ihc := mapComp_size_le tl htl c
    have ihk := mapComp_size_le tl htl k
    simp only [mapComp, Comp.size, compLitSize]; omega
  | _, _, .ite b c d => by
    have ihc := mapComp_size_le tl htl c
    have ihd := mapComp_size_le tl htl d
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .caseOpt b c d => by
    have ihc := mapComp_size_le tl htl c
    have ihd := mapComp_size_le tl htl d
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .caseSum b c d => by
    have ihc := mapComp_size_le tl htl c
    have ihd := mapComp_size_le tl htl d
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | Γ', _, .sample s e => by
    have he := one_le_expr_size e
    have hs := mapSampH_size_le A tl.hsmp (Γ := embedCtx Γ') s
    simp only [mapComp, mapSampCast, Comp.size, compLitSize]; omega
  | _, _, .query g e => by
    have he := one_le_expr_size e
    have hq := htl g (mapExpr e)
    rw [mapExpr_size] at hq
    simp only [mapComp, Comp.size, compLitSize]; omega
  | _, _, .iter n e body => by
    have ih := mapComp_size_le tl htl body
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .findM K l p => by
    have ih := mapComp_size_le tl htl p
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .anyM K l p => by
    have ih := mapComp_size_le tl htl p
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .mapM K l p => by
    have ih := mapComp_size_le tl htl p
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .consumeFirstM K l p mk => by
    have ih := mapComp_size_le tl htl p
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega
  | _, _, .foldM K l z f => by
    have ih := mapComp_size_le tl htl f
    simp only [mapComp, Comp.size, compLitSize, mapExpr_size]; omega

theorem finKeyIndQToNatExpr_v1_size_le (S : SignalPqxdh.Setup) {σ' : Ty pqAtomicSig} :
    (finKeyIndQToNatExpr S (Γ := [σ', (pqKeyIndCodec S).Q]) .v1).size ≤ 400 := by
  simp only [finKeyIndQToNatExpr, finSidToNatExpr, Expr.size, aop, pqAtomicOps, atomicPureOps,
    AtomicPureOp.opSize, Expr.v0, Expr.v1]
  omega

theorem liftKeyIndHandle_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) (S : SignalPqxdh.Setup)
    {σ outH : Ty SignalPqxdh.LegacyCosted.pqSig}
    (h : Comp SignalPqxdh.LegacyCosted.pqxdhOps I
      [σ, (SignalPqxdh.LegacyCosted.keyIndCodec S).Q] outH) :
    (liftKeyIndHandle tl S h).size ≤ 10 * h.size + compLitSize h + 402 := by
  have hq := finKeyIndQToNatExpr_v1_size_le S (σ' := embedTy σ)
  have hm := mapComp_size_le tl htl h
  simp only [liftKeyIndHandle, Comp.size, compRename_size]
  omega

theorem liftKeyInd1Stage_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool out) :
    (liftKeyInd1Stage tl S R).size ≤ 10 * R.size + red1LitSize R + 402 := by
  have hI : (liftKeyInd1Stage tl S R).init.size ≤ 10 * R.init.size + compLitSize R.init :=
    mapComp_size_le tl htl R.init
  have hH : (liftKeyInd1Stage tl S R).handle.size ≤
      10 * R.handle.size + compLitSize R.handle + 402 :=
    liftKeyIndHandle_size_le tl htl S R.handle
  have hF : (liftKeyInd1Stage tl S R).finish.size ≤ 10 * R.finish.size + compLitSize R.finish :=
    mapComp_size_le tl htl R.finish
  unfold CostedReduction.size red1LitSize
  omega

theorem liftKeyInd2Stage_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out) :
    (liftKeyInd2Stage tl S R).size ≤ 10 * R.size + red2LitSize R + 804 := by
  have hI : (liftKeyInd2Stage tl S R).init.size ≤ 10 * R.init.size + compLitSize R.init :=
    mapComp_size_le tl htl R.init
  have hPre : (liftKeyInd2Stage tl S R).handlePre.size ≤
      10 * R.handlePre.size + compLitSize R.handlePre + 402 :=
    liftKeyIndHandle_size_le tl htl S R.handlePre
  have hD : (liftKeyInd2Stage tl S R).chDone.size ≤ 10 * R.chDone.size + compLitSize R.chDone :=
    mapComp_size_le tl htl R.chDone
  have hR : (liftKeyInd2Stage tl S R).resume.size ≤ 10 * R.resume.size + compLitSize R.resume :=
    mapComp_size_le tl htl R.resume
  have hPost : (liftKeyInd2Stage tl S R).handlePost.size ≤
      10 * R.handlePost.size + compLitSize R.handlePost + 402 :=
    liftKeyIndHandle_size_le tl htl S R.handlePost
  have hF : (liftKeyInd2Stage tl S R).finish.size ≤ 10 * R.finish.size + compLitSize R.finish :=
    mapComp_size_le tl htl R.finish
  unfold TwoStageCostedReduction.size red2LitSize
  omega

theorem liftAuth1Stage_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) (S : SignalPqxdh.Setup)
    {rIn out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : CostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool out) :
    (liftAuth1Stage tl S R).size ≤ 10 * R.size + red1LitSize R := by
  have hI : (liftAuth1Stage tl S R).init.size ≤ 10 * R.init.size + compLitSize R.init :=
    mapComp_size_le tl htl R.init
  have hH : (liftAuth1Stage tl S R).handle.size ≤ 10 * R.handle.size + compLitSize R.handle :=
    mapComp_size_le tl htl R.handle
  have hF : (liftAuth1Stage tl S R).finish.size ≤ 10 * R.finish.size + compLitSize R.finish :=
    mapComp_size_le tl htl R.finish
  unfold CostedReduction.size red1LitSize
  omega

theorem liftAuth2Stage_size_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.authSpec S)
      (SignalPqxdh.LegacyCosted.authCodec S) rIn .unit .bool ch rIn2 out) :
    (liftAuth2Stage tl S R).size ≤ 10 * R.size + red2LitSize R := by
  have hI : (liftAuth2Stage tl S R).init.size ≤ 10 * R.init.size + compLitSize R.init :=
    mapComp_size_le tl htl R.init
  have hPre : (liftAuth2Stage tl S R).handlePre.size ≤
      10 * R.handlePre.size + compLitSize R.handlePre :=
    mapComp_size_le tl htl R.handlePre
  have hD : (liftAuth2Stage tl S R).chDone.size ≤ 10 * R.chDone.size + compLitSize R.chDone :=
    mapComp_size_le tl htl R.chDone
  have hR : (liftAuth2Stage tl S R).resume.size ≤ 10 * R.resume.size + compLitSize R.resume :=
    mapComp_size_le tl htl R.resume
  have hPost : (liftAuth2Stage tl S R).handlePost.size ≤
      10 * R.handlePost.size + compLitSize R.handlePost :=
    mapComp_size_le tl htl R.handlePost
  have hF : (liftAuth2Stage tl S R).finish.size ≤ 10 * R.finish.size + compLitSize R.finish :=
    mapComp_size_le tl htl R.finish
  unfold TwoStageCostedReduction.size red2LitSize
  omega

theorem param_le_stepCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) :
    2 * b.q_total + 2 * min b.q_total S.N_dh + 2 * min b.q_total S.N_sess_tot +
      Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot + 1 ≤
      SignalPqxdh.Security.stepCostBudget S b := by
  unfold SignalPqxdh.Security.stepCostBudget
  dsimp only
  have h0 : 2 * b.q_total + 1 ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) := by nlinarith
  have h1 : 2 * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) ≤
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 1 * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) ≤
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem bits_le_bits_stepCostBudget {k : ℕ} (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (hk : k ≤ 2 * b.q_total + 2 * min b.q_total S.N_dh + 2 * min b.q_total S.N_sess_tot +
      Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot + 1) :
    bits k ≤ bits (SignalPqxdh.Security.stepCostBudget S b) :=
  Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono
    (le_trans hk (param_le_stepCostBudget S b))

theorem bits_mul_le_two_bits_stepCostBudget {k₁ k₂ : ℕ}
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (h₁ : k₁ ≤ 2 * b.q_total + 2 * min b.q_total S.N_dh + 2 * min b.q_total S.N_sess_tot +
      Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot + 1)
    (h₂ : k₂ ≤ 2 * b.q_total + 2 * min b.q_total S.N_dh + 2 * min b.q_total S.N_sess_tot +
      Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot + 1) :
    bits (k₁ * k₂) ≤ 2 * bits (SignalPqxdh.Security.stepCostBudget S b) := by
  have hm := Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mul_le k₁ k₂
  have hb₁ := bits_le_bits_stepCostBudget S b h₁
  have hb₂ := bits_le_bits_stepCostBudget S b h₂
  omega

theorem atomicSize_le_budget {sz C₀ C₁ : ℕ} (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 11)
    (hSz : sz ≤ C₀ + C₁ * bits (SignalPqxdh.Security.stepCostBudget S b)) :
    sz ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * bits (SignalPqxdh.Security.stepCostBudget S b) :=
  Computational.Proofs.ReductionDsl.SizeBudgetBridge.size_le_budget_of_log_cost h₀ h₁ hSz

end Computational.Proofs.SignalPqxdh.AtomicLift

