/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds
public import Computational.Proofs.LibsignalCli.MainHaltedPrefixCore -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.CompositionHaltedWitness -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedStartSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogs -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.KindRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHalted -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedInst -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.MacroLift
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Per-Kind and Clamped Cost Bounds for Halted Composition Reductions

Proves online-clamped (`onlineClampedBudget b`) total and per-kind cost bounds (`GRedBounded`,
`GRedCostByKind`, `GRed2Bounded`, `GRed2CostByKind`), `.roQuery` `costAt` bounds, and decoupled
`kindRedHalted` query-bound lemmas for the halted composition reductions.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.CompositionHaltedRedsCost

open scoped BigOperators
open OracleComp OracleSpec
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Var Env Expr Comp CostedReduction
  TwoStageCostedReduction bits atomicSig atomicE2EOps e2eKeyIndTargetIface e2eSessionTargetIface
  keyIndQT keyIndQenc keyIndRT sidT E2EKeyIndTag)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoVerification.LibsignalSession (GRedBounded GRedCostByKind GRed2CostByKind)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes SampledSessionKey GRed2Bounded bhTargetGameSpec
  e2eTargetGameCodec bhQueryKind bhKindCounts bhE2ECostBudget bhE2ECostBudgetByKind
  keyIndReductionBudget)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge (KemFailSessionTrack)
open Computational.Proofs.LibsignalCli.MainHaltedPrefixCore (SessionHaltTracker)
open Computational.Proofs.E2E.Dsl.CompositionHaltedWitness (HaltedTargetAdvPerInstanceBounded
  bhE2ECostBudget_eq_factors e2eFreshScanInnerFactor e2ePerStepWeightedFactor
  totalCost_le_bhE2ECostBudget_of_step_endpoint)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftRen
  renExpr renExpr_cost renComp renComp_cost wk1Ren wk1Comp)
open Computational.Proofs.E2E.Dsl.E2EStateRepr (e2eDrvStateTy cost_bhE2EMirrorE)
open Computational.Proofs.E2E.Dsl.HaltedStartSessionSim (drvTy mirrorClampedE mirrorClampedBodyE
  liftLet1E liftE2EExpr_cost kiQueryOkClampedE kiQueryOkE)
open Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogsAux (lift1Comp liftSessionComp
  liftSessionComp_cost)
open Computational.Proofs.E2E.Dsl.HaltedPrefixSubprogs (kiStepHaltedClampedC kiStepBodyClampedC)
open Computational.Proofs.E2E.Dsl.PrefixRedHaltedByKind (onlineClampedBudget
  onlineClampedBudget_q_total onlineClampedBudget_q_total_le bhKindCounts_zero bhKindCounts_one
  bhKindCounts_sum bhE2ECostBudgetByKind_eq_online_add_roTable bhE2ECostBudget_mono_qTotal
  roStep_mul_le_roTableTerm)

theorem mirrorClampedE_cost_bits {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (krE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndRT (ℓ := ℓ) (Pt := Pt))) :
    (mirrorClampedE (S := S) (Pt := Pt) (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) b σE kqE krE).cost ≤
      σE.cost + kqE.cost + krE.cost + (2 * bits b.q_total + 880) := by
  let nSpk := min b.q_total S.N_spk_tot
  let nOpk := min b.q_total S.N_opk_tot
  have hb := cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT)
    (Γ := [.prod (e2eDrvStateTy S ℓ)
      (.prod (CryptoVerification.E2E.Costed.keyIndQT S) CryptoVerification.E2E.Costed.keyIndRT)])
    (.fst (.var .zero)) (.fst (.snd (.var .zero))) (.snd (.snd (.var .zero)))
  have h1 : bits nSpk ≤ bits b.q_total := bits_mono (Nat.min_le_left _ _)
  have h2 : bits nOpk ≤ bits b.q_total := bits_mono (Nat.min_le_left _ _)
  simp only [mirrorClampedE, mirrorClampedBodyE, liftLet1E, Expr.wkTop1, Expr.renameM_cost,
    liftE2EExpr_cost, E2EStateRepr.drvBase, E2EStateRepr.mbPrins, E2EStateRepr.mbBundles,
    E2EStateRepr.mbOpks, E2EStateRepr.mbSends, Expr.cost, nSpk, nOpk] at hb h1 h2 ⊢
  omega

private theorem renameM_costAt {S₀ : Sig} {O₀ : Ops S₀} {Γ Δ : List (Ty S₀)}
    {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u} {t : Ty S₀} (e : Expr O₀ Γ t)
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v) :
    (Expr.renameM ξ e).costAt ρ₂ = e.costAt ρ₁ := by
  induction e generalizing Δ with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp [Expr.renameM, Expr.costAt, ih1 hξ, ih2 hξ]
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | op _ _ ih | len _ ih | tconst _ ih =>
    simp [Expr.renameM, Expr.costAt, ih hξ]
  | ite c _ _ ihc iha ihb =>
    simp [Expr.renameM, Expr.costAt, Expr.renameM_eval c hξ, ihc hξ, iha hξ, ihb hξ]
  | tset _ _ _ ih1 ih2 ih3 =>
    simp [Expr.renameM, Expr.costAt, ih1 hξ, ih2 hξ, ih3 hξ]
  | caseOpt e _ _ ihe ihn ihs =>
    simp only [Expr.renameM, Expr.costAt, Expr.renameM_eval e hξ, ihe hξ]
    cases e.eval ρ₁ with
    | none => simp [ihn hξ]
    | some x => simp [ihs (_root_.ReductionDsl.get_liftRen hξ x)]
  | caseSum e _ _ ihe ihl ihr =>
    simp only [Expr.renameM, Expr.costAt, Expr.renameM_eval e hξ, ihe hξ]
    cases e.eval ρ₁ with
    | inl x => simp [ihl (_root_.ReductionDsl.get_liftRen hξ x)]
    | inr y => simp [ihr (_root_.ReductionDsl.get_liftRen hξ y)]
  | letE e _ ihe ihb =>
    simp [Expr.renameM, Expr.costAt, Expr.renameM_eval e hξ, ihe hξ,
      ihb (_root_.ReductionDsl.get_liftRen hξ (e.eval ρ₁))]
  | findB _ _ _ ihl _ | anyB _ _ _ ihl _ | mapB _ _ _ ihl _ =>
    simp [Expr.renameM, Expr.costAt, Expr.renameM_cost, ihl hξ]
  | foldrB _ _ _ _ ihl ihz _ =>
    simp [Expr.renameM, Expr.costAt, Expr.renameM_cost, ihl hξ, ihz hξ]

private theorem wkTop1_costAt {S₀ : Sig} {O₀ : Ops S₀} {Γ : List (Ty S₀)} {a t : Ty S₀}
    (e : Expr O₀ [a] t) (x : a.denote) (ρ : Env Γ) :
    (Expr.wkTop1 e).costAt (.cons x ρ) = e.costAt (.cons x .nil) :=
  renameM_costAt e fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

private theorem get_liftRen_asb {S₀ : Sig} {Γ₁ Γ₂ : List (Ty S₀)} {a : Ty S₀}
    {f : ∀ {u}, Var Γ₁ u → Var Γ₂ u} {ρ₁ : Env Γ₁} {ρ₂ : Env Γ₂}
    (hf : ∀ {u} (v : Var Γ₁ u), ρ₂.get (f v) = ρ₁.get v) (x : a.denote) :
    ∀ {u} (v : Var (a :: Γ₁) u), (Env.cons x ρ₂).get (liftRen f v) = (Env.cons x ρ₁).get v
  | _, .zero => rfl
  | _, .succ v => hf v

private theorem renExpr_eval_env {S₀ : Sig} {O₀ : Ops S₀} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    {f : ∀ {u}, Var Γ₁ u → Var Γ₂ u} (e : Expr O₀ Γ₁ t) {ρ₁ : Env Γ₁} {ρ₂ : Env Γ₂}
    (hf : ∀ {u} (v : Var Γ₁ u), ρ₂.get (f v) = ρ₁.get v) :
    (renExpr f e).eval ρ₂ = e.eval ρ₁ := by
  induction e generalizing Γ₂ with
  | var v => exact hf v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2
  | and _ _ ih1 ih2 | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2
  | appendL _ _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp [renExpr, Expr.eval, ih1 hf, ih2 hf]
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | op _ _ ih | len _ ih | tconst _ ih =>
    simp [renExpr, Expr.eval, ih hf]
  | ite _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp [renExpr, Expr.eval, ihc hf, iha hf, ihb hf]
  | caseOpt e _ _ ihe ihn ihs =>
    simp only [renExpr, Expr.eval, ihe hf]
    cases e.eval ρ₁ with
    | none => exact ihn hf
    | some x => exact ihs (get_liftRen_asb hf x)
  | caseSum e _ _ ihe ihl ihr =>
    simp only [renExpr, Expr.eval, ihe hf]
    cases e.eval ρ₁ with
    | inl x => exact ihl (get_liftRen_asb hf x)
    | inr y => exact ihr (get_liftRen_asb hf y)
  | letE e _ ihe ihb =>
    simp only [renExpr, Expr.eval, ihe hf]
    exact ihb (get_liftRen_asb hf (e.eval ρ₁))
  | findB _ _ _ ihl ihp =>
    simp only [renExpr, Expr.eval, ihl hf]; congr 1; funext x; exact ihp (get_liftRen_asb hf x)
  | anyB _ _ _ ihl ihp =>
    simp only [renExpr, Expr.eval, ihl hf]; congr 1; funext x; exact ihp (get_liftRen_asb hf x)
  | mapB _ _ _ ihl ihg =>
    simp only [renExpr, Expr.eval, ihl hf]; congr 1; funext x; exact ihg (get_liftRen_asb hf x)
  | foldrB _ _ _ _ ihl ihz ihg =>
    simp only [renExpr, Expr.eval, ihl hf, ihz hf]
    congr 1; funext x acc; exact ihg (get_liftRen_asb (get_liftRen_asb hf acc) x)

private theorem renExpr_costAt {S₀ : Sig} {O₀ : Ops S₀} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    {f : ∀ {u}, Var Γ₁ u → Var Γ₂ u} (e : Expr O₀ Γ₁ t) {ρ₁ : Env Γ₁} {ρ₂ : Env Γ₂}
    (hf : ∀ {u} (v : Var Γ₁ u), ρ₂.get (f v) = ρ₁.get v) :
    (renExpr f e).costAt ρ₂ = e.costAt ρ₁ := by
  induction e generalizing Γ₂ with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp [renExpr, Expr.costAt, iha hf, ihb hf]
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | op _ _ iha | len _ iha | tconst _ iha =>
    simp [renExpr, Expr.costAt, iha hf]
  | ite c _ _ ihc iha ihb =>
    simp [renExpr, Expr.costAt, renExpr_eval_env c hf, ihc hf, iha hf, ihb hf]
  | tset _ _ _ ihc iha ihb =>
    simp [renExpr, Expr.costAt, ihc hf, iha hf, ihb hf]
  | caseOpt e _ _ ihe ihn ihs =>
    simp only [renExpr, Expr.costAt, renExpr_eval_env e hf, ihe hf]
    cases e.eval ρ₁ with
    | none => simp [ihn hf]
    | some x => simp [ihs (get_liftRen_asb hf x)]
  | caseSum e _ _ ihe ihl ihr =>
    simp only [renExpr, Expr.costAt, renExpr_eval_env e hf, ihe hf]
    cases e.eval ρ₁ with
    | inl x => simp [ihl (get_liftRen_asb hf x)]
    | inr y => simp [ihr (get_liftRen_asb hf y)]
  | letE e _ ihe ihb =>
    simp [renExpr, Expr.costAt, renExpr_eval_env e hf, ihe hf,
      ihb (get_liftRen_asb hf (e.eval ρ₁))]
  | findB _ _ _ ihl _ | anyB _ _ _ ihl _ | mapB _ _ _ ihl _ =>
    simp [renExpr, Expr.costAt, renExpr_cost, ihl hf]
  | foldrB _ _ _ _ ihl ihz _ =>
    simp [renExpr, Expr.costAt, renExpr_cost, ihl hf, ihz hf]

private theorem renComp_pureEval? {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    {f : ∀ {u}, Var Γ₁ u → Var Γ₂ u} (c : Comp O₀ I₀ Γ₁ t) {ρ₁ : Env Γ₁} {ρ₂ : Env Γ₂}
    (hf : ∀ {u} (v : Var Γ₁ u), ρ₂.get (f v) = ρ₁.get v) :
    (renComp f c).pureEval? ρ₂ = c.pureEval? ρ₁ := by
  induction c generalizing Γ₂ with
  | ret e => simp [renComp, Comp.pureEval?, renExpr_eval_env e hf]
  | bind c _ ihc ihk =>
    simp only [renComp, Comp.pureEval?, ihc hf]
    cases c.pureEval? ρ₁ with
    | none => rfl
    | some x => exact ihk (get_liftRen_asb hf x)
  | ite b _ _ ihc ihd =>
    simp [renComp, Comp.pureEval?, renExpr_eval_env b hf, ihc hf, ihd hf]
  | caseOpt e _ _ ihn ihs =>
    simp only [renComp, Comp.pureEval?, renExpr_eval_env e hf]
    cases e.eval ρ₁ with
    | none => exact ihn hf
    | some x => exact ihs (get_liftRen_asb hf x)
  | caseSum e _ _ ihl ihr =>
    simp only [renComp, Comp.pureEval?, renExpr_eval_env e hf]
    cases e.eval ρ₁ with
    | inl x => exact ihl (get_liftRen_asb hf x)
    | inr y => exact ihr (get_liftRen_asb hf y)
  | sample _ _ | query _ _ | iter _ _ _ | findM _ _ _ | anyM _ _ _ | mapM _ _ _
  | consumeFirstM _ _ _ _ | foldM _ _ _ _ => rfl

private theorem renComp_costAt {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ₁ Γ₂ : List (Ty S₀)} {t : Ty S₀}
    {f : ∀ {u}, Var Γ₁ u → Var Γ₂ u} (c : Comp O₀ I₀ Γ₁ t) {ρ₁ : Env Γ₁} {ρ₂ : Env Γ₂}
    (hf : ∀ {u} (v : Var Γ₁ u), ρ₂.get (f v) = ρ₁.get v) :
    (renComp f c).costAt ρ₂ = c.costAt ρ₁ := by
  induction c generalizing Γ₂ with
  | ret e => simp [renComp, Comp.costAt, renExpr_costAt e hf]
  | bind c _ ihc ihk =>
    simp only [renComp, Comp.costAt, ihc hf, renComp_pureEval? c hf, renComp_cost]
    cases c.pureEval? ρ₁ with
    | none => rfl
    | some x => simp [ihk (get_liftRen_asb hf x)]
  | ite b _ _ ihc ihd =>
    simp [renComp, Comp.costAt, renExpr_eval_env b hf, renExpr_costAt b hf, ihc hf, ihd hf]
  | caseOpt e _ _ ihn ihs =>
    simp only [renComp, Comp.costAt, renExpr_eval_env e hf, renExpr_costAt e hf]
    cases e.eval ρ₁ with
    | none => simp [ihn hf]
    | some x => simp [ihs (get_liftRen_asb hf x)]
  | caseSum e _ _ ihl ihr =>
    simp only [renComp, Comp.costAt, renExpr_eval_env e hf, renExpr_costAt e hf]
    cases e.eval ρ₁ with
    | inl x => simp [ihl (get_liftRen_asb hf x)]
    | inr y => simp [ihr (get_liftRen_asb hf y)]
  | sample _ e | query _ e =>
    simp [renComp, Comp.costAt, renExpr_costAt e hf]
  | iter _ e _ | findM _ e _ | anyM _ e _ | mapM _ e _ =>
    simp [renComp, Comp.costAt, renExpr_costAt e hf, renComp_cost]
  | consumeFirstM _ e _ _ =>
    simp [renComp, Comp.costAt, renExpr_costAt e hf, renComp_cost, renExpr_cost]
  | foldM _ l z _ =>
    simp [renComp, Comp.costAt, renExpr_costAt l hf, renExpr_costAt z hf, renComp_cost]

private theorem wk1Comp_costAt {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {a b : Ty S₀} {Γ : List (Ty S₀)}
    (c : Comp O₀ I₀ [a] b) (x : a.denote) (ρ : Env Γ) :
    (wk1Comp (Γ := Γ) c).costAt (.cons x ρ) = c.costAt (.cons x .nil) :=
  renComp_costAt c fun {u} v => by cases v with | zero => rfl | succ w => nomatch w

private theorem costAt_bind_le_cost_right {S₀ : Sig} {O₀ : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t u : Ty S₀}
    (c : Comp O₀ I₀ Γ t) (k : Comp O₀ I₀ (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind c k).costAt ρ ≤ c.costAt ρ + k.cost + 1 := by
  simp only [Comp.costAt]
  rcases c.pureEval? ρ with _ | x <;> dsimp only
  · omega
  · have hk := k.costAt_le_cost (.cons x ρ); omega

private theorem liftE2EExpr_kiQueryOkE_roQuery_costAt_le
    {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (nPrins nInst : ℕ) (d : (drvTy S ℓ Pt).denote) (sec : SignalPqxdh.Bytes) :
    let τ0 : Ty (CryptoVerification.E2E.Costed.e2eSig ℓ) :=
      .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
    (HaltedPrefixSubprogsAux.liftE2EExpr (Pt := Pt) (Γ := [τ0])
      (E2EStateRepr.kiQueryOkE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) nPrins nInst (Γ := [τ0])
        (.fst (.var .zero)) (.snd (.var .zero)))).costAt
      (.cons (d, keyIndQenc (S := S) (ℓ := ℓ) (Pt := Pt) (.roQuery sec)) .nil) ≤ 565 := by
  dsimp only
  unfold E2EStateRepr.kiQueryOkE E2EStateRepr.bhDrvKiQueryOkE
  simp only [E2EStateRepr.kqAcceptHdr?, E2EStateRepr.kqAsTestSession?,
    E2EStateRepr.kqAsRevealDhSecrets?, E2EStateRepr.kqAsInitiateOPK?,
    E2EStateRepr.kqAsInitiateNoOPK?, E2EStateRepr.kqAsAcceptOPK?,
    E2EStateRepr.kqAsAcceptNoOPK?, E2EStateRepr.kqAsCorruptIK?,
    E2EStateRepr.kqR1, E2EStateRepr.kqR2, E2EStateRepr.kqR3, E2EStateRepr.kqR4,
    E2EStateRepr.kqR5, E2EStateRepr.kqR6, E2EStateRepr.kqR7, E2EStateRepr.kqR8,
    E2EStateRepr.kqR9, E2EStateRepr.kqR10, E2EStateRepr.drvBase, E2EStateRepr.drvInstMeta,
    E2EStateRepr.sumRight?, E2EStateRepr.optSumLeft?,
    E2EStateRepr.optSumRight?, PqxdhSimTypes.orE, PqxdhSimTypes.isSomeE,
    PqxdhSimTypes.isNoneE, PqxdhSimTypes.optMapE, PqxdhSimTypes.eLet,
    PqxdhSimTypes.eCaseOpt, PqxdhSimTypes.v, PqxdhSimTypes.Ext.wk,
    HaltedPrefixSubprogsAux.liftE2EExpr,
    Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftVar,
    keyIndQenc, Expr.v0, Expr.eval, Env.get, Expr.costAt,
    Bool.not_false, Bool.not_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  omega

theorem kiQueryOkClampedE_roQuery_costAt_le {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (sec : SignalPqxdh.Bytes)
    (hkq : kqE.eval ρ = keyIndQenc (.roQuery sec)) :
    (kiQueryOkClampedE (S := S) (Pt := Pt) (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) b qStart σE kqE).costAt ρ ≤
      σE.costAt ρ + kqE.costAt ρ + 570 := by
  let τ0 : Ty (CryptoVerification.E2E.Costed.e2eSig ℓ) :=
    .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
  have hbody : ∀ (d : (drvTy S ℓ Pt).denote),
      (HaltedStartSessionSim.liftE2EExpr (Pt := Pt) (Γ := [τ0])
        (E2EStateRepr.kiQueryOkE (S := S) (ℓ := ℓ) (P := P) (C := C) (K := K)
          (decT := decT) (encT := encT) b.q_total (min qStart (min b.q_total S.N_send_tot))
          (Γ := [τ0]) (.fst (.var .zero)) (.snd (.var .zero)))).costAt
        (.cons (d, keyIndQenc (S := S) (ℓ := ℓ) (Pt := Pt) (.roQuery sec)) .nil) ≤ 565 := by
    intro d
    unfold E2EStateRepr.kiQueryOkE E2EStateRepr.bhDrvKiQueryOkE
    simp only [E2EStateRepr.kqAcceptHdr?, E2EStateRepr.kqAsTestSession?,
      E2EStateRepr.kqAsRevealDhSecrets?, E2EStateRepr.kqAsInitiateOPK?,
      E2EStateRepr.kqAsInitiateNoOPK?, E2EStateRepr.kqAsAcceptOPK?,
      E2EStateRepr.kqAsAcceptNoOPK?, E2EStateRepr.kqAsCorruptIK?,
      E2EStateRepr.kqR1, E2EStateRepr.kqR2, E2EStateRepr.kqR3, E2EStateRepr.kqR4,
      E2EStateRepr.kqR5, E2EStateRepr.kqR6, E2EStateRepr.kqR7, E2EStateRepr.kqR8,
      E2EStateRepr.kqR9, E2EStateRepr.kqR10, E2EStateRepr.drvBase, E2EStateRepr.drvInstMeta,
      E2EStateRepr.sumRight?, E2EStateRepr.optSumLeft?,
      E2EStateRepr.optSumRight?, PqxdhSimTypes.orE, PqxdhSimTypes.isSomeE,
      PqxdhSimTypes.isNoneE, PqxdhSimTypes.optMapE, PqxdhSimTypes.eLet,
      PqxdhSimTypes.eCaseOpt, PqxdhSimTypes.v, PqxdhSimTypes.Ext.wk,
      HaltedStartSessionSim.liftE2EExpr,
      Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftVar,
      keyIndQenc, Expr.v0, Expr.eval, Env.get, Expr.costAt,
      Bool.not_false, Bool.not_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
    omega
  dsimp only [kiQueryOkClampedE, kiQueryOkE, liftLet1E, Expr.costAt, Expr.eval]
  rw [hkq, wkTop1_costAt]
  have hb := hbody (σE.eval ρ)
  omega

private theorem costAt_ite_le {S0 : Sig} {O : Ops S0} {ι₀ : Type} {T : OracleSpec ι₀}
    {I : Iface S0 T} {Γ : List (Ty S0)} {a : Ty S0}
    (c : Expr O Γ .bool) (t e : Comp O I Γ a) (ρ : Env Γ) :
    (Comp.ite c t e).costAt ρ ≤ c.costAt ρ + max (t.costAt ρ) (e.costAt ρ) + 1 := by
  simp only [Comp.costAt]; split <;> omega

private theorem castExpr_costAt {S₀ : Sig} {O₀ : Ops S₀} {Γ : List (Ty S₀)} {t₁ t₂ : Ty S₀}
    (h : t₁ = t₂) (e : Expr O₀ Γ t₁) (ρ : Env Γ) :
    (HaltedPrefixSubprogsAux.castExpr h e).costAt ρ = e.costAt ρ := by
  cases h; rfl

private theorem pqxdh1KeyRealStepClampedC_roQuery_costAt_le {S : SignalPqxdh.Setup}
    {Pt : Type} {ℓ : ℕ} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (qTot : ℕ)
    (σv : (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftTy (Pt := Pt)
      (e2eDrvStateTy S ℓ)).denote)
    (sec : SignalPqxdh.Bytes) :
    (liftSessionComp (Pt := Pt)
      (PqxdhSim.pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
        (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) qTot
        (Γ := [.prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)])
        (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0))).costAt
      (.cons (σv, keyIndQenc (S := S) (ℓ := ℓ) (Pt := Pt) (.roQuery sec)) .nil) ≤ 160 := by
  unfold PqxdhSim.pqxdh1KeyRealStepClampedC PqxdhSim.pqxdh1KeyRealStepClampedG
    PqxdhSim.pqxdh1KeyRealBodyClampedG
  simp only [PqxdhSimBranches.ro1KeyRealB, PqxdhSimTypes.mkStepAPqxdhHooks,
    PqxdhSimTypes.bindV, PqxdhSimTypes.rsE, PqxdhSimTypes.rDrKeyE, PqxdhSimTypes.v,
    PqxdhSimTypes.Ext.wk, TablesHonest.e2eCryptoOp,
    liftSessionComp, HaltedPrefixSubprogsAux.liftE2EExpr,
    StartAndExtSmAux.drvSt, Expr.v0,
    Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftVar,
    Comp.costAt, Comp.pureEval?, Expr.costAt, Expr.eval, Env.get, keyIndQenc]
  dsimp only [HaltedPrefixSubprogsAux.castExpr, Expr.costAt,
    HaltedPrefixSubprogsAux.liftE2EOp, atomicE2EOps, Ops.sum, Sum.elim,
    _root_.ReductionDsl.AtomicPqxdhOp.cost]
  simp only [Nat.reduceAdd]
  omega

theorem kiStepHaltedClampedC_roQuery_costAt_le {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (qStart : ℕ) (b : SignalPqxdh.QueryBudget) {Γ : List (Ty (atomicSig ℓ Pt))}
    (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (drvTy S ℓ Pt))
    (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
    (ρ : Env Γ) (sec : SignalPqxdh.Bytes)
    (hkq : kqE.eval ρ = keyIndQenc (.roQuery sec)) :
    (kiStepHaltedClampedC (S := S) (Pt := Pt) (ℓ := ℓ) (P := P) (C := C) (K := K)
        (decT := decT) (encT := encT) qStart b σE kqE).costAt ρ ≤
      σE.costAt ρ + kqE.costAt ρ + 1660 := by
  let nInst := min qStart (min b.q_total S.N_send_tot)
  let τ0 : Ty (CryptoVerification.E2E.Costed.e2eSig ℓ) :=
    .prod (e2eDrvStateTy S ℓ) (CryptoVerification.E2E.Costed.keyIndQT S)
  let τr : Ty (CryptoVerification.E2E.Costed.e2eSig ℓ) :=
    .prod CryptoVerification.E2E.Costed.keyIndRT (PqxdhSimTypes.e2eKeyIndStateTy ℓ S)
  let kOuter : Comp (atomicE2EOps ℓ P C K decT encT) (e2eSessionTargetIface ℓ Pt)
      (Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftTy (Pt := Pt)
        (.prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ)) :: Γ)
      (.prod (e2eTargetGameCodec S ℓ Pt).R (drvTy S ℓ Pt)) :=
    .ret (.pair (.inl (.inl (.fst .v0))) (.snd .v0))
  have hkOuter : kOuter.cost = 8 := rfl
  have hOuter := costAt_bind_le_cost_right
    (lift1Comp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (a := τ0) (b := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
      (.pair σE kqE) (kiStepBodyClampedC qStart b)) kOuter ρ
  have hLift :
      (lift1Comp (Pt := Pt) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (a := τ0) (b := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
        (.pair σE kqE) (kiStepBodyClampedC qStart b)).costAt ρ =
      σE.costAt ρ + kqE.costAt ρ + 3 +
        (liftSessionComp (Pt := Pt)
          (kiStepBodyClampedC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qStart b)).costAt
          (.cons (σE.eval ρ, keyIndQenc (S := S) (ℓ := ℓ) (Pt := Pt) (.roQuery sec)) .nil) := by
    simp only [lift1Comp, Comp.costAt, Comp.pureEval?, Expr.costAt, Expr.eval]
    rw [hkq, wk1Comp_costAt]
    omega
  rw [hLift, hkOuter] at hOuter
  dsimp only [kiStepHaltedClampedC, kOuter] at hOuter ⊢
  let ρ_b : Env [Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge.liftTy (Pt := Pt) τ0] :=
    .cons (σE.eval ρ, keyIndQenc (S := S) (ℓ := ℓ) (Pt := Pt) (.roQuery sec)) .nil
  have hOkCost := liftE2EExpr_kiQueryOkE_roQuery_costAt_le (S := S) (Pt := Pt) (ℓ := ℓ)
    (P := P) (C := C) (K := K) (decT := decT) (encT := encT) b.q_total nInst (σE.eval ρ) sec
  let kMir : Comp (CryptoVerification.E2E.Costed.e2eOps ℓ P C K decT encT)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) [τr, τ0]
      (.prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ)) :=
    .ret (.pair (.fst .v0)
      (E2EStateRepr.bhE2EMirrorE
        (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
        (.snd (.var (.succ .zero))) (.fst .v0)))
  have hset := M3Interfaces.cost_drvSetStE
    (O := CryptoVerification.E2E.Costed.e2eOps ℓ P C K decT encT) (S := S) (ℓ := ℓ)
    (Γ := [τr, τ0]) (.fst (.var (.succ .zero))) (.snd .v0)
  have hmir := cost_bhE2EMirrorE (ℓ := ℓ) (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := [τr, τ0])
    (M3Interfaces.drvSetStE (.fst (.var (.succ .zero))) (.snd .v0))
    (.snd (.var (.succ .zero))) (.fst .v0)
  have hkMir : (liftSessionComp (Pt := Pt) kMir).cost ≤ 880 := by
    rw [liftSessionComp_cost]
    dsimp only [kMir, Comp.cost, Expr.cost, Expr.v0] at hset hmir ⊢
    omega
  have hPqRo :
      (liftSessionComp (Pt := Pt)
        (PqxdhSim.pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
          (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
          (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0))).costAt ρ_b ≤ 160 :=
    pqxdh1KeyRealStepClampedC_roQuery_costAt_le b.q_total (σE.eval ρ) sec
  have hBind :
      (Comp.bind
        (liftSessionComp (Pt := Pt)
          (PqxdhSim.pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
            (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
            (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)))
        (liftSessionComp (Pt := Pt) kMir)).costAt ρ_b ≤ 1045 :=
    (costAt_bind_le_cost_right
      (liftSessionComp (Pt := Pt)
        (PqxdhSim.pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
          (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
          (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)))
      (liftSessionComp (Pt := Pt) kMir) ρ_b).trans (by omega)
  have hElse : (liftSessionComp (Pt := Pt)
      (Comp.ret (O := CryptoVerification.E2E.Costed.e2eOps ℓ P C K decT encT)
        (I := CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) (Γ := [τ0])
        (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
        (.pair (.inl .unit) (.fst .v0)))).costAt ρ_b ≤ 10 := by
    refine (Comp.costAt_le_cost _ _).trans ?_
    rw [liftSessionComp_cost]
    simp only [Comp.cost, Expr.cost, Expr.v0]
    omega
  have hBody :
      (liftSessionComp (Pt := Pt)
        (kiStepBodyClampedC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
          qStart b)).costAt ρ_b ≤ 1630 := by
    have hIte : liftSessionComp (Pt := Pt)
        (kiStepBodyClampedC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qStart b) =
        Comp.ite
          (HaltedPrefixSubprogsAux.liftE2EExpr (Pt := Pt)
            (E2EStateRepr.kiQueryOkE b.q_total nInst (.fst .v0) (.snd .v0)))
          (Comp.bind
            (liftSessionComp (Pt := Pt)
              (PqxdhSim.pqxdh1KeyRealStepClampedC (Pt := Pt) ℓ S P C K decT encT
                (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) b.q_total (Γ := [τ0])
                (StartAndExtSmAux.drvSt (.fst .v0)) (.snd .v0)))
            (liftSessionComp (Pt := Pt) kMir))
          (liftSessionComp (Pt := Pt)
            (Comp.ret (O := CryptoVerification.E2E.Costed.e2eOps ℓ P C K decT encT)
              (I := CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ) (Γ := [τ0])
              (t := .prod CryptoVerification.E2E.Costed.keyIndRT (e2eDrvStateTy S ℓ))
              (.pair (.inl .unit) (.fst .v0)))) := rfl
    rw [hIte]
    refine (costAt_ite_le _ _ _ ρ_b).trans ?_
    have hOkCost' :
        (HaltedPrefixSubprogsAux.liftE2EExpr (Pt := Pt)
          (E2EStateRepr.kiQueryOkE b.q_total nInst (Γ := [τ0]) (.fst .v0) (.snd .v0))).costAt ρ_b ≤
          565 := hOkCost
    omega
  dsimp only [ρ_b] at hBody
  omega

private theorem e2eFactors_mono_qTotal (S : SignalPqxdh.Setup)
    {b₁ b₂ : SignalPqxdh.QueryBudget} (hb : b₁.q_total ≤ b₂.q_total)
    (qStart qInst qep ℓ : ℕ) :
    e2ePerStepWeightedFactor S b₁ qStart qInst qep ℓ ≤
      e2ePerStepWeightedFactor S b₂ qStart qInst qep ℓ ∧
    2 ^ 13 * min qStart (min b₁.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b₁ ≤
      2 ^ 13 * min qStart (min b₂.q_total S.N_send_tot) * e2eFreshScanInnerFactor S b₂ := by
  have hId : min b₁.q_total S.N_id ≤ min b₂.q_total S.N_id :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hSpk : min b₁.q_total S.N_spk_tot ≤ min b₂.q_total S.N_spk_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hOpk : min b₁.q_total S.N_opk_tot ≤ min b₂.q_total S.N_opk_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hSend : min b₁.q_total S.N_send_tot ≤ min b₂.q_total S.N_send_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hRecv : min b₁.q_total S.N_recv_tot ≤ min b₂.q_total S.N_recv_tot :=
    Nat.le_min.mpr ⟨(Nat.min_le_left _ _).trans hb, Nat.min_le_right _ _⟩
  have hInst : min qStart (min b₁.q_total S.N_send_tot) ≤
      min qStart (min b₂.q_total S.N_send_tot) :=
    Nat.le_min.mpr ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans hSend⟩
  refine ⟨?_, Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 13) hInst) ?_⟩
  · dsimp only [e2ePerStepWeightedFactor]; omega
  · dsimp only [e2eFreshScanInnerFactor]; omega

/-- `GRedBounded` against `bhE2ECostBudget S b ...` when `kindRedHalted` runs at `onlineClampedBudget b`. -/
theorem kindRedHalted_bOn_gRedBounded {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let b_on := onlineClampedBudget b
    let qTot := b.q_total + qStart + qDR
    GRedBounded
      (KindRedHalted.kindRedHalted
        (KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b_on) b_on qStart qInst qep)
      (fun _ => 1) (fun _ => 0) qTot (2 * qTot) (bhE2ECostBudget S b qStart qDR qInst qep ℓ) := by
  dsimp only
  let b_on := onlineClampedBudget b
  obtain ⟨hW, hF⟩ := e2eFactors_mono_qTotal S (onlineClampedBudget_q_total_le b) qStart qInst qep ℓ
  have hEnd := (KindRedHaltedInst.mkKindSubprogramsHaltedClamped_endpointCost_le
    smStep b_on qStart qInst qep).trans
    (Nat.add_le_add (Nat.mul_le_mul_left (2 ^ 10) hW) hF)
  have hStep := (KindRedHaltedInst.mkKindSubprogramsHaltedClamped_stepCost_le
    smStep b_on qStart qInst qep).trans (Nat.mul_le_mul_left (2 ^ 10) hW)
  have hBits := bits_mono
    (bhE2ECostBudget_mono_qTotal S (onlineClampedBudget_q_total_le b) qStart qDR qInst qep ℓ)
  have hSz := (KindRedHaltedInst.mkKindSubprogramsHaltedClamped_sizeBound_le
    smStep b_on qStart qDR qInst qep).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 530 hBits) 510000)
  exact KindRedHalted.kindRedHalted_gRedBounded
    (KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b_on) b_on qStart qInst qep
    (b.q_total + qStart + qDR) (bhE2ECostBudget S b qStart qDR qInst qep ℓ)
    (totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ
      (b.q_total + qStart + qDR) _ _ (le_refl _) hEnd hStep)
    (KindRedHalted.kindRedHalted_size_le_budget
      (KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b_on) b_on qStart qInst qep
      (bhE2ECostBudget S b qStart qDR qInst qep ℓ) 510000 530 (by omega) (by omega) hSz)

/-- `GRedCostByKind` against `bhE2ECostBudgetByKind S b ...` when `kindRedHalted` runs at
`onlineClampedBudget b`. -/
theorem kindRedHalted_bOn_gRedCostByKind {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {TrackInv : ℕ → KemFailSessionTrack C.F Bytes → Prop}
    (smStep : KindRedHaltedInst.HaltedLocalSmKindStepInst S ℓ Pt P C K decT encT TrackInv)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qInst qep : ℕ) :
    let b_on := onlineClampedBudget b
    let qKind := bhKindCounts b qStart qDR
    let qSum := (List.ofFn qKind).sum
    GRedCostByKind
      (KindRedHalted.kindRedHalted
        (KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b_on) b_on qStart qInst qep)
      (fun _ => 1) (fun _ => 0) bhQueryKind qKind (2 * qSum)
      (bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ) := by
  dsimp only
  let b_on := onlineClampedBudget b
  let subs := KindRedHaltedInst.mkKindSubprogramsHaltedClamped smStep b_on
  refine PrefixRedHaltedByKind.kindRedHalted_gRedCostByKind subs b_on qStart qInst qep
    570 (2 * bits b_on.q_total + 880) (bhKindCounts b qStart qDR)
    (bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ)
    (fun σE kqE ρ sec hkq => kiQueryOkClampedE_roQuery_costAt_le b_on qStart σE kqE ρ sec hkq)
    (fun σE kqE krE => mirrorClampedE_cost_bits b_on σE kqE krE) ?_
  rw [bhE2ECostBudgetByKind_eq_online_add_roTable, bhKindCounts_zero, bhKindCounts_one]
  have hEnd := KindRedHaltedInst.mkKindSubprogramsHaltedClamped_endpointCost_le
    smStep b_on qStart qInst qep
  have hStep := KindRedHaltedInst.mkKindSubprogramsHaltedClamped_stepCost_le
    smStep b_on qStart qInst qep
  have hOn :
      KindRedHalted.haltedKindEndpointCost subs qStart +
        (min b.q_on b.q_total + qStart + qDR) *
          KindRedHalted.haltedKindStepCost subs b_on qStart qInst qep ≤
      bhE2ECostBudget S b_on qStart qDR qInst qep ℓ := by
    rw [bhE2ECostBudget_eq_factors]
    have hmul := Nat.mul_le_mul_left (min b.q_on b.q_total + qStart + qDR) hStep
    have hpos : min b.q_on b.q_total = b_on.q_total := rfl
    rw [hpos] at hmul ⊢
    set W := e2ePerStepWeightedFactor S b_on qStart qInst qep ℓ
    have hring : (b_on.q_total + qStart + qDR) * (2 ^ 10 * W) + 2 ^ 10 * W =
        2 ^ 10 * (b_on.q_total + qStart + qDR + 1) * W := by ring
    dsimp only [subs] at hEnd hmul ⊢
    omega
  have hRo := roStep_mul_le_roTableTerm (min b.q_on b.q_total) (min b.q_ro b.q_total) qStart qDR
    (570 + (2 * bits b_on.q_total + 880) + 224) (by dsimp only [b_on, onlineClampedBudget]; omega)
  dsimp only at hRo
  exact Nat.add_le_add hOn hRo

/-- `GRed2Bounded` against `bhE2ECostBudget S b ...` when `prefixRedHalted` runs at `onlineClampedBudget b`. -/
theorem prefixRedHalted_bOn_gRed2Bounded {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : PrefixRedHalted.HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop} {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep k : ℕ}
    (hValid : PrefixRedHaltedInst.ValidHaltedPrefixSubprogramsInst subs T TrackInv
      (onlineClampedBudget b) qStart qInst qep)
    (hk : k < qStart)
    (hk_inst : k ≤ min qStart (min (onlineClampedBudget b).q_total S.N_send_tot)) :
    let qTot := b.q_total + qStart + qDR
    GRed2Bounded (PrefixRedHalted.prefixRedHalted subs (onlineClampedBudget b) qStart qInst qep k)
      (fun _ => 1) (fun _ => 0) qTot qTot (bhE2ECostBudget S b qStart qDR qInst qep ℓ) false := by
  dsimp only
  let b_on := onlineClampedBudget b
  obtain ⟨hW, hF⟩ := e2eFactors_mono_qTotal S (onlineClampedBudget_q_total_le b) qStart qInst qep ℓ
  have hEnd := hValid.endpointCost_le.trans
    (Nat.add_le_add (Nat.mul_le_mul_left (2 ^ 10) hW) hF)
  have hStep := hValid.stepCost_le.trans (Nat.mul_le_mul_left (2 ^ 10) hW)
  rcases hValid.sizeBound_le qDR with ⟨C₀, C₁, hC₀, hC₁, hSz₀⟩
  have hBits := bits_mono
    (bhE2ECostBudget_mono_qTotal S (onlineClampedBudget_q_total_le b) qStart qDR qInst qep ℓ)
  have hSz := hSz₀.trans (Nat.add_le_add_left (Nat.mul_le_mul_left C₁ hBits) C₀)
  exact PrefixRedHalted.gRed2Bounded_atomic_of_bounds
    (PrefixRedHalted.prefixRedHalted subs b_on qStart qInst qep k)
    (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
    (bhE2ECostBudget S b qStart qDR qInst qep ℓ) false
    (le_trans
      (PrefixRedHaltedInst.prefixRedHalted_totalCost_le_tight subs b_on qStart qInst qep
        (b.q_total + qStart + qDR) hk_inst)
      (totalCost_le_bhE2ECostBudget_of_step_endpoint S b qStart qDR qInst qep ℓ
        (b.q_total + qStart + qDR) _ _ (le_refl _) hEnd hStep))
    (PrefixRedHalted.prefixRedHalted_size_le_budget subs b_on qStart qInst qep
      (bhE2ECostBudget S b qStart qDR qInst qep ℓ) C₀ C₁ hk hC₀ hC₁ hSz)
    (PrefixRedHalted.prefixRedHalted_stage1Queries subs b_on qStart qInst qep k)
    (PrefixRedHalted.prefixRedHalted_totalQueries_le subs b_on qStart qInst qep k
      (b.q_total + qStart + qDR))

private theorem gRed2CostByKind_of_totalCost_and_ro
    {S0 : Sig} {O : Ops S0} {ι₀ ι : Type} {T0 : OracleSpec ι₀} {I : Iface S0 T0}
    {S : SignalPqxdh.Setup}
    {G : OracleSpec ((SignalPqxdh.KeyIndQuery S ⊕ CryptoVerification.E2E.BHDRCtlQuery S) ⊕ ι)}
    {C0 : GameCodec S0 G} {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (qKind : Fin 2 → ℕ) (qOut h₁ B_on B : ℕ)
    (hOnCost : R.totalCost (qKind 0) ≤ B_on)
    (hPreRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handlePre.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hPostRo : ∀ (s : R.σ.denote) (sec : SignalPqxdh.Bytes),
      R.handlePost.costAt (.cons s (.cons (C0.qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ h₁)
    (hSum : B_on + qKind 1 * max I.uCost (h₁ + C0.codecCost) ≤ B)
    (hStage1Q : R.init.queries wTag wSamp + R.handlePre.queries wTag wSamp +
      R.chDone.queries wTag wSamp = 0)
    (hQ : R.totalQueries wTag wSamp (List.ofFn qKind).sum ≤ qOut) :
    GRed2CostByKind R wTag wSamp bhQueryKind qKind qOut B := by
  refine PrefixRedHaltedByKind.gRed2CostByKind_bhQueryKind_of_online_and_ro R wTag wSamp
    qKind qOut (max R.handlePre.cost R.handlePost.cost) h₁ B
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) hPreRo hPostRo ?_ hStage1Q hQ
  unfold TwoStageCostedReduction.totalCost at hOnCost
  omega

/-- `GRed2CostByKind` against `bhE2ECostBudgetByKind` when `prefixRedHalted` runs at `onlineClampedBudget b`. -/
theorem prefixRedHalted_bOn_gRed2CostByKind {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    {subs : PrefixRedHalted.HaltedPrefixSubprograms S (Pt := Pt) ℓ P C K decT encT SessH}
    {T : SessionHaltTracker (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes SampledSessionKey SessH}
    {TrackInv : ℕ → SessH → Prop} {b : SignalPqxdh.QueryBudget} {qStart qDR qInst qep k : ℕ}
    (hValid : PrefixRedHaltedInst.ValidHaltedPrefixSubprogramsInst subs T TrackInv
      (onlineClampedBudget b) qStart qInst qep)
    (hKiRo : ∀ {Γ : List (Ty (atomicSig ℓ Pt))}
      (σE : Expr (atomicE2EOps ℓ P C K decT encT) Γ subs.drvTy)
      (kqE : Expr (atomicE2EOps ℓ P C K decT encT) Γ (keyIndQT (ℓ := ℓ) (Pt := Pt) S))
      (ρ : Env Γ) (sec : SignalPqxdh.Bytes),
      kqE.eval ρ = keyIndQenc (.roQuery sec) →
      (subs.kiStepC (onlineClampedBudget b) σE kqE).costAt ρ ≤ σE.costAt ρ + kqE.costAt ρ + 1660)
    (hk : k < qStart)
    (hk_inst : k ≤ min qStart (min (onlineClampedBudget b).q_total S.N_send_tot)) :
    let qKind := bhKindCounts b qStart qDR
    let qSum := (List.ofFn qKind).sum
    GRed2CostByKind
      (PrefixRedHalted.prefixRedHalted subs (onlineClampedBudget b) qStart qInst qep k)
      (fun _ => 1) (fun _ => 0) bhQueryKind qKind qSum
      (bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ) := by
  have hG2 := PrefixRedHaltedInst.prefixRedHalted_gRed2Bounded_of_valid_inst
    (qDR := qDR) hValid hk hk_inst
  have hOnCost :
      (PrefixRedHalted.prefixRedHalted subs (onlineClampedBudget b) qStart qInst qep k).totalCost
        (bhKindCounts b qStart qDR 0) ≤
      bhE2ECostBudget S (onlineClampedBudget b) qStart qDR qInst qep ℓ := by
    rw [bhKindCounts_zero]
    exact hG2.1
  have hSum :
      bhE2ECostBudget S (onlineClampedBudget b) qStart qDR qInst qep ℓ +
        bhKindCounts b qStart qDR 1 *
          max (e2eSessionTargetIface ℓ Pt).uCost
            ((1660 + 29) + (e2eTargetGameCodec S ℓ Pt).codecCost) ≤
      bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ := by
    have hu : (e2eSessionTargetIface ℓ Pt).uCost = 1 := rfl
    have hcc : (e2eTargetGameCodec S ℓ Pt).codecCost = 64 := rfl
    rw [hu, hcc, bhE2ECostBudgetByKind_eq_online_add_roTable, bhKindCounts_one]
    have hRo := roStep_mul_le_roTableTerm (min b.q_on b.q_total) (min b.q_ro b.q_total) qStart qDR
      1753 (by omega)
    dsimp only at hRo
    exact Nat.add_le_add_left hRo _
  exact gRed2CostByKind_of_totalCost_and_ro
    (PrefixRedHalted.prefixRedHalted subs (onlineClampedBudget b) qStart qInst qep k)
    (fun _ => 1) (fun _ => 0) (bhKindCounts b qStart qDR)
    (List.ofFn (bhKindCounts b qStart qDR)).sum (1660 + 29)
    (bhE2ECostBudget S (onlineClampedBudget b) qStart qDR qInst qep ℓ)
    (bhE2ECostBudgetByKind S b qStart qDR qInst qep ℓ)
    hOnCost
    (PrefixRedHaltedByKind.prefixHandlePreHalted_roQuery_costAt_le subs (onlineClampedBudget b)
      qStart qInst qep k 1660 hKiRo)
    (PrefixRedHaltedByKind.prefixHandlePostHalted_roQuery_costAt_le subs (onlineClampedBudget b)
      qStart qInst qep k 1660 hKiRo)
    hSum
    (PrefixRedHalted.prefixRedHalted_stage1Queries subs (onlineClampedBudget b) qStart qInst qep k)
    (PrefixRedHalted.prefixRedHalted_totalQueries_le subs (onlineClampedBudget b)
      qStart qInst qep k _)

private def freezeKindBudget {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : KindRedHalted.HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b_sub : SignalPqxdh.QueryBudget) :
    KindRedHalted.HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH :=
  { subs with
    kiQueryOkE := fun _ qSt {_} σE kqE => subs.kiQueryOkE b_sub qSt σE kqE
    kiQueryOkCost := fun _ qSt => subs.kiQueryOkCost b_sub qSt
    kiQueryOkSize := fun _ qSt => subs.kiQueryOkSize b_sub qSt
    kiQueryOkE_cost := fun _ qSt {_} σE kqE => subs.kiQueryOkE_cost b_sub qSt σE kqE
    kiQueryOkE_size := fun _ qSt {_} σE kqE => subs.kiQueryOkE_size b_sub qSt σE kqE
    prepStartSpkE := fun _ qSt {_} σE sidE => subs.prepStartSpkE b_sub qSt σE sidE
    prepStartSpkCost := fun _ qSt => subs.prepStartSpkCost b_sub qSt
    prepStartSpkSize := fun _ qSt => subs.prepStartSpkSize b_sub qSt
    prepStartSpkE_cost := fun _ qSt {_} σE sidE => subs.prepStartSpkE_cost b_sub qSt σE sidE
    prepStartSpkE_size := fun _ qSt {_} σE sidE => subs.prepStartSpkE_size b_sub qSt σE sidE
    finishStartSpkHaltedC := fun _ qSt {_} bmE σHE sidE kr1E kr2E acE =>
      subs.finishStartSpkHaltedC b_sub qSt bmE σHE sidE kr1E kr2E acE
    finishStartSpkHaltedCost := fun _ qSt => subs.finishStartSpkHaltedCost b_sub qSt
    finishStartSpkHaltedSize := fun _ qSt => subs.finishStartSpkHaltedSize b_sub qSt
    finishStartSpkHaltedC_cost := fun _ qSt {_} bmE σHE sidE kr1E kr2E acE =>
      subs.finishStartSpkHaltedC_cost b_sub qSt bmE σHE sidE kr1E kr2E acE
    finishStartSpkHaltedC_size := fun _ qSt {_} bmE σHE sidE kr1E kr2E acE =>
      subs.finishStartSpkHaltedC_size b_sub qSt bmE σHE sidE kr1E kr2E acE
    finishStartSpkHaltedC_queries := fun _ qSt {_} bmE σHE sidE kr1E kr2E acE w =>
      subs.finishStartSpkHaltedC_queries b_sub qSt bmE σHE sidE kr1E kr2E acE w
    haltedStepLocalSmC := fun _ qSt qDR qep {_} σHE idxE sqE =>
      subs.haltedStepLocalSmC b_sub qSt qDR qep σHE idxE sqE
    haltedStepLocalSmCost := fun _ qSt qDR qep => subs.haltedStepLocalSmCost b_sub qSt qDR qep
    haltedStepLocalSmSize := fun _ qSt qDR qep => subs.haltedStepLocalSmSize b_sub qSt qDR qep
    haltedStepLocalSmC_cost := fun _ qSt qDR qep {_} σHE idxE sqE =>
      subs.haltedStepLocalSmC_cost b_sub qSt qDR qep σHE idxE sqE
    haltedStepLocalSmC_size := fun _ qSt qDR qep {_} σHE idxE sqE =>
      subs.haltedStepLocalSmC_size b_sub qSt qDR qep σHE idxE sqE
    haltedStepLocalSmC_queries := fun _ qSt qDR qep {_} σHE idxE sqE w =>
      subs.haltedStepLocalSmC_queries b_sub qSt qDR qep σHE idxE sqE w }

/-- Per-instance `SignalPqxdh.QueryBounded` transfer for `kindRedHalted` at arbitrary internal fuel
`b_sub` (such as `onlineClampedBudget b`) while bounding output queries by `keyIndReductionBudget S qStart b`. -/
theorem kindRedHalted_queryBounded_inst_fuel {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {SessH : Type}
    (subs : KindRedHalted.HaltedKindSubprograms S (Pt := Pt) ℓ P C K decT encT SessH)
    (b_sub b : SignalPqxdh.QueryBudget) (qStart qInst qep : ℕ) (qs : ℕ → ℕ)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : HaltedTargetAdvPerInstanceBounded B_A b qStart qs) :
    SignalPqxdh.QueryBounded
      (⟨(KindRedHalted.kindRedHalted subs b_sub qStart qInst qep).eval
        (fun _ => B_A) ()⟩ : SignalPqxdh.KeyIndAdversary S)
      (keyIndReductionBudget S qStart b) :=
  KindRedHaltedInst.kindRedHalted_queryBounded_of_inst_gen
    (freezeKindBudget subs b_sub) b qStart qInst qep qs B_A hB

end Computational.Proofs.E2E.Dsl.CompositionHaltedRedsCost
