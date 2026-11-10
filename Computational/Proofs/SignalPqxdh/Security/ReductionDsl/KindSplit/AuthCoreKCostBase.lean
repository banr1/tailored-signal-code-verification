/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.KindedDispatch -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.KindedQueries -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBaseRo

/-!
# Base Cost, Dispatch, Query, Size, and AVL Split Bounds for `AuthCoreK`

Proves context-renaming preservation and generic 12-way `DispatchesTo`, `costAt`, `cost`,
`queries`, `queriesAt`, and `size` bounds for `dispatchAuthQ`. Re-exports step-cost,
query-vanishing, syntax-size, and split-budget bounds for the AVL shadow RO arms and post-step
sync helpers from `AuthCoreKCostBaseRo`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase

open OracleSpec OracleComp
open _root_.SignalPqxdh (Setup QueryBudget Bytes PreKeyBundleInput PreKeyMsg AuthQuery authSpec)
open _root_.SignalPqxdh.Security (authQueryKind)
open _root_.SignalPqxdh.Costed (authCodec preKeyMsgV)
open _root_.ReductionDsl (
  Sig Ty Var Expr Comp Env Ops Iface
  pqAtomicSig pqAtomicOps pqAtomicSamplers
  B PB drKeyT bundleV bits
)
open _root_.Computational.Proofs.ReductionDsl.KindedDispatch (
  DispatchesTo costAt_eq_of_dispatchesTo costAt_le_arm_cost_of_dispatchesTo
  queriesAt_eq_of_dispatchesTo queriesAt_le_arm_queries_of_dispatchesTo
  eval_eq_of_dispatchesTo
)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface
  liftRen exprRename compRename exprRename_cost compRename_cost compRename_queries
  exprRename_size compRename_size exprRename_eval compRename_eval
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlHeightCap
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK (
  roAvlTy roRootAvlTy roBothAvlTy roListAtomicTy roRootListAtomicTy
  authBaseAtomicTy authFixedAtomicTy authBaseShadowStTy authFixedShadowStTy
  authQueryAtomicTy authSendQAtomicTy authRecvQAtomicTy authRespAtomicTy
  dispatchAuthQ
  roShadowStepC roRootShadowStepC
  roBaseShadowArmC roRootBaseShadowArmC roFixedShadowArmC roRootFixedShadowArmC
  syncRoHeadB192C syncRoHeadPair32C syncRoBothC
  syncBaseShadowRespC syncFixedShadowRespC
)

/-! ## Context Renaming and Generic `dispatchAuthQ` Spine -/

section DispatchAuthQSpine

private theorem liftRen_get {S : Sig} {Γ Δ : List (Ty S)} {u : Ty S}
    {ξ : ∀ {a}, Var Γ a → Var Δ a} {ρ : Env Γ} {ρ' : Env Δ} (x : u.denote)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    ∀ {a} (v : Var (u :: Γ) a), (Env.cons x ρ').get (liftRen ξ v) = (Env.cons x ρ).get v
  | _, .zero => rfl
  | _, .succ v => hρ v

theorem exprRename_costAt {Γ Δ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (ξ : ∀ {a}, Var Γ a → Var Δ a) (e : Expr pqAtomicOps Γ t) (ρ : Env Γ) (ρ' : Env Δ)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    (exprRename ξ e).costAt ρ' = e.costAt ρ := by
  induction e generalizing Δ with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | take a b iha ihb
  | appendL _ a b iha ihb | tget a b iha ihb =>
    simp [exprRename, Expr.costAt, iha ξ ρ ρ' hρ, ihb ξ ρ ρ' hρ]
  | mulK _ a iha | divK _ a iha | modK _ a iha | not a iha | fst a iha | snd a iha
  | inl a iha | inr a iha | some a iha | op _ a iha | len a iha | tconst a iha =>
    simp [exprRename, Expr.costAt, iha ξ ρ ρ' hρ]
  | findB _ a _ iha _ | anyB _ a _ iha _ | mapB _ a _ iha _ =>
    simp [exprRename, Expr.costAt, exprRename_cost, iha ξ ρ ρ' hρ]
  | foldrB _ l z _ ihl ihz _ =>
    simp [exprRename, Expr.costAt, exprRename_cost, ihl ξ ρ ρ' hρ, ihz ξ ρ ρ' hρ]
  | tset m i a ihm ihi iha =>
    simp [exprRename, Expr.costAt, ihm ξ ρ ρ' hρ, ihi ξ ρ ρ' hρ, iha ξ ρ ρ' hρ]
  | ite c a b ihc iha ihb =>
    simp only [exprRename, Expr.costAt, exprRename_eval c ξ ρ ρ' hρ,
      ihc ξ ρ ρ' hρ, iha ξ ρ ρ' hρ, ihb ξ ρ ρ' hρ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [exprRename, Expr.costAt, exprRename_eval e ξ ρ ρ' hρ, ihe ξ ρ ρ' hρ]
    cases e.eval ρ with
    | none => simp [ihn ξ ρ ρ' hρ]
    | some x => simp [ihs (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)]
  | caseSum e l r ihe ihl ihr =>
    simp only [exprRename, Expr.costAt, exprRename_eval e ξ ρ ρ' hρ, ihe ξ ρ ρ' hρ]
    cases e.eval ρ with
    | inl x => simp [ihl (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)]
    | inr y => simp [ihr (liftRen ξ) (.cons y ρ) (.cons y ρ') (liftRen_get y hρ)]
  | letE e b ihe ihb =>
    simp only [exprRename, Expr.costAt, exprRename_eval e ξ ρ ρ' hρ, ihe ξ ρ ρ' hρ,
      ihb (liftRen ξ) (.cons (e.eval ρ) ρ) (.cons (e.eval ρ) ρ') (liftRen_get (e.eval ρ) hρ)]

theorem compRename_pureEval? {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ Δ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp pqAtomicOps I Γ t) (ρ : Env Γ) (ρ' : Env Δ)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    (compRename ξ c).pureEval? ρ' = c.pureEval? ρ := by
  induction c generalizing Δ with
  | ret e => simp [compRename, Comp.pureEval?, exprRename_eval e ξ ρ ρ' hρ]
  | bind c k ihc ihk =>
    simp only [compRename, Comp.pureEval?, ihc ξ ρ ρ' hρ]
    cases c.pureEval? ρ with
    | none => rfl
    | some x => exact ihk (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)
  | ite b c d ihc ihd =>
    simp only [compRename, Comp.pureEval?, exprRename_eval b ξ ρ ρ' hρ]
    cases b.eval ρ <;> simp [ihc ξ ρ ρ' hρ, ihd ξ ρ ρ' hρ]
  | caseOpt e n s ihn ihs =>
    simp only [compRename, Comp.pureEval?, exprRename_eval e ξ ρ ρ' hρ]
    cases e.eval ρ with
    | none => exact ihn ξ ρ ρ' hρ
    | some x => exact ihs (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)
  | caseSum e l r ihl ihr =>
    simp only [compRename, Comp.pureEval?, exprRename_eval e ξ ρ ρ' hρ]
    cases e.eval ρ with
    | inl x => exact ihl (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)
    | inr y => exact ihr (liftRen ξ) (.cons y ρ) (.cons y ρ') (liftRen_get y hρ)
  | sample _ _ | query _ _ | iter _ _ _ | findM _ _ _ | anyM _ _ _ | mapM _ _ _
  | consumeFirstM _ _ _ _ | foldM _ _ _ _ => rfl

theorem compRename_costAt {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ Δ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp pqAtomicOps I Γ t) (ρ : Env Γ) (ρ' : Env Δ)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    (compRename ξ c).costAt ρ' = c.costAt ρ := by
  induction c generalizing Δ with
  | ret e => simp [compRename, Comp.costAt, exprRename_costAt ξ e ρ ρ' hρ]
  | bind c k ihc ihk =>
    simp only [compRename, Comp.costAt, compRename_pureEval? ξ c ρ ρ' hρ, ihc ξ ρ ρ' hρ]
    cases c.pureEval? ρ with
    | none => simp [compRename_cost]
    | some x => simp [ihk (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)]
  | ite b c d ihc ihd =>
    simp only [compRename, Comp.costAt, exprRename_eval b ξ ρ ρ' hρ,
      exprRename_costAt ξ b ρ ρ' hρ, ihc ξ ρ ρ' hρ, ihd ξ ρ ρ' hρ]
  | caseOpt e n s ihn ihs =>
    simp only [compRename, Comp.costAt, exprRename_eval e ξ ρ ρ' hρ, exprRename_costAt ξ e ρ ρ' hρ]
    cases e.eval ρ with
    | none => simp [ihn ξ ρ ρ' hρ]
    | some x => simp [ihs (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)]
  | caseSum e l r ihl ihr =>
    simp only [compRename, Comp.costAt, exprRename_eval e ξ ρ ρ' hρ, exprRename_costAt ξ e ρ ρ' hρ]
    cases e.eval ρ with
    | inl x => simp [ihl (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)]
    | inr y => simp [ihr (liftRen ξ) (.cons y ρ) (.cons y ρ') (liftRen_get y hρ)]
  | sample _ e | query _ e => simp [compRename, Comp.costAt, exprRename_costAt ξ e ρ ρ' hρ]
  | iter _ e _ _ | findM _ e _ _ | anyM _ e _ _ | mapM _ e _ _ =>
    simp [compRename, Comp.costAt, exprRename_costAt ξ e ρ ρ' hρ, compRename_cost]
  | consumeFirstM _ e _ _ _ =>
    simp [compRename, Comp.costAt, exprRename_costAt ξ e ρ ρ' hρ, compRename_cost, exprRename_cost]
  | foldM _ l z _ _ =>
    simp [compRename, Comp.costAt, exprRename_costAt ξ l ρ ρ' hρ,
      exprRename_costAt ξ z ρ ρ' hρ, compRename_cost]

theorem compRename_queriesAt {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ Δ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig}
    (ξ : ∀ {a}, Var Γ a → Var Δ a) (c : Comp pqAtomicOps I Γ t) (ρ : Env Γ) (ρ' : Env Δ)
    (hρ : ∀ {a} (v : Var Γ a), ρ'.get (ξ v) = ρ.get v) :
    (compRename ξ c).queriesAt w ws ρ' = c.queriesAt w ws ρ := by
  induction c generalizing Δ with
  | ret _ => rfl
  | bind c k ihc ihk =>
    simp only [compRename, Comp.queriesAt, compRename_pureEval? ξ c ρ ρ' hρ, ihc ξ ρ ρ' hρ]
    cases c.pureEval? ρ with
    | none => simp [compRename_queries]
    | some x => simp [ihk (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)]
  | ite b c d ihc ihd =>
    simp only [compRename, Comp.queriesAt, exprRename_eval b ξ ρ ρ' hρ]
    cases b.eval ρ <;> simp [ihc ξ ρ ρ' hρ, ihd ξ ρ ρ' hρ]
  | caseOpt e n s ihn ihs =>
    simp only [compRename, Comp.queriesAt, exprRename_eval e ξ ρ ρ' hρ]
    cases e.eval ρ with
    | none => exact ihn ξ ρ ρ' hρ
    | some x => exact ihs (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)
  | caseSum e l r ihl ihr =>
    simp only [compRename, Comp.queriesAt, exprRename_eval e ξ ρ ρ' hρ]
    cases e.eval ρ with
    | inl x => exact ihl (liftRen ξ) (.cons x ρ) (.cons x ρ') (liftRen_get x hρ)
    | inr y => exact ihr (liftRen ξ) (.cons y ρ) (.cons y ρ') (liftRen_get y hρ)
  | sample _ _ | query _ _ => rfl
  | iter _ _ _ _ | findM _ _ _ _ | anyM _ _ _ _ | mapM _ _ _ _
  | consumeFirstM _ _ _ _ _ | foldM _ _ _ _ =>
    simp [compRename, Comp.queriesAt, compRename_queries]

/-- Witness that `c` at environment `ρ` dispatches in `d` pure steps to a weakened copy of `arm`
    whose `cost`, `costAt`, `queries`, `queriesAt`, and `eval` agree with `arm` at `.cons x ρ`. -/
@[expose] def AuthArmDispatch {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    (c : Comp pqAtomicOps I Γ out) (ρ : Env Γ) (d : ℕ)
    (arm : Comp pqAtomicOps I (argTy :: Γ) out) (x : argTy.denote) : Prop :=
  ∃ (Δ : List (Ty pqAtomicSig)) (arm' : Comp pqAtomicOps I Δ out) (ρ' : Env Δ),
    DispatchesTo c ρ d arm' ρ' ∧
    arm'.cost = arm.cost ∧
    arm'.costAt ρ' = arm.costAt (.cons x ρ) ∧
    (∀ w ws, arm'.queries w ws = arm.queries w ws) ∧
    (∀ w ws, arm'.queriesAt w ws ρ' = arm.queriesAt w ws (.cons x ρ)) ∧
    arm'.eval ρ' = arm.eval (.cons x ρ)

theorem AuthArmDispatch.costAt_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : AuthArmDispatch c ρ d arm x) :
    c.costAt ρ = arm.costAt (.cons x ρ) + d := by
  obtain ⟨_, _, _, hdisp, _, hca, _, _, _⟩ := h
  rw [costAt_eq_of_dispatchesTo hdisp, hca]

theorem AuthArmDispatch.costAt_le_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d cDisp : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : AuthArmDispatch c ρ d arm x) (hd : d ≤ cDisp) :
    c.costAt ρ ≤ arm.cost + cDisp := by
  obtain ⟨_, _, _, hdisp, hc, _, _, _, _⟩ := h
  have := costAt_le_arm_cost_of_dispatchesTo hdisp hd
  omega

theorem AuthArmDispatch.queriesAt_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : AuthArmDispatch c ρ d arm x) :
    c.queriesAt w ws ρ = arm.queriesAt w ws (.cons x ρ) := by
  obtain ⟨_, _, _, hdisp, _, _, _, hqa, _⟩ := h
  rw [queriesAt_eq_of_dispatchesTo w ws hdisp, hqa]

theorem AuthArmDispatch.queriesAt_le_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : AuthArmDispatch c ρ d arm x) :
    c.queriesAt w ws ρ ≤ arm.queries w ws := by
  obtain ⟨_, _, _, hdisp, _, _, hq, _, _⟩ := h
  rw [← hq]
  exact queriesAt_le_arm_queries_of_dispatchesTo w ws hdisp

theorem AuthArmDispatch.eval_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : AuthArmDispatch c ρ d arm x) :
    c.eval ρ = arm.eval (.cons x ρ) := by
  obtain ⟨_, _, _, hdisp, _, _, _, _, hev⟩ := h
  rw [eval_eq_of_dispatchesTo hdisp, hev]

section PerConstructor

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
  {Γ : List (Ty pqAtomicSig)} {out : Ty pqAtomicSig} {S : Setup}
  (qE : Expr pqAtomicOps Γ authQueryAtomicTy)
  (armInitPrin  : Comp pqAtomicOps I (.nat :: Γ) out)
  (armCorrupt   : Comp pqAtomicOps I (.nat :: Γ) out)
  (armGenSpk    : Comp pqAtomicOps I (.prod .nat .nat :: Γ) out)
  (armGenOpk    : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: Γ) out)
  (armSendOpk   : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) out)
  (armSendNoOpk : Comp pqAtomicOps I (authSendQAtomicTy :: Γ) out)
  (armRecvOpk   : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) out)
  (armRecvNoOpk : Comp pqAtomicOps I (authRecvQAtomicTy :: Γ) out)
  (armRo        : Comp pqAtomicOps I (PB 192 :: Γ) out)
  (armRoRoot    : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: Γ) out)
  (armRevealDh  : Comp pqAtomicOps I (.unit :: Γ) out)
  (armRegister  : Comp pqAtomicOps I (PB 32 :: Γ) out)

private theorem mkAuthArmDispatch {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ Δ : List (Ty pqAtomicSig)} {argTy out : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d d' : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    {ξ : ∀ {a}, Var (argTy :: Γ) a → Var (argTy :: Δ) a} {ρ_mid : Env Δ}
    (hdisp : DispatchesTo c ρ d (compRename ξ arm) (.cons x ρ_mid))
    (hd : d = d')
    (hξ0 : ξ .zero = .zero)
    (hξs : ∀ {a} (v : Var Γ a), (Env.cons x ρ_mid).get (ξ (.succ v)) = ρ.get v) :
    AuthArmDispatch c ρ d' arm x := by
  have hget : ∀ {a} (v : Var (argTy :: Γ) a),
      (Env.cons x ρ_mid).get (ξ v) = (Env.cons x ρ).get v := by
    intro a v; cases v with
    | zero => rw [hξ0]; rfl
    | succ v => exact hξs v
  exact ⟨argTy :: Δ, compRename ξ arm, .cons x ρ_mid, hd ▸ hdisp,
    compRename_cost ξ arm,
    compRename_costAt ξ arm (.cons x ρ) (.cons x ρ_mid) hget,
    fun w ws => compRename_queries w ws ξ arm,
    fun w ws => compRename_queriesAt w ws ξ arm (.cons x ρ) (.cons x ρ_mid) hget,
    compRename_eval arm ξ (.cons x ρ) (.cons x ρ_mid) hget⟩

theorem dispatchAuthQ_dispatchesTo_initPrin (ρ : Env Γ) (u : Fin S.N_id)
    (hq : qE.eval ρ = (authCodec S).qenc (.initPrin u)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 1) armInitPrin u.val := by
  refine ⟨.nat :: Γ, armInitPrin, .cons u.val ρ, ?_, rfl, rfl,
    fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  have hd : 0 + qE.costAt ρ + 1 = qE.costAt ρ + 1 := by omega
  exact hd ▸ DispatchesTo.caseSum_inl hq (DispatchesTo.refl _ _)

theorem dispatchAuthQ_dispatchesTo_corruptIK (ρ : Env Γ) (u : Fin S.N_id)
    (hq : qE.eval ρ = (authCodec S).qenc (.corruptIK u)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 3) armCorrupt u.val :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_genSPK (ρ : Env Γ) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hq : qE.eval ρ = (authCodec S).qenc (.genSPK u j)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 5) armGenSpk (u.val, j.val) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_genOPK (ρ : Env Γ)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hq : qE.eval ρ = (authCodec S).qenc (.genOPK u j o)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 7) armGenOpk (u.val, (j.val, o.val)) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_sendOPK (ρ : Env Γ)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bu : PreKeyBundleInput) (m0 m1 : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.sendOPK u i bu m0 m1)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 9) armSendOpk
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_sendNoOPK (ρ : Env Γ)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bu : PreKeyBundleInput) (m0 m1 : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.sendNoOPK u i bu m0 m1)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 11) armSendNoOpk
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_recvOPK (ρ : Env Γ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hq : qE.eval ρ = (authCodec S).qenc (.recvOPK k j o msg)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 13) armRecvOpk (k.val, (j.val, (o.val, preKeyMsgV msg))) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_recvNoOPK (ρ : Env Γ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hq : qE.eval ρ = (authCodec S).qenc (.recvNoOPK k j l msg)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 15) armRecvNoOpk (k.val, (j.val, (l.val, preKeyMsgV msg))) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_roQuery (ρ : Env Γ) (sec : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.roQuery sec)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 17) armRo sec :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_roRootQuery (ρ : Env Γ) (rk dh : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.roRootQuery rk dh)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 19) armRoRoot (rk, dh) :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_revealDhSecrets (ρ : Env Γ)
    (hq : qE.eval ρ = (authCodec S).qenc .revealDhSecrets) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 21) armRevealDh () :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

theorem dispatchAuthQ_dispatchesTo_registerKey (ρ : Env Γ) (sk : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.registerKey sk)) :
    AuthArmDispatch (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 21) armRegister sk :=
  mkAuthArmDispatch
    (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
      DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

private def ArmDispPoly {argTy : Ty pqAtomicSig}
    (c : Comp pqAtomicOps I Γ out) (ρ : Env Γ) (d : ℕ)
    (arm : Comp pqAtomicOps I (argTy :: Γ) out) (x : argTy.denote) : Prop :=
  ∃ (Δ : List (Ty pqAtomicSig)) (arm' : Comp pqAtomicOps I Δ out) (ρ' : Env Δ),
    DispatchesTo c ρ d arm' ρ' ∧
    arm'.cost = arm.cost ∧
    arm'.costAt ρ' = arm.costAt (.cons x ρ) ∧
    (∀ w ws, arm'.queries w ws = arm.queries w ws) ∧
    (∀ w ws, arm'.queriesAt w ws ρ' = arm.queriesAt w ws (.cons x ρ))

private theorem mkArmDispPoly {Δ : List (Ty pqAtomicSig)} {argTy : Ty pqAtomicSig}
    {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d d' : ℕ}
    {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    {ξ : ∀ {a}, Var (argTy :: Γ) a → Var (argTy :: Δ) a} {ρ_mid : Env Δ}
    (hdisp : DispatchesTo c ρ d (compRename ξ arm) (.cons x ρ_mid))
    (hd : d = d')
    (hξ0 : ξ .zero = .zero)
    (hξs : ∀ {a} (v : Var Γ a), (Env.cons x ρ_mid).get (ξ (.succ v)) = ρ.get v) :
    ArmDispPoly c ρ d' arm x := by
  have hget : ∀ {a} (v : Var (argTy :: Γ) a),
      (Env.cons x ρ_mid).get (ξ v) = (Env.cons x ρ).get v := by
    intro a v; cases v with
    | zero => rw [hξ0]; rfl
    | succ v => exact hξs v
  exact ⟨argTy :: Δ, compRename ξ arm, .cons x ρ_mid, hd ▸ hdisp,
    compRename_cost ξ arm,
    compRename_costAt ξ arm (.cons x ρ) (.cons x ρ_mid) hget,
    fun w ws => compRename_queries w ws ξ arm,
    fun w ws => compRename_queriesAt w ws ξ arm (.cons x ρ) (.cons x ρ_mid) hget⟩

private theorem dispPoly_initPrin (ρ : Env Γ) (u : Fin S.N_id)
    (hq : qE.eval ρ = (authCodec S).qenc (.initPrin u)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 1) armInitPrin u.val := by
  refine ⟨.nat :: Γ, armInitPrin, .cons u.val ρ, ?_, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hd : 0 + qE.costAt ρ + 1 = qE.costAt ρ + 1 := by omega
  exact hd ▸ DispatchesTo.caseSum_inl hq (DispatchesTo.refl _ _)

private theorem dispPoly_corruptIK (ρ : Env Γ) (u : Fin S.N_id)
    (hq : qE.eval ρ = (authCodec S).qenc (.corruptIK u)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 3) armCorrupt u.val :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

private theorem dispPoly_genSPK (ρ : Env Γ) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hq : qE.eval ρ = (authCodec S).qenc (.genSPK u j)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 5) armGenSpk (u.val, j.val) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _) (by omega) rfl (fun _ => rfl)

private theorem dispPoly_genOPK (ρ : Env Γ) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hq : qE.eval ρ = (authCodec S).qenc (.genOPK u j o)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 7) armGenOpk (u.val, (j.val, o.val)) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

private theorem dispPoly_sendOPK (ρ : Env Γ)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bu : PreKeyBundleInput) (m0 m1 : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.sendOPK u i bu m0 m1)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 9) armSendOpk
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _) (by omega) rfl (fun _ => rfl)

private theorem dispPoly_sendNoOPK (ρ : Env Γ)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bu : PreKeyBundleInput) (m0 m1 : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.sendNoOPK u i bu m0 m1)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 11) armSendNoOpk
      (u.val, (i.val, (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1)))) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

private theorem dispPoly_recvOPK (ρ : Env Γ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hq : qE.eval ρ = (authCodec S).qenc (.recvOPK k j o msg)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 13) armRecvOpk (k.val, (j.val, (o.val, preKeyMsgV msg))) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _) (by omega) rfl (fun _ => rfl)

private theorem dispPoly_recvNoOPK (ρ : Env Γ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hq : qE.eval ρ = (authCodec S).qenc (.recvNoOPK k j l msg)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 15) armRecvNoOpk (k.val, (j.val, (l.val, preKeyMsgV msg))) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

private theorem dispPoly_roQuery (ρ : Env Γ) (sec : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.roQuery sec)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 17) armRo sec :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _) (by omega) rfl (fun _ => rfl)

private theorem dispPoly_roRootQuery (ρ : Env Γ) (rk dh : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.roRootQuery rk dh)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 19) armRoRoot (rk, dh) :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _)
    (by omega) rfl (fun _ => rfl)

private theorem dispPoly_revealDhSecrets (ρ : Env Γ)
    (hq : qE.eval ρ = (authCodec S).qenc .revealDhSecrets) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 21) armRevealDh () :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inl rfl <| DispatchesTo.refl _ _) (by omega) rfl (fun _ => rfl)

private theorem dispPoly_registerKey (ρ : Env Γ) (sk : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.registerKey sk)) :
    ArmDispPoly (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
      armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister)
      ρ (qE.costAt ρ + 21) armRegister sk :=
  mkArmDispPoly (DispatchesTo.caseSum_inr hq <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.caseSum_var_inr rfl <|
    DispatchesTo.caseSum_var_inr rfl <| DispatchesTo.refl _ _) (by omega) rfl (fun _ => rfl)

private theorem arm_disp_ex {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d B : ℕ}
    {argTy : Ty pqAtomicSig} {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : ArmDispPoly c ρ d arm x) (hd : d ≤ B) :
    ∃ (Δ : List (Ty pqAtomicSig)) (arm' : Comp pqAtomicOps I Δ out) (ρ' : Env Δ) (d' : ℕ),
      DispatchesTo c ρ d' arm' ρ' ∧ d' ≤ B := by
  obtain ⟨Δ, arm', ρ', hdisp, _⟩ := h
  exact ⟨Δ, arm', ρ', d, hdisp, hd⟩

/-- Every encoded `AuthQuery` dispatches through `dispatchAuthQ` in at most `qE.costAt ρ + 21`
    pure steps. -/
theorem dispatchAuthQ_dispatchesTo (ρ : Env Γ) (q : AuthQuery S)
    (hq : qE.eval ρ = (authCodec S).qenc q) :
    ∃ (Δ : List (Ty pqAtomicSig)) (arm' : Comp pqAtomicOps I Δ out) (ρ' : Env Δ) (d : ℕ),
      DispatchesTo (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk
        armSendNoOpk armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister) ρ d arm' ρ' ∧
      d ≤ qE.costAt ρ + 21 := by
  cases q with
  | initPrin u => apply arm_disp_ex; { apply dispPoly_initPrin; exact hq }; omega
  | corruptIK u => apply arm_disp_ex; { apply dispPoly_corruptIK; exact hq }; omega
  | genSPK u j => apply arm_disp_ex; { apply dispPoly_genSPK; exact hq }; omega
  | genOPK u j o => apply arm_disp_ex; { apply dispPoly_genOPK; exact hq }; omega
  | sendOPK u i bu m0 m1 => apply arm_disp_ex; { apply dispPoly_sendOPK; exact hq }; omega
  | sendNoOPK u i bu m0 m1 => apply arm_disp_ex; { apply dispPoly_sendNoOPK; exact hq }; omega
  | recvOPK k j o msg => apply arm_disp_ex; { apply dispPoly_recvOPK; exact hq }; omega
  | recvNoOPK k j l msg => apply arm_disp_ex; { apply dispPoly_recvNoOPK; exact hq }; omega
  | roQuery sec => apply arm_disp_ex; { apply dispPoly_roQuery; exact hq }; omega
  | roRootQuery rk dh => apply arm_disp_ex; { apply dispPoly_roRootQuery; exact hq }; omega
  | revealDhSecrets => apply arm_disp_ex; { apply dispPoly_revealDhSecrets; exact hq }; omega
  | registerKey sk => apply arm_disp_ex; { apply dispPoly_registerKey; exact hq }; omega

private theorem arm_disp_costAt_eq {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d : ℕ}
    {argTy : Ty pqAtomicSig} {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : ArmDispPoly c ρ d arm x) :
    c.costAt ρ = arm.costAt (.cons x ρ) + d := by
  obtain ⟨_, _, _, hdisp, _, hca, _, _⟩ := h
  rw [costAt_eq_of_dispatchesTo hdisp, hca]

theorem dispatchAuthQ_costAt_roQuery_eq (ρ : Env Γ) (sec : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.roQuery sec)) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt ρ =
      armRo.costAt (.cons sec ρ) + (qE.costAt ρ + 17) := by
  apply arm_disp_costAt_eq; apply dispPoly_roQuery; exact hq

theorem dispatchAuthQ_costAt_roRootQuery_eq (ρ : Env Γ) (rk dh : Bytes)
    (hq : qE.eval ρ = (authCodec S).qenc (.roRootQuery rk dh)) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt ρ =
      armRoRoot.costAt (.cons (rk, dh) ρ) + (qE.costAt ρ + 19) := by
  apply arm_disp_costAt_eq; apply dispPoly_roRootQuery; exact hq

private theorem arm_disp_cost_le {c : Comp pqAtomicOps I Γ out} {ρ : Env Γ} {d B cDisp : ℕ}
    {argTy : Ty pqAtomicSig} {arm : Comp pqAtomicOps I (argTy :: Γ) out} {x : argTy.denote}
    (h : ArmDispPoly c ρ d arm x) (harm : arm.cost ≤ B) (hd : d ≤ cDisp) :
    c.costAt ρ ≤ B + cDisp := by
  obtain ⟨_, _, _, hdisp, hcost, _, _, _⟩ := h
  have := costAt_le_arm_cost_of_dispatchesTo hdisp hd
  omega

/-- Kind-1 (`.roQuery` and `.roRootQuery`) `Comp.costAt` bound for `dispatchAuthQ`. -/
theorem dispatchAuthQ_costAt_kind1_le (ρ : Env Γ) (q : AuthQuery S) {B₁ : ℕ}
    (hk : authQueryKind q = 1) (hq : qE.eval ρ = (authCodec S).qenc q)
    (hRo : armRo.cost ≤ B₁) (hRoRoot : armRoRoot.cost ≤ B₁) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt ρ ≤
      B₁ + qE.costAt ρ + 19 := by
  rw [Nat.add_assoc]
  cases q with
  | roQuery sec =>
    apply arm_disp_cost_le; { apply dispPoly_roQuery; exact hq }; { exact hRo }; omega
  | roRootQuery rk dh =>
    apply arm_disp_cost_le; { apply dispPoly_roRootQuery; exact hq }; { exact hRoRoot }; omega
  | _ => simp [authQueryKind] at hk

/-- Kind-0 (online) `Comp.costAt` bound for `dispatchAuthQ`. -/
theorem dispatchAuthQ_costAt_kind0_le (ρ : Env Γ) (q : AuthQuery S) {B₀ : ℕ}
    (hk : authQueryKind q = 0) (hq : qE.eval ρ = (authCodec S).qenc q)
    (hInit : armInitPrin.cost ≤ B₀) (hCorr : armCorrupt.cost ≤ B₀)
    (hSpk : armGenSpk.cost ≤ B₀) (hOpk : armGenOpk.cost ≤ B₀)
    (hSO : armSendOpk.cost ≤ B₀) (hSN : armSendNoOpk.cost ≤ B₀)
    (hRO : armRecvOpk.cost ≤ B₀) (hRN : armRecvNoOpk.cost ≤ B₀)
    (hRev : armRevealDh.cost ≤ B₀) (hReg : armRegister.cost ≤ B₀) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt ρ ≤
      B₀ + qE.costAt ρ + 21 := by
  rw [Nat.add_assoc]
  cases q with
  | initPrin u => apply arm_disp_cost_le; { apply dispPoly_initPrin; exact hq }; { exact hInit }; omega
  | corruptIK u => apply arm_disp_cost_le; { apply dispPoly_corruptIK; exact hq }; { exact hCorr }; omega
  | genSPK u j => apply arm_disp_cost_le; { apply dispPoly_genSPK; exact hq }; { exact hSpk }; omega
  | genOPK u j o => apply arm_disp_cost_le; { apply dispPoly_genOPK; exact hq }; { exact hOpk }; omega
  | sendOPK u i bu m0 m1 => apply arm_disp_cost_le; { apply dispPoly_sendOPK; exact hq }; { exact hSO }; omega
  | sendNoOPK u i bu m0 m1 => apply arm_disp_cost_le; { apply dispPoly_sendNoOPK; exact hq }; { exact hSN }; omega
  | recvOPK k j o msg => apply arm_disp_cost_le; { apply dispPoly_recvOPK; exact hq }; { exact hRO }; omega
  | recvNoOPK k j l msg => apply arm_disp_cost_le; { apply dispPoly_recvNoOPK; exact hq }; { exact hRN }; omega
  | roQuery _ | roRootQuery _ _ => simp [authQueryKind] at hk
  | revealDhSecrets => apply arm_disp_cost_le; { apply dispPoly_revealDhSecrets; exact hq }; { exact hRev }; omega
  | registerKey sk => apply arm_disp_cost_le; { apply dispPoly_registerKey; exact hq }; { exact hReg }; omega

private theorem max_step_cost {l r B k : ℕ} (hl : l ≤ B) (hr : r ≤ B + k) :
    1 + max l r + 1 ≤ B + (k + 2) := by
  have : max l r ≤ B + k := Nat.max_le.mpr ⟨by omega, hr⟩
  omega

theorem dispatchAuthQ_cost_le {B : ℕ}
    (hInit : armInitPrin.cost ≤ B) (hCorr : armCorrupt.cost ≤ B)
    (hSpk : armGenSpk.cost ≤ B) (hOpk : armGenOpk.cost ≤ B)
    (hSO : armSendOpk.cost ≤ B) (hSN : armSendNoOpk.cost ≤ B)
    (hRO : armRecvOpk.cost ≤ B) (hRN : armRecvNoOpk.cost ≤ B)
    (hRo : armRo.cost ≤ B) (hRoR : armRoRoot.cost ≤ B)
    (hRev : armRevealDh.cost ≤ B) (hReg : armRegister.cost ≤ B) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).cost ≤
      B + qE.cost + 21 := by
  unfold dispatchAuthQ
  simp only [Comp.cost, Expr.v0, Expr.cost, compRename_cost]
  have h10 : 1 + max armRevealDh.cost armRegister.cost + 1 ≤ B + 2 :=
    max_step_cost (k := 0) hRev (by omega)
  have h9 := max_step_cost hRoR h10
  have h8 := max_step_cost hRo h9
  have h7 := max_step_cost hRN h8
  have h6 := max_step_cost hRO h7
  have h5 := max_step_cost hSN h6
  have h4 := max_step_cost hSO h5
  have h3 := max_step_cost hOpk h4
  have h2 := max_step_cost hSpk h3
  have h1 := max_step_cost hCorr h2
  have h0 : max armInitPrin.cost _ ≤ B + 20 := Nat.max_le.mpr ⟨by omega, h1⟩
  omega

theorem dispatchAuthQ_queries_le (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Q : ℕ}
    (hInit : armInitPrin.queries w ws ≤ Q) (hCorr : armCorrupt.queries w ws ≤ Q)
    (hSpk : armGenSpk.queries w ws ≤ Q) (hOpk : armGenOpk.queries w ws ≤ Q)
    (hSO : armSendOpk.queries w ws ≤ Q) (hSN : armSendNoOpk.queries w ws ≤ Q)
    (hRO : armRecvOpk.queries w ws ≤ Q) (hRN : armRecvNoOpk.queries w ws ≤ Q)
    (hRo : armRo.queries w ws ≤ Q) (hRoR : armRoRoot.queries w ws ≤ Q)
    (hRev : armRevealDh.queries w ws ≤ Q) (hReg : armRegister.queries w ws ≤ Q) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).queries w ws ≤ Q := by
  unfold dispatchAuthQ
  simp only [Comp.queries, compRename_queries]
  refine Nat.max_le.mpr ⟨hInit, Nat.max_le.mpr ⟨hCorr, Nat.max_le.mpr ⟨hSpk,
    Nat.max_le.mpr ⟨hOpk, Nat.max_le.mpr ⟨hSO, Nat.max_le.mpr ⟨hSN,
      Nat.max_le.mpr ⟨hRO, Nat.max_le.mpr ⟨hRN, Nat.max_le.mpr ⟨hRo,
        Nat.max_le.mpr ⟨hRoR, Nat.max_le.mpr ⟨hRev, hReg⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

private theorem arm_disp_q_le {c : Comp pqAtomicOps I Γ out} {X : Ty pqAtomicSig}
    {arm : Comp pqAtomicOps I (X :: Γ) out} {ρ : Env Γ} {v : X.denote} {d Q : ℕ}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hd : ArmDispPoly c ρ d arm v) (hQ : arm.queries w ws ≤ Q) :
    c.queriesAt w ws ρ ≤ Q := by
  obtain ⟨_, _, _, hdisp, _, _, hq, _⟩ := hd
  have h1 := queriesAt_le_arm_queries_of_dispatchesTo w ws hdisp
  have h2 := hq w ws
  omega

theorem dispatchAuthQ_queriesAt_kind1_le (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (ρ : Env Γ) (q : AuthQuery S) {Q₁ : ℕ}
    (hk : authQueryKind q = 1) (hq : qE.eval ρ = (authCodec S).qenc q)
    (hRo : armRo.queries w ws ≤ Q₁) (hRoRoot : armRoRoot.queries w ws ≤ Q₁) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).queriesAt w ws ρ ≤ Q₁ := by
  cases q with
  | roQuery sec =>
    apply arm_disp_q_le w ws; { apply dispPoly_roQuery; exact hq }; exact hRo
  | roRootQuery rk dh =>
    apply arm_disp_q_le w ws; { apply dispPoly_roRootQuery; exact hq }; exact hRoRoot
  | _ => simp [authQueryKind] at hk

theorem dispatchAuthQ_queriesAt_kind0_le (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (ρ : Env Γ) (q : AuthQuery S) {Q₀ : ℕ}
    (hk : authQueryKind q = 0) (hq : qE.eval ρ = (authCodec S).qenc q)
    (hInit : armInitPrin.queries w ws ≤ Q₀) (hCorr : armCorrupt.queries w ws ≤ Q₀)
    (hSpk : armGenSpk.queries w ws ≤ Q₀) (hOpk : armGenOpk.queries w ws ≤ Q₀)
    (hSO : armSendOpk.queries w ws ≤ Q₀) (hSN : armSendNoOpk.queries w ws ≤ Q₀)
    (hRO : armRecvOpk.queries w ws ≤ Q₀) (hRN : armRecvNoOpk.queries w ws ≤ Q₀)
    (hRev : armRevealDh.queries w ws ≤ Q₀) (hReg : armRegister.queries w ws ≤ Q₀) :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).queriesAt w ws ρ ≤ Q₀ := by
  cases q with
  | initPrin u =>
    apply arm_disp_q_le w ws; { apply dispPoly_initPrin; exact hq }; exact hInit
  | corruptIK u =>
    apply arm_disp_q_le w ws; { apply dispPoly_corruptIK; exact hq }; exact hCorr
  | genSPK u j =>
    apply arm_disp_q_le w ws; { apply dispPoly_genSPK; exact hq }; exact hSpk
  | genOPK u j o =>
    apply arm_disp_q_le w ws; { apply dispPoly_genOPK; exact hq }; exact hOpk
  | sendOPK u i bu m0 m1 =>
    apply arm_disp_q_le w ws; { apply dispPoly_sendOPK; exact hq }; exact hSO
  | sendNoOPK u i bu m0 m1 =>
    apply arm_disp_q_le w ws; { apply dispPoly_sendNoOPK; exact hq }; exact hSN
  | recvOPK k j o msg =>
    apply arm_disp_q_le w ws; { apply dispPoly_recvOPK; exact hq }; exact hRO
  | recvNoOPK k j l msg =>
    apply arm_disp_q_le w ws; { apply dispPoly_recvNoOPK; exact hq }; exact hRN
  | roQuery _ | roRootQuery _ _ => simp [authQueryKind] at hk
  | revealDhSecrets =>
    apply arm_disp_q_le w ws; { apply dispPoly_revealDhSecrets; exact hq }; exact hRev
  | registerKey sk =>
    apply arm_disp_q_le w ws; { apply dispPoly_registerKey; exact hq }; exact hReg

theorem dispatchAuthQ_size_le :
    (dispatchAuthQ qE armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).size ≤
      qE.size + armInitPrin.size + armCorrupt.size + armGenSpk.size + armGenOpk.size +
        armSendOpk.size + armSendNoOpk.size + armRecvOpk.size + armRecvNoOpk.size +
        armRo.size + armRoRoot.size + armRevealDh.size + armRegister.size + 21 := by
  unfold dispatchAuthQ
  simp only [Comp.size, Expr.v0, Expr.size, compRename_size]
  omega

end PerConstructor

section HandlerV1

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
  {sTy out : Ty pqAtomicSig} {Γ₀ : List (Ty pqAtomicSig)} {S : Setup}
  (armInitPrin  : Comp pqAtomicOps I (.nat :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armCorrupt   : Comp pqAtomicOps I (.nat :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armGenSpk    : Comp pqAtomicOps I (.prod .nat .nat :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armGenOpk    : Comp pqAtomicOps I (.prod .nat (.prod .nat .nat) :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armSendOpk   : Comp pqAtomicOps I (authSendQAtomicTy :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armSendNoOpk : Comp pqAtomicOps I (authSendQAtomicTy :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armRecvOpk   : Comp pqAtomicOps I (authRecvQAtomicTy :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armRecvNoOpk : Comp pqAtomicOps I (authRecvQAtomicTy :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armRo        : Comp pqAtomicOps I (PB 192 :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armRoRoot    : Comp pqAtomicOps I (.prod (PB 32) (PB 32) :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armRevealDh  : Comp pqAtomicOps I (.unit :: sTy :: authQueryAtomicTy :: Γ₀) out)
  (armRegister  : Comp pqAtomicOps I (PB 32 :: sTy :: authQueryAtomicTy :: Γ₀) out)

theorem dispatchAuthQ_v1_costAt_kind1_le
    (s : sTy.denote) (q : AuthQuery S) (ρ₀ : Env Γ₀) {B₁ : ℕ}
    (hk : authQueryKind q = 1) (hRo : armRo.cost ≤ B₁) (hRoRoot : armRoRoot.cost ≤ B₁) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt
        (.cons s (.cons ((authCodec S).qenc q) ρ₀)) ≤ B₁ + 20 := by
  have h : (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt
        (.cons s (.cons ((authCodec S).qenc q) ρ₀)) ≤
      B₁ + (Expr.v1 : Expr pqAtomicOps (sTy :: authQueryAtomicTy :: Γ₀) authQueryAtomicTy).costAt
        (.cons s (.cons ((authCodec S).qenc q) ρ₀)) + 19 := by
    apply dispatchAuthQ_costAt_kind1_le
    · exact hk
    · rfl
    · exact hRo
    · exact hRoRoot
  have hv1 : (Expr.v1 : Expr pqAtomicOps (sTy :: authQueryAtomicTy :: Γ₀) authQueryAtomicTy).costAt
      (.cons s (.cons ((authCodec S).qenc q) ρ₀)) = 1 := rfl
  omega

theorem dispatchAuthQ_v1_costAt_kind0_le
    (s : sTy.denote) (q : AuthQuery S) (ρ₀ : Env Γ₀) {B₀ : ℕ}
    (hk : authQueryKind q = 0)
    (hInit : armInitPrin.cost ≤ B₀) (hCorr : armCorrupt.cost ≤ B₀)
    (hSpk : armGenSpk.cost ≤ B₀) (hOpk : armGenOpk.cost ≤ B₀)
    (hSO : armSendOpk.cost ≤ B₀) (hSN : armSendNoOpk.cost ≤ B₀)
    (hRO : armRecvOpk.cost ≤ B₀) (hRN : armRecvNoOpk.cost ≤ B₀)
    (hRev : armRevealDh.cost ≤ B₀) (hReg : armRegister.cost ≤ B₀) :
    (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt
        (.cons s (.cons ((authCodec S).qenc q) ρ₀)) ≤ B₀ + 22 := by
  have h : (dispatchAuthQ .v1 armInitPrin armCorrupt armGenSpk armGenOpk armSendOpk armSendNoOpk
      armRecvOpk armRecvNoOpk armRo armRoRoot armRevealDh armRegister).costAt
        (.cons s (.cons ((authCodec S).qenc q) ρ₀)) ≤
      B₀ + (Expr.v1 : Expr pqAtomicOps (sTy :: authQueryAtomicTy :: Γ₀) authQueryAtomicTy).costAt
        (.cons s (.cons ((authCodec S).qenc q) ρ₀)) + 21 := by
    apply dispatchAuthQ_costAt_kind0_le
    · exact hk
    · rfl
    · exact hInit
    · exact hCorr
    · exact hSpk
    · exact hOpk
    · exact hSO
    · exact hSN
    · exact hRO
    · exact hRN
    · exact hRev
    · exact hReg
  have hv1 : (Expr.v1 : Expr pqAtomicOps (sTy :: authQueryAtomicTy :: Γ₀) authQueryAtomicTy).costAt
      (.cons s (.cons ((authCodec S).qenc q) ρ₀)) = 1 := rfl
  omega

end HandlerV1

end DispatchAuthQSpine

/-! ## Kind-1 AVL Shadow RO Arms -/

section ShadowRoBounds

theorem roShadowStepC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowStepC A cap roListE tblE secE).queries w (fun _ => 0) = 0 :=
  AuthCoreKCostBaseRo.roShadowStepC_queries_zero A w cap roListE tblE secE

theorem roShadowStepC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowStepC A cap roListE tblE secE).cost ≤
      4420 * bits cap + 1175 + roListE.cost + tblE.cost + 2 * secE.cost :=
  AuthCoreKCostBaseRo.roShadowStepC_cost_le A cap roListE tblE secE

theorem roShadowStepC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy)
    (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roShadowStepC A cap roListE tblE secE).size ≤
      1800 + 2 * bits (avlHeightCap cap) + roListE.size + tblE.size + 2 * secE.size :=
  AuthCoreKCostBaseRo.roShadowStepC_size_le A cap roListE tblE secE

theorem roRootShadowStepC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootShadowStepC A cap rootListE tblE inpE).queries w (fun _ => 0) = 0 :=
  AuthCoreKCostBaseRo.roRootShadowStepC_queries_zero A w cap rootListE tblE inpE

theorem roRootShadowStepC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootShadowStepC A cap rootListE tblE inpE).cost ≤
      4080 * bits cap + 775 + rootListE.cost + tblE.cost + 2 * inpE.cost :=
  AuthCoreKCostBaseRo.roRootShadowStepC_cost_le A cap rootListE tblE inpE

theorem roRootShadowStepC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootShadowStepC A cap rootListE tblE inpE).size ≤
      1860 + 2 * bits (avlHeightCap cap) + rootListE.size + tblE.size + 2 * inpE.size :=
  AuthCoreKCostBaseRo.roRootShadowStepC_size_le A cap rootListE tblE inpE

theorem roBaseShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roBaseShadowArmC A cap sE secE).queries w (fun _ => 0) = 0 :=
  AuthCoreKCostBaseRo.roBaseShadowArmC_queries_zero A w cap sE secE

theorem roBaseShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roBaseShadowArmC A cap sE secE).cost ≤
      4420 * bits cap + 1515 + sE.cost + secE.cost :=
  AuthCoreKCostBaseRo.roBaseShadowArmC_cost_le A cap sE secE

theorem roBaseShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192))
    (hs : sE.cost ≤ 5) (hsec : secE.cost ≤ 5) :
    (roBaseShadowArmC A cap sE secE).cost ≤ 4420 * bits cap + 1525 :=
  AuthCoreKCostBaseRo.roBaseShadowArmC_var_cost_le A cap sE secE hs hsec

theorem roBaseShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roBaseShadowArmC A cap sE secE).size ≤
      2200 + 2 * bits (avlHeightCap cap) + sE.size + secE.size :=
  AuthCoreKCostBaseRo.roBaseShadowArmC_size_le A cap sE secE

theorem roRootBaseShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootBaseShadowArmC A cap sE inpE).queries w (fun _ => 0) = 0 :=
  AuthCoreKCostBaseRo.roRootBaseShadowArmC_queries_zero A w cap sE inpE

theorem roRootBaseShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootBaseShadowArmC A cap sE inpE).cost ≤
      4080 * bits cap + 1120 + sE.cost + inpE.cost :=
  AuthCoreKCostBaseRo.roRootBaseShadowArmC_cost_le A cap sE inpE

theorem roRootBaseShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (hs : sE.cost ≤ 5) (hinp : inpE.cost ≤ 5) :
    (roRootBaseShadowArmC A cap sE inpE).cost ≤ 4420 * bits cap + 1350 :=
  AuthCoreKCostBaseRo.roRootBaseShadowArmC_var_cost_le A cap sE inpE hs hinp

theorem roRootBaseShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ authBaseShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootBaseShadowArmC A cap sE inpE).size ≤
      2250 + 2 * bits (avlHeightCap cap) + sE.size + inpE.size :=
  AuthCoreKCostBaseRo.roRootBaseShadowArmC_size_le A cap sE inpE

theorem roFixedShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roFixedShadowArmC A cap fsE secE).queries w (fun _ => 0) = 0 :=
  AuthCoreKCostBaseRo.roFixedShadowArmC_queries_zero A w cap fsE secE

theorem roFixedShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roFixedShadowArmC A cap fsE secE).cost ≤
      4420 * bits cap + 1525 + fsE.cost + secE.cost :=
  AuthCoreKCostBaseRo.roFixedShadowArmC_cost_le A cap fsE secE

theorem roFixedShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192))
    (hfs : fsE.cost ≤ 5) (hsec : secE.cost ≤ 5) :
    (roFixedShadowArmC A cap fsE secE).cost ≤ 4420 * bits cap + 1535 :=
  AuthCoreKCostBaseRo.roFixedShadowArmC_var_cost_le A cap fsE secE hfs hsec

theorem roFixedShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) (secE : Expr pqAtomicOps Γ (PB 192)) :
    (roFixedShadowArmC A cap fsE secE).size ≤
      2350 + 2 * bits (avlHeightCap cap) + fsE.size + secE.size :=
  AuthCoreKCostBaseRo.roFixedShadowArmC_size_le A cap fsE secE

theorem roRootFixedShadowArmC_queries_zero {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (w : A.toIface.Tag → ℕ) (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootFixedShadowArmC A cap fsE inpE).queries w (fun _ => 0) = 0 :=
  AuthCoreKCostBaseRo.roRootFixedShadowArmC_queries_zero A w cap fsE inpE

theorem roRootFixedShadowArmC_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootFixedShadowArmC A cap fsE inpE).cost ≤
      4080 * bits cap + 1135 + fsE.cost + inpE.cost :=
  AuthCoreKCostBaseRo.roRootFixedShadowArmC_cost_le A cap fsE inpE

theorem roRootFixedShadowArmC_var_cost_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32)))
    (hfs : fsE.cost ≤ 5) (hinp : inpE.cost ≤ 5) :
    (roRootFixedShadowArmC A cap fsE inpE).cost ≤ 4420 * bits cap + 1350 :=
  AuthCoreKCostBaseRo.roRootFixedShadowArmC_var_cost_le A cap fsE inpE hfs hinp

theorem roRootFixedShadowArmC_size_le {ι : Type} {T : OracleSpec ι} (A : AtomicIface T)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy)
    (inpE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) :
    (roRootFixedShadowArmC A cap fsE inpE).size ≤
      2400 + 2 * bits (avlHeightCap cap) + fsE.size + inpE.size :=
  AuthCoreKCostBaseRo.roRootFixedShadowArmC_size_le A cap fsE inpE

end ShadowRoBounds

/-! ## Kind-0 Post-Step AVL Sync -/

section SyncRoBothBounds

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}

theorem syncRoHeadB192C_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy) :
    (syncRoHeadB192C (I := I) cap roListE tblE).queries w ws = 0 :=
  AuthCoreKCostBaseRo.syncRoHeadB192C_queries_zero w ws cap roListE tblE

theorem syncRoHeadB192C_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy) :
    (syncRoHeadB192C (I := I) cap roListE tblE).cost ≤
      4420 * bits cap + 1060 + roListE.cost + tblE.cost :=
  AuthCoreKCostBaseRo.syncRoHeadB192C_cost_le cap roListE tblE

theorem syncRoHeadB192C_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy) (tblE : Expr pqAtomicOps Γ roAvlTy) :
    (syncRoHeadB192C (I := I) cap roListE tblE).size ≤
      1800 + 2 * bits (avlHeightCap cap) + roListE.size + tblE.size :=
  AuthCoreKCostBaseRo.syncRoHeadB192C_size_le cap roListE tblE

theorem syncRoHeadPair32C_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    (syncRoHeadPair32C (I := I) cap rootListE tblE).queries w ws = 0 :=
  AuthCoreKCostBaseRo.syncRoHeadPair32C_queries_zero w ws cap rootListE tblE

theorem syncRoHeadPair32C_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    (syncRoHeadPair32C (I := I) cap rootListE tblE).cost ≤
      4080 * bits cap + 700 + rootListE.cost + tblE.cost :=
  AuthCoreKCostBaseRo.syncRoHeadPair32C_cost_le cap rootListE tblE

theorem syncRoHeadPair32C_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy) (tblE : Expr pqAtomicOps Γ roRootAvlTy) :
    (syncRoHeadPair32C (I := I) cap rootListE tblE).size ≤
      1850 + 2 * bits (avlHeightCap cap) + rootListE.size + tblE.size :=
  AuthCoreKCostBaseRo.syncRoHeadPair32C_size_le cap rootListE tblE

theorem syncRoBothC_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := I) cap roListE rootListE roBothE).queries w ws = 0 :=
  AuthCoreKCostBaseRo.syncRoBothC_queries_zero w ws cap roListE rootListE roBothE

theorem syncRoBothC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := I) cap roListE rootListE roBothE).cost ≤
      8500 * bits cap + 1850 + roListE.cost + rootListE.cost + roBothE.cost :=
  AuthCoreKCostBaseRo.syncRoBothC_cost_le cap roListE rootListE roBothE

theorem syncRoBothC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (roListE : Expr pqAtomicOps Γ roListAtomicTy)
    (rootListE : Expr pqAtomicOps Γ roRootListAtomicTy)
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncRoBothC (I := I) cap roListE rootListE roBothE).size ≤
      3700 + 4 * bits (avlHeightCap cap) + roListE.size + rootListE.size + roBothE.size :=
  AuthCoreKCostBaseRo.syncRoBothC_size_le cap roListE rootListE roBothE

theorem syncBaseShadowRespC_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncBaseShadowRespC (I := I) cap rsE roBothE).queries w ws = 0 :=
  AuthCoreKCostBaseRo.syncBaseShadowRespC_queries_zero w ws cap rsE roBothE

theorem syncBaseShadowRespC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncBaseShadowRespC (I := I) cap rsE roBothE).cost ≤
      8500 * bits cap + 2050 + rsE.cost + roBothE.cost :=
  AuthCoreKCostBaseRo.syncBaseShadowRespC_cost_le cap rsE roBothE

theorem syncBaseShadowRespC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authBaseAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncBaseShadowRespC (I := I) cap rsE roBothE).size ≤
      3850 + 4 * bits (avlHeightCap cap) + rsE.size + roBothE.size :=
  AuthCoreKCostBaseRo.syncBaseShadowRespC_size_le cap rsE roBothE

theorem syncFixedShadowRespC_queries_zero (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncFixedShadowRespC (I := I) cap rsfE roBothE).queries w ws = 0 :=
  AuthCoreKCostBaseRo.syncFixedShadowRespC_queries_zero w ws cap rsfE roBothE

theorem syncFixedShadowRespC_cost_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncFixedShadowRespC (I := I) cap rsfE roBothE).cost ≤
      8500 * bits cap + 2050 + rsfE.cost + roBothE.cost :=
  AuthCoreKCostBaseRo.syncFixedShadowRespC_cost_le cap rsfE roBothE

theorem syncFixedShadowRespC_size_le (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (rsfE : Expr pqAtomicOps Γ (.prod authRespAtomicTy authFixedAtomicTy))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    (syncFixedShadowRespC (I := I) cap rsfE roBothE).size ≤
      3900 + 4 * bits (avlHeightCap cap) + rsfE.size + roBothE.size :=
  AuthCoreKCostBaseRo.syncFixedShadowRespC_size_le cap rsfE roBothE

end SyncRoBothBounds

/-! ## Universal AVL Split Budget Inequalities -/

section AvlSplitBudget

/-- Bounds `M_off` offline AVL RO steps and `M_on` online dual-AVL syncs within the one-stage
    split budget. -/
theorem avl_split_budget_le (M_on M_off : ℕ) :
    M_off * (4420 * bits (M_off + 2 * M_on + 1) + 1750) +
      M_on * (8500 * bits (M_off + 2 * M_on + 1) + 2100) ≤
    2 ^ 13 * (M_off + M_on) * (bits (M_off + 2 * M_on + 1) + 4) +
      924 * M_on ^ 2 + 308 * M_on :=
  AuthCoreKCostBaseRo.avl_split_budget_le M_on M_off

/-- Bounds `M_off` offline AVL RO steps and `M_on + 1` online/resume dual-AVL syncs within the
    two-stage split budget. -/
theorem avl_split_budget_twoStage_le (M_on M_off : ℕ) :
    M_off * (4420 * bits (M_off + 2 * M_on + 1) + 1750) +
      (M_on + 1) * (8500 * bits (M_off + 2 * M_on + 1) + 2100) ≤
    2 ^ 13 * (M_off + M_on) * (bits (M_off + 2 * M_on + 1) + 4) +
      19100 * (M_on + 1) ^ 2 :=
  AuthCoreKCostBaseRo.avl_split_budget_twoStage_le M_on M_off

end AvlSplitBudget



end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKCostBase
