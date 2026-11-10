/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest
public import Computational.Proofs.E2E.Dsl.CliAdapterCosted
public import Computational.Proofs.E2E.Dsl.CliAdapterTblByKind
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Covariant `ReductionDsl` Homomorphism into `AtomicOps`

Defines covariant `ReductionDsl` homomorphisms (`OpsHom`, `IfaceHom`, `GameCodecHom`) that lift
expressions, computations, and 1- or 2-stage costed reductions across signature and operation-table
extensions while preserving step costs, query counts, and evaluation semantics. Specializes this
lifting from `e2eSig` to `atomicSig` to construct the atomic binary-harness adapters
`cliToModelAdapterProgAtomic` and `cliToModelAdapterProgTblAtomic`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.AtomicLift

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Samplers Iface GameCodec Expr Comp Mid
  iterM findML anyML mapML consumeFirstML foldML handlerImpl runFuel
  CostedReduction TwoStageCostedReduction OpsSizeHonest SampSizeHonest
  AtomicSort AtomicBaseUnif AtomicPureOp AtomicCurveCheckOp
  atomicSig atomicBaseSamplers atomicPureOps atomicAdapterOps atomicE2EOps)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSession (GRedBounded GRedCostByKind GRed2CostByKind)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes BinState BHDRCtlQuery bhCtlUnStart bhGameSpec bhTargetGameSpec
  e2eTargetGameCodec e2eBhAdapterIface e2eBhAdapterCodec CliToModelAdapterProg CliAdapterCostBounded
  bhQueryKind bhKindCounts bhAdapterCostBudget bhAdapterCostBudgetByKind CliAdapterForwardsKinds
  CliGameAdversary CliGameAdversaryPerInstanceBounded cliGameAdversaryReassoc
  bhIsInstQueryWithSpqr bhClassifyComposed bhClassifyGame bhClassifyGameOnly
  bhClassifyTarget bhClassifyTargetOnly isQueryBoundP_bhAdvRun
  cliE2EExpWithKi L_bh stageOneAsProbComp)
open CryptoVerification.E2E.Costed (E2ESort E2EUnifBase E2EPureOp E2ECryptoOp E2EAdapterTag
  e2eSig e2eSamplers e2ePureOps e2eCurveCheckOps e2eCryptoOps e2eAdapterOps e2eOps
  e2eAdapterIface e2eAdapterCodec sidV keyIndQenc keyIndQdec smQenc gRedBounded_of_bounds)
open _root_.ReductionDsl (atomicBaseSamplers_sizeHonest
  atomicAdapterOps_sizeHonest atomicE2EOps_sizeHonest)
open Computational.Proofs.E2E.Dsl.TablesHonest (adapterCrArm keyIndQdec_keyIndQenc)
open Computational.Proofs.E2E.Dsl.LeafCostBounds (e2eAdapterCostBudgetPreBlock)
open Computational.Proofs.E2E.Dsl.CliAdapterCosted (cliToModelAdapterProg
  totalCost_cliToModelAdapterProg_le_preBlock size_cliToModelAdapterProg_le_preBlock
  totalQueries_cliToModelAdapterProg_le
  cliToModelAdapterProg_perInstanceQueryBounds
  boolBias_cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh
  cliE2EExpWithKiCoinLogged cliQuery cliAdapterTblStateTy
  cliAdapterKiOrCtlArmTbl cliAdapterTrArmTbl cliAdapterChArmTbl
  cliAdapterDlArmTbl cliAdapterIjArmTbl cliAdapterHandleTbl
  cliToModelAdapterProgTbl
  totalCost_cliToModelAdapterProgTbl_le_bhAdapterCostBudget
  size_cliToModelAdapterProgTbl_le_bhAdapterCostBudget
  totalQueries_cliToModelAdapterProgTbl_le
  cliToModelAdapterProgTbl_perInstanceQueryBounds
  cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTbl_eq_L_bh
  boolBias_cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh)
open Computational.Proofs.E2E.Dsl.CliAdapterTblByKind (cliToModelAdapterProgTblRo
  cliToModelAdapterProgTblRo_eval_eq
  totalCost_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget
  size_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget
  totalQueries_cliToModelAdapterProgTblRo_le
  costBoundedByKind_cliToModelAdapterProgTblRo_bhAdapterCostBudgetByKind)

section Homomorphism

@[reducible] def mapTy {S₁ S₂ : Sig} (f : S₁.Base → S₂.Base) : Ty S₁ → Ty S₂
  | .base b => .base (f b)
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .opt t => .opt (mapTy f t)
  | .prod t u => .prod (mapTy f t) (mapTy f u)
  | .sum t u => .sum (mapTy f t) (mapTy f u)
  | .list t => .list (mapTy f t)
  | .tbl t => .tbl (mapTy f t)

def toVal {S₁ S₂ : Sig} (f : S₁.Base → S₂.Base)
    (toDen : (b : S₁.Base) → S₁.den b → S₂.den (f b)) :
    (t : Ty S₁) → t.denote → (mapTy f t).denote
  | .base b, x => toDen b x
  | .unit, x => x
  | .bool, x => x
  | .nat, x => x
  | .opt t, x => x.map (toVal f toDen t)
  | .prod t u, x => (toVal f toDen t x.1, toVal f toDen u x.2)
  | .sum t u, x => Sum.map (toVal f toDen t) (toVal f toDen u) x
  | .list t, x => x.map (toVal f toDen t)
  | .tbl t, m => fun i => toVal f toDen t (m i)

def mapVar {S₁ S₂ : Sig} (f : S₁.Base → S₂.Base) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} → Var Γ t → Var (Γ.map (mapTy f)) (mapTy f t)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (mapVar f v)

def mapEnv {S₁ S₂ : Sig} (f : S₁.Base → S₂.Base)
    (toDen : (b : S₁.Base) → S₁.den b → S₂.den (f b)) :
    {Γ : List (Ty S₁)} → Env Γ → Env (Γ.map (mapTy f))
  | _, .nil => .nil
  | _, .cons x ρ => .cons (toVal f toDen _ x) (mapEnv f toDen ρ)

theorem get_mapEnv {S₁ S₂ : Sig} (f : S₁.Base → S₂.Base)
    (toDen : (b : S₁.Base) → S₁.den b → S₂.den (f b))
    {Γ : List (Ty S₁)} {t : Ty S₁} (ρ : Env Γ) (v : Var Γ t) :
    (mapEnv f toDen ρ).get (mapVar f v) = toVal f toDen t (ρ.get v) := by
  induction v with
  | zero => cases ρ; rfl
  | succ v ih =>
    cases ρ with
    | cons _ ρ => exact ih ρ

def castDen {S : Sig} {t₁ t₂ : Ty S} (h : t₁ = t₂) (x : t₁.denote) : t₂.denote :=
  h ▸ x

@[simp] theorem castDen_self {S : Sig} {t : Ty S} (h : t = t) (x : t.denote) :
    castDen h x = x := by
  cases Subsingleton.elim h rfl
  rfl

@[simp] theorem castDen_symm_castDen {S : Sig} {t₁ t₂ : Ty S} (h : t₁ = t₂) (x : t₁.denote) :
    castDen h.symm (castDen h x) = x := by
  cases h; rfl

def castExpr {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t₁ t₂ : Ty S}
    (h : t₁ = t₂) (e : Expr O Γ t₁) : Expr O Γ t₂ :=
  h ▸ e

@[simp] theorem castExpr_cost {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t₁ t₂ : Ty S}
    (h : t₁ = t₂) (e : Expr O Γ t₁) :
    (castExpr h e).cost = e.cost := by
  cases h; rfl

@[simp] theorem castExpr_size {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t₁ t₂ : Ty S}
    (h : t₁ = t₂) (e : Expr O Γ t₁) :
    (castExpr h e).size = e.size := by
  cases h; rfl

theorem castExpr_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t₁ t₂ : Ty S}
    (h : t₁ = t₂) (e : Expr O Γ t₁) (ρ : Env Γ) :
    (castExpr h e).eval ρ = castDen h (e.eval ρ) := by
  cases h; rfl

def castComp {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t₁ t₂ : Ty S} (h : t₁ = t₂) (c : Comp O I Γ t₁) : Comp O I Γ t₂ :=
  h ▸ c

@[simp] theorem castComp_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t₁ t₂ : Ty S} (h : t₁ = t₂) (c : Comp O I Γ t₁) :
    (castComp h c).cost = c.cost := by
  cases h; rfl

@[simp] theorem castComp_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t₁ t₂ : Ty S} (h : t₁ = t₂) (c : Comp O I Γ t₁) :
    (castComp h c).size = c.size := by
  cases h; rfl

@[simp] theorem castComp_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t₁ t₂ : Ty S}
    (h : t₁ = t₂) (c : Comp O I Γ t₁) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (castComp h c).queries w ws = c.queries w ws := by
  cases h; rfl

theorem castComp_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t₁ t₂ : Ty S} (h : t₁ = t₂) (c : Comp O I Γ t₁) (ρ : Env Γ) :
    (castComp h c).eval ρ = castDen h <$> c.eval ρ := by
  cases h
  change c.eval ρ = id <$> c.eval ρ
  exact (id_map (c.eval ρ)).symm

def castCompCtx {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ₁ Γ₂ : List (Ty S)} {t₁ t₂ : Ty S}
    (hΓ : Γ₁ = Γ₂) (ht : t₁ = t₂) (c : Comp O I Γ₁ t₁) : Comp O I Γ₂ t₂ :=
  hΓ ▸ ht ▸ c

@[simp] theorem castCompCtx_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ₁ Γ₂ : List (Ty S)} {t₁ t₂ : Ty S}
    (hΓ : Γ₁ = Γ₂) (ht : t₁ = t₂) (c : Comp O I Γ₁ t₁) :
    (castCompCtx hΓ ht c).cost = c.cost := by
  cases hΓ; cases ht; rfl

@[simp] theorem castCompCtx_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ₁ Γ₂ : List (Ty S)} {t₁ t₂ : Ty S}
    (hΓ : Γ₁ = Γ₂) (ht : t₁ = t₂) (c : Comp O I Γ₁ t₁) :
    (castCompCtx hΓ ht c).size = c.size := by
  cases hΓ; cases ht; rfl

@[simp] theorem castCompCtx_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ₁ Γ₂ : List (Ty S)} {t₁ t₂ : Ty S}
    (hΓ : Γ₁ = Γ₂) (ht : t₁ = t₂) (c : Comp O I Γ₁ t₁) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (castCompCtx hΓ ht c).queries w ws = c.queries w ws := by
  cases hΓ; cases ht; rfl

/-- Cost- and semantics-preserving operation-table homomorphism from `O₁` to `O₂`. -/
structure OpsHom (S₁ S₂ : Sig) (O₁ : Ops S₁) (O₂ : Ops S₂) where
  fSort : S₁.Base → S₂.Base
  toDen : (b : S₁.Base) → S₁.den b → S₂.den (fSort b)
  fOp : O₁.Op → O₂.Op
  dom_eq : ∀ o, mapTy fSort (O₁.dom o) = O₂.dom (fOp o)
  cod_eq : ∀ o, mapTy fSort (O₁.cod o) = O₂.cod (fOp o)
  cost_eq : ∀ o, O₂.cost (fOp o) = O₁.cost o
  opSize_eq : ∀ o, O₂.opSize (fOp o) = O₁.opSize o
  eval_eq : ∀ o (x : (O₁.dom o).denote),
    O₂.eval (fOp o) (castDen (dom_eq o) (toVal fSort toDen (O₁.dom o) x)) =
      castDen (cod_eq o) (toVal fSort toDen (O₁.cod o) (O₁.eval o x))

def mapExpr {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} (H : OpsHom S₁ S₂ O₁ O₂) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Expr O₁ Γ t → Expr O₂ (Γ.map (mapTy H.fSort)) (mapTy H.fSort t)
  | _, _, .var v => .var (mapVar H.fSort v)
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (mapExpr H a) (mapExpr H b)
  | _, _, .sub a b => .sub (mapExpr H a) (mapExpr H b)
  | _, _, .mulK k a => .mulK k (mapExpr H a)
  | _, _, .divK k a => .divK k (mapExpr H a)
  | _, _, .modK k a => .modK k (mapExpr H a)
  | _, _, .lt a b => .lt (mapExpr H a) (mapExpr H b)
  | _, _, .eqN a b => .eqN (mapExpr H a) (mapExpr H b)
  | _, _, .not a => .not (mapExpr H a)
  | _, _, .and a b => .and (mapExpr H a) (mapExpr H b)
  | _, _, .ite c a b => .ite (mapExpr H c) (mapExpr H a) (mapExpr H b)
  | _, _, .pair a b => .pair (mapExpr H a) (mapExpr H b)
  | _, _, .fst a => .fst (mapExpr H a)
  | _, _, .snd a => .snd (mapExpr H a)
  | _, _, .inl a => .inl (mapExpr H a)
  | _, _, .inr a => .inr (mapExpr H a)
  | _, _, .none => .none
  | _, _, .some a => .some (mapExpr H a)
  | _, _, .caseOpt e n s => .caseOpt (mapExpr H e) (mapExpr H n) (mapExpr H s)
  | _, _, .caseSum e l r => .caseSum (mapExpr H e) (mapExpr H l) (mapExpr H r)
  | _, _, .letE e b => .letE (mapExpr H e) (mapExpr H b)
  | _, _, .op o a =>
    castExpr (H.cod_eq o).symm (.op (H.fOp o) (castExpr (H.dom_eq o) (mapExpr H a)))
  | _, _, .nil => .nil
  | _, _, .cons x l => .cons (mapExpr H x) (mapExpr H l)
  | _, _, .len l => .len (mapExpr H l)
  | _, _, .take n l => .take (mapExpr H n) (mapExpr H l)
  | _, _, .appendL K a b => .appendL K (mapExpr H a) (mapExpr H b)
  | _, _, .findB K l p => .findB K (mapExpr H l) (mapExpr H p)
  | _, _, .anyB K l p => .anyB K (mapExpr H l) (mapExpr H p)
  | _, _, .mapB K l f => .mapB K (mapExpr H l) (mapExpr H f)
  | _, _, .foldrB K l z f => .foldrB K (mapExpr H l) (mapExpr H z) (mapExpr H f)
  | _, _, .tconst a => .tconst (mapExpr H a)
  | _, _, .tget m i => .tget (mapExpr H m) (mapExpr H i)
  | _, _, .tset m i a => .tset (mapExpr H m) (mapExpr H i) (mapExpr H a)

theorem mapExpr_cost {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} (H : OpsHom S₁ S₂ O₁ O₂)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (mapExpr H e).cost = e.cost := by
  induction e <;> simp [mapExpr, Expr.cost, H.cost_eq, *]

theorem mapExpr_size {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} (H : OpsHom S₁ S₂ O₁ O₂)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (mapExpr H e).size = e.size := by
  induction e <;> simp [mapExpr, Expr.size, H.opSize_eq, *]

private theorem list_find?_map {α β : Type} (g : α → β) (p : β → Bool) :
    ∀ xs : List α, (xs.map g).find? p = (xs.find? fun x => p (g x)).map g
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons]
    cases p (g x)
    · exact list_find?_map g p xs
    · rfl

private theorem list_foldr_map_hom {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → β₁) (f₂ : α₂ → β₂ → β₂)
    (hf : ∀ x acc, f₂ (g x) (h acc) = h (f₁ x acc)) (z : β₁) :
    ∀ xs : List α₁, (xs.map g).foldr f₂ (h z) = h (xs.foldr f₁ z)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.foldr_cons, list_foldr_map_hom g h f₁ f₂ hf z xs, hf]

theorem mapExpr_eval {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} (H : OpsHom S₁ S₂ O₁ O₂)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (mapExpr H e).eval (mapEnv H.fSort H.toDen ρ) = toVal H.fSort H.toDen t (e.eval ρ) := by
  induction e with
  | var v => exact get_mapEnv H.fSort H.toDen ρ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | sub _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | mulK _ _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | divK _ _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | modK _ _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | lt _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | eqN _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | not _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | and _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | ite c a b ihc iha ihb =>
    simp only [mapExpr, Expr.eval, ihc ρ]
    change (if c.eval ρ then _ else _) = _
    split_ifs <;> [exact iha ρ; exact ihb ρ]
  | pair _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]
  | fst _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | snd _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | inl _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]; rfl
  | inr _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]; rfl
  | some _ ih => simp only [mapExpr, Expr.eval, toVal, ih ρ]; rfl
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
  | op o a iha =>
    simp only [mapExpr, castExpr_eval, Expr.eval, iha ρ, H.eval_eq, castDen_symm_castDen]
  | cons _ _ ih1 ih2 => simp only [mapExpr, Expr.eval, toVal, ih1 ρ, ih2 ρ]; rfl
  | len _ ih => simp [mapExpr, Expr.eval, toVal, ih ρ]
  | take _ _ ihn ihl =>
    simp only [mapExpr, Expr.eval, ihn ρ, ihl ρ, toVal, List.map_take]
  | appendL K _ _ ih1 ih2 =>
    simp only [mapExpr, Expr.eval, ih1 ρ, ih2 ρ, toVal, ← List.map_append, List.map_take]
  | findB K l p ihl ihp =>
    simp only [mapExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, list_find?_map]
    have hp :
        (fun x => (mapExpr H p).eval (.cons (toVal H.fSort H.toDen _ x) (mapEnv H.fSort H.toDen ρ))) =
          (fun x => p.eval (.cons x ρ)) :=
      funext fun x => ihp (.cons x ρ)
    rw [hp]
  | anyB K l p ihl ihp =>
    simp only [mapExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.any_map]
    have hp :
        ((fun x => (mapExpr H p).eval (.cons x (mapEnv H.fSort H.toDen ρ))) ∘
            toVal H.fSort H.toDen _) =
          (fun x => p.eval (.cons x ρ)) :=
      funext fun x => ihp (.cons x ρ)
    rw [hp]
  | mapB K l f ihl ihf =>
    simp only [mapExpr, Expr.eval, ihl ρ, toVal, ← List.map_take, List.map_map]
    congr 1
    funext x
    exact ihf (.cons x ρ)
  | foldrB K l z f ihl ihz ihf =>
    simp only [mapExpr, Expr.eval, ihl ρ, ihz ρ, toVal, ← List.map_take]
    exact list_foldr_map_hom
      (toVal H.fSort H.toDen _)
      (toVal H.fSort H.toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => (mapExpr H f).eval (.cons x (.cons acc (mapEnv H.fSort H.toDen ρ))))
      (fun x acc => ihf (.cons x (.cons acc ρ)))
      (z.eval ρ) ((l.eval ρ).take K)
  | tconst _ ih =>
    simp only [mapExpr, Expr.eval, toVal, ih ρ]
  | tget _ _ ihm ihi =>
    simp only [mapExpr, Expr.eval, ihm ρ, ihi ρ, toVal]
  | tset m i a ihm ihi iha =>
    simp only [mapExpr, Expr.eval, ihm ρ, ihi ρ, iha ρ, toVal]
    funext j
    split_ifs <;> rfl

/-- Cost-, query-, and semantics-preserving target-interface homomorphism from `I₁` to `I₂`. -/
structure IfaceHom {ι : Type} {T : OracleSpec ι}
    (S₁ S₂ : Sig) (I₁ : Iface S₁ T) (I₂ : Iface S₂ T)
    (fSort : S₁.Base → S₂.Base)
    (toDen : (b : S₁.Base) → S₁.den b → S₂.den (fSort b)) where
  fwdU_eq : ∀ n, I₂.fwdU n = I₁.fwdU n
  uCost_eq : I₂.uCost = I₁.uCost
  fSamp : I₁.smp.Samp → I₂.smp.Samp
  sDom_eq : ∀ s, mapTy fSort (I₁.smp.sDom s) = I₂.smp.sDom (fSamp s)
  sTy_eq : ∀ s, mapTy fSort (I₁.smp.sTy s) = I₂.smp.sTy (fSamp s)
  sCost_eq : ∀ s, I₂.smp.sCost (fSamp s) = I₁.smp.sCost s
  samp_eq : ∀ s (x : (I₁.smp.sDom s).denote),
    I₂.smp.samp (fSamp s) (castDen (sDom_eq s) (toVal fSort toDen (I₁.smp.sDom s) x)) =
      (fun y => castDen (sTy_eq s) (toVal fSort toDen (I₁.smp.sTy s) y)) <$> I₁.smp.samp s x
  fTag : I₁.Tag → I₂.Tag
  qDom_eq : ∀ g, mapTy fSort (I₁.dom g) = I₂.dom (fTag g)
  qCod_eq : ∀ g, mapTy fSort (I₁.cod g) = I₂.cod (fTag g)
  qCost_eq : ∀ g, I₂.qCost (fTag g) = I₁.qCost g
  query_eq : ∀ g (x : (I₁.dom g).denote),
    (let x' := castDen (qDom_eq g) (toVal fSort toDen (I₁.dom g) x)
     I₂.dec (fTag g) x' <$> (liftM (T.query (I₂.enc (fTag g) x')) : OracleComp T _)) =
      (fun y => castDen (qCod_eq g) (toVal fSort toDen (I₁.cod g) y)) <$>
        (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _))

def mapComp {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Comp O₁ I₁ Γ t → Comp O₂ I₂ (Γ.map (mapTy H.fSort)) (mapTy H.fSort t)
  | _, _, .ret e => .ret (mapExpr H e)
  | _, _, .bind c k => .bind (mapComp H HI c) (mapComp H HI k)
  | _, _, .ite b c d => .ite (mapExpr H b) (mapComp H HI c) (mapComp H HI d)
  | _, _, .caseOpt e n s => .caseOpt (mapExpr H e) (mapComp H HI n) (mapComp H HI s)
  | _, _, .caseSum e l r => .caseSum (mapExpr H e) (mapComp H HI l) (mapComp H HI r)
  | _, _, .sample s e =>
    castComp (HI.sTy_eq s).symm
      (.sample (HI.fSamp s) (castExpr (HI.sDom_eq s) (mapExpr H e)))
  | _, _, .query g e =>
    castComp (HI.qCod_eq g).symm
      (.query (HI.fTag g) (castExpr (HI.qDom_eq g) (mapExpr H e)))
  | _, _, .iter n e body => .iter n (mapExpr H e) (mapComp H HI body)
  | _, _, .findM K l p => .findM K (mapExpr H l) (mapComp H HI p)
  | _, _, .anyM K l p => .anyM K (mapExpr H l) (mapComp H HI p)
  | _, _, .mapM K l f => .mapM K (mapExpr H l) (mapComp H HI f)
  | _, _, .consumeFirstM K l p mk =>
    .consumeFirstM K (mapExpr H l) (mapComp H HI p) (mapExpr H mk)
  | _, _, .foldM K l z f => .foldM K (mapExpr H l) (mapExpr H z) (mapComp H HI f)

theorem mapComp_cost {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (mapComp H HI c).cost = c.cost := by
  induction c <;> simp [mapComp, Comp.cost, mapExpr_cost, HI.sCost_eq, HI.qCost_eq, *]

theorem mapComp_size {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (mapComp H HI c).size = c.size := by
  induction c <;> simp [mapComp, Comp.size, mapExpr_size, *]

theorem mapComp_queries {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hw : ∀ g, w₂ (HI.fTag g) = w₁ g) (hws : ∀ s, ws₂ (HI.fSamp s) = ws₁ s)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (mapComp H HI c).queries w₂ ws₂ = c.queries w₁ ws₁ := by
  induction c <;> simp [mapComp, Comp.queries, *]

@[simp] private theorem map_id_lam {m : Type → Type} [Functor m] [LawfulFunctor m]
    {α : Type} (x : m α) : (fun a => a) <$> x = x :=
  id_map x

private theorem iterM_map_hom {m : Type → Type} [Monad m] [LawfulMonad m] {α₁ α₂ : Type}
    (g : α₁ → α₂) (f₁ : α₁ → m α₁) (f₂ : α₂ → m α₂)
    (hf : ∀ a, f₂ (g a) = g <$> f₁ a) :
    ∀ (n : ℕ) (a : α₁), iterM f₂ n (g a) = g <$> iterM f₁ n a
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, bind_map_left, map_bind]
    exact bind_congr fun a' => iterM_map_hom g f₁ f₂ hf n a'

private theorem findML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m] {α₁ α₂ : Type}
    (g : α₁ → α₂) (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α₁, findML p₂ (xs.map g) = Option.map g <$> findML p₁ xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    refine bind_congr fun b => ?_
    cases b
    · exact findML_map_hom g p₁ p₂ hp xs
    · simp

private theorem anyML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m] {α₁ α₂ : Type}
    (g : α₁ → α₂) (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α₁, anyML p₂ (xs.map g) = anyML p₁ xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    refine bind_congr fun b => ?_
    cases b
    · exact anyML_map_hom g p₁ p₂ hp xs
    · rfl

private theorem mapML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → m β₁) (f₂ : α₂ → m β₂) (hf : ∀ x, f₂ (g x) = h <$> f₁ x) :
    ∀ xs : List α₁, mapML f₂ (xs.map g) = List.map h <$> mapML f₁ xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, bind_map_left, map_bind]
    refine bind_congr fun y => ?_
    rw [mapML_map_hom g h f₁ f₂ hf xs, bind_map_left]
    simp

private theorem consumeFirstML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ : Type} (g : α₁ → α₂) (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool)
    (mk₁ : α₁ → α₁) (mk₂ : α₂ → α₂)
    (hp : ∀ x, p₂ (g x) = p₁ x) (hmk : ∀ x, mk₂ (g x) = g (mk₁ x)) :
    ∀ xs : List α₁,
      consumeFirstML p₂ mk₂ (xs.map g) =
        (fun r : Bool × List α₁ => (r.1, r.2.map g)) <$> consumeFirstML p₁ mk₁ xs
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML, hp x, map_bind]
    refine bind_congr fun b => ?_
    cases b
    · rw [consumeFirstML_map_hom g p₁ p₂ mk₁ mk₂ hp hmk xs, bind_map_left]
      simp
    · simp [hmk x]

private theorem foldML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → m β₁) (f₂ : α₂ → β₂ → m β₂)
    (hf : ∀ x acc, f₂ (g x) (h acc) = h <$> f₁ x acc) :
    ∀ (xs : List α₁) (acc : β₁), foldML f₂ (h acc) (xs.map g) = h <$> foldML f₁ acc xs
  | [], acc => by simp [foldML]
  | x :: xs, acc => by
    simp only [List.map_cons, foldML, hf x acc, bind_map_left, map_bind]
    exact bind_congr fun acc' => foldML_map_hom g h f₁ f₂ hf xs acc'

theorem mapComp_eval {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (mapComp H HI c).eval (mapEnv H.fSort H.toDen ρ) =
      toVal H.fSort H.toDen t <$> c.eval ρ := by
  have hLift : ∀ {α : Type} (p : ProbComp α), I₂.liftP p = I₁.liftP p := by
    intro α p
    unfold Iface.liftP
    congr 1
    funext n
    exact HI.fwdU_eq n
  induction c with
  | ret e =>
    simp [mapComp, Comp.eval, mapExpr_eval]
  | bind c k ihc ihk =>
    simp only [mapComp, Comp.eval, ihc ρ, bind_map_left, map_bind]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    simp only [mapComp, Comp.eval, mapExpr_eval H b ρ]
    change (if b.eval ρ then _ else _) = _
    split_ifs <;> [exact ihc ρ; exact ihd ρ]
  | caseOpt e n s ihn ihs =>
    simp only [mapComp, Comp.eval, mapExpr_eval H e ρ]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [mapComp, Comp.eval, mapExpr_eval H e ρ]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample s e =>
    simp only [mapComp, castComp_eval, Comp.eval, castExpr_eval, mapExpr_eval H e ρ,
      hLift, HI.samp_eq]
    unfold Iface.liftP
    rw [simulateQ_map, ← comp_map]
    simp only [Function.comp_def, castDen_symm_castDen]
  | query g e =>
    dsimp only [mapComp]
    rw [castComp_eval]
    have hx :
        (castExpr (HI.qDom_eq g) (mapExpr H e)).eval (mapEnv H.fSort H.toDen ρ) =
          castDen (HI.qDom_eq g) (toVal H.fSort H.toDen (I₁.dom g) (e.eval ρ)) := by
      rw [castExpr_eval, mapExpr_eval]
    have hq :
        (Comp.query (I := I₂) (HI.fTag g) (castExpr (HI.qDom_eq g) (mapExpr H e))).eval
            (mapEnv H.fSort H.toDen ρ) =
          (fun y => castDen (HI.qCod_eq g) (toVal H.fSort H.toDen (I₁.cod g) y)) <$>
            (Comp.query g e).eval ρ :=
      Eq.trans
        (congrArg
          (fun x' => I₂.dec (HI.fTag g) x' <$> (liftM (T.query (I₂.enc (HI.fTag g) x')) : OracleComp T _))
          hx)
        (HI.query_eq g (e.eval ρ))
    rw [hq, ← comp_map]
    simp only [Function.comp_def, castDen_symm_castDen]
  | iter n e body ih =>
    simp only [mapComp, Comp.eval, mapExpr_eval H e ρ]
    exact iterM_map_hom
      (toVal H.fSort H.toDen _)
      (fun a => body.eval (.cons a ρ))
      (fun a => (mapComp H HI body).eval (.cons a (mapEnv H.fSort H.toDen ρ)))
      (fun a => ih (.cons a ρ)) n (e.eval ρ)
  | findM K l p ih =>
    simp only [mapComp, Comp.eval, mapExpr_eval H l ρ, toVal, ← List.map_take]
    exact findML_map_hom
      (toVal H.fSort H.toDen _)
      (fun x => p.eval (.cons x ρ))
      (fun x => (mapComp H HI p).eval (.cons x (mapEnv H.fSort H.toDen ρ)))
      (fun x => (ih (.cons x ρ)).trans (id_map _))
      ((l.eval ρ).take K)
  | anyM K l p ih =>
    simp only [mapComp, Comp.eval, mapExpr_eval H l ρ, toVal, ← List.map_take, map_id_lam]
    exact anyML_map_hom
      (toVal H.fSort H.toDen _)
      (fun x => p.eval (.cons x ρ))
      (fun x => (mapComp H HI p).eval (.cons x (mapEnv H.fSort H.toDen ρ)))
      (fun x => (ih (.cons x ρ)).trans (id_map _))
      ((l.eval ρ).take K)
  | mapM K l f ih =>
    simp only [mapComp, Comp.eval, mapExpr_eval H l ρ, toVal, ← List.map_take]
    exact mapML_map_hom
      (toVal H.fSort H.toDen _)
      (toVal H.fSort H.toDen _)
      (fun x => f.eval (.cons x ρ))
      (fun x => (mapComp H HI f).eval (.cons x (mapEnv H.fSort H.toDen ρ)))
      (fun x => ih (.cons x ρ))
      ((l.eval ρ).take K)
  | consumeFirstM K l p mk ih =>
    simp only [mapComp, Comp.eval, mapExpr_eval H l ρ, toVal, ← List.map_take]
    exact consumeFirstML_map_hom
      (toVal H.fSort H.toDen _)
      (fun x => p.eval (.cons x ρ))
      (fun x => (mapComp H HI p).eval (.cons x (mapEnv H.fSort H.toDen ρ)))
      (fun x => mk.eval (.cons x ρ))
      (fun x => (mapExpr H mk).eval (.cons x (mapEnv H.fSort H.toDen ρ)))
      (fun x => (ih (.cons x ρ)).trans (id_map _))
      (fun x => mapExpr_eval H mk (.cons x ρ))
      ((l.eval ρ).take K)
  | foldM K l z f ih =>
    simp only [mapComp, Comp.eval, mapExpr_eval H l ρ, mapExpr_eval H z ρ, toVal, ← List.map_take]
    exact foldML_map_hom
      (toVal H.fSort H.toDen _)
      (toVal H.fSort H.toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun x acc => (mapComp H HI f).eval (.cons x (.cons acc (mapEnv H.fSort H.toDen ρ))))
      (fun x acc => ih (.cons x (.cons acc ρ)))
      ((l.eval ρ).take K) (z.eval ρ)

/-- Cost- and semantics-preserving game-codec homomorphism from `C₁` to `C₂`. -/
structure GameCodecHom {κ : Type} {G : OracleSpec κ}
    (S₁ S₂ : Sig) (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G)
    (fSort : S₁.Base → S₂.Base)
    (toDen : (b : S₁.Base) → S₁.den b → S₂.den (fSort b)) where
  Q_eq : mapTy fSort C₁.Q = C₂.Q
  R_eq : mapTy fSort C₁.R = C₂.R
  codecCost_eq : C₂.codecCost = C₁.codecCost
  qenc_eq : ∀ t, C₂.qenc t = castDen Q_eq (toVal fSort toDen C₁.Q (C₁.qenc t))
  rdec_eq : ∀ t r, C₂.rdec t (castDen R_eq (toVal fSort toDen C₁.R r)) = C₁.rdec t r

/-- Lift a 1-stage boolean `CostedReduction` across `(H, HI, HC)`. -/
def mapCostedReduction {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool) :
    CostedReduction O₂ I₂ G C₂ .unit .unit .bool .bool where
  σ := mapTy H.fSort R.σ
  init := mapComp H HI R.init
  handle :=
    castCompCtx
      (congrArg (fun q => [mapTy H.fSort R.σ, q]) HC.Q_eq)
      (congrArg (Ty.prod · (mapTy H.fSort R.σ)) HC.R_eq)
      (mapComp H HI R.handle)
  finish := mapComp H HI R.finish

theorem mapCostedReduction_totalCost {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool) (q : ℕ) :
    (mapCostedReduction H HI HC R).totalCost q = R.totalCost q := by
  simp [mapCostedReduction, CostedReduction.totalCost, mapComp_cost, HI.uCost_eq, HC.codecCost_eq]

theorem mapCostedReduction_size {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool) :
    (mapCostedReduction H HI HC R).size = R.size := by
  simp [mapCostedReduction, CostedReduction.size, mapComp_size]

theorem mapCostedReduction_totalQueries {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hw : ∀ g, w₂ (HI.fTag g) = w₁ g) (hws : ∀ s, ws₂ (HI.fSamp s) = ws₁ s)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool) (q : ℕ) :
    (mapCostedReduction H HI HC R).totalQueries w₂ ws₂ q = R.totalQueries w₁ ws₁ q := by
  simp [mapCostedReduction, CostedReduction.totalQueries,
    mapComp_queries H HI w₁ ws₁ w₂ ws₂ hw hws]

theorem simulateQ_handlerImpl_map {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    {σ : Ty S₁} (h : Comp O₁ I₁ [σ, C₁.Q] (.prod C₁.R σ))
    {α : Type} (oa : OracleComp (unifSpec + G) α) (s : σ.denote) :
    (simulateQ
        (handlerImpl (C := C₂)
          (castCompCtx
            (congrArg (fun q => [mapTy H.fSort σ, q]) HC.Q_eq)
            (congrArg (Ty.prod · (mapTy H.fSort σ)) HC.R_eq)
            (mapComp H HI h)))
        oa).run (toVal H.fSort H.toDen σ s) =
      (fun p : α × σ.denote => (p.1, toVal H.fSort H.toDen σ p.2)) <$>
        (simulateQ (handlerImpl (C := C₁) h) oa).run s := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, codecCost₂⟩
  rcases HC with ⟨hQ, hR, _, hqenc, hrdec⟩
  dsimp only at hQ hR hqenc hrdec ⊢
  subst hQ; subst hR
  simp only [castDen_self] at hqenc hrdec
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp [simulateQ_pure]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, handlerImpl, HI.fwdU_eq, StateT.run_bind,
        StateT.run_lift, bind_assoc, pure_bind, map_bind]
      exact bind_congr fun u => ih u s
    | inr t =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, handlerImpl, StateT.run_bind, StateT.run_mk,
        hqenc t, map_bind]
      have hStep := mapComp_eval H HI h (.cons s (.cons (C₁.qenc t) .nil))
      dsimp only [castCompCtx, mapEnv] at hStep ⊢
      rw [hStep]
      simp only [bind_map_left, bind_assoc, pure_bind]
      refine bind_congr fun p => ?_
      dsimp only [toVal]
      rw [hrdec t p.1]
      exact ih (C₁.rdec t p.1) p.2

theorem mapCostedReduction_eval {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool) :
    (mapCostedReduction H HI HC R).eval = R.eval := by
  funext A x
  cases x
  unfold CostedReduction.eval CostedReduction.impl mapCostedReduction
  dsimp only
  have hInit := mapComp_eval H HI R.init (.cons () .nil)
  dsimp only [mapEnv, toVal] at hInit
  rw [hInit, bind_map_left]
  refine bind_congr fun ⟨a, s⟩ => ?_
  cases a
  rw [simulateQ_handlerImpl_map H HI HC R.handle (A ()) s, bind_map_left]
  refine bind_congr fun ⟨b, s'⟩ => ?_
  have hFin := mapComp_eval H HI R.finish (.cons s' (.cons b .nil))
  simpa [mapEnv, toVal] using hFin

def mapMid {κ : Type} {G : OracleSpec κ} {α π₁ π₂ σ₁ σ₂ χ₁ χ₂ : Type}
    (gπ : π₁ → π₂) (gσ : σ₁ → σ₂) (gχ : χ₁ → χ₂) :
    Mid G α π₁ σ₁ χ₁ → Mid G α π₂ σ₂ χ₂
  | .done a s => .done a (gσ s)
  | .paused t c p s k => .paused t (gχ c) (gπ p) (gσ s) k

/-- Lift a 2-stage boolean `TwoStageCostedReduction` across `(H, HI, HC)` and `hch`. -/
def mapTwoStageCostedReduction {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool) :
    TwoStageCostedReduction O₂ I₂ G C₂ .unit .unit .bool ch₂ .bool .bool where
  σ := mapTy H.fSort R.σ
  π := mapTy H.fSort R.π
  init := mapComp H HI R.init
  handlePre :=
    castCompCtx
      (congrArg (fun q => [mapTy H.fSort R.σ, q]) HC.Q_eq)
      (congrArg₂ Ty.sum
        (congrArg (Ty.prod · (mapTy H.fSort R.σ)) HC.R_eq)
        (congrArg (Ty.prod · (.prod (mapTy H.fSort R.π) (mapTy H.fSort R.σ))) hch))
      (mapComp H HI R.handlePre)
  chDone := castComp hch (mapComp H HI R.chDone)
  resume :=
    castCompCtx rfl
      (congrArg (Ty.prod · (mapTy H.fSort R.σ)) HC.R_eq)
      (mapComp H HI R.resume)
  handlePost :=
    castCompCtx
      (congrArg (fun q => [mapTy H.fSort R.σ, q]) HC.Q_eq)
      (congrArg (Ty.prod · (mapTy H.fSort R.σ)) HC.R_eq)
      (mapComp H HI R.handlePost)
  finish := mapComp H HI R.finish

theorem mapTwoStageCostedReduction_totalCost {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool) (q : ℕ) :
    (mapTwoStageCostedReduction H HI HC hch R).totalCost q = R.totalCost q := by
  simp [mapTwoStageCostedReduction, TwoStageCostedReduction.totalCost, mapComp_cost,
    HI.uCost_eq, HC.codecCost_eq]

theorem mapTwoStageCostedReduction_size {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool) :
    (mapTwoStageCostedReduction H HI HC hch R).size = R.size := by
  simp [mapTwoStageCostedReduction, TwoStageCostedReduction.size, mapComp_size]

theorem mapTwoStageCostedReduction_totalQueries {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hw : ∀ g, w₂ (HI.fTag g) = w₁ g) (hws : ∀ s, ws₂ (HI.fSamp s) = ws₁ s)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool) (q : ℕ) :
    (mapTwoStageCostedReduction H HI HC hch R).totalQueries w₂ ws₂ q =
      R.totalQueries w₁ ws₁ q := by
  simp [mapTwoStageCostedReduction, TwoStageCostedReduction.totalQueries,
    mapComp_queries H HI w₁ ws₁ w₂ ws₂ hw hws]

theorem mapTwoStageCostedReduction_stage1Queries {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hw : ∀ g, w₂ (HI.fTag g) = w₁ g) (hws : ∀ s, ws₂ (HI.fSamp s) = ws₁ s)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool) :
    (let R' := mapTwoStageCostedReduction H HI HC hch R
     R'.init.queries w₂ ws₂ + R'.handlePre.queries w₂ ws₂ + R'.chDone.queries w₂ ws₂) =
      R.init.queries w₁ ws₁ + R.handlePre.queries w₁ ws₁ + R.chDone.queries w₁ ws₁ := by
  simp [mapTwoStageCostedReduction, mapComp_queries H HI w₁ ws₁ w₂ ws₂ hw hws]

theorem run1_mapTwoStage {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α)
    (fuel : ℕ) (s : R.σ.denote) :
    (mapTwoStageCostedReduction H HI HC hch R).run1 dflt oa fuel (toVal H.fSort H.toDen R.σ s) =
      mapMid (toVal H.fSort H.toDen R.π) (toVal H.fSort H.toDen R.σ)
        (fun c => castDen hch (toVal H.fSort H.toDen ch₁ c)) <$>
        R.run1 dflt oa fuel s := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, codecCost₂⟩
  rcases HC with ⟨hQ, hR, _, hqenc, hrdec⟩
  dsimp only at hQ hR hqenc hrdec ⊢
  subst hQ; subst hR; subst hch
  simp only [castDen_self] at hqenc hrdec ⊢
  have hfwd : I₂.fwdU = I₁.fwdU := funext HI.fwdU_eq
  unfold TwoStageCostedReduction.run1 mapTwoStageCostedReduction
  dsimp only [castCompCtx]
  rw [hfwd]
  induction oa using OracleComp.inductionOn generalizing fuel s with
  | pure a =>
    simp [construct_pure, mapMid]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      simp only [construct_query_bind, map_bind]
      exact bind_congr fun u => ih u fuel s
    | inr t =>
      cases fuel with
      | zero =>
        simp [construct_query_bind, mapMid]
      | succ f =>
        simp only [construct_query_bind, hqenc t, map_bind]
        have hStep := mapComp_eval H HI R.handlePre (.cons s (.cons (C₁.qenc t) .nil))
        dsimp only [mapEnv] at hStep ⊢
        rw [hStep, bind_map_left]
        refine bind_congr fun res => ?_
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · dsimp only [toVal, Sum.map, Sum.elim, Function.comp_apply]
          rw [hrdec t v]
          exact ih (C₁.rdec t v) f s'
        · simp [toVal, Sum.map, mapMid]

theorem runFuel_mapOps {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    {σ : Ty S₁} (h : Comp O₁ I₁ [σ, C₁.Q] (.prod C₁.R σ))
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α)
    (fuel : ℕ) (s : σ.denote) :
    runFuel (C := C₂)
        (castCompCtx
          (congrArg (fun q => [mapTy H.fSort σ, q]) HC.Q_eq)
          (congrArg (Ty.prod · (mapTy H.fSort σ)) HC.R_eq)
          (mapComp H HI h))
        dflt oa fuel (toVal H.fSort H.toDen σ s) =
      (fun p : α × σ.denote => (p.1, toVal H.fSort H.toDen σ p.2)) <$>
        runFuel (C := C₁) h dflt oa fuel s := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, codecCost₂⟩
  rcases HC with ⟨hQ, hR, _, hqenc, hrdec⟩
  dsimp only at hQ hR hqenc hrdec ⊢
  subst hQ; subst hR
  simp only [castDen_self] at hqenc hrdec
  have hfwd : I₂.fwdU = I₁.fwdU := funext HI.fwdU_eq
  unfold runFuel
  dsimp only [castCompCtx]
  rw [hfwd]
  induction oa using OracleComp.inductionOn generalizing fuel s with
  | pure a =>
    simp [construct_pure]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      simp only [construct_query_bind, map_bind]
      exact bind_congr fun u => ih u fuel s
    | inr t =>
      cases fuel with
      | zero =>
        simp [construct_query_bind]
      | succ f =>
        simp only [construct_query_bind, hqenc t, map_bind]
        have hStep := mapComp_eval H HI h (.cons s (.cons (C₁.qenc t) .nil))
        dsimp only [mapEnv] at hStep ⊢
        rw [hStep, bind_map_left]
        refine bind_congr fun ⟨v, s'⟩ => ?_
        dsimp only [toVal]
        rw [hrdec t v]
        exact ih (C₁.rdec t v) f s'

theorem mapTwoStageCostedReduction_eval1 {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    (A : Unit → OracleComp (unifSpec + G) Bool) (fuel : ℕ) (dflt : Bool) :
    (mapTwoStageCostedReduction H HI HC hch R).eval1 A () fuel dflt =
      (fun cm =>
        (castDen hch (toVal H.fSort H.toDen ch₁ cm.1),
         mapMid (toVal H.fSort H.toDen R.π) (toVal H.fSort H.toDen R.σ)
           (fun c => castDen hch (toVal H.fSort H.toDen ch₁ c)) cm.2)) <$>
        R.eval1 A () fuel dflt := by
  have hInit :
      (mapTwoStageCostedReduction H HI HC hch R).init.eval (.cons () .nil) =
        (fun p : Unit × R.σ.denote => (p.1, toVal H.fSort H.toDen R.σ p.2)) <$>
          R.init.eval (.cons () .nil) := by
    simpa [mapTwoStageCostedReduction, mapEnv, toVal] using mapComp_eval H HI R.init (.cons () .nil)
  have hRun1 := fun s => run1_mapTwoStage H HI HC hch R dflt (A ()) fuel s
  unfold TwoStageCostedReduction.eval1
  dsimp only [mapTwoStageCostedReduction, Ty.denote] at hInit hRun1 ⊢
  rw [hInit, bind_map_left, map_bind]
  refine bind_congr fun ⟨a, s⟩ => ?_
  cases a
  rw [hRun1 s, bind_map_left, map_bind]
  refine bind_congr fun m => ?_
  cases m with
  | done b s' =>
    dsimp only [mapMid]
    rw [castComp_eval]
    have hCh := mapComp_eval H HI R.chDone (.cons s' (.cons b .nil))
    dsimp only [mapEnv, toVal] at hCh
    rw [hCh, ← comp_map, bind_map_left, map_bind]
    simp
  | paused t c p s' k =>
    simp [mapMid]

theorem mapTwoStageCostedReduction_eval2 {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    (m : Mid G Bool R.π.denote R.σ.denote ch₁.denote) (y : Bool) (fuel : ℕ) (dflt : Bool) :
    (mapTwoStageCostedReduction H HI HC hch R).eval2
        (mapMid (toVal H.fSort H.toDen R.π) (toVal H.fSort H.toDen R.σ)
          (fun c => castDen hch (toVal H.fSort H.toDen ch₁ c)) m)
        y fuel dflt =
      R.eval2 m y fuel dflt := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, codecCost₂⟩
  rcases HC with ⟨hQ, hR, hCost, hqenc, hrdec⟩
  dsimp only at hQ hR hqenc hrdec ⊢
  subst hQ; subst hR
  simp only [castDen_self] at hqenc hrdec
  let HC' : GameCodecHom S₁ S₂ C₁ ⟨_, _, qenc₂, rdec₂, codecCost₂⟩ H.fSort H.toDen :=
    ⟨rfl, rfl, hCost, fun t => by simpa using hqenc t, fun t r => by simpa using hrdec t r⟩
  cases m with
  | done b s =>
    unfold TwoStageCostedReduction.eval2 mapMid mapTwoStageCostedReduction
    simp only [pure_bind]
    have hFin := mapComp_eval H HI R.finish (.cons s (.cons b (.cons y .nil)))
    simpa [mapEnv, toVal] using hFin
  | paused t c p s k =>
    have hRes :
        (mapTwoStageCostedReduction H HI HC' hch R).resume.eval
            (.cons (toVal H.fSort H.toDen R.σ s)
              (.cons (toVal H.fSort H.toDen R.π p) (.cons y .nil))) =
          toVal H.fSort H.toDen (.prod C₁.R R.σ) <$>
            R.resume.eval (.cons s (.cons p (.cons y .nil))) := by
      simpa [mapTwoStageCostedReduction, castCompCtx, mapEnv, toVal] using
        mapComp_eval H HI R.resume (.cons s (.cons p (.cons y .nil)))
    have hFuel := fun v s₁ =>
      runFuel_mapOps H HI HC' R.handlePost dflt (k (C₁.rdec t v)) fuel s₁
    unfold TwoStageCostedReduction.eval2 mapMid
    dsimp only [mapTwoStageCostedReduction, mapTy, Ty.denote] at hRes hFuel ⊢
    rw [hRes, bind_map_left]
    refine bind_congr fun ⟨v, s₁⟩ => ?_
    dsimp only [toVal]
    rw [hrdec t v, hFuel v s₁, bind_map_left]
    refine bind_congr fun ⟨b, s₂⟩ => ?_
    have hFin := mapComp_eval H HI R.finish (.cons s₂ (.cons b (.cons y .nil)))
    simpa [mapEnv, toVal] using hFin

@[simp] theorem castExpr_costAt {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t₁ t₂ : Ty S}
    (h : t₁ = t₂) (e : Expr O Γ t₁) (ρ : Env Γ) :
    (castExpr h e).costAt ρ = e.costAt ρ := by
  cases h; rfl

theorem castComp_pureEval? {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t₁ t₂ : Ty S} (h : t₁ = t₂) (c : Comp O I Γ t₁) (ρ : Env Γ) :
    (castComp h c).pureEval? ρ = (c.pureEval? ρ).map (castDen h) := by
  cases h
  unfold castComp castDen
  cases c.pureEval? ρ <;> rfl

@[simp] theorem castComp_costAt {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t₁ t₂ : Ty S} (h : t₁ = t₂) (c : Comp O I Γ t₁) (ρ : Env Γ) :
    (castComp h c).costAt ρ = c.costAt ρ := by
  cases h; rfl

theorem mapExpr_costAt {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} (H : OpsHom S₁ S₂ O₁ O₂)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (mapExpr H e).costAt (mapEnv H.fSort H.toDen ρ) = e.costAt ρ := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | sub _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | mulK _ _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | divK _ _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | modK _ _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | lt _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | eqN _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | not _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | and _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | ite c a b ihc iha ihb =>
    simp only [mapExpr, Expr.costAt, mapExpr_eval H c ρ, ihc ρ]
    change c.costAt ρ + (if c.eval ρ then _ else _) + 1 = _
    split_ifs <;> [rw [iha ρ]; rw [ihb ρ]]
  | pair _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | fst _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | snd _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | inl _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | inr _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | some _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [mapExpr, Expr.costAt, mapExpr_eval H e ρ, ihe ρ]
    cases e.eval ρ with
    | none => exact congrArg (fun m => e.costAt ρ + m + 1) (ihn ρ)
    | some x => exact congrArg (fun m => e.costAt ρ + m + 1) (ihs (.cons x ρ))
  | caseSum e l r ihe ihl ihr =>
    simp only [mapExpr, Expr.costAt, mapExpr_eval H e ρ, ihe ρ]
    cases e.eval ρ with
    | inl x => exact congrArg (fun m => e.costAt ρ + m + 1) (ihl (.cons x ρ))
    | inr y => exact congrArg (fun m => e.costAt ρ + m + 1) (ihr (.cons y ρ))
  | letE e b ihe ihb =>
    simp only [mapExpr, Expr.costAt, mapExpr_eval H e ρ, ihe ρ]
    exact congrArg (fun m => e.costAt ρ + m + 1) (ihb (.cons (e.eval ρ) ρ))
  | op o a iha =>
    simp only [mapExpr, castExpr_costAt, Expr.costAt, H.cost_eq, iha ρ]
  | cons _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | len _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | take _ _ ihn ihl => simp only [mapExpr, Expr.costAt, ihn ρ, ihl ρ]
  | appendL _ _ _ ih1 ih2 => simp only [mapExpr, Expr.costAt, ih1 ρ, ih2 ρ]
  | findB _ l _ ihl _ => simp only [mapExpr, Expr.costAt, mapExpr_cost, ihl ρ]
  | anyB _ l _ ihl _ => simp only [mapExpr, Expr.costAt, mapExpr_cost, ihl ρ]
  | mapB _ l _ ihl _ => simp only [mapExpr, Expr.costAt, mapExpr_cost, ihl ρ]
  | foldrB _ l z _ ihl ihz _ => simp only [mapExpr, Expr.costAt, mapExpr_cost, ihl ρ, ihz ρ]
  | tconst _ ih => simp only [mapExpr, Expr.costAt, ih ρ]
  | tget _ _ ihm ihi => simp only [mapExpr, Expr.costAt, ihm ρ, ihi ρ]
  | tset _ _ _ ihm ihi iha => simp only [mapExpr, Expr.costAt, ihm ρ, ihi ρ, iha ρ]

theorem mapComp_pureEval? {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (mapComp H HI c).pureEval? (mapEnv H.fSort H.toDen ρ) =
      (c.pureEval? ρ).map (toVal H.fSort H.toDen t) := by
  induction c with
  | ret e => simp only [mapComp, Comp.pureEval?, mapExpr_eval H e ρ, Option.map_some]
  | bind c k ihc ihk =>
    simp only [mapComp, Comp.pureEval?, ihc ρ]
    cases c.pureEval? ρ with
    | none => rfl
    | some x => exact ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    simp only [mapComp, Comp.pureEval?, mapExpr_eval H b ρ]
    change (if b.eval ρ then _ else _) = _
    split_ifs <;> [exact ihc ρ; exact ihd ρ]
  | caseOpt e n s ihn ihs =>
    simp only [mapComp, Comp.pureEval?, mapExpr_eval H e ρ]
    cases e.eval ρ with
    | none => exact ihn ρ
    | some x => exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [mapComp, Comp.pureEval?, mapExpr_eval H e ρ]
    cases e.eval ρ with
    | inl x => exact ihl (.cons x ρ)
    | inr y => exact ihr (.cons y ρ)
  | sample _ _ | query _ _ => simp [mapComp, castComp_pureEval?, Comp.pureEval?]
  | iter _ _ _ | findM _ _ _ | anyM _ _ _ | mapM _ _ _ | consumeFirstM _ _ _ _ | foldM _ _ _ _ => rfl

theorem mapComp_costAt {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (mapComp H HI c).costAt (mapEnv H.fSort H.toDen ρ) = c.costAt ρ := by
  induction c with
  | ret e => simp only [mapComp, Comp.costAt, mapExpr_costAt H e ρ]
  | bind c k ihc ihk =>
    simp only [mapComp, Comp.costAt, mapComp_pureEval? H HI c ρ, mapComp_cost H HI k, ihc ρ]
    cases c.pureEval? ρ with
    | none => rfl
    | some x => exact congrArg (fun m => c.costAt ρ + m + 1) (ihk (.cons x ρ))
  | ite b c d ihc ihd =>
    simp only [mapComp, Comp.costAt, mapExpr_eval H b ρ, mapExpr_costAt H b ρ]
    change b.costAt ρ + (if b.eval ρ then _ else _) + 1 = _
    split_ifs <;> [rw [ihc ρ]; rw [ihd ρ]]
  | caseOpt e n s ihn ihs =>
    simp only [mapComp, Comp.costAt, mapExpr_eval H e ρ, mapExpr_costAt H e ρ]
    cases e.eval ρ with
    | none => exact congrArg (fun m => e.costAt ρ + m + 1) (ihn ρ)
    | some x => exact congrArg (fun m => e.costAt ρ + m + 1) (ihs (.cons x ρ))
  | caseSum e l r ihl ihr =>
    simp only [mapComp, Comp.costAt, mapExpr_eval H e ρ, mapExpr_costAt H e ρ]
    cases e.eval ρ with
    | inl x => exact congrArg (fun m => e.costAt ρ + m + 1) (ihl (.cons x ρ))
    | inr y => exact congrArg (fun m => e.costAt ρ + m + 1) (ihr (.cons y ρ))
  | sample s e =>
    simp only [mapComp, castComp_costAt, Comp.costAt, castExpr_costAt, mapExpr_costAt H e ρ, HI.sCost_eq]
  | query g e =>
    simp only [mapComp, castComp_costAt, Comp.costAt, castExpr_costAt, mapExpr_costAt H e ρ, HI.qCost_eq]
  | iter _ e _ _ => simp only [mapComp, Comp.costAt, mapExpr_costAt H e ρ, mapComp_cost]
  | findM _ l _ _ => simp only [mapComp, Comp.costAt, mapExpr_costAt H l ρ, mapComp_cost]
  | anyM _ l _ _ => simp only [mapComp, Comp.costAt, mapExpr_costAt H l ρ, mapComp_cost]
  | mapM _ l _ _ => simp only [mapComp, Comp.costAt, mapExpr_costAt H l ρ, mapComp_cost]
  | consumeFirstM _ l _ _ _ =>
    simp only [mapComp, Comp.costAt, mapExpr_costAt H l ρ, mapComp_cost, mapExpr_cost]
  | foldM _ l z _ _ =>
    simp only [mapComp, Comp.costAt, mapExpr_costAt H l ρ, mapExpr_costAt H z ρ, mapComp_cost]

theorem mapCostedReduction_validKindCosts {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool)
    (hSurj : Function.Surjective (toVal H.fSort H.toDen R.σ))
    {n : ℕ} (kind : κ → Fin n) (hCost : Fin n → ℕ)
    (hValid : R.ValidKindCosts kind hCost) :
    (mapCostedReduction H HI HC R).ValidKindCosts kind hCost := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, codecCost₂⟩
  rcases HC with ⟨hQ, hR, _, hqenc, _⟩
  dsimp only at hQ hR hqenc ⊢
  subst hQ; subst hR
  simp only [castDen_self] at hqenc
  intro s' t
  obtain ⟨s, rfl⟩ := hSurj s'
  have hEq := mapComp_costAt H HI R.handle (.cons s (.cons (C₁.qenc t) .nil))
  dsimp only [mapCostedReduction, castCompCtx, mapEnv] at hEq ⊢
  rw [hqenc t, hEq]
  exact hValid s t

theorem mapCostedReduction_totalCostByKind {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool)
    {n : ℕ} (hCost qKind : Fin n → ℕ) :
    (mapCostedReduction H HI HC R).totalCostByKind hCost qKind =
      R.totalCostByKind hCost qKind := by
  simp [mapCostedReduction, CostedReduction.totalCostByKind, mapComp_cost, HI.uCost_eq, HC.codecCost_eq]

theorem mapCostedReduction_costBoundedByKind {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool)
    (hSurj : Function.Surjective (toVal H.fSort H.toDen R.σ))
    {n : ℕ} {kind : κ → Fin n} {qKind : Fin n → ℕ} {B : ℕ}
    (hBnd : R.CostBoundedByKind kind qKind B) :
    (mapCostedReduction H HI HC R).CostBoundedByKind kind qKind B := by
  obtain ⟨hCost, hValid, hLe⟩ := hBnd
  exact ⟨hCost, mapCostedReduction_validKindCosts H HI HC R hSurj kind hCost hValid,
    (mapCostedReduction_totalCostByKind H HI HC R hCost qKind).trans_le hLe⟩

theorem mapCostedReduction_gRedCostByKind {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hw : ∀ g, w₂ (HI.fTag g) = w₁ g) (hws : ∀ s, ws₂ (HI.fSamp s) = ws₁ s)
    (R : CostedReduction O₁ I₁ G C₁ .unit .unit .bool .bool)
    (hSurj : Function.Surjective (toVal H.fSort H.toDen R.σ))
    {n : ℕ} {kind : κ → Fin n} {qKind : Fin n → ℕ} {qOut costBudget : ℕ}
    (h : GRedCostByKind R w₁ ws₁ kind qKind qOut costBudget) :
    GRedCostByKind (mapCostedReduction H HI HC R) w₂ ws₂ kind qKind qOut costBudget :=
  ⟨mapCostedReduction_costBoundedByKind H HI HC R hSurj h.1,
    (mapCostedReduction_totalQueries H HI HC w₁ ws₁ w₂ ws₂ hw hws R _).trans_le h.2⟩

theorem mapTwoStageCostedReduction_validKindCosts {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    (hSurj : Function.Surjective (toVal H.fSort H.toDen R.σ))
    {n : ℕ} (kind : κ → Fin n) (hCost : Fin n → ℕ)
    (hValid : R.ValidKindCosts kind hCost) :
    (mapTwoStageCostedReduction H HI HC hch R).ValidKindCosts kind hCost := by
  rcases C₂ with ⟨Q₂, R₂, qenc₂, rdec₂, codecCost₂⟩
  rcases HC with ⟨hQ, hR, _, hqenc, _⟩
  dsimp only at hQ hR hqenc ⊢
  subst hch; subst hQ; subst hR
  simp only [castDen_self] at hqenc
  intro s' t
  obtain ⟨s, rfl⟩ := hSurj s'
  have hPre := mapComp_costAt H HI R.handlePre (.cons s (.cons (C₁.qenc t) .nil))
  have hPost := mapComp_costAt H HI R.handlePost (.cons s (.cons (C₁.qenc t) .nil))
  dsimp only [mapTwoStageCostedReduction, castCompCtx, mapEnv] at hPre hPost ⊢
  rw [hqenc t, hPre, hPost]
  exact hValid s t

theorem mapTwoStageCostedReduction_totalCostByKind {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    {n : ℕ} (hCost qKind : Fin n → ℕ) :
    (mapTwoStageCostedReduction H HI HC hch R).totalCostByKind hCost qKind =
      R.totalCostByKind hCost qKind := by
  simp [mapTwoStageCostedReduction, TwoStageCostedReduction.totalCostByKind, mapComp_cost,
    HI.uCost_eq, HC.codecCost_eq]

theorem mapTwoStageCostedReduction_costBoundedByKind {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    (hSurj : Function.Surjective (toVal H.fSort H.toDen R.σ))
    {n : ℕ} {kind : κ → Fin n} {qKind : Fin n → ℕ} {B : ℕ}
    (hBnd : R.CostBoundedByKind kind qKind B) :
    (mapTwoStageCostedReduction H HI HC hch R).CostBoundedByKind kind qKind B := by
  obtain ⟨hCost, hValid, hLe⟩ := hBnd
  exact ⟨hCost, mapTwoStageCostedReduction_validKindCosts H HI HC hch R hSurj kind hCost hValid,
    (mapTwoStageCostedReduction_totalCostByKind H HI HC hch R hCost qKind).trans_le hLe⟩

theorem mapTwoStageCostedReduction_gRed2CostByKind {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {G : OracleSpec κ} {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G}
    {ch₁ : Ty S₁} {ch₂ : Ty S₂}
    (H : OpsHom S₁ S₂ O₁ O₂) (HI : IfaceHom S₁ S₂ I₁ I₂ H.fSort H.toDen)
    (HC : GameCodecHom S₁ S₂ C₁ C₂ H.fSort H.toDen)
    (hch : mapTy H.fSort ch₁ = ch₂)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hw : ∀ g, w₂ (HI.fTag g) = w₁ g) (hws : ∀ s, ws₂ (HI.fSamp s) = ws₁ s)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ .unit .unit .bool ch₁ .bool .bool)
    (hSurj : Function.Surjective (toVal H.fSort H.toDen R.σ))
    {n : ℕ} {kind : κ → Fin n} {qKind : Fin n → ℕ} {qOut costBudget : ℕ}
    (h : GRed2CostByKind R w₁ ws₁ kind qKind qOut costBudget) :
    GRed2CostByKind (mapTwoStageCostedReduction H HI HC hch R) w₂ ws₂ kind qKind qOut costBudget :=
  ⟨mapTwoStageCostedReduction_costBoundedByKind H HI HC hch R hSurj h.1,
    (mapTwoStageCostedReduction_stage1Queries H HI HC hch w₁ ws₁ w₂ ws₂ hw hws R).trans h.2.1,
    (mapTwoStageCostedReduction_totalQueries H HI HC hch w₁ ws₁ w₂ ws₂ hw hws R _).trans_le h.2.2⟩

end Homomorphism

def ιSort : E2ESort → AtomicSort
  | .pbytes w => .pbytes w
  | .pu32 => .pu32
  | .bytes w => .bytes w
  | .u8 => .u8
  | .u32 => .u32
  | .u64 => .u64
  | .bv128 => .bv128
  | .bv256 => .bv256
  | .bv512 => .bv512
  | .fin n => .fin n
  | .pk => .pk
  | .idKey => .idKey
  | .plain => .plain
  | .ghostSt => .ghostSt
  | .binSt => .binSt

def toDen (ℓ : ℕ) (Pt : Type) : (b : E2ESort) → (e2eSig ℓ).den b → (atomicSig ℓ Pt).den (ιSort b)
  | .pbytes _, x => x
  | .pu32, x => x
  | .bytes _, x => x
  | .u8, x => x
  | .u32, x => x
  | .u64, x => x
  | .bv128, x => x
  | .bv256, x => x
  | .bv512, x => x
  | .fin _, x => x
  | .pk, x => x
  | .idKey, x => x
  | .plain, x => x
  | .ghostSt, x => x
  | .binSt, x => x

def ιUnifBase : E2EUnifBase → AtomicBaseUnif
  | .bv256 => .bv256
  | .bv512 => .bv512

def ιSamp : _root_.ReductionDsl.UniformSamplerTag E2EUnifBase →
    _root_.ReductionDsl.UniformSamplerTag AtomicBaseUnif
  | .bool => .bool
  | .index N => .index N
  | .base b => .base (ιUnifBase b)

def ιPureOp : E2EPureOp → AtomicPureOp
  | .pbytesLit w v => .pbytesLit w v | .pbytesCat m n => .pbytesCat m n
  | .pbytesCons b w => .pbytesCons b w | .pbytesWiden w d => .pbytesWiden w d
  | .pbytesTakeK w k => .pbytesTakeK w k | .pbytesTake w => .pbytesTake w
  | .pbytesDrop w => .pbytesDrop w | .pbytesLen w => .pbytesLen w | .pbytesEq m n => .pbytesEq m n
  | .bytesLit w v => .bytesLit w v | .bytesCat m n => .bytesCat m n
  | .bytesCons b w => .bytesCons b w | .bytesWiden w d => .bytesWiden w d
  | .bytesTakeK w k => .bytesTakeK w k | .bytesTake w => .bytesTake w
  | .bytesDrop w => .bytesDrop w | .bytesLen w => .bytesLen w | .bytesEq m n => .bytesEq m n
  | .bytesLtOp m n => .bytesLtOp m n | .pbytesToBytes w => .pbytesToBytes w
  | .bytesToPbytes w => .bytesToPbytes w | .pu32Lit k => .pu32Lit k | .pu32OfNat => .pu32OfNat
  | .pu32ToNat => .pu32ToNat | .pu32Eq => .pu32Eq | .pu32ToU32 => .pu32ToU32
  | .u32ToPu32 => .u32ToPu32 | .u8Lit v => .u8Lit v | .u8OfNat => .u8OfNat | .u8ToNat => .u8ToNat
  | .u8Eq => .u8Eq | .u8Lt => .u8Lt | .u32Lit v => .u32Lit v | .u32OfNat => .u32OfNat
  | .u32ToNat => .u32ToNat | .u32Eq => .u32Eq | .u32Lt => .u32Lt | .u32Add => .u32Add
  | .u32Sub => .u32Sub | .u32BeBytes => .u32BeBytes | .u64Lit v => .u64Lit v
  | .u64OfNat => .u64OfNat | .u64ToNat => .u64ToNat | .u64Eq => .u64Eq | .u64Lt => .u64Lt
  | .u64Add => .u64Add | .u64Sub => .u64Sub | .u64Trunc8 => .u64Trunc8 | .finVal n => .finVal n
  | .finEq n => .finEq n | .bv128Eq => .bv128Eq | .bv256Lit v => .bv256Lit v
  | .bv256Eq => .bv256Eq | .bv256ToPbytes32 => .bv256ToPbytes32
  | .pbytesToBv256 => .pbytesToBv256 | .bv256ToBytes32 => .bv256ToBytes32
  | .bytesToBv256 => .bytesToBv256 | .bv512Lit v => .bv512Lit v
  | .bv512ToBytes64 => .bv512ToBytes64 | .idKeyOfPbytes => .idKeyOfPbytes
  | .idKeySerialize => .idKeySerialize | .idKeyEq => .idKeyEq | .pkOfPbytes => .pkOfPbytes
  | .pkDeserialize => .pkDeserialize | .pkSerialize => .pkSerialize | .pkEq => .pkEq
  | .plainDefault => .plainDefault | .plainToBytes => .plainToBytes
  | .bytesToPlain => .bytesToPlain | .plainEq => .plainEq
  | .checkShortCiphertext => .checkShortCiphertext | .parsePreKeyWire => .parsePreKeyWire
  | .partneredInnerBytes => .partneredInnerBytes | .wireInnerBytes => .wireInnerBytes
  | .splitWhisperWire => .splitWhisperWire | .isValidSignalWire => .isValidSignalWire
  | .signalMsgParse => .signalMsgParse | .wrapWhisperWire => .wrapWhisperWire
  | .wrapPreKeyWire => .wrapPreKeyWire | .spqrParsePreamble => .spqrParsePreamble
  | .spqrAssembleMsg => .spqrAssembleMsg | .spqrStateSplit => .spqrStateSplit
  | .spqrStateJoin => .spqrStateJoin | .ghostStateSplit => .ghostStateSplit
  | .ghostStateJoin => .ghostStateJoin | .encodeSessionRecord => .encodeSessionRecord

def ιCurveCheckOp : CryptoVerification.E2E.Costed.E2ECurveCheckOp → AtomicCurveCheckOp
  | .decEncCheck => .decEncCheck
  | .checkRatchetKeyOnCurve => .checkRatchetKeyOnCurve

def ιAdapterOp {ℓ : ℕ} {Pt : Type} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    (e2eAdapterOps ℓ decT encT).Op → (atomicAdapterOps ℓ decT encT).Op
  | .inl o => .inl (ιPureOp o)
  | .inr cc => .inr (ιCurveCheckOp cc)

def ιE2EOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    (e2eOps ℓ P C K decT encT).Op → (atomicE2EOps ℓ P C K decT encT).Op
  | .inl o => .inl (.inl (ιPureOp o))
  | .inr (.inl cc) => .inl (.inr (ιCurveCheckOp cc))
  | .inr (.inr c) =>
    match c with
    | .x25519 => .inr (.inr (.inr (.inr .x25519)))
    | .x25519Base => .inr (.inr (.inr (.inr .x25519Base)))
    | .pow8 => .inr (.inr (.inr (.inr .pow8)))
    | .isCanonical => .inr (.inr (.inr (.inr .isCanonical)))
    | .sigSign => .inr (.inr (.inr (.inr .sigSign)))
    | .sigVerify => .inr (.inr (.inr (.inr .sigVerify)))
    | .kemKeyGen => .inr (.inr (.inr (.inr .kemKeyGen)))
    | .kemEncaps => .inr (.inr (.inr (.inr .kemEncaps)))
    | .kemDecaps => .inr (.inr (.inr (.inr .kemDecaps)))
    | .hkdfDerive96 => .inr (.inr (.inr (.inr .hkdfDerive96)))
    | .sessionKeyPairGen => .inr (.inr (.inl .sessionKeyPairGen))
    | .sessionRootCreateChain => .inr (.inr (.inl .sessionRootCreateChain))
    | .chainStep => .inr (.inr (.inl .chainStep))
    | .deriveMsgKeys => .inr (.inr (.inl .deriveMsgKeys))
    | .aes256CbcEnc => .inr (.inr (.inl .aes256CbcEnc))
    | .aes256CbcDec => .inr (.inr (.inl .aes256CbcDec))
    | .signalMsgEncode => .inr (.inr (.inl .signalMsgEncode))
    | .signalMsgVerifyMac => .inr (.inr (.inl .signalMsgVerifyMac))
    | .spqrV1InitOp => .inr (.inr (.inr (.inl .spqrV1InitOp)))
    | .spqrNegotiateInit => .inr (.inr (.inr (.inl .spqrNegotiateInit)))
    | .spqrBraidSend => .inr (.inr (.inr (.inl .spqrBraidSend)))
    | .spqrBraidRecv => .inr (.inr (.inr (.inl .spqrBraidRecv)))
    | .spqrChainFromVn => .inr (.inr (.inr (.inl .spqrChainFromVn)))
    | .spqrChainAddEpoch => .inr (.inr (.inr (.inl .spqrChainAddEpoch)))
    | .spqrChainNextKey => .inr (.inr (.inr (.inl .spqrChainNextKey)))

theorem atomic_e2eReadProstVarint_eq :
    ∀ bs : List (BitVec 8),
      _root_.ReductionDsl.e2eReadProstVarint bs =
        CryptoVerification.E2E.Costed.e2eReadProstVarint bs
  | [] => rfl
  | b :: rest => by
    simp only [_root_.ReductionDsl.e2eReadProstVarint,
      CryptoVerification.E2E.Costed.e2eReadProstVarint, atomic_e2eReadProstVarint_eq rest]

theorem atomic_e2eDecodePreKeyMsg_eq (c : Bytes) :
    _root_.ReductionDsl.e2eDecodePreKeyMsg c =
      CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg c := by
  have hraw : _root_.ReductionDsl.e2eDecodePreKeyRaw c =
      CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw c := by
    unfold _root_.ReductionDsl.e2eDecodePreKeyRaw CryptoVerification.E2E.Costed.e2eDecodePreKeyRaw
      _root_.ReductionDsl.e2eParseOptPreKeyId CryptoVerification.E2E.Costed.e2eParseOptPreKeyId
      _root_.ReductionDsl.e2eParseDjbKeyField CryptoVerification.E2E.Costed.e2eParseDjbKeyField
      _root_.ReductionDsl.e2eParseInnerMsgField CryptoVerification.E2E.Costed.e2eParseInnerMsgField
      _root_.ReductionDsl.e2eParseUint32Field CryptoVerification.E2E.Costed.e2eParseUint32Field
      _root_.ReductionDsl.e2eParseKyberCtField CryptoVerification.E2E.Costed.e2eParseKyberCtField
    simp only [funext atomic_e2eReadProstVarint_eq]
    rfl
  unfold _root_.ReductionDsl.e2eDecodePreKeyMsg CryptoVerification.E2E.Costed.e2eDecodePreKeyMsg
  rw [hraw]
  rfl

theorem atomic_splitSpqrPrev_eq :
    ∀ (fuel : ℕ) (bs : Bytes),
      _root_.ReductionDsl.splitSpqrPrev fuel bs =
        CryptoVerification.E2E.Costed.splitSpqrPrev fuel bs
  | 0, _ => rfl
  | fuel + 1, bs => by
    simp only [_root_.ReductionDsl.splitSpqrPrev, CryptoVerification.E2E.Costed.splitSpqrPrev,
      atomic_splitSpqrPrev_eq fuel (bs.drop 36)]
    rfl

theorem atomic_e2eRecordExtras_eq :
    _root_.ReductionDsl.e2eRecordExtras = CryptoVerification.E2E.Costed.e2eRecordExtras := by
  funext regIdA regIdB bobRemoteRegId hdr p
  cases p <;> rfl

abbrev toAtomicVal (ℓ : ℕ) (Pt : Type) :
    (t : Ty (e2eSig ℓ)) → t.denote →
      (mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort t).denote :=
  toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)

theorem mapTy_ιSort_denote (ℓ : ℕ) (Pt : Type) :
    (t : Ty (e2eSig ℓ)) →
      (mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort t).denote = t.denote
  | .base b => by cases b <;> rfl
  | .unit => rfl
  | .bool => rfl
  | .nat => rfl
  | .opt t => congrArg Option (mapTy_ιSort_denote ℓ Pt t)
  | .prod t u => congrArg₂ Prod (mapTy_ιSort_denote ℓ Pt t) (mapTy_ιSort_denote ℓ Pt u)
  | .sum t u => congrArg₂ Sum (mapTy_ιSort_denote ℓ Pt t) (mapTy_ιSort_denote ℓ Pt u)
  | .list t => congrArg List (mapTy_ιSort_denote ℓ Pt t)
  | .tbl t => congrArg (fun α => ℕ → α) (mapTy_ιSort_denote ℓ Pt t)

theorem cast_option_map {α β : Type} (h : β = α) (f : α → β)
    (hf : ∀ a, cast h (f a) = a) (x : Option α) :
    cast (congrArg Option h) (x.map f) = x := by
  cases h
  cases x with
  | none => rfl
  | some a => exact congrArg some (hf a)

theorem cast_prod_mk {α₁ α₂ β₁ β₂ : Type} (h₁ : β₁ = α₁) (h₂ : β₂ = α₂)
    (x₁ : β₁) (x₂ : β₂) :
    cast (congrArg₂ Prod h₁ h₂) (x₁, x₂) = (cast h₁ x₁, cast h₂ x₂) := by
  cases h₁; cases h₂; rfl

theorem cast_sum_map {α₁ α₂ β₁ β₂ : Type} (h₁ : β₁ = α₁) (h₂ : β₂ = α₂)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂)
    (hf₁ : ∀ a, cast h₁ (f₁ a) = a) (hf₂ : ∀ b, cast h₂ (f₂ b) = b)
    (x : α₁ ⊕ α₂) :
    cast (congrArg₂ Sum h₁ h₂) (Sum.map f₁ f₂ x) = x := by
  cases h₁; cases h₂
  cases x with
  | inl a => exact congrArg Sum.inl (hf₁ a)
  | inr b => exact congrArg Sum.inr (hf₂ b)

theorem cast_list_map {α β : Type} (h : β = α) (f : α → β)
    (hf : ∀ a, cast h (f a) = a) (xs : List α) :
    cast (congrArg List h) (xs.map f) = xs := by
  cases h
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg₂ List.cons (hf a) ih

theorem cast_tbl_map {α β : Type} (h : β = α) (f : α → β)
    (hf : ∀ a, cast h (f a) = a) (m : ℕ → α) :
    cast (congrArg (fun γ => ℕ → γ) h) (fun i => f (m i)) = m := by
  cases h
  funext i
  exact hf (m i)

theorem cast_toVal_ιSort (ℓ : ℕ) (Pt : Type) :
    (t : Ty (e2eSig ℓ)) → (x : t.denote) →
      cast (mapTy_ιSort_denote ℓ Pt t) (toAtomicVal ℓ Pt t x) = x
  | .base b, x => by cases b <;> rfl
  | .unit, _ => rfl
  | .bool, _ => rfl
  | .nat, _ => rfl
  | .opt t, x =>
    cast_option_map (mapTy_ιSort_denote ℓ Pt t) (toAtomicVal ℓ Pt t) (cast_toVal_ιSort ℓ Pt t) x
  | .prod t u, (x, y) => by
    dsimp only [toAtomicVal, toVal]
    rw [cast_prod_mk (mapTy_ιSort_denote ℓ Pt t) (mapTy_ιSort_denote ℓ Pt u),
      cast_toVal_ιSort ℓ Pt t x, cast_toVal_ιSort ℓ Pt u y]
  | .sum t u, x =>
    cast_sum_map (mapTy_ιSort_denote ℓ Pt t) (mapTy_ιSort_denote ℓ Pt u)
      (toAtomicVal ℓ Pt t) (toAtomicVal ℓ Pt u)
      (cast_toVal_ιSort ℓ Pt t) (cast_toVal_ιSort ℓ Pt u) x
  | .list t, xs =>
    cast_list_map (mapTy_ιSort_denote ℓ Pt t) (toAtomicVal ℓ Pt t) (cast_toVal_ιSort ℓ Pt t) xs
  | .tbl t, m =>
    cast_tbl_map (mapTy_ιSort_denote ℓ Pt t) (toAtomicVal ℓ Pt t) (cast_toVal_ιSort ℓ Pt t) m

private theorem cast_inj_local {α β : Type} (h : α = β) {u v : α} (huv : cast h u = cast h v) :
    u = v := by
  cases h
  exact huv

theorem toAtomicVal_surjective (ℓ : ℕ) (Pt : Type) (t : Ty (e2eSig ℓ)) :
    Function.Surjective (toAtomicVal ℓ Pt t) := fun y =>
  ⟨cast (mapTy_ιSort_denote ℓ Pt t) y,
    cast_inj_local (mapTy_ιSort_denote ℓ Pt t)
      (cast_toVal_ιSort ℓ Pt t (cast (mapTy_ιSort_denote ℓ Pt t) y))⟩

theorem castDen_toVal_ιSort_heq (ℓ : ℕ) (Pt : Type) (t : Ty (e2eSig ℓ))
    {t' : Ty (atomicSig ℓ Pt)}
    (h : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort t = t') (x : t.denote) :
    HEq (castDen h (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) t x)) x := by
  cases h
  simp only [castDen_self]
  exact (cast_heq (mapTy_ιSort_denote ℓ Pt t) (toAtomicVal ℓ Pt t x)).symm.trans
    (heq_of_eq (cast_toVal_ιSort ℓ Pt t x))

theorem castDen_toVal_ιSort_eq_cast (ℓ : ℕ) (Pt : Type) (t : Ty (e2eSig ℓ))
    {t' : Ty (atomicSig ℓ Pt)}
    (h : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort t = t')
    (hD : t.denote = t'.denote) (x : t.denote) :
    castDen h (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) t x) =
      cast hD x :=
  eq_of_heq ((castDen_toVal_ιSort_heq ℓ Pt t h x).trans (cast_heq hD x).symm)

private theorem op_eval_hom_eq (ℓ : ℕ) (Pt : Type)
    {dom₁ cod₁ : Ty (e2eSig ℓ)} {dom₂ cod₂ : Ty (atomicSig ℓ Pt)}
    (hdom : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort dom₁ = dom₂)
    (hcod : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort cod₁ = cod₂)
    (hdomD : dom₁.denote = dom₂.denote) (hcodD : cod₁.denote = cod₂.denote)
    (f₁ : dom₁.denote → cod₁.denote) (f₂ : dom₂.denote → cod₂.denote)
    (x : dom₁.denote)
    (hf : f₂ (cast hdomD x) = cast hcodD (f₁ x)) :
    f₂ (castDen hdom (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) dom₁ x)) =
      castDen hcod (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) cod₁ (f₁ x)) := by
  rw [castDen_toVal_ιSort_eq_cast ℓ Pt dom₁ hdom hdomD x,
      castDen_toVal_ιSort_eq_cast ℓ Pt cod₁ hcod hcodD (f₁ x)]
  exact hf

theorem atomic_spqrDirToV_eq (ℓ : ℕ) (Pt : Type)
    (d : CryptoVerification.LibsignalSpqrV1.EpochDirectionPB) :
    _root_.ReductionDsl.spqrDirToV (ℓ := ℓ) (Pt := Pt) d =
      CryptoVerification.E2E.Costed.spqrDirToV (ℓ := ℓ) d :=
  congrArg (fun p => (d.ctr, (d.next.take 64, p))) (atomic_splitSpqrPrev_eq 2201 d.prev)

theorem atomic_spqrChainToV_eq (ℓ : ℕ) (Pt : Type)
    (c : CryptoVerification.LibsignalSpqrV1.ChainPB) :
    _root_.ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) c =
      CryptoVerification.E2E.Costed.spqrChainToV (ℓ := ℓ) c :=
  congrArg
    (fun dirF =>
      let links := (c.links.take 4).map fun lk => (lk.send.map dirF, lk.recv.map dirF)
      (c.direction, (c.currentEpoch, (links, (c.nextRoot.take 64, (c.sendEpoch,
        c.params.map _root_.ReductionDsl.spqrParamsToV))))))
    (funext (atomic_spqrDirToV_eq ℓ Pt))

theorem pureOp_dom_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort ((e2ePureOps ℓ).dom o) =
      (atomicPureOps ℓ Pt).dom (ιPureOp o) := by
  cases o <;> rfl

theorem pureOp_cod_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort ((e2ePureOps ℓ).cod o) =
      (atomicPureOps ℓ Pt).cod (ιPureOp o) := by
  cases o <;> rfl

theorem pureOp_cost_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    (atomicPureOps ℓ Pt).cost (ιPureOp o) = (e2ePureOps ℓ).cost o := by
  cases o <;> rfl

theorem pureOp_opSize_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp) :
    (atomicPureOps ℓ Pt).opSize (ιPureOp o) = (e2ePureOps ℓ).opSize o := by
  cases o <;> rfl

private theorem atomic_spqrSplitEval_eq (ℓ : ℕ) (Pt : Type) (x : Bytes) :
    _root_.ReductionDsl.spqrSplitEval (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.spqrSplitEval (ℓ := ℓ) x := by
  unfold _root_.ReductionDsl.spqrSplitEval CryptoVerification.E2E.Costed.spqrSplitEval
  have hvn :
      _root_.ReductionDsl.spqrVnToV (ℓ := ℓ) (Pt := Pt) =
        CryptoVerification.E2E.Costed.spqrVnToV (ℓ := ℓ) := by
    funext vn; cases vn.chainParams <;> rfl
  have hch :
      _root_.ReductionDsl.spqrChainToV (ℓ := ℓ) (Pt := Pt) =
        CryptoVerification.E2E.Costed.spqrChainToV (ℓ := ℓ) :=
    funext (atomic_spqrChainToV_eq ℓ Pt)
  rw [hvn, hch]
  cases CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState x with
  | error _ => rfl
  | ok st =>
    cases st.inner with
    | none => rfl
    | some i => cases i; rfl

private theorem atomic_spqrJoinEval_eq (ℓ : ℕ) (Pt : Type)
    (x : (CryptoVerification.E2E.Costed.spqrStatePartsT (ℓ := ℓ)).denote) :
    _root_.ReductionDsl.spqrJoinEval (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.spqrJoinEval (ℓ := ℓ) x := by
  rcases x with ⟨v1?, vn?, ch?⟩
  unfold _root_.ReductionDsl.spqrJoinEval CryptoVerification.E2E.Costed.spqrJoinEval
  dsimp only
  apply congrArg (List.take (32 * 11000))
  rcases v1? with _ | v1Raw <;> rcases vn? with _ | vn <;> rcases ch? with _ | ch <;> rfl

private theorem atomic_e2eEncodeSessionRecord_eq (ℓ : ℕ) (Pt : Type)
    (x : ((e2ePureOps ℓ).dom .encodeSessionRecord).denote) :
    _root_.ReductionDsl.e2eEncodeSessionRecord (ℓ := ℓ) (Pt := Pt) x =
      CryptoVerification.E2E.Costed.e2eEncodeSessionRecord (ℓ := ℓ) x := by
  rcases x with ⟨⟨regIdA, regIdB, bobReg, hdr⟩, g⟩
  have hbs :
      CryptoVerification.E2E.binStateOfUnderExtras
        (_root_.ReductionDsl.e2eRecordExtras regIdA regIdB bobReg
          (_root_.ReductionDsl.hdrOfV (ℓ := ℓ) (Pt := Pt) hdr)) g =
      CryptoVerification.E2E.binStateOfUnderExtras
        (CryptoVerification.E2E.Costed.e2eRecordExtras regIdA regIdB bobReg
          (CryptoVerification.E2E.Costed.hdrOfV (ℓ := ℓ) hdr)) g := by
    rw [atomic_e2eRecordExtras_eq]
    rfl
  exact congrArg (fun bs : BinState => { bs with bytes := bs.bytes.take (32 * 24000) }) hbs

set_option maxHeartbeats 800000 in
theorem pureOp_eval_eq (ℓ : ℕ) (Pt : Type) (o : E2EPureOp)
    (x : ((e2ePureOps ℓ).dom o).denote) :
    (atomicPureOps ℓ Pt).eval (ιPureOp o)
        (castDen (pureOp_dom_eq ℓ Pt o)
          (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)
            ((e2ePureOps ℓ).dom o) x)) =
      castDen (pureOp_cod_eq ℓ Pt o)
        (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)
          ((e2ePureOps ℓ).cod o) ((e2ePureOps ℓ).eval o x)) := by
  cases o <;>
    refine op_eval_hom_eq ℓ Pt (pureOp_dom_eq ℓ Pt _) (pureOp_cod_eq ℓ Pt _) rfl rfl
      ((e2ePureOps ℓ).eval _) ((atomicPureOps ℓ Pt).eval (ιPureOp _)) x ?_
  case checkShortCiphertext =>
    rcases x with ⟨c, _ | i⟩ <;> rfl
  case splitWhisperWire =>
    rcases x with _ | ⟨t, body⟩ <;> rfl
  case parsePreKeyWire =>
    exact congrArg
      (Option.map fun m =>
        (m.regId, (_root_.ReductionDsl.hdrV (_root_.ReductionDsl.e2eHdrOfPreKeyMsg m),
          m.inner.take x.length)))
      (atomic_e2eDecodePreKeyMsg_eq x)
  case partneredInnerBytes =>
    rcases x with ⟨bobAcc, regIdA, hdr, c⟩
    change _root_.ReductionDsl.e2ePartneredInnerBytes bobAcc regIdA
        (_root_.ReductionDsl.hdrOfV hdr) c =
      CryptoVerification.E2E.Costed.e2ePartneredInnerBytes bobAcc regIdA
        (CryptoVerification.E2E.Costed.hdrOfV hdr) c
    simp only [_root_.ReductionDsl.e2ePartneredInnerBytes,
      CryptoVerification.E2E.Costed.e2ePartneredInnerBytes,
      atomic_e2eDecodePreKeyMsg_eq]
    rfl
  case wireInnerBytes =>
    change _root_.ReductionDsl.e2eWireInnerBytes x =
      CryptoVerification.E2E.Costed.e2eWireInnerBytes x
    simp only [_root_.ReductionDsl.e2eWireInnerBytes,
      CryptoVerification.E2E.Costed.e2eWireInnerBytes,
      atomic_e2eDecodePreKeyMsg_eq]
    rfl
  case wrapPreKeyWire =>
    rcases x with ⟨regIdA, hdr, inner⟩
    change (if inner.isEmpty then []
        else (CryptoVerification.E2E.wirePrekey ::
          (_root_.ReductionDsl.e2eExpectedPreKeyMsg regIdA
            (_root_.ReductionDsl.hdrOfV hdr) inner).bytes).take
          (32 * (2 * (ℓ / 32) + 84))) =
      (if inner.isEmpty then []
        else (CryptoVerification.E2E.wirePrekey ::
          (CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg regIdA
            (CryptoVerification.E2E.Costed.hdrOfV hdr) inner).bytes).take
          (32 * (2 * (ℓ / 32) + 84)))
    have hexp :
        _root_.ReductionDsl.e2eExpectedPreKeyMsg regIdA
          (_root_.ReductionDsl.hdrOfV (ℓ := ℓ) (Pt := Pt) hdr) inner =
        CryptoVerification.E2E.Costed.e2eExpectedPreKeyMsg regIdA
          (CryptoVerification.E2E.Costed.hdrOfV (ℓ := ℓ) hdr) inner := rfl
    rw [hexp]
  case spqrStateSplit =>
    exact atomic_spqrSplitEval_eq ℓ Pt x
  case spqrStateJoin =>
    exact atomic_spqrJoinEval_eq ℓ Pt x
  case ghostStateSplit =>
    cases x.party <;> rfl
  case ghostStateJoin =>
    cases x.1 <;> rfl
  case encodeSessionRecord =>
    exact atomic_e2eEncodeSessionRecord_eq ℓ Pt x
  all_goals rfl

theorem curveCheckOp_dom_eq (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cc : CryptoVerification.E2E.Costed.E2ECurveCheckOp) :
    mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort
        ((e2eCurveCheckOps ℓ decT encT).dom cc) =
      (_root_.ReductionDsl.atomicCurveCheckOps ℓ decT encT).dom (ιCurveCheckOp cc) := by
  cases cc <;> rfl

theorem curveCheckOp_cod_eq (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cc : CryptoVerification.E2E.Costed.E2ECurveCheckOp) :
    mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort
        ((e2eCurveCheckOps ℓ decT encT).cod cc) =
      (_root_.ReductionDsl.atomicCurveCheckOps ℓ decT encT).cod (ιCurveCheckOp cc) := by
  cases cc <;> rfl

theorem curveCheckOp_eval_eq (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (cc : CryptoVerification.E2E.Costed.E2ECurveCheckOp)
    (x : ((e2eCurveCheckOps ℓ decT encT).dom cc).denote) :
    (_root_.ReductionDsl.atomicCurveCheckOps ℓ decT encT).eval (ιCurveCheckOp cc)
        (castDen (curveCheckOp_dom_eq ℓ decT encT cc)
          (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)
            ((e2eCurveCheckOps ℓ decT encT).dom cc) x)) =
      castDen (curveCheckOp_cod_eq ℓ decT encT cc)
        (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)
          ((e2eCurveCheckOps ℓ decT encT).cod cc)
          ((e2eCurveCheckOps ℓ decT encT).eval cc x)) := by
  cases cc <;> rfl

def adapterOpsHom (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsHom (e2eSig ℓ) (atomicSig ℓ Pt) (e2eAdapterOps ℓ decT encT)
      (atomicAdapterOps ℓ decT encT) where
  fSort := ιSort
  toDen := toDen ℓ Pt
  fOp := ιAdapterOp
  dom_eq := by
    rintro (o | cc)
    · exact pureOp_dom_eq ℓ Pt o
    · exact curveCheckOp_dom_eq ℓ decT encT cc
  cod_eq := by
    rintro (o | cc)
    · exact pureOp_cod_eq ℓ Pt o
    · exact curveCheckOp_cod_eq ℓ decT encT cc
  cost_eq := by
    rintro (o | cc)
    · exact pureOp_cost_eq ℓ Pt o
    · cases cc <;> rfl
  opSize_eq := by
    rintro (o | cc)
    · exact pureOp_opSize_eq ℓ Pt o
    · cases cc <;> rfl
  eval_eq := by
    rintro (o | cc) x
    · exact pureOp_eval_eq ℓ Pt o x
    · exact curveCheckOp_eval_eq ℓ decT encT cc x

theorem e2eOp_dom_eq (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (o : (e2eOps ℓ P C K decT encT).Op) :
    mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort
        ((e2eOps ℓ P C K decT encT).dom o) =
      (atomicE2EOps ℓ P C K decT encT).dom (ιE2EOp o) := by
  rcases o with o | (cc | c)
  · exact pureOp_dom_eq ℓ Pt o
  · exact curveCheckOp_dom_eq ℓ decT encT cc
  · cases c <;> rfl

theorem e2eOp_cod_eq (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (o : (e2eOps ℓ P C K decT encT).Op) :
    mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort
        ((e2eOps ℓ P C K decT encT).cod o) =
      (atomicE2EOps ℓ P C K decT encT).cod (ιE2EOp o) := by
  rcases o with o | (cc | c)
  · exact pureOp_cod_eq ℓ Pt o
  · exact curveCheckOp_cod_eq ℓ decT encT cc
  · cases c <;> rfl

theorem e2eOp_cost_eq (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).cost (ιE2EOp o) =
      (e2eOps ℓ P C K decT encT).cost o := by
  rcases o with o | (cc | c)
  · exact pureOp_cost_eq ℓ Pt o
  · cases cc <;> rfl
  · cases c <;> rfl

theorem e2eOp_opSize_eq (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (o : (e2eOps ℓ P C K decT encT).Op) :
    (atomicE2EOps ℓ P C K decT encT).opSize (ιE2EOp o) =
      (e2eOps ℓ P C K decT encT).opSize o := by
  rcases o with o | (cc | c)
  · exact pureOp_opSize_eq ℓ Pt o
  · cases cc <;> rfl
  · cases c <;> rfl

def e2eOpsHom (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    OpsHom (e2eSig ℓ) (atomicSig ℓ Pt) (e2eOps ℓ P C K decT encT)
      (atomicE2EOps ℓ P C K decT encT) where
  fSort := ιSort
  toDen := toDen ℓ Pt
  fOp := ιE2EOp
  dom_eq := e2eOp_dom_eq ℓ P C K decT encT
  cod_eq := e2eOp_cod_eq ℓ P C K decT encT
  cost_eq := e2eOp_cost_eq ℓ P C K decT encT
  opSize_eq := e2eOp_opSize_eq ℓ P C K decT encT
  eval_eq := by
    rintro (o | (cc | c)) x
    · exact pureOp_eval_eq ℓ Pt o x
    · exact curveCheckOp_eval_eq ℓ decT encT cc x
    · cases c <;>
        refine op_eval_hom_eq ℓ Pt
          (e2eOp_dom_eq ℓ P C K decT encT _)
          (e2eOp_cod_eq ℓ P C K decT encT _)
          rfl rfl
          ((e2eOps ℓ P C K decT encT).eval _)
          ((atomicE2EOps ℓ P C K decT encT).eval (ιE2EOp _))
          x ?_
      case spqrChainFromVn =>
        change _root_.ReductionDsl.spqrChainFromVnEval (ℓ := ℓ) (Pt := Pt) C.F x =
          CryptoVerification.E2E.Costed.spqrChainFromVnEval (ℓ := ℓ) C.F x
        unfold _root_.ReductionDsl.spqrChainFromVnEval CryptoVerification.E2E.Costed.spqrChainFromVnEval
        have hvn : _root_.ReductionDsl.spqrVnOfV (ℓ := ℓ) (Pt := Pt) x =
            CryptoVerification.E2E.Costed.spqrVnOfV (ℓ := ℓ) x := rfl
        rw [hvn]
        cases CryptoVerification.LibsignalSpqrV1.chainFromVersionNegotiation
            (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F)
            (CryptoVerification.E2E.Costed.spqrVnOfV (ℓ := ℓ) x) with
        | error _ => rfl
        | ok c =>
          dsimp only
          exact congrArg some (atomic_spqrChainToV_eq ℓ Pt c.intoPb)
      case spqrChainAddEpoch =>
        rcases x with ⟨ch, ep, sec⟩
        change _root_.ReductionDsl.spqrChainAddEpochEval (ℓ := ℓ) (Pt := Pt) C.F ch ep sec =
          CryptoVerification.E2E.Costed.spqrChainAddEpochEval (ℓ := ℓ) C.F ch ep sec
        unfold _root_.ReductionDsl.spqrChainAddEpochEval CryptoVerification.E2E.Costed.spqrChainAddEpochEval
        have hch : _root_.ReductionDsl.spqrChainOfV (ℓ := ℓ) (Pt := Pt) ch =
            CryptoVerification.E2E.Costed.spqrChainOfV (ℓ := ℓ) ch := rfl
        rw [hch]
        cases CryptoVerification.LibsignalSpqrV1.Chain.fromPb
            (CryptoVerification.E2E.Costed.spqrChainOfV (ℓ := ℓ) ch) with
        | error _ => rfl
        | ok c0 =>
          dsimp only
          cases c0.addEpoch (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith C.F)
              ⟨ep, CryptoGames.HMAC.keyToBytes32 sec⟩ with
          | error _ => rfl
          | ok c1 =>
            dsimp only
            exact congrArg (fun v => (false, some v)) (atomic_spqrChainToV_eq ℓ Pt c1.intoPb)
      all_goals rfl

def ιKeyIndTag : CryptoVerification.E2E.Costed.E2EKeyIndTag → _root_.ReductionDsl.E2EKeyIndTag
  | .keyInd => .keyInd

def ιSessionTag : CryptoVerification.E2E.Costed.E2ESessionTag → _root_.ReductionDsl.E2ESessionTag
  | .tr => .tr | .ch => .ch | .dl => .dl | .ij => .ij | .cr => .cr

def ιAdapterTag : CryptoVerification.E2E.Costed.E2EAdapterTag → _root_.ReductionDsl.E2EAdapterTag
  | .ki => .ki | .ctl => .ctl | .tr => .tr | .ch => .ch | .dl => .dl | .ij => .ij | .cr => .cr

theorem atomic_sidV_eq {S : SignalPqxdh.Setup} (ℓ : ℕ) (Pt : Type) (sid : SignalPqxdh.SessionId S) :
    _root_.ReductionDsl.sidV (ℓ := ℓ) (Pt := Pt) sid =
      CryptoVerification.E2E.Costed.sidV (ℓ := ℓ) sid := by
  cases sid <;> rfl

theorem atomic_sidOfV_eq {S : SignalPqxdh.Setup} (ℓ : ℕ) (Pt : Type)
    (sid : (CryptoVerification.E2E.Costed.sidT (ℓ := ℓ) S).denote) :
    _root_.ReductionDsl.sidOfV (ℓ := ℓ) (Pt := Pt) (S := S) sid =
      CryptoVerification.E2E.Costed.sidOfV (ℓ := ℓ) (S := S) sid := by
  rcases sid with ⟨_, _⟩ | (⟨_, _⟩ | (⟨_, _, _⟩ | ⟨_, _, _⟩)) <;> rfl

theorem atomic_keyIndQenc_eq {S : SignalPqxdh.Setup} (ℓ : ℕ) (Pt : Type)
    (kq : SignalPqxdh.KeyIndQuery S) :
    _root_.ReductionDsl.keyIndQenc (ℓ := ℓ) (Pt := Pt) kq =
      CryptoVerification.E2E.Costed.keyIndQenc (ℓ := ℓ) kq := by
  cases kq <;> simp only [_root_.ReductionDsl.keyIndQenc,
    CryptoVerification.E2E.Costed.keyIndQenc, atomic_sidV_eq] <;> rfl

theorem atomic_keyIndQdec_eq {S : SignalPqxdh.Setup} (ℓ : ℕ) (Pt : Type)
    (q : (CryptoVerification.E2E.Costed.keyIndQT (ℓ := ℓ) S).denote) :
    _root_.ReductionDsl.keyIndQdec (ℓ := ℓ) (Pt := Pt) (S := S) q =
      CryptoVerification.E2E.Costed.keyIndQdec (ℓ := ℓ) (S := S) q := by
  rcases q with u | (u | (⟨u, j⟩ | (⟨u, j, o⟩ | (⟨u, i, b⟩ | (⟨u, i, b⟩ |
    (⟨k, j, o, h⟩ | (⟨k, j, l, h⟩ | (sid | (sec | (⟨⟩ | (sid | (sk | ⟨u, j⟩)))))))))))) <;>
    simp only [_root_.ReductionDsl.keyIndQdec, CryptoVerification.E2E.Costed.keyIndQdec,
      atomic_sidOfV_eq] <;> rfl

theorem atomic_keyIndRenc_eq (ℓ : ℕ) (Pt : Type) (r : SignalPqxdh.KeyIndResponse) :
    _root_.ReductionDsl.keyIndRenc (ℓ := ℓ) (Pt := Pt) r =
      CryptoVerification.E2E.Costed.keyIndRenc (ℓ := ℓ) r := by
  cases r <;> rfl

theorem atomic_keyIndRdec_eq (ℓ : ℕ) (Pt : Type)
    (r : (CryptoVerification.E2E.Costed.keyIndRT (ℓ := ℓ)).denote) :
    _root_.ReductionDsl.keyIndRdec (ℓ := ℓ) (Pt := Pt) r =
      CryptoVerification.E2E.Costed.keyIndRdec (ℓ := ℓ) r := by
  rcases r with ⟨⟩ | (⟨_, _⟩ | (_ | (⟨_, _⟩ | (b | (h | (⟨dk, h⟩ |
    (⟨⟩ | (dk | (⟨_, _, _, _⟩ | _))))))))) <;> rfl

theorem atomic_recvResultEnc_eq (ℓ : ℕ) (Pt : Type) :
    _root_.ReductionDsl.recvResultEnc (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.recvResultEnc (ℓ := ℓ) := by
  funext rr
  cases rr <;> rfl

theorem atomic_recvResultDec_eq (ℓ : ℕ) (Pt : Type) :
    _root_.ReductionDsl.recvResultDec (ℓ := ℓ) (Pt := Pt) =
      CryptoVerification.E2E.Costed.recvResultDec (ℓ := ℓ) := by
  funext rr
  rcases rr with ⟨⟩ | ⟨_, _, _⟩ <;> rfl

theorem atomic_smQenc_eq {St : Type} (ℓ : ℕ) (Pt : Type)
    (sq : (CryptoGames.SM.spec St (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes).Domain) :
    _root_.ReductionDsl.smQenc (ℓ := ℓ) (Pt := Pt) sq =
      CryptoVerification.E2E.Costed.smQenc (ℓ := ℓ) sq := by
  rcases sq with (((⟨p, _, _⟩ | ⟨p, _, _, _⟩) | ⟨p, _⟩) | ⟨p, _⟩) | p <;> cases p <;> rfl

theorem samp_hom_eq (ℓ : ℕ) (Pt : Type)
    (s : _root_.ReductionDsl.UniformSamplerTag E2EUnifBase)
    (hDom : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort ((e2eSamplers ℓ).sDom s) =
      (atomicBaseSamplers ℓ Pt).sDom (ιSamp s))
    (hTy : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort ((e2eSamplers ℓ).sTy s) =
      (atomicBaseSamplers ℓ Pt).sTy (ιSamp s))
    (x : ((e2eSamplers ℓ).sDom s).denote) :
    (atomicBaseSamplers ℓ Pt).samp (ιSamp s)
        (castDen hDom (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)
          ((e2eSamplers ℓ).sDom s) x)) =
      (fun y =>
          castDen hTy (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt)
            ((e2eSamplers ℓ).sTy s) y)) <$>
        (e2eSamplers ℓ).samp s x := by
  cases s with
  | bool => exact (id_map _).symm
  | index _ => exact (id_map _).symm
  | base b => cases b <;> exact (id_map _).symm

private theorem cast_oracleComp_eq_map {ι : Type} {T : OracleSpec ι} {α β : Type}
    (h : α = β) (m : OracleComp T α) :
    cast (congrArg (OracleComp T) h) m = cast h <$> m := by
  cases h
  exact (id_map m).symm

private theorem iface_query_hom_eq {ι : Type} {T : OracleSpec ι} (ℓ : ℕ) (Pt : Type)
    {dom₁ cod₁ : Ty (e2eSig ℓ)} {dom₂ cod₂ : Ty (atomicSig ℓ Pt)}
    (hdom : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort dom₁ = dom₂)
    (hcod : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort cod₁ = cod₂)
    (hdomD : dom₁.denote = dom₂.denote) (hcodD : cod₁.denote = cod₂.denote)
    (q₁ : dom₁.denote → OracleComp T cod₁.denote)
    (q₂ : dom₂.denote → OracleComp T cod₂.denote)
    (x : dom₁.denote)
    (hq : q₂ (cast hdomD x) = cast (congrArg (OracleComp T) hcodD) (q₁ x)) :
    q₂ (castDen hdom (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) dom₁ x)) =
      (fun y => castDen hcod (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) cod₁ y)) <$>
        q₁ x := by
  rw [castDen_toVal_ιSort_eq_cast ℓ Pt dom₁ hdom hdomD x, hq]
  have hFun :
      (fun y => castDen hcod (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) cod₁ y)) =
        cast hcodD := by
    funext y
    exact castDen_toVal_ιSort_eq_cast ℓ Pt cod₁ hcod hcodD y
  rw [hFun]
  exact cast_oracleComp_eq_map hcodD (q₁ x)

private theorem codec_qenc_hom_eq {κ : Type} (ℓ : ℕ) (Pt : Type)
    {Q₁ : Ty (e2eSig ℓ)} {Q₂ : Ty (atomicSig ℓ Pt)}
    (hQ : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort Q₁ = Q₂)
    (hQD : Q₁.denote = Q₂.denote)
    (qenc₁ : κ → Q₁.denote) (qenc₂ : κ → Q₂.denote) (q : κ)
    (hq : qenc₂ q = cast hQD (qenc₁ q)) :
    qenc₂ q =
      castDen hQ (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) Q₁ (qenc₁ q)) := by
  rw [castDen_toVal_ιSort_eq_cast ℓ Pt Q₁ hQ hQD (qenc₁ q)]
  exact hq

private theorem codec_rdec_hom_eq {κ : Type} {G : OracleSpec κ} (ℓ : ℕ) (Pt : Type)
    {R₁ : Ty (e2eSig ℓ)} {R₂ : Ty (atomicSig ℓ Pt)}
    (hR : mapTy (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort R₁ = R₂)
    (hRD : R₁.denote = R₂.denote)
    (rdec₁ : (q : κ) → R₁.denote → G q) (rdec₂ : (q : κ) → R₂.denote → G q)
    (q : κ) (r : R₁.denote)
    (hr : rdec₂ q (cast hRD r) = rdec₁ q r) :
    rdec₂ q (castDen hR (toVal (S₁ := e2eSig ℓ) (S₂ := atomicSig ℓ Pt) ιSort (toDen ℓ Pt) R₁ r)) =
      rdec₁ q r := by
  rw [castDen_toVal_ιSort_eq_cast ℓ Pt R₁ hR hRD r]
  exact hr

def adapterIfaceHom (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    IfaceHom (e2eSig ℓ) (atomicSig ℓ Pt)
      (CryptoVerification.E2E.Costed.e2eAdapterIface S ℓ BHDRCtlQuery.startDR)
      (e2eBhAdapterIface S ℓ Pt)
      ιSort (toDen ℓ Pt) where
  fwdU_eq _ := rfl
  uCost_eq := rfl
  fSamp := ιSamp
  sDom_eq _ := rfl
  sTy_eq s := by
    cases s with
    | bool => rfl
    | index _ => rfl
    | base b => cases b <;> rfl
  sCost_eq s := by
    cases s with
    | bool => rfl
    | index _ => rfl
    | base b => cases b <;> rfl
  samp_eq s x := samp_hom_eq ℓ Pt s _ _ x
  fTag := ιAdapterTag
  qDom_eq g := by cases g <;> rfl
  qCod_eq g := by cases g <;> rfl
  qCost_eq g := by cases g <;> rfl
  query_eq g x := by
    let I₁ := CryptoVerification.E2E.Costed.e2eAdapterIface S ℓ BHDRCtlQuery.startDR
    let I₂ := e2eBhAdapterIface S ℓ Pt
    refine iface_query_hom_eq ℓ Pt
      (by cases g <;> rfl) (by cases g <;> rfl)
      (by cases g <;> rfl) (by cases g <;> rfl)
      (fun z => I₁.dec g z <$>
        (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (I₁.enc g z)) : OracleComp _ _))
      (fun z => I₂.dec (ιAdapterTag g) z <$>
        (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (I₂.enc (ιAdapterTag g) z)) :
          OracleComp _ _))
      x ?_
    cases g
    case ki =>
      exact congrArg₂ Functor.map (funext (atomic_keyIndRenc_eq ℓ Pt))
        (congrArg
          (fun kq =>
            (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query (.inr (.inl (.inl kq)))) :
              OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) SignalPqxdh.KeyIndResponse))
          (atomic_keyIndQdec_eq ℓ Pt x))
    case ctl =>
      exact congrArg
        (fun sid =>
          (fun y => y) <$>
            (liftM ((unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).query
              (.inr (.inl (.inr (BHDRCtlQuery.startDR sid))))) :
              OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) (Option ℕ)))
        (atomic_sidOfV_eq ℓ Pt x)
    case tr =>
      rcases x with ⟨i, p, m, r?⟩
      cases p <;> rfl
    case ch =>
      rcases x with ⟨i, p, m0, m1, r?⟩
      cases p <;> rfl
    case dl =>
      rcases x with ⟨i, p, c⟩
      cases p <;> exact congrArg (fun f => Option.map f <$> _) (atomic_recvResultEnc_eq ℓ Pt)
    case ij =>
      rcases x with ⟨i, p, c⟩
      cases p <;> exact congrArg (fun f => Option.map f <$> _) (atomic_recvResultEnc_eq ℓ Pt)
    case cr =>
      rcases x with ⟨i, p⟩
      cases p <;> rfl

def keyIndTargetIfaceHom (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    IfaceHom (e2eSig ℓ) (atomicSig ℓ Pt)
      (CryptoVerification.E2E.Costed.e2eKeyIndTargetIface S ℓ)
      (_root_.ReductionDsl.e2eKeyIndTargetIface S ℓ Pt)
      ιSort (toDen ℓ Pt) where
  fwdU_eq _ := rfl
  uCost_eq := rfl
  fSamp := ιSamp
  sDom_eq _ := rfl
  sTy_eq s := by
    cases s with
    | bool => rfl
    | index _ => rfl
    | base b => cases b <;> rfl
  sCost_eq s := by
    cases s with
    | bool => rfl
    | index _ => rfl
    | base b => cases b <;> rfl
  samp_eq s x := samp_hom_eq ℓ Pt s _ _ x
  fTag := ιKeyIndTag
  qDom_eq g := by cases g; rfl
  qCod_eq g := by cases g; rfl
  qCost_eq g := by cases g; rfl
  query_eq g x := by
    let I₁ := CryptoVerification.E2E.Costed.e2eKeyIndTargetIface S ℓ
    let I₂ := _root_.ReductionDsl.e2eKeyIndTargetIface S ℓ Pt
    cases g
    refine iface_query_hom_eq ℓ Pt rfl rfl rfl rfl
      (fun z => I₁.dec .keyInd z <$> (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (I₁.enc .keyInd z)) : OracleComp _ _))
      (fun z => I₂.dec .keyInd z <$> (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (I₂.enc .keyInd z)) : OracleComp _ _))
      x ?_
    exact congrArg₂ Functor.map (funext (atomic_keyIndRenc_eq ℓ Pt))
      (congrArg
        (fun kq =>
          (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
            OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) SignalPqxdh.KeyIndResponse))
        (atomic_keyIndQdec_eq ℓ Pt x))

def sessionTargetIfaceHom (ℓ : ℕ) (Pt : Type) :
    IfaceHom (e2eSig ℓ) (atomicSig ℓ Pt)
      (CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ)
      (_root_.ReductionDsl.e2eSessionTargetIface ℓ Pt)
      ιSort (toDen ℓ Pt) where
  fwdU_eq _ := rfl
  uCost_eq := rfl
  fSamp := ιSamp
  sDom_eq _ := rfl
  sTy_eq s := by
    cases s with
    | bool => rfl
    | index _ => rfl
    | base b => cases b <;> rfl
  sCost_eq s := by
    cases s with
    | bool => rfl
    | index _ => rfl
    | base b => cases b <;> rfl
  samp_eq s x := samp_hom_eq ℓ Pt s _ _ x
  fTag := ιSessionTag
  qDom_eq g := by cases g <;> rfl
  qCod_eq g := by cases g <;> rfl
  qCost_eq g := by cases g <;> rfl
  query_eq g x := by
    let I₁ := CryptoVerification.E2E.Costed.e2eSessionTargetIface ℓ
    let I₂ := _root_.ReductionDsl.e2eSessionTargetIface ℓ Pt
    refine iface_query_hom_eq ℓ Pt
      (by cases g <;> rfl) (by cases g <;> rfl)
      (by cases g <;> rfl) (by cases g <;> rfl)
      (fun z => I₁.dec g z <$>
        (liftM ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes).query
          (I₁.enc g z)) : OracleComp _ _))
      (fun z => I₂.dec (ιSessionTag g) z <$>
        (liftM ((unifSpec + CryptoGames.SM.spec (GhostState Bytes) (CryptoGames.CBC.Plain ℓ) (BitVec 512) Bytes).query
          (I₂.enc (ιSessionTag g) z)) : OracleComp _ _))
      x ?_
    cases g
    case tr =>
      rcases x with ⟨p, m, r?⟩
      cases p <;> rfl
    case ch =>
      rcases x with ⟨p, m0, m1, r?⟩
      cases p <;> rfl
    case dl =>
      rcases x with ⟨p, c⟩
      cases p <;> exact congrArg (fun f => Option.map f <$> _) (atomic_recvResultEnc_eq ℓ Pt)
    case ij =>
      rcases x with ⟨p, c⟩
      cases p <;> exact congrArg (fun f => Option.map f <$> _) (atomic_recvResultEnc_eq ℓ Pt)
    case cr =>
      cases x <;> rfl

theorem adapterCodecHom (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    GameCodecHom (e2eSig ℓ) (atomicSig ℓ Pt)
      (CryptoVerification.E2E.Costed.e2eAdapterCodec S ℓ bhCtlUnStart)
      (e2eBhAdapterCodec S ℓ Pt)
      ιSort (toDen ℓ Pt) where
  Q_eq := rfl
  R_eq := rfl
  codecCost_eq := rfl
  qenc_eq := by
    intro q
    refine codec_qenc_hom_eq ℓ Pt rfl rfl
      (CryptoVerification.E2E.Costed.e2eAdapterCodec S ℓ bhCtlUnStart).qenc
      (e2eBhAdapterCodec S ℓ Pt).qenc q ?_
    rcases q with (kq | cq) | ⟨i, sq⟩
    · exact congrArg Sum.inl (congrArg Sum.inl (atomic_keyIndQenc_eq ℓ Pt kq))
    · exact congrArg Sum.inl (congrArg Sum.inr (atomic_sidV_eq ℓ Pt _))
    · exact congrArg Sum.inr (congrArg (Prod.mk i) (atomic_smQenc_eq ℓ Pt sq))
  rdec_eq := by
    intro q r
    refine codec_rdec_hom_eq ℓ Pt rfl rfl
      (CryptoVerification.E2E.Costed.e2eAdapterCodec S ℓ bhCtlUnStart).rdec
      (e2eBhAdapterCodec S ℓ Pt).rdec q r ?_
    rcases q with (kq | cq) | ⟨i, sq⟩ <;> rcases r with (kr | cr) | sr
    · exact atomic_keyIndRdec_eq ℓ Pt kr
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _
      · rfl
      · rfl
      · exact congrArg (Option.map · sr.2.1) (atomic_recvResultDec_eq ℓ Pt)
      · exact congrArg (Option.map · sr.2.1) (atomic_recvResultDec_eq ℓ Pt)
      · rfl

theorem targetGameCodecHom (S : SignalPqxdh.Setup) (ℓ : ℕ) (Pt : Type) :
    GameCodecHom (e2eSig ℓ) (atomicSig ℓ Pt)
      (CryptoVerification.E2E.Costed.e2eGameCodec S ℓ bhCtlUnStart)
      (e2eTargetGameCodec S ℓ Pt)
      ιSort (toDen ℓ Pt) where
  Q_eq := rfl
  R_eq := rfl
  codecCost_eq := rfl
  qenc_eq := by
    intro q
    refine codec_qenc_hom_eq ℓ Pt rfl rfl
      (CryptoVerification.E2E.Costed.e2eGameCodec S ℓ bhCtlUnStart).qenc
      (e2eTargetGameCodec S ℓ Pt).qenc q ?_
    rcases q with (kq | cq) | ⟨i, sq⟩
    · exact congrArg Sum.inl (congrArg Sum.inl (atomic_keyIndQenc_eq ℓ Pt kq))
    · exact congrArg Sum.inl (congrArg Sum.inr (atomic_sidV_eq ℓ Pt _))
    · exact congrArg Sum.inr (congrArg (Prod.mk i) (atomic_smQenc_eq ℓ Pt sq))
  rdec_eq := by
    intro q r
    refine codec_rdec_hom_eq ℓ Pt rfl rfl
      (CryptoVerification.E2E.Costed.e2eGameCodec S ℓ bhCtlUnStart).rdec
      (e2eTargetGameCodec S ℓ Pt).rdec q r ?_
    rcases q with (kq | cq) | ⟨i, sq⟩ <;> rcases r with (kr | cr) | sr
    · exact atomic_keyIndRdec_eq ℓ Pt kr
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _
      · rfl
      · rfl
      · exact congrArg (Option.map · sr.2.1) (atomic_recvResultDec_eq ℓ Pt)
      · exact congrArg (Option.map · sr.2.1) (atomic_recvResultDec_eq ℓ Pt)
      · rfl

/-- Binary-harness `CostedReduction` adapter lifted onto `atomicAdapterOps`. -/
def cliToModelAdapterProgAtomic {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProg S ℓ decT encT :=
  mapCostedReduction
    (adapterOpsHom ℓ decT encT)
    (adapterIfaceHom S ℓ Pt)
    (adapterCodecHom S ℓ Pt)
    (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT)

theorem cliToModelAdapterProgAtomic_totalCost_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT).totalCost q =
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalCost q :=
  mapCostedReduction_totalCost _ _ _ _ q

theorem cliToModelAdapterProgAtomic_size_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT).size =
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).size :=
  mapCostedReduction_size _ _ _ _

theorem cliToModelAdapterProgAtomic_totalQueries_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT).totalQueries
        (fun _ => 1) (fun _ => 0) q =
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).totalQueries
        (fun _ => 1) (fun _ => 0) q :=
  mapCostedReduction_totalQueries _ _ _ (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) _ q

theorem cliToModelAdapterProgAtomic_eval_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT).eval =
      (cliToModelAdapterProg (S := S) (ℓ := ℓ) decT encT).eval :=
  mapCostedReduction_eval _ _ _ _

/-- Unconditional `GRedBounded` in `e2eAdapterCostBudgetPreBlock` for
`cliToModelAdapterProgAtomic`. -/
theorem gRedBounded_cliToModelAdapterProgAtomic_preBlock
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    GRedBounded (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ) := by
  refine gRedBounded_of_bounds
    (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT)
    (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
    (e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ) ?_ ?_ ?_
    (atomicAdapterOps_sizeHonest ℓ decT encT)
    (atomicBaseSamplers_sizeHonest ℓ Pt)
  · rw [cliToModelAdapterProgAtomic_totalCost_eq]
    exact totalCost_cliToModelAdapterProg_le_preBlock decT encT b qStart qDR
  · rw [cliToModelAdapterProgAtomic_size_eq]
    exact size_cliToModelAdapterProg_le_preBlock decT encT b qStart qDR
  · rw [cliToModelAdapterProgAtomic_totalQueries_eq]
    exact totalQueries_cliToModelAdapterProg_le decT encT (b.q_total + qStart + qDR)

/-- Per-instance `IsQueryBoundP` transfer for `cliToModelAdapterProgAtomic`. -/
theorem cliToModelAdapterProgAtomic_perInstanceQueryBounds
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hA : CliGameAdversaryPerInstanceBounded A b qStart qs) :
    let B_A :=
      (cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
      (∑ k ∈ Finset.range qStart, qs k) ∧
    (∀ k < qStart, B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      (qs k)) := by
  dsimp only
  rw [cliToModelAdapterProgAtomic_eval_eq]
  exact cliToModelAdapterProg_perInstanceQueryBounds decT encT A b qStart qs hA

/-- Exact `boolBias` equivalence between `cliToModelAdapterProgAtomic` and `L_bh` inside
`cliE2EExpWithKi`. -/
theorem boolBias_cliE2EExpWithKi_cliToModelAdapterProgAtomic_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((cliToModelAdapterProgAtomic (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias =
      (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias := by
  rw [cliToModelAdapterProgAtomic_eval_eq]
  exact boolBias_cliE2EExpWithKi_cliToModelAdapterProg_eq_L_bh S P C K ℓ qep decT encT A

/-- `Ty.tbl`-backed binary-harness `CostedReduction` adapter lifted onto `atomicAdapterOps`. -/
def cliToModelAdapterProgTblAtomic {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProg S ℓ decT encT :=
  mapCostedReduction
    (adapterOpsHom ℓ decT encT)
    (adapterIfaceHom S ℓ Pt)
    (adapterCodecHom S ℓ Pt)
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT)

theorem cliToModelAdapterProgTblAtomic_totalCost_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).totalCost q =
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalCost q :=
  mapCostedReduction_totalCost _ _ _ _ q

theorem cliToModelAdapterProgTblAtomic_size_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).size =
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).size :=
  mapCostedReduction_size _ _ _ _

theorem cliToModelAdapterProgTblAtomic_totalQueries_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).totalQueries
        (fun _ => 1) (fun _ => 0) q =
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalQueries
        (fun _ => 1) (fun _ => 0) q :=
  mapCostedReduction_totalQueries _ _ _ (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
    (fun _ => rfl) (fun _ => rfl) _ q

theorem cliToModelAdapterProgTblAtomic_eval_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval =
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval :=
  (mapCostedReduction_eval
    (adapterOpsHom ℓ decT encT) (adapterIfaceHom S ℓ Pt) (adapterCodecHom S ℓ Pt)
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT)).trans
    (cliToModelAdapterProgTblRo_eval_eq decT encT)

private def wKiOnly : E2EAdapterTag → ℕ
  | .ki => 1
  | _ => 0

private theorem isQueryBoundP_congr_pred_atomic {ι α : Type} {spec : OracleSpec ι}
    {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x ↔ q x) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨h.1.imp (mt (hpq t).mpr) id, fun u => ?_⟩
    by_cases ht : p t
    · have hqt : q t := (hpq t).mp ht
      simpa [ht, hqt] using ih u (by simpa [ht] using h.2 u)
    · have hqt : ¬ q t := mt (hpq t).mpr ht
      simpa [ht, hqt] using ih u (by simpa [ht] using h.2 u)

private theorem simulateQ_run_stateT_of_step_le_atomic
    {ι κ σ α : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {impl : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((impl q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ}
    (hoa : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ impl oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a => simp [simulateQ_pure]
  | query_bind q cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hoa.1.resolve_left (not_not.mpr hp)
      have hcont : ∀ u, (cont u).IsQueryBoundP P_src (n - 1) := fun u => by
        simpa [hp] using hoa.2 u
      refine (isQueryBoundP_bind (hstep q s) fun z _ => ih z.1 (hcont z.1) z.2).mono ?_
      simp only [hp, ↓reduceIte]
      omega
    · have hcont : ∀ u, (cont u).IsQueryBoundP P_src n := fun u => by
        simpa [hp] using hoa.2 u
      refine (isQueryBoundP_bind (hstep q s) fun z _ => ih z.1 (hcont z.1) z.2).mono ?_
      simp only [hp, ↓reduceIte]
      omega

private theorem cliAdapterHandleTbl_queries_wKiOnly
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterHandleTbl decT encT S ℓ).queries wKiOnly (fun _ => 0) = 1 := by
  simp [cliAdapterHandleTbl, cliAdapterKiOrCtlArmTbl, cliAdapterTrArmTbl,
    cliAdapterChArmTbl, cliAdapterDlArmTbl, cliAdapterIjArmTbl, adapterCrArm,
    cliQuery, wKiOnly, Comp.queries]

set_option linter.unusedSimpArgs false in
private theorem isQueryBoundP_cliAdapterHandleTbl_kiPred
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (s : (cliAdapterTblStateTy S ℓ).denote) (t : (bhGameSpec S ℓ (BitVec 512)).Domain) :
    ((cliAdapterHandleTbl decT encT S ℓ).eval
      (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true)
      (if bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t then 1 else 0) := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true
  have hU0 : ∀ n, ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ).fwdU n).IsQueryBoundP P_tgt 0 := fun n =>
    (isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
      P_tgt (Sum.inl n) 0).2 (by simp [P_tgt, bhClassifyTarget])
  have hwKi : ∀ g x, P_tgt ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ).enc g x) → 1 ≤ wKiOnly g := by
    intro g x hx
    cases g <;> simp [P_tgt, wKiOnly, Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface,
      e2eAdapterIface, bhClassifyTarget, bhClassifyTargetOnly] at hx ⊢
  by_cases hp : bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t = true
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hp))]
    rw [← cliAdapterHandleTbl_queries_wKiOnly (S := S) (ℓ := ℓ) decT encT]
    exact _root_.ReductionDsl.Comp.queryBound_eval P_tgt wKiOnly (fun _ => 0) hwKi hU0
      (cliAdapterHandleTbl decT encT S ℓ)
      (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil))
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hp h))]
    have hpFalse : bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t = false :=
      Bool.eq_false_iff.mpr hp
    rcases t with (kq | cq) | ⟨i, sq⟩
    · simp only [bhClassifyGameOnly] at hpFalse
      change ((cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval
          (.cons (.inl (keyIndQenc kq))
            (.cons s (.cons (.inl (.inl (keyIndQenc kq))) .nil)))).IsQueryBoundP P_tgt 0
      simp only [cliAdapterKiOrCtlArmTbl, cliQuery, Comp.eval, Expr.eval, Expr.v0]
      refine (isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun x _ => isQueryBoundP_pure P_tgt _ 0))
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro hq
      change pKi (keyIndQdec (keyIndQenc kq)) = true at hq
      rw [keyIndQdec_keyIndQenc, hpFalse] at hq
      exact False.elim (Bool.false_ne_true hq)
    · rcases cq with ⟨sid⟩
      let cCtl : Comp (e2eAdapterOps ℓ decT encT)
          (Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ)
          [CryptoVerification.E2E.Costed.sidT S,
           .sum (CryptoVerification.E2E.Costed.keyIndQT S) (CryptoVerification.E2E.Costed.sidT S),
           cliAdapterTblStateTy S ℓ,
           (Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).Q]
          (.prod (Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
        .bind (cliQuery E2EAdapterTag.ctl .v0)
          (.caseOpt .v0
            (.ret (.pair (.inl (.inr .none)) .v3))
            (.caseOpt (Computational.Proofs.E2E.Dsl.CliAdapterCosted.guardPromoteTblExpr (.snd (.snd .v4)) .v2)
              (.ret (.pair (.inl (.inr (.some .v0))) .v4))
              (.ret (.pair (.inl (.inr (.some .v1)))
                (.pair (.tset (.fst .v5) .v1 (.some .v0)) (.snd .v5))))))
      have hc0 : cCtl.queries wKiOnly (fun _ => 0) = 0 := by
        simp [cCtl, cliQuery, wKiOnly, Comp.queries]
      change (cCtl.eval (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons s (.cons (.inl (.inr (sidV sid))) .nil))))).IsQueryBoundP P_tgt 0
      exact (_root_.ReductionDsl.Comp.queryBound_eval P_tgt wKiOnly (fun _ => 0) hwKi hU0 cCtl
        (.cons (sidV sid) (.cons (.inr (sidV sid))
          (.cons s (.cons (.inl (.inr (sidV sid))) .nil))))).mono (by rw [hc0])
    · let cSm : Comp (e2eAdapterOps ℓ decT encT)
          (Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ)
          [.prod .nat CryptoVerification.E2E.Costed.smQT, cliAdapterTblStateTy S ℓ,
           (Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).Q]
          (.prod (Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
        .caseSum (.snd .v0)
          (cliAdapterTrArmTbl S ℓ decT encT)
          (.caseSum .v0
            (cliAdapterChArmTbl S ℓ decT encT)
            (.caseSum .v0
              (cliAdapterDlArmTbl S ℓ decT encT)
              (.caseSum .v0
                (cliAdapterIjArmTbl S ℓ decT encT)
                (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
                  (Computational.Proofs.E2E.Dsl.CliAdapterCosted.drvMirrorTblTy S ℓ)))))
      have hc0 : cSm.queries wKiOnly (fun _ => 0) = 0 := by
        simp [cSm, cliAdapterTrArmTbl, cliAdapterChArmTbl, cliAdapterDlArmTbl,
          cliAdapterIjArmTbl, adapterCrArm, cliQuery, wKiOnly, Comp.queries]
      change (cSm.eval (.cons (i, smQenc sq)
          (.cons s (.cons (.inr (i, smQenc sq)) .nil)))).IsQueryBoundP P_tgt 0
      exact (_root_.ReductionDsl.Comp.queryBound_eval P_tgt wKiOnly (fun _ => 0) hwKi hU0 cSm
        (.cons (i, smQenc sq) (.cons s (.cons (.inr (i, smQenc sq)) .nil)))).mono (by rw [hc0])

theorem cliAdapterForwardsKinds_cliToModelAdapterProgTblAtomic
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (qKind : Fin 2 → ℕ) :
    CliAdapterForwardsKinds
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT) qKind := by
  intro A hA i
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  let P_src (k : Fin 2) : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => SignalPqxdh.isGameQueryOfKind bhQueryKind k q = true
  let P_tgt (k : Fin 2) : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q' => SignalPqxdh.isGameQueryOfKind bhQueryKind k q' = true
  have hstep : ∀ (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain)
      (s : (cliAdapterTblStateTy S ℓ).denote),
      (((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).impl q).run s).IsQueryBoundP
        (P_tgt i) (if P_src i q then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      have hnc : ¬ P_src i (.inl m) := by simp [P_src, SignalPqxdh.isGameQueryOfKind]
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnc h))]
      show ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ).fwdU m >>=
          fun a => pure (a, s)).IsQueryBoundP (P_tgt i) 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        ((isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
          (P_tgt i) (Sum.inl m) 0).2 (by simp [P_tgt, SignalPqxdh.isGameQueryOfKind]))
        (fun a _ => isQueryBoundP_pure (P_tgt i) (a, s) 0)
    | inr t =>
      show ((cliAdapterHandleTbl decT encT S ℓ).eval
          (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil)) >>=
          fun p => pure ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP
        (P_tgt i) (if P_src i (.inr t) then 1 else 0)
      suffices hh :
          ((cliAdapterHandleTbl decT encT S ℓ).eval
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
          (P_tgt i) (if P_src i (.inr t) then 1 else 0) by
        simpa only [Nat.add_zero] using isQueryBoundP_bind hh
          (fun p _ => isQueryBoundP_pure (P_tgt i) _ 0)
      rcases i with ⟨_ | _ | n, hn⟩
      ·
        change ((cliAdapterHandleTbl decT encT S ℓ).eval
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
          (P_tgt 0) (if P_src 0 (.inr t) then 1 else 0)
        by_cases hp : P_src 0 (.inr t)
        · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hp))]
          have hq1 : (cliAdapterHandleTbl decT encT S ℓ).queries (fun _ => 1) (fun _ => 0) = 1 := by
            simp [cliAdapterHandleTbl, cliAdapterKiOrCtlArmTbl, cliAdapterTrArmTbl,
              cliAdapterChArmTbl, cliAdapterDlArmTbl, cliAdapterIjArmTbl, adapterCrArm,
              cliQuery, Comp.queries]
          have hU0 : ∀ n, ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ).fwdU n).IsQueryBoundP (P_tgt 0) 0 := fun n =>
            (isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
              (P_tgt 0) (Sum.inl n) 0).2 (by simp [P_tgt, SignalPqxdh.isGameQueryOfKind])
          exact (_root_.ReductionDsl.Comp.queryBound_eval (P_tgt 0) (fun _ => 1) (fun _ => 0)
            (fun _ _ _ => le_rfl) hU0 (cliAdapterHandleTbl decT encT S ℓ)
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil))).mono
            (by rw [hq1])
        · rw [ite_eq_right_iff.mpr (fun h => False.elim (hp h))]
          rcases t with (kq | cq) | ⟨idx, sq⟩
          · cases kq with
            | roQuery sec =>
              change ((cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval
                  (.cons (.inl (keyIndQenc (.roQuery sec)))
                    (.cons s (.cons (.inl (.inl (keyIndQenc (.roQuery sec)))) .nil)))).IsQueryBoundP (P_tgt 0) 0
              simp only [cliAdapterKiOrCtlArmTbl, cliQuery, Comp.eval, Expr.eval, Expr.v0]
              refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure (P_tgt 0) _ 0)
              rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
              intro hq
              change P_tgt 0 (.inr (.inl (.inl (keyIndQdec (ℓ := ℓ)
                (keyIndQenc (ℓ := ℓ) (SignalPqxdh.KeyIndQuery.roQuery (S := S) sec)))))) at hq
              rw [keyIndQdec_keyIndQenc] at hq
              simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhQueryKind] at hq
            | _ =>
              exfalso; apply hp
              simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind]
          · exfalso; apply hp
            simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind]
          · exfalso; apply hp
            simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind]
      ·
        change ((cliAdapterHandleTbl decT encT S ℓ).eval
            (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil))).IsQueryBoundP
          (P_tgt 1) (if P_src 1 (.inr t) then 1 else 0)
        let isRoKi : SignalPqxdh.KeyIndQuery S → Bool
          | .roQuery _ => true
          | _ => false
        have hSrcEq : P_src 1 (.inr t) ↔
            bhClassifyGameOnly isRoKi (fun _ => false) (fun _ => false) t = true := by
          rcases t with (kq | cq) | ⟨idx, sq⟩
          · cases kq <;> simp [P_src, isRoKi, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyGameOnly]
          · simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyGameOnly]
          · simp [P_src, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyGameOnly]
        have hTgtEq :
            ∀ q' : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain,
              (bhClassifyTarget isRoKi (fun _ => false) (fun _ => false) q' = true) ↔ P_tgt 1 q' := by
          intro q'
          cases q' with
          | inl _ => simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhClassifyTarget]
          | inr t' =>
            rcases t' with (kq | cq) | ⟨idx, sq⟩
            · cases kq <;> simp [P_tgt, isRoKi, SignalPqxdh.isGameQueryOfKind, bhQueryKind,
                bhClassifyTarget, bhClassifyTargetOnly]
            · simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyTarget, bhClassifyTargetOnly]
            · simp [P_tgt, SignalPqxdh.isGameQueryOfKind, bhQueryKind, bhClassifyTarget, bhClassifyTargetOnly]
        have h1 := isQueryBoundP_congr_pred_atomic hTgtEq
          (isQueryBoundP_cliAdapterHandleTbl_kiPred decT encT isRoKi s t)
        by_cases hs : P_src 1 (.inr t)
        · have hs' : bhClassifyGameOnly isRoKi (fun _ => false) (fun _ => false) t = true := hSrcEq.mp hs
          simpa [hs, hs'] using h1
        · have hs' : ¬ (bhClassifyGameOnly isRoKi (fun _ => false) (fun _ => false) t = true) := mt hSrcEq.mpr hs
          simpa [hs, hs'] using h1
      · omega
  have hsim := simulateQ_run_stateT_of_step_le_atomic hstep (hA () i)
  have hinit :
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).init.eval
        (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP (P_tgt i) 0 :=
    isQueryBoundP_pure (P_tgt i) _ 0
  have hfin : ∀ s' b,
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).finish.eval
        (Env.cons s' (Env.cons b Env.nil))).IsQueryBoundP (P_tgt i) 0 :=
    fun _ _ => isQueryBoundP_pure (P_tgt i) _ 0
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

/-- Unconditional `CliAdapterCostBounded` witness for `cliToModelAdapterProgTblAtomic`. -/
theorem gRedBounded_cliToModelAdapterProgTblAtomic_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    CliAdapterCostBounded decT encT b qStart qDR
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT) := by
  unfold CliAdapterCostBounded
  refine ⟨?_, ?_, cliAdapterForwardsKinds_cliToModelAdapterProgTblAtomic decT encT _⟩
  · refine gRedBounded_of_bounds
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT)
      (fun _ => 1) (fun _ => 0) (b.q_total + qStart + qDR) (b.q_total + qStart + qDR)
      (bhAdapterCostBudget S b qStart qDR ℓ) ?_ ?_ ?_
      (atomicAdapterOps_sizeHonest ℓ decT encT)
      (atomicBaseSamplers_sizeHonest ℓ Pt)
    · rw [cliToModelAdapterProgTblAtomic_totalCost_eq]
      exact totalCost_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget decT encT b qStart qDR
    · rw [cliToModelAdapterProgTblAtomic_size_eq]
      exact size_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget decT encT b qStart qDR
    · rw [cliToModelAdapterProgTblAtomic_totalQueries_eq]
      exact totalQueries_cliToModelAdapterProgTblRo_le decT encT (b.q_total + qStart + qDR)
  · exact mapCostedReduction_gRedCostByKind
      (adapterOpsHom ℓ decT encT) (adapterIfaceHom S ℓ Pt) (adapterCodecHom S ℓ Pt)
      (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)
      (fun _ => rfl) (fun _ => rfl)
      (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT)
      (toAtomicVal_surjective ℓ Pt _)
      ⟨costBoundedByKind_cliToModelAdapterProgTblRo_bhAdapterCostBudgetByKind decT encT b qStart qDR,
       totalQueries_cliToModelAdapterProgTblRo_le decT encT _⟩

private theorem isQueryBoundP_cliToModelAdapterProgTbl_kiPred
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (A : CliGameAdversary S ℓ (BitVec 512)) (n : ℕ)
    (h : A.run.IsQueryBoundP
      (fun q => bhClassifyComposed pKi (fun _ => false) (fun _ => false) q = true) n) :
    ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval
      (fun _ => cliGameAdversaryReassoc A) ()).IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n := by
  let P_tgt : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain → Prop :=
    fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true
  have hAdv := isQueryBoundP_bhAdvRun pKi (fun _ => false) (fun _ => false) A n h
  have hstep : ∀ (q : (unifSpec + bhGameSpec S ℓ (BitVec 512)).Domain)
      (s : (cliAdapterTblStateTy S ℓ).denote),
      (((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).impl q).run s).IsQueryBoundP
        P_tgt (if bhClassifyGame pKi (fun _ => false) (fun _ => false) q = true then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      show ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterIface S ℓ).fwdU m >>= fun a => pure (a, s)).IsQueryBoundP P_tgt 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        ((isQueryBoundP_query_iff (spec := unifSpec + bhTargetGameSpec S ℓ (BitVec 512))
          P_tgt (Sum.inl m) 0).2 (by simp [P_tgt, bhClassifyTarget]))
        (fun a _ => isQueryBoundP_pure P_tgt (a, s) 0)
    | inr t =>
      show ((cliAdapterHandleTbl decT encT S ℓ).eval
          (.cons s (.cons ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).qenc t) .nil)) >>=
          fun p => pure ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).rdec t p.1, p.2)).IsQueryBoundP
        P_tgt (if bhClassifyGameOnly pKi (fun _ => false) (fun _ => false) t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_cliAdapterHandleTbl_kiPred decT encT pKi s t)
        (fun p _ => isQueryBoundP_pure P_tgt
          ((Computational.Proofs.E2E.Dsl.CliAdapterCosted.e2eBhAdapterCodec S ℓ).rdec t p.1, p.2) 0)
  have hsim := simulateQ_run_stateT_of_step_le_atomic hstep hAdv
  have hinit :
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).init.eval
        (Env.cons (t := .unit) () Env.nil)).IsQueryBoundP P_tgt 0 :=
    isQueryBoundP_pure P_tgt _ 0
  have hfin : ∀ s' b,
      ((cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).finish.eval
        (Env.cons s' (Env.cons b Env.nil))).IsQueryBoundP P_tgt 0 :=
    fun _ _ => isQueryBoundP_pure P_tgt _ 0
  unfold CostedReduction.eval
  exact (isQueryBoundP_bind hinit
    (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind (hsim s)
        (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

/-- Per-instance `IsQueryBoundP` transfer for `cliToModelAdapterProgTblAtomic`. -/
theorem cliToModelAdapterProgTblAtomic_perInstanceQueryBounds
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512))
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ) (qs : ℕ → ℕ)
    (hA : CliGameAdversaryPerInstanceBounded A b qStart qs) :
    let B_A :=
      (cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval
        (fun _ => cliGameAdversaryReassoc A) ()
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart ∧
    B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
      (∑ k ∈ Finset.range qStart, qs k) ∧
    (∀ k < qStart, B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun i => i == k) q = true)
      (qs k)) := by
  dsimp only
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  exact cliToModelAdapterProgTbl_perInstanceQueryBounds decT encT A b qStart qs hA

/-- Exact `ProbComp (Bool × List (BitVec 512))` equivalence between
`cliToModelAdapterProgTblAtomic` and `L_bh` inside `cliE2EExpWithKiCoinLogged` under
`WellFormedPrimitivesδ P`. -/
theorem cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTblAtomic_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep decT encT
        ((cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) =
      cliE2EExpWithKiCoinLogged true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()) := by
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  exact cliE2EExpWithKiCoinLogged_cliToModelAdapterProgTbl_eq_L_bh S P hP C K ℓ qep decT encT A

/-- Exact `boolBias` equivalence between `cliToModelAdapterProgTblAtomic` and `L_bh` inside
`cliE2EExpWithKi` under `WellFormedPrimitivesδ P`. -/
theorem boolBias_cliE2EExpWithKi_cliToModelAdapterProgTblAtomic_eq_L_bh
    (S : SignalPqxdh.Setup) (P : SignalPqxdh.Primitives)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (C : Crypto) (K : MlKem) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((cliToModelAdapterProgTblAtomic (S := S) (ℓ := ℓ) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias =
      (evalDist (cliE2EExpWithKi true S P (SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P) C K ℓ qep
        decT encT
        ((L_bh (S := S) (ℓ := ℓ) (PQC := BitVec 512) decT encT).eval
          (fun _ => cliGameAdversaryReassoc A) ()))).boolBias := by
  rw [cliToModelAdapterProgTblAtomic_eval_eq]
  exact boolBias_cliE2EExpWithKi_cliToModelAdapterProgTbl_eq_L_bh S P hP C K ℓ qep decT encT A

end Computational.Proofs.E2E.Dsl.AtomicLift
