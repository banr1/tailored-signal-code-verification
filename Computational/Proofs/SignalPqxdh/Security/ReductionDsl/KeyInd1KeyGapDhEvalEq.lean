/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhGrow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEvalEq
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence for `fgKeyInd1KeyGapDhProg`

**Checked by Lean.** Proves that `(fgKeyInd1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)`
equals the shallow reduction `(fgKeyInd1KeyGapDhAdv4 S b A).run U V` for every bounded `KeyInd`
adversary `A`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.FgGapDh.Ik SignalPqxdh.Security.FgGapDh.Opk
open SignalPqxdh.Security.FgGapDh1Key
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

/-! ## Evaluation of `renameExpr` and `renameComp` -/

/-- Pulls back an environment along a variable renaming `ρ : Ren Γ Δ`. -/
def pullEnv : {Γ : List PT} → {Δ : List PT} → Ren Γ Δ → Env Δ → Env Γ
  | [], _, _, _ => .nil
  | _ :: _, _, ρ, env => .cons (env.get (ρ .zero)) (pullEnv (fun x => ρ (.succ x)) env)

@[simp] theorem pullEnv_get :
    ∀ {Γ Δ : List PT} {τ : PT} (ρ : Ren Γ Δ) (env : Env Δ) (x : Var Γ τ),
      (pullEnv ρ env).get x = env.get (ρ x)
  | _ :: _, _, _, _, _, .zero => rfl
  | _ :: _, _, _, ρ, env, .succ x => pullEnv_get (fun y => ρ (.succ y)) env x

theorem pullEnv_succ :
    ∀ {Γ Δ : List PT} {σ : PT} (ρ : Ren Γ Δ) (x : σ.denote) (env : Env Δ),
      pullEnv (fun {τ} (v : Var Γ τ) => Var.succ (u := σ) (ρ v)) (.cons x env) = pullEnv ρ env
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, ρ, x, env => congrArg (Env.cons _) (pullEnv_succ (fun v => ρ (.succ v)) x env)

@[simp] theorem pullEnv_liftRen {Γ Δ : List PT} {σ : PT}
    (ρ : Ren Γ Δ) (x : σ.denote) (env : Env Δ) :
    pullEnv (liftRen ρ) (.cons x env) = .cons x (pullEnv ρ env) :=
  congrArg (Env.cons x) (pullEnv_succ ρ x env)

@[simp] theorem pullEnv_twoVarRen {Δ : List PT} {τ₁ τ₂ : PT}
    (v₁ : Var Δ τ₁) (v₂ : Var Δ τ₂) (env : Env Δ) :
    pullEnv (twoVarRen v₁ v₂) env = .cons (env.get v₁) (.cons (env.get v₂) .nil) := rfl

@[simp] theorem renameExpr_eval :
    ∀ {Γ Δ : List PT} {t : PT} (ρ : Ren Γ Δ) (e : Expr pqxdhOps Γ t) (env : Env Δ),
      (renameExpr ρ e).eval env = e.eval (pullEnv ρ env)
  | _, _, _, ρ, .var x, env => (pullEnv_get ρ env x).symm
  | _, _, _, _, .unit, _ => rfl
  | _, _, _, _, .bool _, _ => rfl
  | _, _, _, _, .nat _, _ => rfl
  | _, _, _, ρ, .add a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .sub a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .mulK _ a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .divK _ a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .modK _ a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .lt a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .eqN a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .not a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .and a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .ite c a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ c env,
      renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .pair a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .fst a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .snd a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .inl a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .inr a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, _, .none, _ => rfl
  | _, _, _, ρ, .some a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .caseOpt e n s, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ e env]
    cases e.eval (pullEnv ρ env) with
    | none => exact renameExpr_eval ρ n env
    | some x => exact (renameExpr_eval (liftRen ρ) s (.cons x env)).trans (by rw [pullEnv_liftRen])
  | _, _, _, ρ, .caseSum e l r, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ e env]
    cases e.eval (pullEnv ρ env) with
    | inl x => exact (renameExpr_eval (liftRen ρ) l (.cons x env)).trans (by rw [pullEnv_liftRen])
    | inr y => exact (renameExpr_eval (liftRen ρ) r (.cons y env)).trans (by rw [pullEnv_liftRen])
  | _, _, _, ρ, .letE e b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ e env,
      renameExpr_eval (liftRen ρ) b (.cons (e.eval (pullEnv ρ env)) env), pullEnv_liftRen]
  | _, _, _, ρ, .op _ a, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, ρ, .cons x l, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ x env, renameExpr_eval ρ l env]
  | _, _, _, ρ, .len l, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ l env]
  | _, _, _, ρ, .take n l, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ n env, renameExpr_eval ρ l env]
  | _, _, _, ρ, .appendL _ a b, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env, renameExpr_eval ρ b env]
  | _, _, _, ρ, .findB K l p, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ l env]
    have hfn : (fun x => (renameExpr (liftRen ρ) p).eval (.cons x env)) =
        (fun x => p.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameExpr_eval (liftRen ρ) p (.cons x env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .anyB K l p, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ l env]
    have hfn : (fun x => (renameExpr (liftRen ρ) p).eval (.cons x env)) =
        (fun x => p.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameExpr_eval (liftRen ρ) p (.cons x env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .mapB K l f, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ l env]
    have hfn : (fun x => (renameExpr (liftRen ρ) f).eval (.cons x env)) =
        (fun x => f.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameExpr_eval (liftRen ρ) f (.cons x env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .foldrB K l z f, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ l env, renameExpr_eval ρ z env]
    have hfn : (fun x acc => (renameExpr (liftRen (liftRen ρ)) f).eval (.cons x (.cons acc env))) =
        (fun x acc => f.eval (.cons x (.cons acc (pullEnv ρ env)))) := by
      funext x acc
      rw [renameExpr_eval (liftRen (liftRen ρ)) f (.cons x (.cons acc env)),
        pullEnv_liftRen, pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .tconst a, env => by
    funext i; simp only [renameExpr, Expr.eval, renameExpr_eval ρ a env]
  | _, _, _, ρ, .tget m i, env => by
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ m env, renameExpr_eval ρ i env]
  | _, _, _, ρ, .tset m i a, env => by
    funext j
    simp only [renameExpr, Expr.eval, renameExpr_eval ρ m env,
      renameExpr_eval ρ i env, renameExpr_eval ρ a env]

@[simp] theorem renameComp_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} :
    ∀ {Γ Δ : List PT} {t : PT} (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ t) (env : Env Δ),
      (renameComp ρ c).eval env = c.eval (pullEnv ρ env)
  | _, _, _, ρ, .ret e, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
  | _, _, _, ρ, .bind c k, env => by
    simp only [renameComp, Comp.eval, renameComp_eval ρ c env]
    congr 1; funext x
    rw [renameComp_eval (liftRen ρ) k (.cons x env), pullEnv_liftRen]
  | _, _, _, ρ, .ite b c d, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    cases b.eval (pullEnv ρ env) <;> simp [renameComp_eval]
  | _, _, _, ρ, .caseOpt e n s, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    cases e.eval (pullEnv ρ env) with
    | none => exact renameComp_eval ρ n env
    | some x => exact (renameComp_eval (liftRen ρ) s (.cons x env)).trans (by rw [pullEnv_liftRen])
  | _, _, _, ρ, .caseSum e l r, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    cases e.eval (pullEnv ρ env) with
    | inl x => exact (renameComp_eval (liftRen ρ) l (.cons x env)).trans (by rw [pullEnv_liftRen])
    | inr y => exact (renameComp_eval (liftRen ρ) r (.cons y env)).trans (by rw [pullEnv_liftRen])
  | _, _, _, ρ, .sample s e, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
  | _, _, _, ρ, .query g e, env => by
    dsimp only [renameComp, Comp.eval]
    rw [renameExpr_eval ρ e env]
  | _, _, _, ρ, .iter n e body, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    have hfn : (fun a => (renameComp (liftRen ρ) body).eval (.cons a env)) =
        (fun a => body.eval (.cons a (pullEnv ρ env))) := by
      funext a; rw [renameComp_eval (liftRen ρ) body (.cons a env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .findM K l p, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    have hfn : (fun x => (renameComp (liftRen ρ) p).eval (.cons x env)) =
        (fun x => p.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameComp_eval (liftRen ρ) p (.cons x env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .anyM K l p, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    have hfn : (fun x => (renameComp (liftRen ρ) p).eval (.cons x env)) =
        (fun x => p.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameComp_eval (liftRen ρ) p (.cons x env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .mapM K l f, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    have hfn : (fun x => (renameComp (liftRen ρ) f).eval (.cons x env)) =
        (fun x => f.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameComp_eval (liftRen ρ) f (.cons x env), pullEnv_liftRen]
    rw [hfn]
  | _, _, _, ρ, .consumeFirstM K l p mk, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval, pullEnv_liftRen]
    have hfn1 : (fun x => (renameComp (liftRen ρ) p).eval (.cons x env)) =
        (fun x => p.eval (.cons x (pullEnv ρ env))) := by
      funext x; rw [renameComp_eval (liftRen ρ) p (.cons x env), pullEnv_liftRen]
    rw [hfn1]
  | _, _, _, ρ, .foldM K l z f, env => by
    simp only [renameComp, Comp.eval, renameExpr_eval]
    have hfn : (fun x acc => (renameComp (liftRen (liftRen ρ)) f).eval (.cons x (.cons acc env))) =
        (fun x acc => f.eval (.cons x (.cons acc (pullEnv ρ env)))) := by
      funext x acc
      rw [renameComp_eval (liftRen (liftRen ρ)) f (.cons x (.cons acc env)),
        pullEnv_liftRen, pullEnv_liftRen]
    rw [hfn]

/-! ## `liftGdhToSign` Homomorphism and `liftGdhComp_eval` -/

@[simp] theorem liftGdhToSign_pure {α : Type} (a : α) :
    liftGdhToSign (Pure.pure a) = Pure.pure a := rfl

@[simp] theorem liftGdhToSign_bind {α β : Type}
    (m : OracleComp GdhSimSpec α) (k : α → OracleComp GdhSimSpec β) :
    liftGdhToSign (m >>= k) =
      liftGdhToSign m >>= fun a => liftGdhToSign (k a) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    rcases q with bq | dq
    · change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u >>= k)) =
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u)) >>= fun a => liftGdhToSign (k a)
      rw [bind_assoc]
      congr 1; funext u; exact ih u
    · change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u >>= k)) =
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u)) >>= fun a => liftGdhToSign (k a)
      rw [bind_assoc]
      congr 1; funext u; exact ih u

@[simp] theorem liftGdhToSign_map {α β : Type}
    (f : α → β) (m : OracleComp GdhSimSpec α) :
    liftGdhToSign (f <$> m) = f <$> liftGdhToSign m := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, liftGdhToSign_bind]
  rfl

@[simp] theorem liftGdhToSign_query_inl (bq : ℕ ⊕ PrimQuery) :
    liftGdhToSign (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl bq))) =
      liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) := by
  change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>= pure) = _
  exact bind_pure _

@[simp] theorem liftGdhToSign_query_inr (dq : DdhQuery) :
    liftGdhToSign (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inr dq))) =
      liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) := by
  change (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>= pure) = _
  exact bind_pure _

theorem pqSigAndDdhIface_liftP_eq {α : Type} (p : ProbComp α) :
    pqSigAndDdhIface.liftP p = liftGdhToSign (pqGapDhIface.liftP p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    simp only [Iface.liftP, simulateQ_query_bind, liftGdhToSign_bind]
    congr 1; funext u; exact ih u

theorem liftGdhToSign_findML {α : Type} (p : α → OracleComp GdhSimSpec Bool) :
    ∀ (L : List α),
      liftGdhToSign (findML p L) = findML (fun x => liftGdhToSign (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [findML, liftGdhToSign_bind]
    congr 1; funext b; cases b
    · exact liftGdhToSign_findML p xs
    · rfl

theorem liftGdhToSign_anyML {α : Type} (p : α → OracleComp GdhSimSpec Bool) :
    ∀ (L : List α),
      liftGdhToSign (anyML p L) = anyML (fun x => liftGdhToSign (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [anyML, liftGdhToSign_bind]
    congr 1; funext b; cases b
    · exact liftGdhToSign_anyML p xs
    · rfl

theorem liftGdhToSign_mapML {α β : Type} (f : α → OracleComp GdhSimSpec β) :
    ∀ (L : List α),
      liftGdhToSign (mapML f L) = mapML (fun x => liftGdhToSign (f x)) L
  | [] => rfl
  | x :: xs => by
    simp only [mapML, liftGdhToSign_bind, liftGdhToSign_pure, liftGdhToSign_mapML f xs]

theorem liftGdhToSign_consumeFirstML {α : Type}
    (p : α → OracleComp GdhSimSpec Bool) (m : α → α) :
    ∀ (L : List α),
      liftGdhToSign (consumeFirstML p m L) =
        consumeFirstML (fun x => liftGdhToSign (p x)) m L
  | [] => rfl
  | x :: xs => by
    simp only [consumeFirstML, liftGdhToSign_bind]
    congr 1; funext b; cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, liftGdhToSign_bind,
        liftGdhToSign_consumeFirstML p m xs, liftGdhToSign_pure]
    · rfl

theorem liftGdhToSign_foldML {α β : Type} (f : α → β → OracleComp GdhSimSpec β) :
    ∀ (init : β) (L : List α),
      liftGdhToSign (foldML f init L) =
        foldML (fun x acc => liftGdhToSign (f x acc)) init L
  | _, [] => rfl
  | init, x :: xs => by
    simp only [foldML, liftGdhToSign_bind]
    congr 1; funext b'; exact liftGdhToSign_foldML f b' xs

theorem liftGdhToSign_iterM {α : Type} (f : α → OracleComp GdhSimSpec α) :
    ∀ (n : ℕ) (a : α),
      liftGdhToSign (iterM f n a) = iterM (fun x => liftGdhToSign (f x)) n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, liftGdhToSign_bind]
    congr 1; funext a'; exact liftGdhToSign_iterM f n a'

@[simp] theorem liftGdhComp_eval {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) (env : Env Γ) :
    (liftGdhComp c).eval env = liftGdhToSign (c.eval env) := by
  induction c with
  | ret _ => rfl
  | bind c k ihc ihk =>
    simp only [liftGdhComp, Comp.eval, ihc env, liftGdhToSign_bind]
    congr 1; funext x; exact ihk (.cons x env)
  | ite b c d ihc ihd =>
    simp only [liftGdhComp, Comp.eval]
    cases b.eval env <;> simp [ihc env, ihd env]
  | caseOpt e n s ihn ihs =>
    simp only [liftGdhComp, Comp.eval]
    cases e.eval env with
    | none => exact ihn env
    | some x => exact ihs (.cons x env)
  | caseSum e l r ihl ihr =>
    simp only [liftGdhComp, Comp.eval]
    cases e.eval env with
    | inl x => exact ihl (.cons x env)
    | inr y => exact ihr (.cons y env)
  | sample s e =>
    simp only [liftGdhComp, Comp.eval, pqSigAndDdhIface_liftP_eq]
    rfl
  | query g e =>
    cases g with
    | inl t =>
      simp only [liftGdhComp, Comp.eval, pqSigAndDdhIface, pqGapDhIface, pqChalIface,
        liftGdhToSign_map]
      rw [liftGdhToSign_query_inl]; rfl
    | inr u =>
      have hu : u = () := rfl
      subst hu
      simp only [liftGdhComp, Comp.eval, pqSigAndDdhIface, pqGapDhIface, pqChalIface,
        sigAndDdhOracle, gapDhDdhOracle, liftGdhToSign_map]
      rw [liftGdhToSign_query_inr]; rfl
  | iter n e body ihb =>
    simp only [liftGdhComp, Comp.eval, liftGdhToSign_iterM]
    have hfn : (fun a => (liftGdhComp body).eval (.cons a env)) =
        (fun a => liftGdhToSign (body.eval (.cons a env))) := by
      funext a; exact ihb (.cons a env)
    rw [hfn]
  | findM K l p ihp =>
    simp only [liftGdhComp, Comp.eval, liftGdhToSign_findML]
    have hfn : (fun x => (liftGdhComp p).eval (.cons x env)) =
        (fun x => liftGdhToSign (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hfn]
  | anyM K l p ihp =>
    simp only [liftGdhComp, Comp.eval, liftGdhToSign_anyML]
    have hfn : (fun x => (liftGdhComp p).eval (.cons x env)) =
        (fun x => liftGdhToSign (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hfn]
  | mapM K l f ihf =>
    simp only [liftGdhComp, Comp.eval, liftGdhToSign_mapML]
    have hfn : (fun x => (liftGdhComp f).eval (.cons x env)) =
        (fun x => liftGdhToSign (f.eval (.cons x env))) := by
      funext x; exact ihf (.cons x env)
    rw [hfn]
  | consumeFirstM K l p mk ihp =>
    simp only [liftGdhComp, Comp.eval, liftGdhToSign_consumeFirstML]
    have hfn : (fun x => (liftGdhComp p).eval (.cons x env)) =
        (fun x => liftGdhToSign (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hfn]
  | foldM K l z f ihf =>
    simp only [liftGdhComp, Comp.eval, liftGdhToSign_foldML]
    have hfn : (fun x acc => (liftGdhComp f).eval (.cons x (.cons acc env))) =
        (fun x acc => liftGdhToSign (f.eval (.cons x (.cons acc env)))) := by
      funext x acc; exact ihf (.cons x (.cons acc env))
    rw [hfn]

@[simp] theorem sigChalQ_dsl_eval (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) (env : Env Γ) :
    (sigChalQ_dsl m msg).eval env = sigChalQ (msg.eval env) := by
  simp [sigChalQ_dsl, Comp.eval, pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, sigChalQ]

@[simp] theorem liftGdhComp_gPrim_sBytes32_eval {Γ : List PT} (env : Env Γ) :
    (liftGdhComp (gPrim sBytes32)).eval env = unifGdhSign sampleScalar32 := by
  simp [liftGdhComp_eval, sBytes32_eval, unifGdhSign, unifGdh, sampleScalar32]

@[simp] theorem liftGdhComp_gPrim_sRandom64_eval {Γ : List PT} (env : Env Γ) :
    (liftGdhComp (gPrim sRandom64)).eval env = unifGdhSign sampleRandom64 := by
  simp [liftGdhComp_eval, sRandom64_eval, unifGdhSign, unifGdh]

@[simp] theorem liftGdhComp_gPrim_sBool_eval {Γ : List PT} (env : Env Γ) :
    (liftGdhComp (gPrim sBool)).eval env = unifGdhSign ($ᵗ Bool) := by
  simp [liftGdhComp_eval, sBool_eval, unifGdhSign, unifGdh]

@[simp] theorem liftGdhComp_gPrim_sIndex_eval (N : ℕ) {Γ : List PT} (env : Env Γ) :
    (liftGdhComp (gPrim (sIndex N))).eval env = unifGdhSign (FgGapDh.sampleIndexRange N) := by
  simp only [liftGdhComp_eval, gPrim_eval, sIndex_eval, unifGdhSign, unifGdh,
    FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq]

private theorem liftGdhToSign_embedPrim_primQ (op : PrimQuery) :
    liftGdhToSign (_root_.SignalPqxdh.Security.embedPrim (spec := gapDhOracleSpec)
      (_root_.SignalPqxdh.Security.primQ op)) = primGdhSignQ op := by
  have h1 : _root_.SignalPqxdh.Security.embedPrim (spec := gapDhOracleSpec)
      (_root_.SignalPqxdh.Security.primQ op) =
      liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inr op))) := by
    change (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inr op))) >>= pure) = _
    exact bind_pure _
  rw [h1, liftGdhToSign_query_inl]
  rfl

@[simp] theorem liftGdhComp_gPrim_qX25519Base_eval {Γ : List PT}
    (e : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (liftGdhComp (gPrim (qX25519Base e))).eval env = primGdhSignQ (.x25519Base (e.eval env)) := by
  simp only [liftGdhComp_eval, gPrim_eval, qX25519Base_eval]
  exact liftGdhToSign_embedPrim_primQ _

@[simp] theorem liftGdhComp_gPrim_qKemKeyGen_eval {Γ : List PT}
    (e : Expr pqxdhOps Γ (B 64)) (env : Env Γ) :
    (liftGdhComp (gPrim (qKemKeyGen e))).eval env = primGdhSignQ (.kemKeyGen (e.eval env)) := by
  simp only [liftGdhComp_eval, gPrim_eval, qKemKeyGen_eval]
  exact liftGdhToSign_embedPrim_primQ _

/-! ## One-Key Handler and Extractor Dispatch -/

def encGdh1KeyRS {S : Setup} (pa : paramsTy.denote)
    (p : KeyIndResponse × FgKeyInd1KeySimState S) :
    (Ty.prod keyIndRespTy gdh1KeyStateTy).denote :=
  (keyIndRespToVal p.1, sim1KeyStateToVal pa p.2)

theorem callGdhHandle_eval {S : Setup} (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (qV : Var Δ keyIndQueryTy) (env : Env Δ)
    (pa : paramsTy.denote) (st : FgKeyInd1KeySimState S) (q : KeyIndQuery S)
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (hst : env.get st1 = sim1KeyStateToVal pa st)
    (hq : env.get qV = keyIndQueryToVal q)
    (hGdh : (gdhHandle S K).eval (.cons (pa, simStateToVal st.sim) (.cons (keyIndQueryToVal q) .nil)) =
      encGdhRS pa <$> f st.sim) :
    (callGdhHandle S K st1 qV).eval env =
      encGdh1KeyRS pa <$> liftSimStep1Key f st := by
  unfold callGdhHandle liftSimStep1Key
  simp only [letV_eval, bindV, Comp.eval, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
    Env.get_zero', Env.get_succ', renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval,
    hst, hq, sim1KeyStateToVal, hGdh,
    map_eq_bind_pure_comp, liftGdhToSign_bind, liftGdhToSign_pure,
    bind_assoc, Function.comp_def, pure_bind, encGdhRS, encGdh1KeyRS]

theorem initPrin1KeyB_eval {S : Setup} (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (uV : Var Γ₂ .nat) (env : Env Δ)
    (pa : paramsTy.denote) (st : FgKeyInd1KeySimState S) (u : Fin S.N_id)
    (hst : env.get (Ext.wk st1) = sim1KeyStateToVal pa st)
    (hu : env.get (Ext.wk uV) = u.val)
    (hB : FgSimListsBounded st.sim K) :
    (initPrin1KeyB K st1 uV).eval env =
      encGdh1KeyRS pa <$> fgInitPrin1KeyGdh pa.2.2.2.1 pa.2.2.2.2.1 pa.2.2.1 u st := by
  unfold initPrin1KeyB fgInitPrin1KeyGdh
  simp only [letV_eval, bindV, Comp.eval, liftGdhComp_gPrim_sBytes32_eval,
    liftGdhComp_gPrim_qX25519Base_eval]
  gdh_simp [hst, hu, sim1KeyStateToVal, List.take_of_length_le, hB.base_le.principals_le]
  by_cases h : (st.sim.base.principals.any fun x => x.1 == ↑u) = true
  · simp [h, encGdh1KeyRS, sim1KeyStateToVal, keyIndRespToVal, simStateToVal]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine _root_.bind_congr fun sk0 => ?_
    refine _root_.bind_congr fun pk0 => ?_
    simp [encGdh1KeyRS, sim1KeyStateToVal, keyIndRespToVal, simStateToVal,
      keyIndStateToVal, principalEntryToVal]

set_option maxHeartbeats 800000 in
theorem genSpk1KeyB_eval {S : Setup} (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (qV : Var Δ keyIndQueryTy)
    (xV : Var Δ (.prod .nat .nat)) (env : Env Δ)
    (pa : paramsTy.denote) (st : FgKeyInd1KeySimState S)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (hst : env.get st1 = sim1KeyStateToVal pa st)
    (hq : env.get qV = keyIndQueryToVal (.genSPK u j))
    (hx : env.get xV = (u.val, j.val))
    (hB : FgSimListsBounded st.sim K) :
    (genSpk1KeyB S K st1 qV xV).eval env =
      encGdh1KeyRS pa <$>
        fgGenSPK1KeyGdh pa.2.2.2.1 pa.2.2.2.2.1
          pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K pa.1 pa.2.1 u j st := by
  unfold genSpk1KeyB fgGenSPK1KeyGdh
  have hCond : (Expr.and (paPrinFlag (.fst (.fst (v st1))))
      (natEq (.fst (v xV)) (paPrinIdx (.fst (.fst (v st1)))))).eval env =
      (pa.2.2.2.1 && (u.val == pa.2.2.2.2.1)) := by
    simp [paPrinFlag, paPrinIdx, natEq_eval, v, Expr.eval, Ext.refl_wk',
      hst, hx, sim1KeyStateToVal]
  simp only [Comp.eval, hCond]
  by_cases hT : (pa.2.2.2.1 && (u.val == pa.2.2.2.2.1)) = true
  · simp only [hT, ↓reduceIte]
    simp only [letV_eval, bindV, caseOptV, Comp.eval,
      liftGdhComp_gPrim_sBytes32_eval, liftGdhComp_gPrim_sRandom64_eval,
      liftGdhComp_gPrim_qX25519Base_eval, liftGdhComp_gPrim_qKemKeyGen_eval,
      sigChalQ_dsl_eval]
    gdh_simp [hst, hx, sim1KeyStateToVal, min_N_recv_spk_tot u, List.take_of_length_le,
      hB.base_le.principals_le, hB.base_le.spkBundles_le, nat2_beq, FgGapDh.spkBundleFlatIdx]
    by_cases hAny : (st.sim.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
    · simp [hAny, encGdh1KeyRS, sim1KeyStateToVal, keyIndRespToVal, simStateToVal]
    · rcases hf : st.sim.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨idx, uE⟩
      · simp [hAny, hf, encGdh1KeyRS, sim1KeyStateToVal, keyIndRespToVal, simStateToVal]
      · simp only [hAny, hf, Bool.false_eq_true, ↓reduceIte, Option.map_some]
        by_cases hZ : (st.sigBudget == 0) = true
        · simp [hZ, encGdh1KeyRS, sim1KeyStateToVal, keyIndRespToVal, simStateToVal]
        · simp only [hZ, Bool.false_eq_true, ↓reduceIte,
            map_eq_bind_pure_comp, bind_assoc, pure_bind]
          refine _root_.bind_congr fun spkSkRaw => ?_
          refine _root_.bind_congr fun spkPkRaw => ?_
          refine _root_.bind_congr fun spkSig => ?_
          refine _root_.bind_congr fun seed => ?_
          refine _root_.bind_congr fun ⟨pqPk, pqSk⟩ => ?_
          refine _root_.bind_congr fun pqSig => ?_
          simp [encGdh1KeyRS, sim1KeyStateToVal, keyIndRespToVal, simStateToVal,
            keyIndStateToVal, spkBundleEntryToVal, principalEntryToVal]
  · simp only [hT, Bool.false_eq_true, ↓reduceIte]
    have hStep := gdhHandle_eval_step S K pa (.genSPK u j) st.sim hB
    exact callGdhHandle_eval K st1 qV env pa st (.genSPK u j) _ hst hq hStep

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

theorem gdh1KeyHandle_eval_step (S : Setup) (K : Nat) (pa : paramsTy.denote)
    (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) (hB : FgSimListsBounded st.sim K) :
    (gdh1KeyHandle S K).eval (.cons (sim1KeyStateToVal pa st) (.cons (keyIndQueryToVal q) .nil)) =
      encGdh1KeyRS pa <$>
        match q with
        | .initPrin u =>
          fgInitPrin1KeyGdh pa.2.2.2.1 pa.2.2.2.2.1 pa.2.2.1 u st
        | .genSPK u j =>
          fgGenSPK1KeyGdh pa.2.2.2.1 pa.2.2.2.2.1
            pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K pa.1 pa.2.1 u j st
        | .genOPK u j o =>
          liftSimStep1Key
            (if pa.2.2.2.2.2.2.2.2.1 then
               fgGenOPKGdhOpk pa.2.2.2.2.2.2.2.2.2.1 S pa.2.1 u j o
             else
               fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
                 pa.1 pa.2.1 (.genOPK u j o)) st
        | .acceptOPK k j o hdr =>
          liftSimStep1Key
            (if pa.2.2.2.2.2.2.2.2.1 then
               fgRunAcceptOPKGdhOpk S K k j o hdr
             else
               fgRunAcceptOPKGdh S K k j o hdr) st
        | q =>
          liftSimStep1Key
            (fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
              pa.1 pa.2.1 q) st := by
  cases q with
  | initPrin u =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact initPrin1KeyB_eval K _ _ _ pa st u rfl rfl hB
  | corruptIK u =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.corruptIK u) _ rfl rfl
      (gdhHandle_eval_step S K pa (.corruptIK u) st.sim hB)
  | genSPK u j =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact genSpk1KeyB_eval K _ _ _ _ pa st u j rfl rfl rfl hB
  | genOPK u j o =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    have hStep := gdhHandle_eval_step S K pa (.genOPK u j o) st.sim hB
    refine callGdhHandle_eval K _ _ _ pa st (.genOPK u j o) _ rfl rfl ?_
    cases h : pa.2.2.2.2.2.2.2.2.1 <;>
      simp only [h, ↓reduceIte, Bool.false_eq_true] at hStep ⊢ <;>
      exact hStep
  | initiateOPK u i b =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.initiateOPK u i b) _ rfl rfl
      (gdhHandle_eval_step S K pa (.initiateOPK u i b) st.sim hB)
  | initiateNoOPK u i b =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.initiateNoOPK u i b) _ rfl rfl
      (gdhHandle_eval_step S K pa (.initiateNoOPK u i b) st.sim hB)
  | acceptOPK k j o h =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    have hStep := gdhHandle_eval_step S K pa (.acceptOPK k j o h) st.sim hB
    refine callGdhHandle_eval K _ _ _ pa st (.acceptOPK k j o h) _ rfl rfl ?_
    cases h' : pa.2.2.2.2.2.2.2.2.1 <;>
      simp only [h', ↓reduceIte, Bool.false_eq_true] at hStep ⊢ <;>
      exact hStep
  | acceptNoOPK k j l h =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.acceptNoOPK k j l h) _ rfl rfl
      (gdhHandle_eval_step S K pa (.acceptNoOPK k j l h) st.sim hB)
  | testSession sid =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.testSession sid) _ rfl rfl
      (gdhHandle_eval_step S K pa (.testSession sid) st.sim hB)
  | roQuery sec =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.roQuery sec) _ rfl rfl
      (gdhHandle_eval_step S K pa (.roQuery sec) st.sim hB)
  | revealDhSecrets =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st .revealDhSecrets _ rfl rfl
      (gdhHandle_eval_step S K pa .revealDhSecrets st.sim hB)
  | revealSessionKey sid =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.revealSessionKey sid) _ rfl rfl
      (gdhHandle_eval_step S K pa (.revealSessionKey sid) st.sim hB)
  | registerKey sk =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.registerKey sk) _ rfl rfl
      (gdhHandle_eval_step S K pa (.registerKey sk) st.sim hB)
  | revealSpkSk u j =>
    simp only [gdh1KeyHandle, keyIndQueryToVal, keyIndQenc, caseSumV,
      Comp.eval, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.refl_wk']
    exact callGdhHandle_eval K _ _ _ pa st (.revealSpkSk u j) _ rfl rfl
      (gdhHandle_eval_step S K pa (.revealSpkSk u j) st.sim hB)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Env.get Ext.wk
end

def params1KeyIkVal (S : Setup) (tIdx pIdx : Nat) (U V : Bytes) : paramsTy.denote :=
  (V, (U, (U, (true, (pIdx, (false, (tIdx, (S.N_spk_tot, (false, (S.N_opk_tot, 2))))))))))

@[simp] theorem initParams1KeyIk_eval (S : Setup) {Γ : List PT}
    (tIdx pIdx : Expr pqxdhOps Γ .nat) (U V : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (initParams1KeyIk S tIdx pIdx U V).eval env =
      params1KeyIkVal S (tIdx.eval env) (pIdx.eval env) (U.eval env) (V.eval env) := by
  simp [initParams1KeyIk, paMk, params1KeyIkVal, Expr.eval]

theorem gdh1KeyHandle_eval_dh (S : Setup) (K : Nat) (useDh1 : Bool) (tIdx spkIdx : Nat)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S)
    (hB : FgSimListsBounded st.sim K) :
    (gdh1KeyHandle S K).eval
      (.cons (sim1KeyStateToVal (paramsDhVal S useDh1 tIdx spkIdx U V) st)
        (.cons (keyIndQueryToVal q) .nil)) =
      encGdh1KeyRS (paramsDhVal S useDh1 tIdx spkIdx U V) <$>
        fgKeyInd1KeyStep useDh1 tIdx spkIdx S K U V q st := by
  rw [gdh1KeyHandle_eval_step S K (paramsDhVal S useDh1 tIdx spkIdx U V) q st hB]
  cases q <;> rfl

theorem gdh1KeyHandle_eval_ik (S : Setup) (K : Nat) (tIdx pIdx : Nat)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S)
    (hB : FgSimListsBounded st.sim K) :
    (gdh1KeyHandle S K).eval
      (.cons (sim1KeyStateToVal (params1KeyIkVal S tIdx pIdx U V) st)
        (.cons (keyIndQueryToVal q) .nil)) =
      encGdh1KeyRS (params1KeyIkVal S tIdx pIdx U V) <$>
        fgKeyInd1KeyStepIk tIdx pIdx S K U V q st := by
  rw [gdh1KeyHandle_eval_step S K (params1KeyIkVal S tIdx pIdx U V) q st hB]
  cases q <;> rfl

theorem gdh1KeyHandle_eval_opk (S : Setup) (K : Nat) (tIdx oIdx : Nat)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S)
    (hB : FgSimListsBounded st.sim K) :
    (gdh1KeyHandle S K).eval
      (.cons (sim1KeyStateToVal (paramsOpkVal S tIdx oIdx U V) st)
        (.cons (keyIndQueryToVal q) .nil)) =
      encGdh1KeyRS (paramsOpkVal S tIdx oIdx U V) <$>
        fgKeyInd1KeyStepOpk tIdx oIdx S K U V q st := by
  rw [gdh1KeyHandle_eval_step S K (paramsOpkVal S tIdx oIdx U V) q st hB]
  cases q <;> rfl

theorem gdh1KeyFinish_eval_eq (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyInd1KeySimState S) :
    (gdh1KeyFinish S K).eval (.cons (sim1KeyStateToVal pa st) (.cons a .nil)) =
      liftGdhToSign ((gdhFinish S K).eval (.cons (pa, simStateToVal st.sim) (.cons a .nil))) := by
  simp [gdh1KeyFinish, sim1KeyStateToVal, letV_eval, renameComp_eval,
    pullEnv_twoVarRen, liftGdhComp_eval, v, Expr.eval,
    Env.get_zero', Env.get_succ', Ext.refl_wk']

theorem gdh1KeyFinish_eval_mode0 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyInd1KeySimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 0)
    (hPows : st.sim.advKeyPows.length ≤ K) (hB : KeyIndListsBounded st.sim.base K) :
    (gdh1KeyFinish S K).eval (.cons (sim1KeyStateToVal pa st) (.cons a .nil)) =
      liftGdhToSign (extractCdhFromSimState S true K pa.1 pa.2.1 st.sim) := by
  rw [gdh1KeyFinish_eval_eq, gdhFinish_eval_mode0 S K a pa st.sim hmode hPows hB]

theorem gdh1KeyFinish_eval_mode1 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyInd1KeySimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 1) :
    (gdh1KeyFinish S K).eval (.cons (sim1KeyStateToVal pa st) (.cons a .nil)) =
      liftGdhToSign (extractCdhFromSimState S false K pa.1 pa.2.1 st.sim) := by
  rw [gdh1KeyFinish_eval_eq, gdhFinish_eval_mode1 S K a pa st.sim hmode]

theorem gdh1KeyFinish_eval_mode2 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyInd1KeySimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 2) :
    (gdh1KeyFinish S K).eval (.cons (sim1KeyStateToVal pa st) (.cons a .nil)) =
      liftGdhToSign (extractCdh2FromAdvRoLog K pa.1 pa.2.1 st.sim.advRoLog) := by
  rw [gdh1KeyFinish_eval_eq, gdhFinish_eval_mode2 S K a pa st.sim hmode]

theorem gdh1KeyFinish_eval_mode3 (S : Setup) (K : Nat) (a : Bool) (pa : paramsTy.denote)
    (st : FgKeyInd1KeySimState S) (hmode : pa.2.2.2.2.2.2.2.2.2.2 = 3) :
    (gdh1KeyFinish S K).eval (.cons (sim1KeyStateToVal pa st) (.cons a .nil)) =
      liftGdhToSign (extractCdh4FromAdvRoLog K pa.1 pa.2.1 st.sim.advRoLog) := by
  rw [gdh1KeyFinish_eval_eq, gdhFinish_eval_mode3 S K a pa st.sim hmode]

/-! ## One-Step Growth Bounds -/

theorem mem_support_liftGdhToSign {α : Type} {mx : OracleComp GdhSimSpec α} {x : α}
    (hx : x ∈ support (liftGdhToSign mx)) : x ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    change x ∈ support (pure a : OracleComp GdhSignSimSpec α) at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx ⊢
    exact hx
  | query_bind q r ih =>
    rcases q with bq | dq
    · change x ∈ support
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl bq)) >>=
          fun u => liftGdhToSign (r u)) at hx
      simp only [MonadAttach.mem_support_bind] at hx ⊢
      obtain ⟨u, _, hu⟩ := hx
      exact ⟨u, mem_support_query _ _, ih u hu⟩
    · change x ∈ support
        (liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => liftGdhToSign (r u)) at hx
      simp only [MonadAttach.mem_support_bind] at hx ⊢
      obtain ⟨u, _, hu⟩ := hx
      exact ⟨u, mem_support_query _ _, ih u hu⟩

theorem liftSimStep1Key_grow {S : Setup}
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (st : FgKeyInd1KeySimState S)
    (hf : ∀ y ∈ support (f st.sim), Grow st.sim y.2) :
    ∀ x ∈ support (liftSimStep1Key f st), Grow st.sim x.2.sim := by
  intro x hx
  unfold liftSimStep1Key at hx
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨resp, sim'⟩, hy, rfl⟩
  exact hf (resp, sim') (mem_support_liftGdhToSign hy)

theorem fgInitPrin1KeyGdh_grow {S : Setup} (prinFlag : Bool) (prinIdx : ℕ) (Up : Bytes)
    (u : Fin S.N_id) (st : FgKeyInd1KeySimState S) :
    ∀ x ∈ support (fgInitPrin1KeyGdh prinFlag prinIdx Up u st), Grow st.sim x.2.sim := by
  show AllOut (fgInitPrin1KeyGdh prinFlag prinIdx Up u st) (fun x => Grow st.sim x.2.sim)
  unfold fgInitPrin1KeyGdh
  grow_loop
  all_goals grow_leaf

theorem fgGenSPK1KeyGdh_grow {S : Setup} (prinFlag : Bool) (prinIdx : ℕ)
    (useDh1 : Bool) (targetIdx targetSpkIdx K : ℕ) (U V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgKeyInd1KeySimState S) :
    ∀ x ∈ support
        (fgGenSPK1KeyGdh prinFlag prinIdx useDh1 targetIdx targetSpkIdx S K U V u j st),
      Grow st.sim x.2.sim := by
  unfold fgGenSPK1KeyGdh
  by_cases hT : (prinFlag && (u.val == prinIdx)) = true
  · simp only [hT, ↓reduceIte]
    show AllOut _ (fun (x : KeyIndResponse × FgKeyInd1KeySimState S) => Grow st.sim x.2.sim)
    grow_loop
    all_goals grow_leaf
  · simp only [hT, Bool.false_eq_true, ↓reduceIte]
    exact liftSimStep1Key_grow _ st (fgKeyIndStep_grow useDh1 targetIdx targetSpkIdx K U V
      (.genSPK u j) st.sim)

theorem fgKeyInd1KeyStep_grow {S : Setup} (useDh1 : Bool) (t s K : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    ∀ x ∈ support (fgKeyInd1KeyStep useDh1 t s S K U V q st), Grow st.sim x.2.sim := by
  unfold fgKeyInd1KeyStep
  split
  · exact fgInitPrin1KeyGdh_grow useDh1 t U _ st
  · exact fgGenSPK1KeyGdh_grow useDh1 t useDh1 t s K U V _ _ st
  · exact liftSimStep1Key_grow _ st (fgKeyIndStep_grow useDh1 t s K U V _ st.sim)

theorem fgKeyInd1KeyStepIk_grow {S : Setup} (t p K : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    ∀ x ∈ support (fgKeyInd1KeyStepIk t p S K U V q st), Grow st.sim x.2.sim := by
  unfold fgKeyInd1KeyStepIk
  split
  · exact fgInitPrin1KeyGdh_grow true p U _ st
  · exact fgGenSPK1KeyGdh_grow true p false t (FgGapDh.Ik.noSpkIdx S) K V U _ _ st
  · exact liftSimStep1Key_grow _ st
      (fgKeyIndStep_grow false t (FgGapDh.Ik.noSpkIdx S) K V U _ st.sim)

theorem fgKeyInd1KeyStepOpk_grow {S : Setup} (t o K : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyInd1KeySimState S) :
    ∀ x ∈ support (fgKeyInd1KeyStepOpk t o S K U V q st), Grow st.sim x.2.sim := by
  unfold fgKeyInd1KeyStepOpk
  split
  · exact fgInitPrin1KeyGdh_grow false S.N_id U _ st
  · exact fgGenSPK1KeyGdh_grow false S.N_id false t (FgGapDh.Opk.noSpkIdx S) K U V _ _ st
  · exact liftSimStep1Key_grow _ st (fgKeyIndStepOpk_grow t o K U V _ st.sim)

/-! ## Runner Bridge and Evaluation Equivalence -/

/-- Runner bridge for `ReductionDsl.handlerImpl` over `pqSigAndDdhIface`. -/
theorem simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {C : GameCodec pqSig GSpec}
    {σ : PT} {σS α β : Type}
    (h : Comp pqxdhOps pqSigAndDdhIface [σ, C.Q] (.prod C.R σ))
    (stepS : (q : ιI) → σS → OracleComp GdhSignSimSpec (GSpec.Range q × σS))
    (enc : σS → σ.denote) (InvS : Nat → σS → Prop)
    (hMono : ∀ k s, InvS (k + 1) s → InvS k s)
    (hStep : ∀ k q s, InvS (k + 1) s →
      (do let p ← h.eval (.cons (enc s) (.cons (C.qenc q) .nil))
          pure (C.rdec q p.1, p.2)) =
        (fun x => (x.1, enc x.2)) <$> stepS q s)
    (hPres : ∀ k q s, InvS (k + 1) s → ∀ x ∈ support (stepS q s), InvS k x.2)
    (f : α × σ.denote → OracleComp GdhSignSimSpec β)
    (g : α × σS → OracleComp GdhSignSimSpec β)
    (hfg : ∀ a s, InvS 0 s → f (a, enc s) = g (a, s))
    (mx : OracleComp (unifSpec + GSpec) α) (qTotal : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) qTotal)
    (s : σS) (hs : InvS qTotal s) :
    ((simulateQ (handlerImpl (C := C) h) mx).run (enc s) >>= f) =
      (runWithGdhSignStep stepS mx s >>= g) := by
  induction mx using OracleComp.inductionOn generalizing qTotal s with
  | pure a =>
    have h0 : InvS 0 s := by
      clear hMx
      induction qTotal with
      | zero => exact hs
      | succ n ih => exact ih (hMono n s hs)
    simp only [simulateQ_pure, StateT.run_pure, runWithGdhSignStep, OracleComp.construct_pure,
      pure_bind]
    exact hfg a s h0
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hMx
    rcases q with uq | gq
    · rcases hMx with ⟨_, hCont⟩
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte] at hCont
      rw [simulateQ_query_bind, StateT.run_bind]
      change (((pqSigAndDdhIface.fwdU uq >>= fun u => pure (u, enc s)) >>= fun x =>
          (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) >>= f) =
        ((liftM (OracleSpec.query (spec := GdhSignSimSpec) (Sum.inl (Sum.inl uq))) >>= fun u =>
          runWithGdhSignStep stepS (k u) s) >>= g)
      simp only [pqSigAndDdhIface, pqChalIface, bind_assoc, pure_bind]
      exact _root_.bind_congr fun u => ih u qTotal (hCont u) s hs
    · rcases hMx with ⟨hFirst, hCont⟩
      have hPos : 0 < qTotal := by
        rcases hFirst with hAbs | hPos
        · exact absurd rfl hAbs
        · exact hPos
      simp only [Sum.isRight_inr, ↓reduceIte] at hCont
      obtain ⟨n, rfl⟩ : ∃ n, qTotal = n + 1 := ⟨qTotal - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hCont
      rw [simulateQ_query_bind, StateT.run_bind]
      change (((do let p ← h.eval (.cons (enc s) (.cons (C.qenc gq) .nil))
                   pure (C.rdec gq p.1, p.2)) >>= fun x =>
          (simulateQ (handlerImpl (C := C) h) (k x.1)).run x.2) >>= f) =
        ((stepS gq s >>= fun p => runWithGdhSignStep stepS (k p.1) p.2) >>= g)
      rw [hStep n gq s hs]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      refine bind_congr_of_forall_mem_support _ (fun x hx => ?_)
      exact ih x.1 n (hCont x.1) x.2 (hPres n gq s hs x hx)

def runFrom1Key (S : Setup) (K : Nat) (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (x0 : gdh1KeyStateTy.denote) : OracleComp GdhSignSimSpec Bytes := do
  let (b, s') ← (simulateQ (handlerImpl (C := keyIndCodec S) (gdh1KeyHandle S K)) A).run x0
  (gdh1KeyFinish S K).eval (.cons s' (.cons b .nil))

theorem runFrom1Key_eq (S : Setup) (K : Nat) (pa : paramsTy.denote)
    (stepS : (q : KeyIndQuery S) → FgKeyInd1KeySimState S →
      OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeySimState S))
    (hStep : ∀ q st, FgSimListsBounded st.sim K →
      (gdh1KeyHandle S K).eval (.cons (sim1KeyStateToVal pa st) (.cons (keyIndQueryToVal q) .nil)) =
        encGdh1KeyRS pa <$> stepS q st)
    (hGrow : ∀ q st, ∀ x ∈ support (stepS q st), Grow st.sim x.2.sim)
    (ext : FgKeyInd1KeySimState S → OracleComp GdhSignSimSpec Bytes)
    (hFin : ∀ (a : Bool) st, FgSimListsBounded st.sim K →
      (gdh1KeyFinish S K).eval (.cons (sim1KeyStateToVal pa st) (.cons a .nil)) = ext st)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP A (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K) (secb : Bool) :
    runFrom1Key S K A (sim1KeyStateToVal pa (FgKeyInd1KeySimState.empty S secb)) =
      (do
        let (_, stF) ← runWithGdhSignStep stepS A (FgKeyInd1KeySimState.empty S secb)
        ext stF) := by
  unfold runFrom1Key
  refine simulateQ_handlerImpl_bind_eq_runWithGdhSignStep_bind
    (C := keyIndCodec S) (σ := gdh1KeyStateTy) (gdh1KeyHandle S K) stepS
    (sim1KeyStateToVal pa) (fun k st => Inv K k st.sim)
    (fun k st h => Inv.mono K k st.sim h)
    (fun k q st h => ?_)
    (fun k q st h x hx => Inv.of_grow K k st.sim x.2.sim h (hGrow q st x hx))
    (fun p => (gdh1KeyFinish S K).eval (.cons p.2 (.cons p.1 .nil)))
    (fun p => ext p.2)
    (fun a st h => hFin a st (Inv.bnd K 0 st.sim h)) A K hA _
    (Inv.empty S K secb)
  dsimp only [keyIndCodec, keyIndQueryToVal]
  rw [hStep q st (Inv.bnd K (k + 1) st.sim h)]
  simp only [encGdh1KeyRS, keyIndRespToVal, keyIndRdec_keyIndRenc,
    map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

def params1KeyFlatVal (S : Setup) (U V : Bytes) (idx : Nat) : paramsTy.denote :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then
    paramsDhVal S true (idx / S.N_spk_tot) (idx % S.N_spk_tot) U V
  else if idx < nA + nC then
    let r := idx - nA
    paramsDhVal S false (r / S.N_spk_tot) (r % S.N_spk_tot) U V
  else if idx < nA + nC + nB then
    let r := idx - (nA + nC)
    params1KeyIkVal S (r / S.N_id) (r % S.N_id) U V
  else
    let r := idx - (nA + nC + nB)
    paramsOpkVal S (r / S.N_opk_tot) (r % S.N_opk_tot) U V

@[simp] theorem initParams1KeyFlat_eval (S : Setup) {Γ : List PT}
    (U V : Expr pqxdhOps Γ (B 32)) (idx : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (initParams1KeyFlat S U V idx).eval env =
      params1KeyFlatVal S (U.eval env) (V.eval env) (idx.eval env) := by
  simp only [initParams1KeyFlat, params1KeyFlatVal, initParamsDh_eval, initParams1KeyIk_eval,
    initParamsOpk_eval, Expr.eval]
  split_ifs <;> simp_all

theorem fgKeyInd1KeyGapDhProg_eval_runFrom1Key (S : Setup) (K : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyInd1KeyGapDhProg S K).eval (fun _ => A) (U, V) =
      (do
        let idx ← unifGdhSign (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
        let secb ← unifGdhSign ($ᵗ Bool)
        runFrom1Key S K A
          (sim1KeyStateToVal (params1KeyFlatVal S U V idx)
            (FgKeyInd1KeySimState.empty S secb))) := by
  simp only [CostedReduction.eval, fgKeyInd1KeyGapDhProg, initAdv4_1Key, initAdv4_1KeyBase,
    bindV, letV_eval, Comp.eval, liftGdhComp_eval, gPrim_eval,
    sIndex_eval, sBool_eval, initParams1KeyFlat_eval, emptySimE_eval (S := S),
    v, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
    liftGdhToSign_bind, liftGdhToSign_pure, unifGdhSign, unifGdh,
    FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq,
    sim1KeyStateToVal, FgKeyInd1KeySimState.empty,
    bind_assoc, pure_bind]
  rfl

def fgKeyInd1KeyGapDhRunAtFlatComp (S : Setup) (K idx : Nat)
    (A : OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    OracleComp GdhSignSimSpec Bytes :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then do
    let secb ← unifGdhSign ($ᵗ Bool)
    let initSt := FgKeyInd1KeySimState.empty S secb
    let (_, finalSt) ← runWithGdhSignStep
      (fgKeyInd1KeyStep true (idx / S.N_spk_tot) (idx % S.N_spk_tot) S K U V) A initSt
    liftGdhToSign (extractCdhFromSimState S true K U V finalSt.sim)
  else if idx < nA + nC then do
    let r := idx - nA
    let secb ← unifGdhSign ($ᵗ Bool)
    let initSt := FgKeyInd1KeySimState.empty S secb
    let (_, finalSt) ← runWithGdhSignStep
      (fgKeyInd1KeyStep false (r / S.N_spk_tot) (r % S.N_spk_tot) S K U V) A initSt
    liftGdhToSign (extractCdhFromSimState S false K U V finalSt.sim)
  else if idx < nA + nC + nB then do
    let r := idx - (nA + nC)
    let secb ← unifGdhSign ($ᵗ Bool)
    let initSt := FgKeyInd1KeySimState.empty S secb
    let (_, finalSt) ← runWithGdhSignStep
      (fgKeyInd1KeyStepIk (r / S.N_id) (r % S.N_id) S K U V) A initSt
    liftGdhToSign (extractCdh2FromAdvRoLog K V U finalSt.sim.advRoLog)
  else do
    let r := idx - (nA + nC + nB)
    let secb ← unifGdhSign ($ᵗ Bool)
    let initSt := FgKeyInd1KeySimState.empty S secb
    let (_, finalSt) ← runWithGdhSignStep
      (fgKeyInd1KeyStepOpk (r / S.N_opk_tot) (r % S.N_opk_tot) S K U V) A initSt
    liftGdhToSign (extractCdh4FromAdvRoLog K U V finalSt.sim.advRoLog)

/-- Evaluation equivalence for `fgKeyInd1KeyGapDhProg S K` on any adversary making at most `K` game
queries. -/
theorem fgKeyInd1KeyGapDhProg_eval_eq_of_queryBound (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP (A ()) (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K)
    (U V : Bytes) :
    (fgKeyInd1KeyGapDhProg S K).eval A (U, V) =
      (do
        let idx ← unifGdhSign (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
        fgKeyInd1KeyGapDhRunAtFlatComp S K idx (A ()) U V) := by
  have hfun : A = (fun _ => A ()) := funext fun ⟨⟩ => rfl
  rw [hfun, fgKeyInd1KeyGapDhProg_eval_runFrom1Key]
  refine _root_.bind_congr fun idx => ?_
  unfold fgKeyInd1KeyGapDhRunAtFlatComp params1KeyFlatVal
  by_cases h1 : idx < S.N_id * S.N_spk_tot
  · simp only [h1, ↓reduceIte]
    refine _root_.bind_congr fun secb => ?_
    exact runFrom1Key_eq S K _ _
      (fun q st hB => gdh1KeyHandle_eval_dh S K true _ _ U V q st hB)
      (fun q st => fgKeyInd1KeyStep_grow true _ _ K U V q st) _
      (fun a st hB => gdh1KeyFinish_eval_mode0 S K a _ st rfl hB.advKeyPows_le
        hB.base_le)
      (A ()) hA secb
  by_cases h2 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
  · simp only [h1, h2, ↓reduceIte]
    refine _root_.bind_congr fun secb => ?_
    exact runFrom1Key_eq S K _ _
      (fun q st hB => gdh1KeyHandle_eval_dh S K false _ _ U V q st hB)
      (fun q st => fgKeyInd1KeyStep_grow false _ _ K U V q st) _
      (fun a st _ => gdh1KeyFinish_eval_mode1 S K a _ st rfl)
      (A ()) hA secb
  by_cases h3 : idx < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id
  · simp only [h1, h2, h3, ↓reduceIte]
    refine _root_.bind_congr fun secb => ?_
    exact runFrom1Key_eq S K _ _
      (fun q st hB => gdh1KeyHandle_eval_ik S K _ _ U V q st hB)
      (fun q st => fgKeyInd1KeyStepIk_grow _ _ K U V q st) _
      (fun a st _ => gdh1KeyFinish_eval_mode2 S K a _ st rfl)
      (A ()) hA secb
  · simp only [h1, h2, h3, ↓reduceIte]
    refine _root_.bind_congr fun secb => ?_
    exact runFrom1Key_eq S K _ _
      (fun q st hB => gdh1KeyHandle_eval_opk S K _ _ U V q st hB)
      (fun q st => fgKeyInd1KeyStepOpk_grow _ _ K U V q st) _
      (fun a st _ => gdh1KeyFinish_eval_mode3 S K a _ st rfl)
      (A ()) hA secb

/-- `(fgKeyInd1KeyGapDhProg S b.q_total).eval` equals `(fgKeyInd1KeyGapDhAdv4 S b A).run U V` for
every bounded `KeyInd` adversary `A`. -/
theorem fgKeyInd1KeyGapDhProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) :
    (fgKeyInd1KeyGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V) =
      (fgKeyInd1KeyGapDhAdv4 S b A).run U V := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    obtain ⟨_, _, _, h, _⟩ := A.2
    convert h using 1
    funext q; cases q <;> rfl
  rw [fgKeyInd1KeyGapDhProg_eval_eq_of_queryBound S b.q_total (fun _ => A.1.run) hA U V]
  rfl

end SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

namespace SignalPqxdh.Security.ReductionDsl.KeyInd
export SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  fgKeyInd1KeyGapDhProg_eval_eq_of_queryBound
  fgKeyInd1KeyGapDhProg_eval_eq
)
end SignalPqxdh.Security.ReductionDsl.KeyInd
