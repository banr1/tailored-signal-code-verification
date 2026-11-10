/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigProg
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEvalEq
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation Equivalence for `sigKeyInd1KeyProg`

**Checked by Lean.** Proves that `(sigKeyInd1KeyProg S b.q_total).eval (fun _ => A.1.run) pk`
evaluates identically to `(sigReductionKeyInd1Key S b A).run pk` for every bounded `KeyInd`
adversary `A`.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

theorem Env.get_ofRename {S : Sig} {Γ Δ : List (Ty S)} {τ : Ty S}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (env : Env Δ) (v : Var Γ τ) :
    (Env.ofRename ρ env).get v = env.get (ρ v) := by
  induction v with
  | zero => rfl
  | succ w ih => exact ih (fun x => ρ (.succ x))

theorem Env.ofRename_succ {S : Sig} : {Γ Δ : List (Ty S)} → {u : Ty S} →
    (ρ : ∀ {t}, Var Γ t → Var Δ t) → (x : u.denote) → (env : Env Δ) →
    Env.ofRename (fun v => Var.succ (u := u) (ρ v)) (.cons x env) = Env.ofRename ρ env
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, ρ, x, env =>
    congrArg (Env.cons _) (Env.ofRename_succ (fun v => ρ (.succ v)) x env)

@[simp] theorem Env.ofRename_liftRename {S : Sig} {Γ Δ : List (Ty S)} {u : Ty S}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (x : u.denote) (env : Env Δ) :
    Env.ofRename (Var.liftRename (u := u) ρ) (.cons x env) = .cons x (Env.ofRename ρ env) :=
  congrArg (Env.cons x) (Env.ofRename_succ ρ x env)

@[simp] theorem Expr.rename_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (env : Env Δ),
    (e.rename ρ).eval env = e.eval (Env.ofRename ρ env) := by
  induction e with
  | var v =>
    intro Δ ρ env
    exact (Env.get_ofRename ρ env v).symm
  | unit => intro Δ ρ env; rfl
  | bool _ => intro Δ ρ env; rfl
  | nat _ => intro Δ ρ env; rfl
  | add a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | sub a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | mulK k a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | divK k a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | modK k a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | lt a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | eqN a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | not a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | and a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | ite c a b ihc iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, ihc, iha, ihb]
  | pair a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | fst a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | snd a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | inl a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | inr a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | none => intro Δ ρ env; rfl
  | some a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | caseOpt e n s ihe ihn ihs =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihe]
    cases e.eval (Env.ofRename ρ env) with
    | none => exact ihn ρ env
    | some x =>
      dsimp only
      exact (ihs _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
  | caseSum e l r ihe ihl ihr =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihe]
    cases e.eval (Env.ofRename ρ env) with
    | inl x =>
      dsimp only
      exact (ihl _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
    | inr y =>
      dsimp only
      exact (ihr _ (.cons y env)).trans (by rw [Env.ofRename_liftRename])
  | letE e b ihe ihb =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihe, ihb, Env.ofRename_liftRename]
  | op o a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | nil => intro Δ ρ env; rfl
  | cons x l ihx ihl => intro Δ ρ env; simp only [Expr.rename, Expr.eval, ihx, ihl]
  | len l ihl => intro Δ ρ env; simp only [Expr.rename, Expr.eval, ihl]
  | take n l ihn ihl => intro Δ ρ env; simp only [Expr.rename, Expr.eval, ihn, ihl]
  | appendL K a b iha ihb => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha, ihb]
  | findB K l p ihl ihp =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihl]
    congr 1; funext x
    exact (ihp _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
  | anyB K l p ihl ihp =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihl]
    congr 1; funext x
    exact (ihp _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
  | mapB K l f ihl ihf =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihl]
    congr 1; funext x
    exact (ihf _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
  | foldrB K l z f ihl ihz ihf =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihl, ihz]
    congr 1; funext x acc
    exact (ihf _ (.cons x (.cons acc env))).trans
      (by rw [Env.ofRename_liftRename, Env.ofRename_liftRename])
  | tconst a iha => intro Δ ρ env; simp only [Expr.rename, Expr.eval, iha]
  | tget m i ihm ihi => intro Δ ρ env; simp only [Expr.rename, Expr.eval, ihm, ihi]
  | tset m i a ihm ihi iha =>
    intro Δ ρ env
    simp only [Expr.rename, Expr.eval, ihm, ihi, iha]

@[simp] theorem Comp.rename_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ {Δ : List (Ty S)} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (env : Env Δ),
    (c.rename ρ).eval env = c.eval (Env.ofRename ρ env) := by
  induction c with
  | ret e =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
  | bind c k ihc ihk =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, ihc]
    congr 1; funext x
    exact (ihk _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
  | ite b c d ihc ihd =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval, ihc, ihd]
  | caseOpt e n s ihn ihs =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    cases e.eval (Env.ofRename ρ env) with
    | none => exact ihn ρ env
    | some x =>
      dsimp only
      exact (ihs _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
  | caseSum e l r ihl ihr =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    cases e.eval (Env.ofRename ρ env) with
    | inl x =>
      dsimp only
      exact (ihl _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
    | inr y =>
      dsimp only
      exact (ihr _ (.cons y env)).trans (by rw [Env.ofRename_liftRename])
  | sample s e =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
  | query g e =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval]
    rw [Expr.rename_eval]
  | iter n e body ihb =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    have hFn : (fun a => (body.rename (Var.liftRename ρ)).eval (.cons a env)) =
        (fun a => body.eval (.cons a (Env.ofRename ρ env))) := by
      funext a
      exact (ihb _ (.cons a env)).trans (by rw [Env.ofRename_liftRename])
    rw [hFn]
  | findM K l p ihp =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    have hFn : (fun x => (p.rename (Var.liftRename ρ)).eval (.cons x env)) =
        (fun x => p.eval (.cons x (Env.ofRename ρ env))) := by
      funext x
      exact (ihp _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
    rw [hFn]
  | anyM K l p ihp =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    have hFn : (fun x => (p.rename (Var.liftRename ρ)).eval (.cons x env)) =
        (fun x => p.eval (.cons x (Env.ofRename ρ env))) := by
      funext x
      exact (ihp _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
    rw [hFn]
  | mapM K l f ihf =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    have hFn : (fun x => (f.rename (Var.liftRename ρ)).eval (.cons x env)) =
        (fun x => f.eval (.cons x (Env.ofRename ρ env))) := by
      funext x
      exact (ihf _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
    rw [hFn]
  | consumeFirstM K l p mk ihp =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval, Env.ofRename_liftRename]
    have hFn : (fun x => (p.rename (Var.liftRename ρ)).eval (.cons x env)) =
        (fun x => p.eval (.cons x (Env.ofRename ρ env))) := by
      funext x
      exact (ihp _ (.cons x env)).trans (by rw [Env.ofRename_liftRename])
    rw [hFn]
  | foldM K l z f ihf =>
    intro Δ ρ env
    simp only [Comp.rename, Comp.eval, Expr.rename_eval]
    have hFn : (fun x acc =>
          (f.rename (Var.liftRename (Var.liftRename ρ))).eval (.cons x (.cons acc env))) =
        (fun x acc => f.eval (.cons x (.cons acc (Env.ofRename ρ env)))) := by
      funext x acc
      exact (ihf _ (.cons x (.cons acc env))).trans
        (by rw [Env.ofRename_liftRename, Env.ofRename_liftRename])
    rw [hFn]

end ReductionDsl

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open OracleSpec OracleComp

/-! ## `embedGdhSigDdh` and `liftGdhToSigDdh` evaluation -/

@[simp] theorem embedGdhSigDdh_pure {α : Type} (a : α) :
    embedGdhSigDdh (Pure.pure a) = Pure.pure a := rfl

@[simp] theorem embedGdhSigDdh_bind {α β : Type}
    (m : OracleComp GdhSimSpec α) (k : α → OracleComp GdhSimSpec β) :
    embedGdhSigDdh (m >>= k) = embedGdhSigDdh m >>= fun a => embedGdhSigDdh (k a) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    rcases q with pq | dq
    · change (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => embedGdhSigDdh (r u >>= k)) =
        (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => embedGdhSigDdh (r u)) >>= fun a => embedGdhSigDdh (k a)
      rw [bind_assoc]
      congr 1; funext u; exact ih u
    · change (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => embedGdhSigDdh (r u >>= k)) =
        (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => embedGdhSigDdh (r u)) >>= fun a => embedGdhSigDdh (k a)
      rw [bind_assoc]
      congr 1; funext u; exact ih u

@[simp] theorem embedGdhSigDdh_map {α β : Type} (f : α → β) (m : OracleComp GdhSimSpec α) :
    embedGdhSigDdh (f <$> m) = f <$> embedGdhSigDdh m := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, embedGdhSigDdh_bind]
  rfl

@[simp] theorem embedGdhSigDdh_embedPrim {α : Type} (m : OracleComp PrimBaseSpec α) :
    embedGdhSigDdh (_root_.SignalPqxdh.Security.embedPrim (spec := gapDhOracleSpec) m) =
      _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) m := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    change (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl q)) >>=
        fun u => embedGdhSigDdh (_root_.SignalPqxdh.Security.embedPrim (spec := gapDhOracleSpec) (r u))) =
      liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl q)) >>=
        fun u => _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) (r u)
    congr 1; funext u; exact ih u

@[simp] theorem embedGdhSigDdh_iterM {α : Type} (f : α → OracleComp GdhSimSpec α) :
    ∀ (n : ℕ) (a : α),
      embedGdhSigDdh (iterM f n a) = iterM (fun x => embedGdhSigDdh (f x)) n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, embedGdhSigDdh_bind]
    congr 1; funext a'; exact embedGdhSigDdh_iterM f n a'

@[simp] theorem embedPrim_sigAndDdhFrag {α : Type} (m : OracleComp PrimBaseSpec α) :
    _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhOracle.spec) m =
      _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) m := rfl

@[simp] theorem embedPrim_primSigDdhQ (q : PrimQuery) :
    _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) (primQ q) = primSigDdhQ q := by
  change (liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inr q))) >>= pure) = _
  exact bind_pure _

@[simp] theorem embedGdhSigDdh_findML {α : Type} (p : α → OracleComp GdhSimSpec Bool) :
    ∀ (L : List α),
      embedGdhSigDdh (findML p L) = findML (fun x => embedGdhSigDdh (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [findML, embedGdhSigDdh_bind]
    congr 1; funext b; cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact embedGdhSigDdh_findML p xs
    · rfl

@[simp] theorem embedGdhSigDdh_anyML {α : Type} (p : α → OracleComp GdhSimSpec Bool) :
    ∀ (L : List α),
      embedGdhSigDdh (anyML p L) = anyML (fun x => embedGdhSigDdh (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [anyML, embedGdhSigDdh_bind]
    congr 1; funext b; cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact embedGdhSigDdh_anyML p xs
    · rfl

@[simp] theorem embedGdhSigDdh_mapML {α β : Type} (f : α → OracleComp GdhSimSpec β) :
    ∀ (L : List α),
      embedGdhSigDdh (mapML f L) = mapML (fun x => embedGdhSigDdh (f x)) L
  | [] => rfl
  | x :: xs => by
    simp only [mapML, embedGdhSigDdh_bind, embedGdhSigDdh_pure, embedGdhSigDdh_mapML f xs]

@[simp] theorem embedGdhSigDdh_consumeFirstML {α : Type}
    (p : α → OracleComp GdhSimSpec Bool) (mk : α → α) :
    ∀ (L : List α),
      embedGdhSigDdh (consumeFirstML p mk L) =
        consumeFirstML (fun x => embedGdhSigDdh (p x)) mk L
  | [] => rfl
  | x :: xs => by
    simp only [consumeFirstML, embedGdhSigDdh_bind]
    congr 1; funext b; cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, embedGdhSigDdh_bind, embedGdhSigDdh_pure,
        embedGdhSigDdh_consumeFirstML p mk xs]
    · rfl

@[simp] theorem embedGdhSigDdh_foldML {α β : Type} (f : α → β → OracleComp GdhSimSpec β) :
    ∀ (init : β) (L : List α),
      embedGdhSigDdh (foldML f init L) =
        foldML (fun x acc => embedGdhSigDdh (f x acc)) init L
  | _, [] => rfl
  | init, x :: xs => by
    simp only [foldML, embedGdhSigDdh_bind]
    congr 1; funext b'; exact embedGdhSigDdh_foldML f b' xs

@[simp] theorem liftGdhToSigDdh_eval {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) (env : Env Γ) :
    (liftGdhToSigDdh c).eval env = embedGdhSigDdh (c.eval env) := by
  induction c with
  | ret e => rfl
  | bind c k ihc ihk =>
    simp only [liftGdhToSigDdh, Comp.eval, ihc env, embedGdhSigDdh_bind]
    congr 1; funext x; exact ihk (.cons x env)
  | ite b c d ihc ihd =>
    simp only [liftGdhToSigDdh, Comp.eval]
    cases b.eval env <;> simp [ihc env, ihd env]
  | caseOpt e n s ihn ihs =>
    simp only [liftGdhToSigDdh, Comp.eval]
    cases e.eval env with
    | none => exact ihn env
    | some x => exact ihs (.cons x env)
  | caseSum e l r ihl ihr =>
    simp only [liftGdhToSigDdh, Comp.eval]
    cases e.eval env with
    | inl x => exact ihl (.cons x env)
    | inr y => exact ihr (.cons y env)
  | sample s e =>
    simp only [liftGdhToSigDdh, Comp.eval, pqGapDhIface, pqSigAndDdhIface,
      pqChalIface_liftP, KeyIndGapDh.embedPrim_gapDhFrag, embedPrim_sigAndDdhFrag,
      embedGdhSigDdh_embedPrim]
    rfl
  | query g e =>
    rcases g with g | u
    · simp only [liftGdhToSigDdh, Comp.eval, pqGapDhIface, pqSigAndDdhIface,
        pqChalIface, embedGdhSigDdh_map]
      rfl
    · cases (u : Unit)
      simp only [liftGdhToSigDdh, Comp.eval, pqGapDhIface, pqSigAndDdhIface,
        pqChalIface, gapDhDdhOracle, sigAndDdhOracle, embedGdhSigDdh_map]
      rfl
  | iter n e body ihb =>
    simp only [liftGdhToSigDdh, Comp.eval, embedGdhSigDdh_iterM]
    have hFn : (fun a => (liftGdhToSigDdh body).eval (.cons a env)) =
        (fun a => embedGdhSigDdh (body.eval (.cons a env))) := by
      funext a; exact ihb (.cons a env)
    rw [hFn]
  | findM K l p ihp =>
    simp only [liftGdhToSigDdh, Comp.eval, embedGdhSigDdh_findML]
    have hFn : (fun x => (liftGdhToSigDdh p).eval (.cons x env)) =
        (fun x => embedGdhSigDdh (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | anyM K l p ihp =>
    simp only [liftGdhToSigDdh, Comp.eval, embedGdhSigDdh_anyML]
    have hFn : (fun x => (liftGdhToSigDdh p).eval (.cons x env)) =
        (fun x => embedGdhSigDdh (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | mapM K l f ihf =>
    simp only [liftGdhToSigDdh, Comp.eval, embedGdhSigDdh_mapML]
    have hFn : (fun x => (liftGdhToSigDdh f).eval (.cons x env)) =
        (fun x => embedGdhSigDdh (f.eval (.cons x env))) := by
      funext x; exact ihf (.cons x env)
    rw [hFn]
  | consumeFirstM K l p mk ihp =>
    simp only [liftGdhToSigDdh, Comp.eval, embedGdhSigDdh_consumeFirstML]
    have hFn : (fun x => (liftGdhToSigDdh p).eval (.cons x env)) =
        (fun x => embedGdhSigDdh (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | foldM K l z f ihf =>
    simp only [liftGdhToSigDdh, Comp.eval, embedGdhSigDdh_foldML]
    have hFn : (fun x acc => (liftGdhToSigDdh f).eval (.cons x (.cons acc env))) =
        (fun x acc => embedGdhSigDdh (f.eval (.cons x (.cons acc env)))) := by
      funext x acc; exact ihf (.cons x (.cons acc env))
    rw [hFn]

@[simp] theorem qSigDdhSign_eval (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (B m)) (env : Env Γ) :
    (qSigDdhSign m msg).eval env = sigChalQ (msg.eval env) := by
  simp [qSigDdhSign, Comp.eval, pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, sigChalQ]

@[simp] theorem s1Prim_eval {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) (env : Env Γ) :
    (s1Prim c).eval env =
      _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec) (c.eval env) :=
  liftBase_eval (C := sigAndDdhOracle) c env

/-! ## Handler evaluation agreement -/

section
set_option allowUnsafeReducibility true
attribute [local implicit_reducible] Env.get Ext.wk

theorem delegateFgC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ sig1KeyStTy) (qV : Var Γ₂ keyIndQueryTy) (env : Env Δ)
    (st : Sig1KeySimState S) (q : KeyIndQuery S)
    (hs : env.get (Ext.wk sV) = sig1KeyStToVal st)
    (hq : env.get (Ext.wk qV) = keyIndQueryToVal q)
    (hB : KeyIndGapDh.FgSimListsBounded st.fg K) :
    (delegateFgC S K sV qV).eval env =
      (fun p => encSig1KeyRS (p.1, { st with fg := p.2 })) <$>
        embedGdhSigDdh (fgKeyIndStep false S.N_send_tot S.N_spk_tot S K [] st.targetPk q st.fg) := by
  have hInB : KeyIndGapDh.InBoundsParams2 S (pa2ZeroVal st.targetPk) :=
    Or.inr ⟨by simp [pa2ZeroVal], by simp [pa2ZeroVal], by simp [pa2ZeroVal], by simp [pa2ZeroVal]⟩
  have hMap := (KeyIndGapDh.gdhHandle2_eval_map_eq S K (pa2ZeroVal st.targetPk) hInB
    (simStateToVal st.fg) q).1
  unfold delegateFgC
  simp only [letV_eval, bindV, Comp.eval, liftGdhToSigDdh_eval, Comp.rename_eval,
    pa2Zero, pa2Mk, litB_eval, v, Expr.eval, hs, sig1KeyStToVal,
    s1Pk, s1Fg, s1Upd, s1Mk, s1Target, s1Budget, s1Forgery,
    Env.ofRename, renamePair, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', hq]
  have hStep :
      (embedGdhSigDdh ((gdhHandle2 S K).eval
          (.cons (pa2ZeroVal st.targetPk, simStateToVal st.fg)
            (.cons (keyIndQueryToVal q) .nil))) >>=
        fun r => pure (r.1, (r.2.2, (st.targetParty, (st.targetPk, (st.signBudget, st.forgery)))))) =
      (embedGdhSigDdh (((fun r : keyIndRespTy.denote × gdhState2Ty.denote =>
            (r.1, (params2ToFlat S r.2.1, r.2.2))) <$>
          (gdhHandle2 S K).eval
            (.cons (pa2ZeroVal st.targetPk, simStateToVal st.fg)
              (.cons ((keyIndCodec S).qenc q) .nil)))) >>=
        fun r => pure (r.1, (r.2.2, (st.targetParty, (st.targetPk, (st.signBudget, st.forgery)))))) := by
    simp only [keyIndCodec, keyIndQueryToVal, map_eq_bind_pure_comp, embedGdhSigDdh_bind,
      embedGdhSigDdh_pure, bind_assoc, Function.comp_def, pure_bind]
  change (embedGdhSigDdh ((gdhHandle2 S K).eval
          (.cons (pa2ZeroVal st.targetPk, simStateToVal st.fg)
            (.cons (keyIndQueryToVal q) .nil))) >>=
        fun r => pure (r.1, (r.2.2, (st.targetParty, (st.targetPk, (st.signBudget, st.forgery)))))) = _
  rw [hStep, hMap]
  change (embedGdhSigDdh ((gdhHandle S K).eval
      (.cons (KeyIndGapDh.paramsDhVal S false S.N_send_tot S.N_spk_tot [] st.targetPk,
        simStateToVal st.fg) (.cons (keyIndQueryToVal q) .nil))) >>=
      fun r => pure (r.1, (r.2.2, (st.targetParty, (st.targetPk, (st.signBudget, st.forgery)))))) = _
  rw [KeyIndGapDh.gdhHandle_eval_dh S K false S.N_send_tot S.N_spk_tot [] st.targetPk q st.fg hB]
  simp only [KeyIndGapDh.encGdhRS, encSig1KeyRS, sig1KeyStToVal,
    map_eq_bind_pure_comp, embedGdhSigDdh_bind, embedGdhSigDdh_pure,
    bind_assoc, Function.comp_def, pure_bind]

theorem extract1KeyC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ sig1KeyStTy) (buV : Var Γ₂ preKeyBundleTy) (env : Env Δ)
    (st : Sig1KeySimState S) (bu : PreKeyBundleInput)
    (hs : env.get (Ext.wk sV) = sig1KeyStToVal st)
    (hbu : env.get (Ext.wk buV) = preKeyBundleToVal bu)
    (hB : KeyIndListsBounded st.fg.base K) :
    (extract1KeyC S K sV buV).eval env =
      _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec)
        (extractBundleForgeryPrim S st.targetParty st.targetPk
          st.fg.base.principals st.fg.base.spkBundles bu st.forgery) := by
  rcases st with ⟨fgSt, tp, tpk, bud, fg⟩
  unfold extract1KeyC extractBundleForgeryPrim
  simp only [bindV, letV_eval, Comp.eval, s1Prim_eval]
  rw [honestPeerC_eval]
  core_simp [hs, hbu, s1Base, s1Fg, s1Forgery, s1Target, s1Pk, smBase,
    sig1KeyStToVal, simStateToVal, decPrin_enc,
    preKeyBundleToVal, List.take_of_length_le, hB.spkBundles_le, widenEC_eval]
  simp only [embedPrim_bind, embedPrim_pure, Prod.map, id]
  rw [decPrin_enc, List.take_of_length_le hB.principals_le]
  refine bind_congr2 rfl fun peer => bind_congr2 ?_ fun v1 => bind_congr2 ?_ fun v2 => ?_
  · rw [hs, hbu]; rfl
  · rw [hs, hbu]; rfl
  · congr 1
    rcases fg with _ | fg
    · rcases peer with _ | k
      · rfl
      · simp only [encodeEC, encodeKEM]
        rfl
    · rfl

theorem sig1KeyInitPrinB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ sig1KeyStTy) (uV : Var Γ₂ .nat) (env : Env Δ)
    (st : Sig1KeySimState S) (u : Fin S.N_id)
    (hs : env.get (Ext.wk sV) = sig1KeyStToVal st)
    (hu : env.get (Ext.wk uV) = u.val)
    (hfg : st.forgery = none)
    (hB : KeyIndListsBounded st.fg.base K) :
    (sig1KeyInitPrinB K sV uV).eval env =
      encSig1KeyRS <$> sig1KeyStep S K (.initPrin u) st := by
  rcases st with ⟨fgSt, tp, tpk, bud, fg⟩
  subst hfg
  unfold sig1KeyInitPrinB
  have c1 : (eAny K (stPrin (s1Base (v sV))) fun e => natEq (.fst (v e)) (v uV)).eval env =
      fgSt.base.principals.any (fun x => x.1 == u.val) := by
    simp only [Expr.eval, v, eAny, hs, hu, stPrin, s1Base, s1Fg, smBase, natEq_eval,
      Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
      keyIndStateToVal, simStateToVal, sig1KeyStToVal, List.any_map,
      Function.comp_def, List.take_of_length_le, List.length_map, hB.principals_le, Prod.map, id]
  simp only [Comp.eval, c1]
  by_cases h1 : (fgSt.base.principals.any fun x => x.1 == u.val) = true
  · simp only [h1, ↓reduceIte, sig1KeyStep, Option.isSome_none, Bool.false_eq_true,
      map_pure, Expr.eval, v, hs, rNone, encSig1KeyRS, keyIndRespToVal, keyIndRenc]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, sig1KeyStep, Option.isSome_none]
    core_simp [hs, hu, s1Pk, s1Upd, s1Mk, s1Fg, s1Base, s1Target, s1Budget, s1Forgery,
      smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows,
      sig1KeyStToVal, simStateToVal, s1Prim_eval]
    simp only [unifSigDdh, primSigDdhQ, primQ, sampleScalar32,
      bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def, encSig1KeyRS, sig1KeyStToVal, simStateToVal,
      keyIndStateToVal, keyIndRespToVal, keyIndRenc, List.map_cons]
    refine congrArg (fun h => _ >>= h) (funext fun s0 => ?_)
    refine congrArg (fun h => _ >>= h) (funext fun ik => ?_)
    cases (u.val == tp) <;> rfl

theorem sig1KeyTargetGenSpkB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ sig1KeyStTy) (xV : Var Γ₂ (.prod .nat .nat)) (env : Env Δ)
    (st : Sig1KeySimState S) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hs : env.get (Ext.wk sV) = sig1KeyStToVal st)
    (hx : env.get (Ext.wk xV) = (u.val, j.val))
    (hfg : st.forgery = none)
    (htgt : (u.val == st.targetParty) = true)
    (hB : KeyIndListsBounded st.fg.base K) :
    (sig1KeyTargetGenSpkB K sV xV).eval env =
      encSig1KeyRS <$> sig1KeyStep S K (.genSPK u j) st := by
  rcases st with ⟨fgSt, tp, tpk, bud, fg⟩
  subst hfg
  dsimp only at htgt
  unfold sig1KeyTargetGenSpkB
  have c3 : (eAny K (stSpks (s1Base (v sV))) fun e => nat2Eq (.fst (v e)) (v xV)).eval env =
      fgSt.base.spkBundles.any (fun x => x.1.1 == u.val && x.1.2 == j.val) := by
    core_simp [hs, hx, s1Base, s1Fg, smBase, sig1KeyStToVal, simStateToVal,
      List.take_of_length_le, hB.spkBundles_le, Prod.map, id]
  simp only [Comp.eval, c3, sig1KeyStep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    htgt, nat2_beq]
  by_cases h3 : (fgSt.base.spkBundles.any fun x => x.1.1 == u.val && x.1.2 == j.val) = true
  · simp only [h3, ↓reduceIte, map_pure, Expr.eval, v, hs, rNone,
      encSig1KeyRS, keyIndRespToVal, keyIndRenc]
  · simp only [h3, Bool.false_eq_true, ↓reduceIte]
    core_simp [hs, hx, s1Base, s1Fg, s1Upd, s1Mk, s1Pk, s1Target, s1Budget, s1Forgery,
      smUpd, smMk, smBase, smFgL, smRaw, smLog, smPows,
      sig1KeyStToVal, simStateToVal, List.take_of_length_le, hB.principals_le,
      s1Prim_eval, qSigDdhSign_eval]
    rcases hfd : fgSt.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨i, e⟩
    · simp [hfd, encSig1KeyRS, sig1KeyStToVal, simStateToVal, keyIndStateToVal,
        keyIndRespToVal, keyIndRenc]
    · have hfd' : List.find? (fun x : Nat × PrincipalEntry =>
          (Prod.map id principalEntryToVal x).1 == u.val) fgSt.base.principals = some (i, e) := hfd
      rw [hfd', hfd]
      cases bud with
      | zero =>
        simp [encSig1KeyRS, sig1KeyStToVal, simStateToVal, keyIndStateToVal,
          keyIndRespToVal, keyIndRenc]
      | succ bud' =>
        simp only [Option.map, beq_iff_eq, Nat.add_one_ne_zero,
          ↓reduceIte, Nat.add_sub_cancel, unifSigDdh, sampleScalar32,
          bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def,
          encSig1KeyRS, sig1KeyStToVal, simStateToVal, keyIndStateToVal,
          bundleV, keyIndRespToVal, keyIndRenc, List.map_cons, encodeEC, encodeKEM]
        rfl

theorem sig1KeyInitiateCheckC_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sV : Var Γ₁ sig1KeyStTy) (xV : Var Γ₂ initQTy) (env : Env Δ)
    (st : Sig1KeySimState S) (uVal iVal : Nat) (bu : PreKeyBundleInput)
    (hs : env.get (Ext.wk sV) = sig1KeyStToVal st)
    (hx : env.get (Ext.wk xV) = (uVal, (iVal, preKeyBundleToVal bu)))
    (hB : KeyIndListsBounded st.fg.base K) :
    (sig1KeyInitiateCheckC S K sV xV).eval env =
      (do
        let fg' ← _root_.SignalPqxdh.Security.embedPrim (spec := sigAndDdhSpec)
          (extractBundleForgeryPrim S st.targetParty st.targetPk
            st.fg.base.principals st.fg.base.spkBundles bu st.forgery)
        if fg'.isSome then
          pure (.inl (encSig1KeyRS (.noneResp, { st with forgery := fg' })))
        else
          pure (.inr ())) := by
  have hE := extract1KeyC_eval S K sV
    (Γ₂ := preKeyBundleTy :: Δ) .zero (.cons (preKeyBundleToVal bu) env) st bu
    (by simp [hs]) rfl hB
  unfold sig1KeyInitiateCheckC
  simp only [letV_eval, bindV, Comp.eval, Expr.eval, v, hx]
  rw [hE]
  refine congrArg (fun h => _ >>= h) (funext fun fg' => ?_)
  cases fg' <;>
    simp [isSomeE, Expr.eval, hs, encSig1KeyRS, sig1KeyStToVal, rNone, keyIndRespToVal, keyIndRenc]

theorem sig1KeyHandleC_eval (S : Setup) (K : Nat)
    (q : KeyIndQuery S) (st : Sig1KeySimState S) (hB : KeyIndGapDh.FgSimListsBounded st.fg K) :
    (sig1KeyHandleC S K).eval (.cons (sig1KeyStToVal st) (.cons (keyIndQueryToVal q) .nil)) =
      encSig1KeyRS <$> sig1KeyStep S K q st := by
  let env0 : Env [sig1KeyStTy, keyIndQueryTy] :=
    .cons (sig1KeyStToVal st) (.cons (keyIndQueryToVal q) .nil)
  change (sig1KeyHandleC S K).eval env0 = encSig1KeyRS <$> sig1KeyStep S K q st
  rcases hfg : st.forgery with _ | fgVal
  ·
    have hIsSome : ∀ (qVal : keyIndQueryTy.denote),
        (isSomeE (s1Forgery (Expr.var Var.zero))).eval
          (.cons (sig1KeyStToVal st) (.cons qVal .nil)) = false := by
      intro qVal
      simp [isSomeE, s1Forgery, sig1KeyStToVal, hfg, Expr.eval]
    cases q with
    | initPrin u =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
      rw [sig1KeyInitPrinB_eval S K .zero .zero _ st u rfl rfl hfg hB.1]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | genSPK u j =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
      have hTarget : ∀ {Δ : List PT} (xV : Var Δ (.prod .nat .nat))
          (sV : Var Δ sig1KeyStTy) (env : Env Δ),
          env.get xV = (u.val, j.val) → env.get sV = sig1KeyStToVal st →
          (natEq (.fst (Expr.var xV)) (s1Target (Expr.var sV))).eval env =
            (u.val == st.targetParty) := by
        intro Δ xV sV env hx hs
        simp [natEq_eval, s1Target, sig1KeyStToVal, Expr.eval, hx, hs]
      rw [hTarget _ _ _ rfl rfl]
      by_cases htgt : (u.val == st.targetParty) = true
      · simp only [htgt, ↓reduceIte]
        rw [sig1KeyTargetGenSpkB_eval S K .zero .zero _ st u j rfl rfl hfg htgt hB.1]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      · simp only [htgt, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.genSPK u j) rfl rfl hB]
        simp only [sig1KeyStep, hfg, Option.isSome_none, htgt, Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | initiateOPK u i bu =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
      rw [sig1KeyInitiateCheckC_eval S K .zero .zero _ st u.val i.val bu rfl rfl hB.1]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, map_eq_bind_pure_comp, Function.comp_def]
      refine congrArg (fun h => _ >>= h) (funext fun fg' => ?_)
      by_cases hfg' : fg'.isSome = true
      · simp only [hfg', ↓reduceIte, pure_bind]
      · simp only [hfg', Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.initiateOPK u i bu) rfl rfl hB]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, hfg]
    | initiateNoOPK u i bu =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
      rw [sig1KeyInitiateCheckC_eval S K .zero .zero _ st u.val i.val bu rfl rfl hB.1]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        bind_assoc, map_eq_bind_pure_comp, Function.comp_def]
      refine congrArg (fun h => _ >>= h) (funext fun fg' => ?_)
      by_cases hfg' : fg'.isSome = true
      · simp only [hfg', ↓reduceIte, pure_bind]
      · simp only [hfg', Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.initiateNoOPK u i bu) rfl rfl hB]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, hfg]
    | corruptIK u =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.corruptIK u) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | genOPK u j o =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.genOPK u j o) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | acceptOPK k j o hdr =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.acceptOPK k j o hdr) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | acceptNoOPK k j l hdr =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.acceptNoOPK k j l hdr) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | testSession sid =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.testSession sid) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | roQuery sec =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.roQuery sec) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | revealDhSecrets =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st .revealDhSecrets rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | revealSessionKey sid =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.revealSessionKey sid) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | registerKey sk =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.registerKey sk) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    | revealSpkSk u j =>
      simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0,
        keyIndQueryToVal, keyIndQenc, v, hIsSome, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', pure_bind]
      rw [delegateFgC_eval S K .zero (.succ .zero) _ st (.revealSpkSk u j) rfl rfl hB]
      simp only [sig1KeyStep, hfg, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  ·
    have hIsSome : ∀ (qVal : keyIndQueryTy.denote),
        (isSomeE (s1Forgery (Expr.var Var.zero))).eval
          (.cons (sig1KeyStToVal st) (.cons qVal .nil)) = true := by
      intro qVal
      simp [isSomeE, s1Forgery, sig1KeyStToVal, hfg, Expr.eval]
    simp only [sig1KeyHandleC, sig1KeyPreDispatchC, bindV, caseSumV, Comp.eval, env0, v,
      hIsSome, ↓reduceIte, pure_bind, sig1KeyStep, hfg, Option.isSome_some, map_pure,
      Expr.eval, Env.get_zero', Ext.refl_wk', rNone,
      encSig1KeyRS, keyIndRespToVal, keyIndRenc]

end

/-! ## End-to-end evaluation equivalence -/

theorem AllOut_embedGdhSigDdh {α : Type} {mx : OracleComp GdhSimSpec α} {P : α → Prop}
    (h : KeyIndGapDh.AllOut mx P) : KeyIndGapDh.AllOut (embedGdhSigDdh mx) P := by
  classical
  have hEq : (mx >>= fun a => pure (decide (P a))) = (mx >>= fun _ => pure true) :=
    bind_congr_of_forall_mem_support mx (fun a ha => by simp [h a ha])
  have hEmb := congrArg embedGdhSigDdh hEq
  simp only [embedGdhSigDdh_bind, embedGdhSigDdh_pure] at hEmb
  intro x hx
  have hmem : decide (P x) ∈ support (embedGdhSigDdh mx >>= fun a => pure (decide (P a))) := by
    rw [support_bind, Set.mem_iUnion]
    exact ⟨x, Set.mem_iUnion.mpr ⟨hx, by simp⟩⟩
  rw [hEmb, support_bind, Set.mem_iUnion] at hmem
  rcases hmem with ⟨_, hmem⟩
  rw [Set.mem_iUnion] at hmem
  rcases hmem with ⟨_, htrue⟩
  simp only [support_pure, Set.mem_singleton_iff] at htrue
  exact of_decide_eq_true htrue

theorem grow_refl {S : Setup} (st : FgKeyIndSimState S) : KeyIndGapDh.Grow st st := by
  simp only [KeyIndGapDh.Grow]; omega

theorem sig1KeyStep_grow {S : Setup} (K : Nat) (q : KeyIndQuery S) (st : Sig1KeySimState S) :
    KeyIndGapDh.AllOut (sig1KeyStep S K q st) (fun x => KeyIndGapDh.Grow st.fg x.2.fg) := by
  unfold sig1KeyStep
  split
  · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
  · have hDel : ∀ q', KeyIndGapDh.AllOut
        (do
          let (out, fg') ← embedGdhSigDdh
            (fgKeyIndStep false S.N_send_tot S.N_spk_tot S K [] st.targetPk q' st.fg)
          return (out, { st with fg := fg' }))
        (fun x => KeyIndGapDh.Grow st.fg x.2.fg) := by
      intro q' x hx
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨out, fg'⟩, hmem, rfl⟩
      exact AllOut_embedGdhSigDdh
        (KeyIndGapDh.fgKeyIndStep_grow false S.N_send_tot S.N_spk_tot K [] st.targetPk q' st.fg)
        (out, fg') hmem
    cases q with
    | initPrin u =>
      dsimp only
      split
      · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
      · refine KeyIndGapDh.AllOut.bind_of (fun _ => KeyIndGapDh.AllOut.bind_of (fun _ => ?_))
        refine KeyIndGapDh.AllOut.pure_of ?_
        simp only [KeyIndGapDh.Grow, List.length_cons]; omega
    | genSPK u j =>
      dsimp only
      split
      · split
        · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
        · split
          · split
            · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
            · refine KeyIndGapDh.AllOut.bind_of (fun _ => KeyIndGapDh.AllOut.bind_of (fun _ =>
                KeyIndGapDh.AllOut.bind_of (fun _ => KeyIndGapDh.AllOut.bind_of (fun _ =>
                KeyIndGapDh.AllOut.bind_of (fun _ => KeyIndGapDh.AllOut.bind_of (fun _ => ?_))))))
              refine KeyIndGapDh.AllOut.pure_of ?_
              simp only [KeyIndGapDh.Grow, List.length_cons]; omega
          · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
      · exact hDel (.genSPK u j)
    | initiateOPK u i bundle =>
      dsimp only
      refine KeyIndGapDh.AllOut.bind_of (fun fg' => ?_)
      split
      · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
      · exact hDel (.initiateOPK u i bundle)
    | initiateNoOPK u i bundle =>
      dsimp only
      refine KeyIndGapDh.AllOut.bind_of (fun fg' => ?_)
      split
      · exact KeyIndGapDh.AllOut.pure_of (grow_refl st.fg)
      · exact hDel (.initiateNoOPK u i bundle)
    | corruptIK u => exact hDel (.corruptIK u)
    | genOPK u j o => exact hDel (.genOPK u j o)
    | acceptOPK k j o hdr => exact hDel (.acceptOPK k j o hdr)
    | acceptNoOPK k j l hdr => exact hDel (.acceptNoOPK k j l hdr)
    | testSession sid => exact hDel (.testSession sid)
    | roQuery sec => exact hDel (.roQuery sec)
    | revealDhSecrets => exact hDel .revealDhSecrets
    | revealSessionKey sid => exact hDel (.revealSessionKey sid)
    | registerKey sk => exact hDel (.registerKey sk)
    | revealSpkSk u j => exact hDel (.revealSpkSk u j)

theorem simulateQ_handlerImpl_bind_eq_runWithSigDdhStep_bind {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {C : GameCodec pqSig GSpec}
    {σ : PT} {σS α β : Type}
    (h : Comp pqxdhOps pqSigAndDdhIface [σ, C.Q] (.prod C.R σ))
    (stepS : (q : ιI) → σS → OracleComp SigDdhSimSpec (GSpec.Range q × σS))
    (enc : σS → σ.denote) (InvP : Nat → σS → Prop)
    (hMono : ∀ k s, InvP (k + 1) s → InvP k s)
    (hStep : ∀ k q s, InvP (k + 1) s →
      (do let p ← h.eval (.cons (enc s) (.cons (C.qenc q) .nil))
          pure (C.rdec q p.1, p.2)) =
        (fun x => (x.1, enc x.2)) <$> stepS q s)
    (hPres : ∀ k q s, InvP (k + 1) s → ∀ x ∈ support (stepS q s), InvP k x.2)
    (f : α × σ.denote → OracleComp SigDdhSimSpec β)
    (g : α × σS → OracleComp SigDdhSimSpec β)
    (hfg : ∀ a s, InvP 0 s → f (a, enc s) = g (a, s))
    (mx : OracleComp (unifSpec + GSpec) α) (qTotal : Nat)
    (hMx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => q.isRight = true) qTotal)
    (s : σS) (hs : InvP qTotal s) :
    ((simulateQ (handlerImpl (C := C) h) mx).run (enc s) >>= f) =
      (runWithSigDdhStep stepS mx s >>= g) := by
  induction mx using OracleComp.inductionOn generalizing qTotal s with
  | pure a =>
    have h0 : InvP 0 s := by
      clear hMx
      induction qTotal with
      | zero => exact hs
      | succ n ih => exact ih (hMono n s hs)
    simp only [simulateQ_pure, StateT.run_pure, runWithSigDdhStep, OracleComp.construct_pure,
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
        ((liftM (OracleSpec.query (spec := SigDdhSimSpec) (Sum.inl (Sum.inl uq))) >>= fun u =>
          runWithSigDdhStep stepS (k u) s) >>= g)
      simp only [pqSigAndDdhIface, pqChalIface, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u qTotal (hCont u) s hs
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
        ((stepS gq s >>= fun p => runWithSigDdhStep stepS (k p.1) p.2) >>= g)
      rw [hStep n gq s hs]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      refine bind_congr_of_forall_mem_support _ (fun x hx => ?_)
      exact ih x.1 n (hCont x.1) x.2 (hPres n gq s hs x hx)

theorem sigKeyInd1KeyProg_eval_eq_of_queryBound (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : IsQueryBoundP (A ()) (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) K)
    (pk : Bytes) :
    (sigKeyInd1KeyProg S K).eval A pk =
      (do
        let k ← unifSigDdh (RoKem.sampleIndexRange S.N_id)
        let secb ← unifSigDdh ($ᵗ Bool)
        let initSt := Sig1Key.Sig1KeySimState.empty S secb k pk
        let (_, finalSt) ← runWithSigDdhStep (sig1KeyStep S K) (A ()) initSt
        return finalSt.forgery.getD ([], [])) := by
  have hfun : A = (fun _ => A ()) := funext fun ⟨⟩ => rfl
  rw [hfun]
  simp only [CostedReduction.eval, CostedReduction.impl, sigKeyInd1KeyProg, bindV, Comp.eval,
    s1Prim_eval, sIndex_eval, sBool_eval, KeyIndGapDh.emptySimE_eval (S := S),
    s1Mk, v, Expr.eval, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk',
    unifSigDdh, bind_assoc, pure_bind]
  refine bind_congr fun k => bind_congr fun secb => ?_
  let initSt := Sig1Key.Sig1KeySimState.empty S secb k pk
  let initStK : Sig1KeySimState S := { initSt with signBudget := min K initSt.signBudget }
  rw [← runWithSigDdhStep_sig1KeyStep_forgery_eq K (A ()) initSt hA]
  change ((simulateQ (handlerImpl (C := keyIndCodec S) (sig1KeyHandleC S K)) (A ())).run
      (sig1KeyStToVal initStK) >>= fun p =>
        pure ((eCaseOpt (s1Forgery (.var .zero)) (.pair (litB 1569 []) (litB 64 []))
          fun fg => v fg).eval (.cons p.2 (.cons (t := .bool) p.1 .nil)))) = _
  refine simulateQ_handlerImpl_bind_eq_runWithSigDdhStep_bind
    (C := keyIndCodec S) (σ := sig1KeyStTy) (α := Bool) (sig1KeyHandleC S K) (sig1KeyStep S K)
    sig1KeyStToVal (fun n st => KeyIndGapDh.Inv K n st.fg)
    (fun n st h => KeyIndGapDh.Inv.mono K n st.fg h)
    (fun n q st h => ?_)
    (fun n q st h x hx => KeyIndGapDh.Inv.of_grow K n st.fg x.2.fg h (sig1KeyStep_grow K q st x hx))
    (fun p => pure ((eCaseOpt (s1Forgery (.var .zero)) (.pair (litB 1569 []) (litB 64 []))
      fun fg => v fg).eval (.cons p.2 (.cons (t := .bool) p.1 .nil))))
    (fun p => pure (p.2.forgery.getD ([], [])))
    (fun _ st _ => ?_)
    (A ()) K hA initStK (KeyIndGapDh.Inv.empty S K secb)
  · dsimp only [keyIndCodec, keyIndQueryToVal]
    rw [sig1KeyHandleC_eval S K q st (KeyIndGapDh.Inv.bnd K (n + 1) st.fg h)]
    simp only [encSig1KeyRS, keyIndRespToVal, keyIndRdec_keyIndRenc,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  · rcases hfg : st.forgery with _ | fgVal <;>
      simp [eCaseOpt, s1Forgery, sig1KeyStToVal, hfg, litB_eval, Expr.eval, v]

/-- `(sigKeyInd1KeyProg S b.q_total).eval` agrees pointwise with `(sigReductionKeyInd1Key S b A).run`. -/
theorem sigKeyInd1KeyProg_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    (sigKeyInd1KeyProg S b.q_total).eval (fun _ => A.1.run) pk =
      (sigReductionKeyInd1Key S b A).run pk := by
  have hA : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => q.isRight = true) b.q_total := by
    obtain ⟨_, _, _, h, _⟩ := A.2
    convert h using 1
    funext q; cases q <;> rfl
  rw [sigKeyInd1KeyProg_eval_eq_of_queryBound S b.q_total (fun _ => A.1.run) hA pk]
  rfl

end SignalPqxdh.Security.ReductionDsl.KeyInd
