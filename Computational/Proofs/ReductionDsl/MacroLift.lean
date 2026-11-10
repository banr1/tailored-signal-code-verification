/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Monadic Macro Compiler for `ReductionDsl`

Compiles `ReductionDsl` expressions, computations, and one- or two-stage `CostedReduction` programs
from an abstract operation table `O₁` and interface `I₁` into target tables `O₂` and `I₂`,
threading a read-only auxiliary context `aux : auxT.denote`. Establishes query, static cost, AST
size, and `OracleComp` evaluation bounds, together with length-guarded `GRedBounded` and
`GTwoStageBounded` wrappers (`guardRed`, `guardTwoStageRed`).
-/

@[expose] public section

set_option autoImplicit false

/-! ## Variable renaming on `Expr` and `Comp` -/

namespace ReductionDsl

open OracleSpec OracleComp

def liftRen {S : Sig} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {a : Ty S} :
    ∀ ⦃u⦄, Var (a :: Γ) u → Var (a :: Δ) u
  | _, .zero => .zero
  | _, .succ v => .succ (ξ v)

theorem get_liftRen {S : Sig} {Γ Δ : List (Ty S)} {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u}
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v)
    {a : Ty S} (x : a.denote) ⦃u : Ty S⦄ (v : Var (a :: Γ) u) :
    (Env.cons x ρ₂).get (liftRen ξ v) = (Env.cons x ρ₁).get v := by
  cases v with
  | zero => rfl
  | succ v => exact hξ v

def Expr.renameM {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} : Expr O Γ t → Expr O Δ t
  | .var v => .var (ξ v)
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .add a b => .add (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .sub a b => .sub (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .mulK k a => .mulK k (Expr.renameM ξ a)
  | .divK k a => .divK k (Expr.renameM ξ a)
  | .modK k a => .modK k (Expr.renameM ξ a)
  | .lt a b => .lt (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .eqN a b => .eqN (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .not a => .not (Expr.renameM ξ a)
  | .and a b => .and (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .ite c a b => .ite (Expr.renameM ξ c) (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .pair a b => .pair (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .fst a => .fst (Expr.renameM ξ a)
  | .snd a => .snd (Expr.renameM ξ a)
  | .inl a => .inl (Expr.renameM ξ a)
  | .inr a => .inr (Expr.renameM ξ a)
  | .none => .none
  | .some a => .some (Expr.renameM ξ a)
  | .caseOpt e n s =>
    .caseOpt (Expr.renameM ξ e) (Expr.renameM ξ n) (Expr.renameM (liftRen ξ) s)
  | .caseSum e l r =>
    .caseSum (Expr.renameM ξ e) (Expr.renameM (liftRen ξ) l) (Expr.renameM (liftRen ξ) r)
  | .letE e b => .letE (Expr.renameM ξ e) (Expr.renameM (liftRen ξ) b)
  | .op o a => .op o (Expr.renameM ξ a)
  | .nil => .nil
  | .cons x l => .cons (Expr.renameM ξ x) (Expr.renameM ξ l)
  | .len l => .len (Expr.renameM ξ l)
  | .take n l => .take (Expr.renameM ξ n) (Expr.renameM ξ l)
  | .appendL K a b => .appendL K (Expr.renameM ξ a) (Expr.renameM ξ b)
  | .findB K l p => .findB K (Expr.renameM ξ l) (Expr.renameM (liftRen ξ) p)
  | .anyB K l p => .anyB K (Expr.renameM ξ l) (Expr.renameM (liftRen ξ) p)
  | .mapB K l f => .mapB K (Expr.renameM ξ l) (Expr.renameM (liftRen ξ) f)
  | .foldrB K l z f =>
    .foldrB K (Expr.renameM ξ l) (Expr.renameM ξ z) (Expr.renameM (liftRen (liftRen ξ)) f)
  | .tconst a => .tconst (Expr.renameM ξ a)
  | .tget m i => .tget (Expr.renameM ξ m) (Expr.renameM ξ i)
  | .tset m i a => .tset (Expr.renameM ξ m) (Expr.renameM ξ i) (Expr.renameM ξ a)

@[simp] theorem Expr.renameM_cost {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    (Expr.renameM ξ e).cost = e.cost := by
  induction e generalizing Δ <;> simp only [Expr.renameM, Expr.cost, *]

theorem Expr.one_le_size {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : 1 ≤ e.size := by
  cases e with
  | nat n => exact one_le_bits n
  | mulK k _ | divK k _ | modK k _ =>
    have := one_le_bits k
    simp only [Expr.size]
    omega
  | _ =>
    simp only [Expr.size]
    omega

@[simp] theorem Expr.renameM_size {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    (Expr.renameM ξ e).size = e.size := by
  induction e generalizing Δ <;> simp only [Expr.renameM, Expr.size, *]

/-- Bit-length-independent AST node count (every constructor and literal counts `1`). -/
@[simp] def Expr.nodes {S : Sig} {O : Ops S} : {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil => 1
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .letE a b | _, _, .appendL _ a b | _, _, .findB _ a b
  | _, _, .anyB _ a b | _, _, .mapB _ a b | _, _, .tget a b => a.nodes + b.nodes + 1
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a | _, _, .op _ a => a.nodes + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b
  | _, _, .foldrB _ c a b | _, _, .tset c a b => c.nodes + a.nodes + b.nodes + 1

@[simp] theorem Expr.renameM_nodes {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} (e : Expr O Γ t) :
    (Expr.renameM ξ e).nodes = e.nodes := by
  induction e generalizing Δ <;> simp only [Expr.renameM, Expr.nodes, *]

theorem Expr.renameM_eval {S : Sig} {O : Ops S} {Γ Δ : List (Ty S)}
    {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u} {t : Ty S} (e : Expr O Γ t)
    {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v) :
    (Expr.renameM ξ e).eval ρ₂ = e.eval ρ₁ := by
  induction e generalizing Δ with
  | var v => exact hξ v
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | sub _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | mulK _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | divK _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | modK _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | lt _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | eqN _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | not _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | and _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | ite _ _ _ ihc iha ihb => simp [Expr.renameM, Expr.eval, ihc hξ, iha hξ, ihb hξ]
  | pair _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | fst _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | snd _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | inl _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | inr _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | some _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | caseOpt e n s ihe ihn ihs =>
    simp only [Expr.renameM, Expr.eval, ihe hξ]
    cases e.eval ρ₁ with
    | none => exact ihn hξ
    | some x => exact ihs (get_liftRen hξ x)
  | caseSum e l r ihe ihl ihr =>
    simp only [Expr.renameM, Expr.eval, ihe hξ]
    cases e.eval ρ₁ with
    | inl x => exact ihl (get_liftRen hξ x)
    | inr y => exact ihr (get_liftRen hξ y)
  | letE e b ihe ihb =>
    simp only [Expr.renameM, Expr.eval, ihe hξ]
    exact ihb (get_liftRen hξ (e.eval ρ₁))
  | op _ _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | cons _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | len _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | take _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | appendL _ _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | findB K l p ihl ihp =>
    simp only [Expr.renameM, Expr.eval, ihl hξ]
    congr 1; funext x; exact ihp (get_liftRen hξ x)
  | anyB K l p ihl ihp =>
    simp only [Expr.renameM, Expr.eval, ihl hξ]
    congr 1; funext x; exact ihp (get_liftRen hξ x)
  | mapB K l f ihl ihf =>
    simp only [Expr.renameM, Expr.eval, ihl hξ]
    congr 1; funext x; exact ihf (get_liftRen hξ x)
  | foldrB K l z f ihl ihz ihf =>
    simp only [Expr.renameM, Expr.eval, ihl hξ, ihz hξ]
    congr 1; funext x acc; exact ihf (get_liftRen (get_liftRen hξ acc) x)
  | tconst _ ih => simp [Expr.renameM, Expr.eval, ih hξ]
  | tget _ _ ih1 ih2 => simp [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ]
  | tset _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.renameM, Expr.eval, ih1 hξ, ih2 hξ, ih3 hξ]

def Comp.renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S} :
    Comp O I Γ t → Comp O I Δ t
  | .ret e => .ret (Expr.renameM ξ e)
  | .bind c k => .bind (Comp.renameM ξ c) (Comp.renameM (liftRen ξ) k)
  | .ite b c d => .ite (Expr.renameM ξ b) (Comp.renameM ξ c) (Comp.renameM ξ d)
  | .caseOpt e n s =>
    .caseOpt (Expr.renameM ξ e) (Comp.renameM ξ n) (Comp.renameM (liftRen ξ) s)
  | .caseSum e l r =>
    .caseSum (Expr.renameM ξ e) (Comp.renameM (liftRen ξ) l) (Comp.renameM (liftRen ξ) r)
  | .sample s e => .sample s (Expr.renameM ξ e)
  | .query g e => .query g (Expr.renameM ξ e)
  | .iter n e body => .iter n (Expr.renameM ξ e) (Comp.renameM (liftRen ξ) body)
  | .findM K l p => .findM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) p)
  | .anyM K l p => .anyM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) p)
  | .mapM K l f => .mapM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) f)
  | .consumeFirstM K l p mk =>
    .consumeFirstM K (Expr.renameM ξ l) (Comp.renameM (liftRen ξ) p) (Expr.renameM (liftRen ξ) mk)
  | .foldM K l z f =>
    .foldM K (Expr.renameM ξ l) (Expr.renameM ξ z) (Comp.renameM (liftRen (liftRen ξ)) f)

@[simp] theorem Comp.renameM_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) :
    (Comp.renameM ξ c).cost = c.cost := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.cost, Expr.renameM_cost, *]

@[simp] theorem Comp.renameM_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) :
    (Comp.renameM ξ c).size = c.size := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.size, Expr.renameM_size, *]

@[simp] def Comp.nodes {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e | _, _, .sample _ e | _, _, .query _ e => e.nodes + 1
  | _, _, .bind c k => c.nodes + k.nodes + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    b.nodes + c.nodes + d.nodes + 1
  | _, _, .iter _ e body | _, _, .findM _ e body | _, _, .anyM _ e body | _, _, .mapM _ e body =>
    e.nodes + body.nodes + 1
  | _, _, .consumeFirstM _ l p mk => l.nodes + p.nodes + mk.nodes + 1
  | _, _, .foldM _ l z f => l.nodes + z.nodes + f.nodes + 1

@[simp] theorem Comp.renameM_nodes {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) :
    (Comp.renameM ξ c).nodes = c.nodes := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.nodes, Expr.renameM_nodes, *]

@[simp] def CostedReduction.nodes {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out) : ℕ :=
  R.init.nodes + R.handle.nodes + R.finish.nodes

@[simp] theorem Comp.renameM_queries {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u) {t : Ty S}
    (c : Comp O I Γ t) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (Comp.renameM ξ c).queries w ws = c.queries w ws := by
  induction c generalizing Δ <;> simp only [Comp.renameM, Comp.queries, *]

private theorem iterM_congr {m : Type → Type} [Monad m] {α : Type}
    {f g : α → m α} (h : ∀ a, f a = g a) :
    ∀ (n : ℕ) (a : α), iterM f n a = iterM g n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, h a]
    exact bind_congr fun b => iterM_congr h n b

private theorem findML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, findML p xs = findML q xs
  | [] => rfl
  | x :: xs => by simp only [findML, h x, findML_congr h xs]

private theorem anyML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} (h : ∀ x, p x = q x) :
    ∀ xs : List α, anyML p xs = anyML q xs
  | [] => rfl
  | x :: xs => by simp only [anyML, h x, anyML_congr h xs]

private theorem mapML_congr {m : Type → Type} [Monad m] {α β : Type}
    {f g : α → m β} (h : ∀ x, f x = g x) :
    ∀ xs : List α, mapML f xs = mapML g xs
  | [] => rfl
  | x :: xs => by simp only [mapML, h x, mapML_congr h xs]

private theorem consumeFirstML_congr {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} {mk₁ mk₂ : α → α}
    (hp : ∀ x, p x = q x) (hm : ∀ x, mk₁ x = mk₂ x) :
    ∀ xs : List α, consumeFirstML p mk₁ xs = consumeFirstML q mk₂ xs
  | [] => rfl
  | x :: xs => by simp only [consumeFirstML, hp x, hm x, consumeFirstML_congr hp hm xs]

private theorem foldML_congr {m : Type → Type} [Monad m] {α β : Type}
    {f g : α → β → m β} (h : ∀ x b, f x b = g x b) :
    ∀ (b : β) (xs : List α), foldML f b xs = foldML g b xs
  | _, [] => rfl
  | b, x :: xs => by
    simp only [foldML, h x b]
    exact bind_congr fun b' => foldML_congr h b' xs

theorem Comp.renameM_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ Δ : List (Ty S)} {ξ : ∀ ⦃u⦄, Var Γ u → Var Δ u}
    {t : Ty S} (c : Comp O I Γ t) {ρ₁ : Env Γ} {ρ₂ : Env Δ}
    (hξ : ∀ ⦃u⦄ (v : Var Γ u), ρ₂.get (ξ v) = ρ₁.get v) :
    (Comp.renameM ξ c).eval ρ₂ = c.eval ρ₁ := by
  induction c generalizing Δ with
  | ret e => simp [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
  | bind c k ihc ihk =>
    simp only [Comp.renameM, Comp.eval, ihc hξ]
    exact bind_congr fun x => ihk (get_liftRen hξ x)
  | ite b c d ihc ihd =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval b hξ]
    split_ifs <;> [exact ihc hξ; exact ihd hξ]
  | caseOpt e n s ihn ihs =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
    cases e.eval ρ₁ with
    | none => exact ihn hξ
    | some x => exact ihs (get_liftRen hξ x)
  | caseSum e l r ihl ihr =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
    cases e.eval ρ₁ with
    | inl x => exact ihl (get_liftRen hξ x)
    | inr y => exact ihr (get_liftRen hξ y)
  | sample s e =>
    simp only [Comp.renameM, Comp.eval]
    rw [Expr.renameM_eval e hξ]
  | query g e =>
    simp only [Comp.renameM, Comp.eval]
    rw [Expr.renameM_eval e hξ]
  | iter n e body ihb =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval e hξ]
    exact iterM_congr (fun a => ihb (get_liftRen hξ a)) n (e.eval ρ₁)
  | findM K l p ihp =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact findML_congr (fun x => ihp (get_liftRen hξ x)) _
  | anyM K l p ihp =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact anyML_congr (fun x => ihp (get_liftRen hξ x)) _
  | mapM K l f ihf =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact mapML_congr (fun x => ihf (get_liftRen hξ x)) _
  | consumeFirstM K l p mk ihp =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ]
    exact consumeFirstML_congr (fun x => ihp (get_liftRen hξ x))
      (fun x => Expr.renameM_eval mk (get_liftRen hξ x)) _
  | foldM K l z f ihf =>
    simp only [Comp.renameM, Comp.eval, Expr.renameM_eval l hξ, Expr.renameM_eval z hξ]
    exact foldML_congr (fun x acc => ihf (get_liftRen (get_liftRen hξ acc) x)) _ _

@[reducible] def Comp.wk1 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I Γ t) : Comp O I (a :: Γ) t :=
  Comp.renameM (fun ⦃_⦄ v => .succ v) c

@[reducible] def Comp.wk2 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I Γ t) : Comp O I (a :: b :: Γ) t :=
  Comp.renameM (fun ⦃_⦄ v => .succ (.succ v)) c

theorem Comp.wk1_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a t : Ty S} (c : Comp O I Γ t) (x : a.denote) (ρ : Env Γ) :
    (Comp.wk1 c).eval (.cons x ρ) = c.eval ρ :=
  Comp.renameM_eval c (fun ⦃_⦄ _ => rfl)

theorem Comp.wk2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I Γ t)
    (x : a.denote) (y : b.denote) (ρ : Env Γ) :
    (Comp.wk2 c).eval (.cons x (.cons y ρ)) = c.eval ρ :=
  Comp.renameM_eval c (fun ⦃_⦄ _ => rfl)

theorem Comp.renameM_liftRen_wk1_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {a b t : Ty S}
    (c : Comp O I (a :: Γ) t) (x : a.denote) (y : b.denote) (ρ : Env Γ) :
    (Comp.renameM (liftRen (fun ⦃_⦄ v => .succ v)) c).eval (.cons x (.cons y ρ)) =
      c.eval (.cons x ρ) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by cases v <;> rfl

theorem Comp.renameM_liftRen_wk2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {a b d t : Ty S}
    (c : Comp O I (a :: Γ) t) (x : a.denote) (y : b.denote) (z : d.denote) (ρ : Env Γ) :
    (Comp.renameM (liftRen (fun ⦃_⦄ v => .succ (.succ v))) c).eval
        (.cons x (.cons y (.cons z ρ))) =
      c.eval (.cons x ρ) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by cases v <;> rfl

theorem Comp.renameM_liftRen2_wk2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {a b c d t : Ty S}
    (e : Comp O I (a :: b :: Γ) t)
    (x : a.denote) (y : b.denote) (z₁ : c.denote) (z₂ : d.denote) (ρ : Env Γ) :
    (Comp.renameM (liftRen (liftRen (fun ⦃_⦄ v => .succ (.succ v)))) e).eval
        (.cons x (.cons y (.cons z₁ (.cons z₂ ρ)))) =
      e.eval (.cons x (.cons y ρ)) :=
  Comp.renameM_eval e fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w => cases w <;> rfl

theorem Comp.renameM_liftRen2_wk3_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {a b c d g t : Ty S}
    (e : Comp O I (a :: b :: Γ) t)
    (x : a.denote) (y : b.denote) (z₁ : c.denote) (z₂ : d.denote) (z₃ : g.denote)
    (ρ : Env Γ) :
    (Comp.renameM (liftRen (liftRen (fun ⦃_⦄ v => .succ (.succ (.succ v))))) e).eval
        (.cons x (.cons y (.cons z₁ (.cons z₂ (.cons z₃ ρ))))) =
      e.eval (.cons x (.cons y ρ)) :=
  Comp.renameM_eval e fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w => cases w <;> rfl

@[reducible] def Expr.wkClosed {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O [] t) : Expr O Γ t :=
  Expr.renameM (fun ⦃_⦄ v => by cases v) e

@[reducible] def Expr.wkTop1 {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a t : Ty S}
    (e : Expr O [a] t) : Expr O (a :: Γ) t :=
  Expr.renameM (fun ⦃_⦄ v => match v with | .zero => .zero | .succ w => nomatch w) e

theorem Expr.wkTop1_eval {S : Sig} {O : Ops S} {Γ : List (Ty S)} {a t : Ty S}
    (e : Expr O [a] t) (x : a.denote) (ρ : Env Γ) :
    (Expr.wkTop1 e).eval (.cons x ρ) = e.eval (.cons x .nil) :=
  Expr.renameM_eval e fun ⦃_⦄ v => by cases v with | zero => rfl | succ w => nomatch w

@[reducible] def Comp.wkTop2 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I [a, b] t) :
    Comp O I (a :: b :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
      | .succ (.succ w) => nomatch w) c

theorem Comp.wkTop2_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b t : Ty S} (c : Comp O I [a, b] t)
    (x : a.denote) (y : b.denote) (ρ : Env Γ) :
    (Comp.wkTop2 c).eval (.cons x (.cons y ρ)) = c.eval (.cons x (.cons y .nil)) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w =>
      cases w with
      | zero => rfl
      | succ u => nomatch u

@[reducible] def Comp.wkTop3 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d t : Ty S} (c : Comp O I [a, b, d] t) :
    Comp O I (a :: b :: d :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
      | .succ (.succ .zero) => .succ (.succ .zero)
      | .succ (.succ (.succ w)) => nomatch w) c

theorem Comp.wkTop3_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d t : Ty S} (c : Comp O I [a, b, d] t)
    (x : a.denote) (y : b.denote) (z : d.denote) (ρ : Env Γ) :
    (Comp.wkTop3 c).eval (.cons x (.cons y (.cons z ρ))) =
      c.eval (.cons x (.cons y (.cons z .nil))) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ w =>
      cases w with
      | zero => rfl
      | succ u =>
        cases u with
        | zero => rfl
        | succ q => nomatch q

@[reducible] def Comp.wkTop4 {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d g t : Ty S} (c : Comp O I [a, b, d, g] t) :
    Comp O I (a :: b :: d :: g :: Γ) t :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ .zero
      | .succ (.succ .zero) => .succ (.succ .zero)
      | .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
      | .succ (.succ (.succ (.succ w))) => nomatch w) c

theorem Comp.wkTop4_eval {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a b d g t : Ty S} (c : Comp O I [a, b, d, g] t)
    (x : a.denote) (y : b.denote) (z : d.denote) (w : g.denote) (ρ : Env Γ) :
    (Comp.wkTop4 c).eval (.cons x (.cons y (.cons z (.cons w ρ)))) =
      c.eval (.cons x (.cons y (.cons z (.cons w .nil)))) :=
  Comp.renameM_eval c fun ⦃_⦄ v => by
    cases v with
    | zero => rfl
    | succ v1 =>
      cases v1 with
      | zero => rfl
      | succ v2 =>
        cases v2 with
        | zero => rfl
        | succ v3 =>
          cases v3 with
          | zero => rfl
          | succ v4 => nomatch v4

end ReductionDsl

namespace Computational.Proofs.ReductionDsl.MacroLift

open OracleSpec OracleComp
open _root_.ReductionDsl
open CryptoVerification.LibsignalSession (GRedBounded GTwoStageBounded evalTwoStage1)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)

/-! ## Sort-to-type substitution and auxiliary-rooted environments -/

section Subst

@[reducible] def mapTy {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) : Ty S₁ → Ty S₂
  | .base b => f b
  | .unit => .unit
  | .bool => .bool
  | .nat => .nat
  | .opt t => .opt (mapTy f t)
  | .prod t u => .prod (mapTy f t) (mapTy f u)
  | .sum t u => .sum (mapTy f t) (mapTy f u)
  | .list t => .list (mapTy f t)
  | .tbl t => .tbl (mapTy f t)

def toVal {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂)
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) :
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

/-- Translated context `Γ.map (mapTy f) ++ [auxT]`, definitionally commuting with `cons`. -/
@[reducible] def mapCtx {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂) :
    List (Ty S₁) → List (Ty S₂)
  | [] => [auxT]
  | t :: Γ => mapTy f t :: mapCtx f auxT Γ

def mapVarAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} → Var Γ t → Var (mapCtx f auxT Γ) (mapTy f t)
  | _, _, .zero => .zero
  | _, _, .succ v => .succ (mapVarAux f auxT v)

def auxVar {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂) :
    (Γ : List (Ty S₁)) → Var (mapCtx f auxT Γ) auxT
  | [] => .zero
  | _ :: Γ => .succ (auxVar f auxT Γ)

def mapEnvAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote) :
    {Γ : List (Ty S₁)} → Env Γ → Env (mapCtx f auxT Γ)
  | _, .nil => .cons aux .nil
  | _, .cons x ρ => .cons (toVal f toDen _ x) (mapEnvAux f toDen aux ρ)

theorem get_mapEnvAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote)
    {Γ : List (Ty S₁)} {t : Ty S₁} (ρ : Env Γ) (v : Var Γ t) :
    (mapEnvAux f toDen aux ρ).get (mapVarAux f auxT v) = toVal f toDen t (ρ.get v) := by
  induction v with
  | zero => cases ρ; rfl
  | succ v ih =>
    cases ρ with
    | cons _ ρ => exact ih ρ

theorem get_auxVar {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote) :
    ∀ {Γ : List (Ty S₁)} (ρ : Env Γ),
      (mapEnvAux f toDen aux ρ).get (auxVar f auxT Γ) = aux
  | _, .nil => rfl
  | _, .cons _ ρ => get_auxVar f toDen aux ρ

def callMacroAux {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) :
    Comp O₂ I₂ (a :: mapCtx f auxT Γ) b :=
  Comp.renameM
    (fun ⦃_⦄ v => match v with
      | .zero => .zero
      | .succ .zero => .succ (auxVar f auxT Γ))
    c

@[simp] theorem callMacroAux_cost {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) :
    (callMacroAux f auxT Γ c).cost = c.cost :=
  Comp.renameM_cost _ c

@[simp] theorem callMacroAux_size {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) :
    (callMacroAux f auxT Γ c).size = c.size :=
  Comp.renameM_size _ c

@[simp] theorem callMacroAux_queries {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι} {I₂ : Iface S₂ T}
    {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b)
    (w : I₂.Tag → ℕ) (ws : I₂.smp.Samp → ℕ) :
    (callMacroAux f auxT Γ c).queries w ws = c.queries w ws :=
  Comp.renameM_queries _ c w ws

theorem callMacroAux_eval {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) {auxT : Ty S₂}
    (toDen : (b : S₁.Base) → S₁.den b → (f b).denote) (aux : auxT.denote)
    {Γ : List (Ty S₁)} (ρ : Env Γ) {O₂ : Ops S₂} {ι : Type} {T : OracleSpec ι}
    {I₂ : Iface S₂ T} {a b : Ty S₂} (c : Comp O₂ I₂ [a, auxT] b) (x : a.denote) :
    (callMacroAux f auxT Γ c).eval (.cons x (mapEnvAux f toDen aux ρ)) =
      c.eval (.cons x (.cons aux .nil)) := by
  refine Comp.renameM_eval c ?_
  intro u v
  cases v with
  | zero => rfl
  | succ v =>
    cases v with
    | zero => exact get_auxVar f toDen aux ρ
    | succ v => nomatch v

end Subst

/-! ## Monadic macro compiler -/

/-- Target `Comp O₂ I₂` macros implementing each operator, sampler, and query tag of `(O₁, I₁)`
with access to `(arg, aux)`. -/
structure MacroBundle (S₁ S₂ : Sig) (O₁ : Ops S₁) (O₂ : Ops S₂)
    {ι : Type} {T : OracleSpec ι} (I₁ : Iface S₁ T) (I₂ : Iface S₂ T)
    (auxT : Ty S₂) where
  fSort : S₁.Base → Ty S₂
  opMacro : (o : O₁.Op) → Comp O₂ I₂ [mapTy fSort (O₁.dom o), auxT] (mapTy fSort (O₁.cod o))
  sampMacro : (s : I₁.smp.Samp) →
    Comp O₂ I₂ [mapTy fSort (I₁.smp.sDom s), auxT] (mapTy fSort (I₁.smp.sTy s))
  queryMacro : (g : I₁.Tag) →
    Comp O₂ I₂ [mapTy fSort (I₁.dom g), auxT] (mapTy fSort (I₁.cod g))

section Compile

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}

def compileExpr (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Expr O₁ Γ t → Comp O₂ I₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .var v => .ret (.var (mapVarAux M.fSort auxT v))
  | _, _, .unit => .ret .unit
  | _, _, .bool b => .ret (.bool b)
  | _, _, .nat n => .ret (.nat n)
  | _, _, .add a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.add (.var (.succ .zero)) (.var .zero))))
  | _, _, .sub a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.sub (.var (.succ .zero)) (.var .zero))))
  | _, _, .mulK k a => .bind (compileExpr M a) (.ret (.mulK k (.var .zero)))
  | _, _, .divK k a => .bind (compileExpr M a) (.ret (.divK k (.var .zero)))
  | _, _, .modK k a => .bind (compileExpr M a) (.ret (.modK k (.var .zero)))
  | _, _, .lt a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.lt (.var (.succ .zero)) (.var .zero))))
  | _, _, .eqN a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.eqN (.var (.succ .zero)) (.var .zero))))
  | _, _, .not a => .bind (compileExpr M a) (.ret (.not (.var .zero)))
  | _, _, .and a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.and (.var (.succ .zero)) (.var .zero))))
  | _, _, .ite c a b =>
    .bind (compileExpr M c)
      (.ite (.var .zero) ((compileExpr M a).wk1) ((compileExpr M b).wk1))
  | _, _, .pair a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.pair (.var (.succ .zero)) (.var .zero))))
  | _, _, .fst a => .bind (compileExpr M a) (.ret (.fst (.var .zero)))
  | _, _, .snd a => .bind (compileExpr M a) (.ret (.snd (.var .zero)))
  | _, _, .inl a => .bind (compileExpr M a) (.ret (.inl (.var .zero)))
  | _, _, .inr a => .bind (compileExpr M a) (.ret (.inr (.var .zero)))
  | _, _, .none => .ret .none
  | _, _, .some a => .bind (compileExpr M a) (.ret (.some (.var .zero)))
  | _, _, .caseOpt e n s =>
    .bind (compileExpr M e)
      (.caseOpt (.var .zero) ((compileExpr M n).wk1)
        ((compileExpr M s).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .caseSum e l r =>
    .bind (compileExpr M e)
      (.caseSum (.var .zero)
        ((compileExpr M l).renameM (liftRen (fun ⦃_⦄ v => .succ v)))
        ((compileExpr M r).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .letE e b => .bind (compileExpr M e) (compileExpr M b)
  | Γ, _, .op o a =>
    .bind (compileExpr M a) (callMacroAux M.fSort auxT Γ (M.opMacro o))
  | _, _, .nil => .ret .nil
  | _, _, .cons x l =>
    .bind (compileExpr M x)
      (.bind ((compileExpr M l).wk1) (.ret (.cons (.var (.succ .zero)) (.var .zero))))
  | _, _, .len l => .bind (compileExpr M l) (.ret (.len (.var .zero)))
  | _, _, .take n l =>
    .bind (compileExpr M n)
      (.bind ((compileExpr M l).wk1) (.ret (.take (.var (.succ .zero)) (.var .zero))))
  | _, _, .appendL K a b =>
    .bind (compileExpr M a)
      (.bind ((compileExpr M b).wk1) (.ret (.appendL K (.var (.succ .zero)) (.var .zero))))
  | _, _, .findB K l p =>
    .bind (compileExpr M l)
      (.findM K (.var .zero) ((compileExpr M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .anyB K l p =>
    .bind (compileExpr M l)
      (.anyM K (.var .zero) ((compileExpr M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .mapB K l f =>
    .bind (compileExpr M l)
      (.mapM K (.var .zero) ((compileExpr M f).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .foldrB K l z f =>
    .bind (compileExpr M l)
      (.bind (.foldM K (.var .zero) .nil (.ret (.cons (.var .zero) (.var (.succ .zero)))))
        (.bind ((compileExpr M z).wk2)
          (.foldM K (.var (.succ .zero)) (.var .zero)
            ((compileExpr M f).renameM
              (liftRen (liftRen (fun ⦃_⦄ v => .succ (.succ (.succ v)))))))))
  | _, _, .tconst a => .bind (compileExpr M a) (.ret (.tconst (.var .zero)))
  | _, _, .tget m i =>
    .bind (compileExpr M m)
      (.bind ((compileExpr M i).wk1) (.ret (.tget (.var (.succ .zero)) (.var .zero))))
  | _, _, .tset m i a =>
    .bind (compileExpr M m)
      (.bind ((compileExpr M i).wk1)
        (.bind ((compileExpr M a).wk2)
          (.ret (.tset (.var (.succ (.succ .zero))) (.var (.succ .zero)) (.var .zero)))))

def compileComp (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT) :
    {Γ : List (Ty S₁)} → {t : Ty S₁} →
      Comp O₁ I₁ Γ t → Comp O₂ I₂ (mapCtx M.fSort auxT Γ) (mapTy M.fSort t)
  | _, _, .ret e => compileExpr M e
  | _, _, .bind c k => .bind (compileComp M c) (compileComp M k)
  | _, _, .ite b c d =>
    .bind (compileExpr M b)
      (.ite (.var .zero) ((compileComp M c).wk1) ((compileComp M d).wk1))
  | _, _, .caseOpt e n s =>
    .bind (compileExpr M e)
      (.caseOpt (.var .zero) ((compileComp M n).wk1)
        ((compileComp M s).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .caseSum e l r =>
    .bind (compileExpr M e)
      (.caseSum (.var .zero)
        ((compileComp M l).renameM (liftRen (fun ⦃_⦄ v => .succ v)))
        ((compileComp M r).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | Γ, _, .sample s e =>
    .bind (compileExpr M e) (callMacroAux M.fSort auxT Γ (M.sampMacro s))
  | Γ, _, .query g e =>
    .bind (compileExpr M e) (callMacroAux M.fSort auxT Γ (M.queryMacro g))
  | _, _, .iter n e body =>
    .bind (compileExpr M e)
      (.iter n (.var .zero) ((compileComp M body).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .findM K l p =>
    .bind (compileExpr M l)
      (.findM K (.var .zero) ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .anyM K l p =>
    .bind (compileExpr M l)
      (.anyM K (.var .zero) ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .mapM K l f =>
    .bind (compileExpr M l)
      (.mapM K (.var .zero) ((compileComp M f).renameM (liftRen (fun ⦃_⦄ v => .succ v))))
  | _, _, .consumeFirstM K l p mk =>
    .bind (compileExpr M l)
      (.bind
        (.foldM K (.var .zero) (.pair (.bool false) .nil)
          (.ite (.fst (.var (.succ .zero)))
            (.ret (.pair (.bool true) (.cons (.var .zero) (.snd (.var (.succ .zero))))))
            (.bind
              ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ (.succ v))))
              (.ite (.var .zero)
                (.bind
                  ((compileExpr M mk).renameM
                    (fun ⦃_⦄ v => match v with
                      | .zero => .succ .zero
                      | .succ w => .succ (.succ (.succ (.succ w)))))
                  (.ret (.pair (.bool true)
                    (.cons (.var .zero) (.snd (.var (.succ (.succ (.succ .zero)))))))))
                (.ret (.pair (.bool false)
                  (.cons (.var (.succ .zero)) (.snd (.var (.succ (.succ .zero)))))))))))
        (.bind
          (.foldM K (.snd (.var .zero)) .nil (.ret (.cons (.var .zero) (.var (.succ .zero)))))
          (.ret (.pair (.fst (.var (.succ .zero))) (.var .zero)))))
  | _, _, .foldM K l z f =>
    .bind (compileExpr M l)
      (.bind ((compileExpr M z).wk1)
        (.foldM K (.var (.succ .zero)) (.var .zero)
          ((compileComp M f).renameM (liftRen (liftRen (fun ⦃_⦄ v => .succ (.succ v)))))))

theorem compileExpr_queries (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compileExpr M e).queries w₂ ws₂ = 0 := by
  induction e with
  | op o a iha => simp only [compileExpr, callMacroAux_queries, Comp.queries, iha, hOpQ, add_zero]
  | _ => simp only [compileExpr, Comp.wk1, Comp.renameM_queries, Comp.queries,
      add_zero, Nat.max_zero, mul_zero, *]

theorem compileComp_queries_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compileComp M c).queries w₂ ws₂ ≤ c.queries w₁ ws₁ := by
  induction c with
  | ret e => simp [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e]
  | bind c k ihc ihk =>
    simp only [compileComp, Comp.queries]
    omega
  | ite b c d ihc ihd =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ b,
      Comp.renameM_queries, zero_add]
    exact max_le_max ihc ihd
  | caseOpt e n s ihn ihs =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      Comp.renameM_queries, zero_add]
    exact max_le_max ihn ihs
  | caseSum e l r ihl ihr =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      Comp.renameM_queries, zero_add]
    exact max_le_max ihl ihr
  | sample s e =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      callMacroAux_queries, zero_add]
    exact hSampQ s
  | query g e =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      callMacroAux_queries, zero_add]
    exact hQueryQ g
  | iter n e body ihb =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ e,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left n ihb
  | findM K l p ihp =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihp
  | anyM K l p ihp =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihp
  | mapM K l f ihf =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihf
  | consumeFirstM K l p mk ihp =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      compileExpr_queries M w₂ ws₂ hOpQ mk, Comp.renameM_queries, zero_add, add_zero,
      Nat.max_zero, Nat.zero_max, mul_zero]
    exact Nat.mul_le_mul_left K ihp
  | foldM K l z f ihf =>
    simp only [compileComp, Comp.queries, compileExpr_queries M w₂ ws₂ hOpQ l,
      compileExpr_queries M w₂ ws₂ hOpQ z, Comp.renameM_queries, zero_add]
    exact Nat.mul_le_mul_left K ihf

theorem compileExpr_cost_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (C_m : ℕ) (hCm : 10 ≤ C_m)
    (hOpC : ∀ o, (M.opMacro o).cost + 1 ≤ C_m * O₁.cost o)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compileExpr M e).cost ≤ C_m * e.cost := by
  induction e with
  | var _ | unit | bool _ =>
    simp only [compileExpr, Comp.cost, Expr.cost]; omega
  | nat n =>
    have hb := CryptoVerification.E2E.Costed.Expr.one_le_cost (.nat n : Expr O₁ [] .nat)
    simp only [compileExpr, Comp.cost, Expr.cost] at hb ⊢
    nlinarith
  | none | nil =>
    simp only [compileExpr, Comp.cost, Expr.cost]; omega
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | take a b iha ihb =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | mulK k a iha | divK k a iha | modK k a iha =>
    have hbk := CryptoVerification.E2E.Costed.Expr.one_le_cost (.nat k : Expr O₁ [] .nat)
    simp only [Expr.cost] at hbk
    simp only [compileExpr, Comp.cost, Expr.cost]
    nlinarith
  | not a iha | fst a iha | snd a iha | inl a iha | inr a iha
  | some a iha | len a iha | tconst a iha =>
    simp only [compileExpr, Comp.cost, Expr.cost]
    nlinarith
  | ite c a b ihc iha ihb =>
    have hmax : max (compileExpr M a).cost (compileExpr M b).cost ≤ C_m * max a.cost b.cost := by
      rcases le_total a.cost b.cost with h | h
      · rw [max_eq_right h]; exact max_le (iha.trans (Nat.mul_le_mul_left C_m h)) ihb
      · rw [max_eq_left h]; exact max_le iha (ihb.trans (Nat.mul_le_mul_left C_m h))
    simp only [compileExpr, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | caseOpt e n s ihe ihn ihs =>
    have hmax : max (compileExpr M n).cost (compileExpr M s).cost ≤ C_m * max n.cost s.cost := by
      rcases le_total n.cost s.cost with h | h
      · rw [max_eq_right h]; exact max_le (ihn.trans (Nat.mul_le_mul_left C_m h)) ihs
      · rw [max_eq_left h]; exact max_le ihn (ihs.trans (Nat.mul_le_mul_left C_m h))
    simp only [compileExpr, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | caseSum e l r ihe ihl ihr =>
    have hmax : max (compileExpr M l).cost (compileExpr M r).cost ≤ C_m * max l.cost r.cost := by
      rcases le_total l.cost r.cost with h | h
      · rw [max_eq_right h]; exact max_le (ihl.trans (Nat.mul_le_mul_left C_m h)) ihr
      · rw [max_eq_left h]; exact max_le ihl (ihr.trans (Nat.mul_le_mul_left C_m h))
    simp only [compileExpr, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | letE e b ihe ihb =>
    simp only [compileExpr, Comp.cost, Expr.cost]
    nlinarith
  | op o a iha =>
    have ho := hOpC o
    simp only [compileExpr, callMacroAux_cost, Comp.cost, Expr.cost]
    nlinarith
  | appendL K a b iha ihb =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | findB K l p ihl ihp | anyB K l p ihl ihp | mapB K l p ihl ihp =>
    have hmul : K * ((compileExpr M p).cost + 1) ≤ K * (C_m * (p.cost + 1)) :=
      Nat.mul_le_mul_left K (by nlinarith)
    simp only [compileExpr, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | foldrB K l z f ihl ihz ihf =>
    have hf1 := CryptoVerification.E2E.Costed.Expr.one_le_cost f
    have hmul : K * ((compileExpr M f).cost + 7) ≤ K * (C_m * (f.cost + 1)) :=
      Nat.mul_le_mul_left K (by nlinarith)
    simp only [compileExpr, Comp.wk2, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | tget m i ihm ihi =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | tset m i a ihm ihi iha =>
    simp only [compileExpr, Comp.wk1, Comp.wk2, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith

theorem compileComp_cost_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (C_0 : ℕ) (hC0 : 32 ≤ C_0)
    (hOpC : ∀ o, (M.opMacro o).cost + 1 ≤ C_0 * O₁.cost o)
    (hSampC : ∀ s, (M.sampMacro s).cost + 1 ≤ C_0 * max 1 (I₁.smp.sCost s))
    (hQueryC : ∀ g, (M.queryMacro g).cost + 1 ≤ C_0 * max 1 (I₁.qCost g))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compileComp M c).cost ≤ (2 * C_0) * c.cost := by
  have hC010 : 10 ≤ C_0 := by omega
  let C_m := 2 * C_0
  change (compileComp M c).cost ≤ C_m * c.cost
  have hCm : C_m = 2 * C_0 := rfl
  induction c with
  | ret e =>
    have he := compileExpr_cost_le M C_0 hC010 hOpC e
    simp only [compileComp, Comp.cost]
    nlinarith
  | bind c k ihc ihk =>
    simp only [compileComp, Comp.cost]
    nlinarith
  | ite b c d ihc ihd =>
    have hb := compileExpr_cost_le M C_0 hC010 hOpC b
    have hmax : max (compileComp M c).cost (compileComp M d).cost ≤ C_m * max c.cost d.cost := by
      rcases le_total c.cost d.cost with h | h
      · rw [max_eq_right h]; exact max_le (ihc.trans (Nat.mul_le_mul_left C_m h)) ihd
      · rw [max_eq_left h]; exact max_le ihc (ihd.trans (Nat.mul_le_mul_left C_m h))
    simp only [compileComp, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | caseOpt e n s ihn ihs =>
    have he := compileExpr_cost_le M C_0 hC010 hOpC e
    have hmax : max (compileComp M n).cost (compileComp M s).cost ≤ C_m * max n.cost s.cost := by
      rcases le_total n.cost s.cost with h | h
      · rw [max_eq_right h]; exact max_le (ihn.trans (Nat.mul_le_mul_left C_m h)) ihs
      · rw [max_eq_left h]; exact max_le ihn (ihs.trans (Nat.mul_le_mul_left C_m h))
    simp only [compileComp, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | caseSum e l r ihl ihr =>
    have he := compileExpr_cost_le M C_0 hC010 hOpC e
    have hmax : max (compileComp M l).cost (compileComp M r).cost ≤ C_m * max l.cost r.cost := by
      rcases le_total l.cost r.cost with h | h
      · rw [max_eq_right h]; exact max_le (ihl.trans (Nat.mul_le_mul_left C_m h)) ihr
      · rw [max_eq_left h]; exact max_le ihl (ihr.trans (Nat.mul_le_mul_left C_m h))
    simp only [compileComp, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | sample s e =>
    have he := compileExpr_cost_le M C_0 hC010 hOpC e
    have he1 := CryptoVerification.E2E.Costed.Expr.one_le_cost e
    have hs := hSampC s
    simp only [compileComp, callMacroAux_cost, Comp.cost]
    rcases Nat.eq_zero_or_pos (I₁.smp.sCost s) with h0 | hpos
    · rw [h0] at hs ⊢; simp at hs; nlinarith
    · rw [max_eq_right hpos] at hs; nlinarith
  | query g e =>
    have he := compileExpr_cost_le M C_0 hC010 hOpC e
    have he1 := CryptoVerification.E2E.Costed.Expr.one_le_cost e
    have hg := hQueryC g
    simp only [compileComp, callMacroAux_cost, Comp.cost]
    rcases Nat.eq_zero_or_pos (I₁.qCost g) with h0 | hpos
    · rw [h0] at hg ⊢; simp at hg; nlinarith
    · rw [max_eq_right hpos] at hg; nlinarith
  | iter n e body ihb =>
    have he := compileExpr_cost_le M C_0 hC010 hOpC e
    have hmul : n * ((compileComp M body).cost + 1) ≤ n * (C_m * (body.cost + 1)) :=
      Nat.mul_le_mul_left n (by nlinarith)
    simp only [compileComp, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | findM K l p ihp | anyM K l p ihp | mapM K l p ihp =>
    have hl := compileExpr_cost_le M C_0 hC010 hOpC l
    have hmul : K * ((compileComp M p).cost + 1) ≤ K * (C_m * (p.cost + 1)) :=
      Nat.mul_le_mul_left K (by nlinarith)
    simp only [compileComp, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith
  | consumeFirstM K l p mk ihp =>
    have hl := compileExpr_cost_le M C_0 hC010 hOpC l
    have hl1 := CryptoVerification.E2E.Costed.Expr.one_le_cost l
    have hmk := compileExpr_cost_le M C_0 hC010 hOpC mk
    have hmk1 := CryptoVerification.E2E.Costed.Expr.one_le_cost mk
    simp only [compileComp, Comp.renameM_cost, Comp.cost, Expr.cost, Nat.reduceAdd]
    have hstep :
        2 + max 7 ((compileComp M p).cost +
          (1 + max ((compileExpr M mk).cost + 7 + 1) 7 + 1) + 1) + 1 + 1 ≤
          (compileComp M p).cost + (compileExpr M mk).cost + 16 := by omega
    have hmul1 := Nat.mul_le_mul_left K hstep
    have hmul2 :
        K * ((compileComp M p).cost + (compileExpr M mk).cost + 16) + K * 5 ≤
          K * (C_m * (p.cost + mk.cost + 1)) := by
      rw [← Nat.left_distrib]
      exact Nat.mul_le_mul_left K (by nlinarith)
    nlinarith
  | foldM K l z f ihf =>
    have hl := compileExpr_cost_le M C_0 hC010 hOpC l
    have hz := compileExpr_cost_le M C_0 hC010 hOpC z
    have hmul : K * ((compileComp M f).cost + 1) ≤ K * (C_m * (f.cost + 1)) :=
      Nat.mul_le_mul_left K (by nlinarith)
    simp only [compileComp, Comp.wk1, Comp.renameM_cost, Comp.cost, Expr.cost]
    nlinarith

theorem compileExpr_size_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (C_m : ℕ) (hCm : 16 ≤ C_m)
    (hOpS : ∀ o, (M.opMacro o).size + 1 ≤ C_m)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compileExpr M e).size ≤ C_m * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    simp only [compileExpr, Comp.size, Expr.size]; omega
  | nat n =>
    have hb := ReductionDsl.one_le_bits n
    simp only [compileExpr, Comp.size, Expr.size]
    nlinarith
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb | take a b iha ihb =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | mulK k a iha | divK k a iha | modK k a iha =>
    have hbk := ReductionDsl.one_le_bits k
    simp only [compileExpr, Comp.size, Expr.size]
    nlinarith
  | not a iha | fst a iha | snd a iha | inl a iha | inr a iha
  | some a iha | len a iha | tconst a iha =>
    simp only [compileExpr, Comp.size, Expr.size]
    nlinarith
  | ite c a b ihc iha ihb =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | caseOpt e n s ihe ihn ihs =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | caseSum e l r ihe ihl ihr =>
    simp only [compileExpr, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | letE e b ihe ihb =>
    simp only [compileExpr, Comp.size, Expr.size]
    nlinarith
  | op o a iha =>
    have ho := hOpS o
    simp only [compileExpr, callMacroAux_size, Comp.size, Expr.size]
    nlinarith
  | appendL K a b iha ihb =>
    have hbK := ReductionDsl.one_le_bits K
    simp only [compileExpr, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | findB K l p ihl ihp | anyB K l p ihl ihp | mapB K l p ihl ihp =>
    have hbK := ReductionDsl.one_le_bits K
    simp only [compileExpr, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | foldrB K l z f ihl ihz ihf =>
    have hbK := ReductionDsl.one_le_bits K
    simp only [compileExpr, Comp.wk2, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | tget m i ihm ihi =>
    simp only [compileExpr, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | tset m i a ihm ihi iha =>
    simp only [compileExpr, Comp.wk1, Comp.wk2, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith

theorem compileComp_size_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (C_0 : ℕ) (hC0 : 32 ≤ C_0)
    (hOpS : ∀ o, (M.opMacro o).size + 1 ≤ C_0)
    (hSampS : ∀ s, (M.sampMacro s).size + 1 ≤ C_0)
    (hQueryS : ∀ g, (M.queryMacro g).size + 1 ≤ C_0)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compileComp M c).size ≤ (2 * C_0) * c.size := by
  have hC016 : 16 ≤ C_0 := by omega
  let C_m := 2 * C_0
  change (compileComp M c).size ≤ C_m * c.size
  have hCm : C_m = 2 * C_0 := rfl
  induction c with
  | ret e =>
    have he := compileExpr_size_le M C_0 hC016 hOpS e
    simp only [compileComp, Comp.size]
    nlinarith
  | bind c k ihc ihk =>
    simp only [compileComp, Comp.size]
    nlinarith
  | ite b c d ihc ihd =>
    have hb := compileExpr_size_le M C_0 hC016 hOpS b
    simp only [compileComp, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | caseOpt e n s ihn ihs =>
    have he := compileExpr_size_le M C_0 hC016 hOpS e
    simp only [compileComp, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | caseSum e l r ihl ihr =>
    have he := compileExpr_size_le M C_0 hC016 hOpS e
    simp only [compileComp, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | sample s e =>
    have he := compileExpr_size_le M C_0 hC016 hOpS e
    have hs := hSampS s
    simp only [compileComp, callMacroAux_size, Comp.size]
    nlinarith
  | query g e =>
    have he := compileExpr_size_le M C_0 hC016 hOpS e
    have hg := hQueryS g
    simp only [compileComp, callMacroAux_size, Comp.size]
    nlinarith
  | iter n e body ihb =>
    have he := compileExpr_size_le M C_0 hC016 hOpS e
    simp only [compileComp, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | findM K l p ihp | anyM K l p ihp | mapM K l p ihp =>
    have hl := compileExpr_size_le M C_0 hC016 hOpS l
    simp only [compileComp, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith
  | consumeFirstM K l p mk ihp =>
    have hl := compileExpr_size_le M C_0 hC016 hOpS l
    have hmk := compileExpr_size_le M C_0 hC016 hOpS mk
    have hbK := ReductionDsl.one_le_bits K
    simp only [compileComp, Comp.renameM_size, Comp.size, Expr.size, Nat.reduceAdd]
    nlinarith
  | foldM K l z f ihf =>
    have hl := compileExpr_size_le M C_0 hC016 hOpS l
    have hz := compileExpr_size_le M C_0 hC016 hOpS z
    simp only [compileComp, Comp.wk1, Comp.renameM_size, Comp.size, Expr.size]
    nlinarith

/-! ### Evaluation agreement -/

private theorem findML_pure_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p : α → Bool) (q : β → m Bool)
    (hq : ∀ x, q (g x) = pure (p x)) :
    ∀ xs : List α, findML q (xs.map g) = pure ((xs.find? p).map g)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, findML, hq x, pure_bind, List.find?_cons]
    cases p x with
    | false => exact findML_pure_map g p q hq xs
    | true => rfl

private theorem anyML_pure_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p : α → Bool) (q : β → m Bool)
    (hq : ∀ x, q (g x) = pure (p x)) :
    ∀ xs : List α, anyML q (xs.map g) = pure (xs.any p)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hq x, pure_bind, List.any_cons]
    cases p x with
    | false => exact anyML_pure_map g p q hq xs
    | true => rfl

private theorem mapML_pure_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁) (f₂ : α₂ → m β₂)
    (hf : ∀ x, f₂ (g x) = pure (h (f₁ x))) :
    ∀ xs : List α₁, mapML f₂ (xs.map g) = pure ((xs.map f₁).map h)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, mapML_pure_map g h f₁ f₂ hf xs, pure_bind]

private theorem foldML_rev {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ (acc xs : List α), foldML (fun x l => (pure (x :: l) : m (List α))) acc xs =
      pure (xs.reverse ++ acc)
  | acc, [] => by simp [foldML]
  | acc, x :: xs => by
    simp only [foldML, pure_bind, foldML_rev (x :: acc) xs, List.reverse_cons, List.append_assoc,
      List.singleton_append]

private theorem foldML_pure_foldl {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → β₁) (f₂ : α₂ → β₂ → m β₂)
    (hf : ∀ x b, f₂ (g x) (h b) = pure (h (f₁ x b))) :
    ∀ (b : β₁) (xs : List α₁),
      foldML f₂ (h b) (xs.map g) = pure (h (xs.foldl (fun acc x => f₁ x acc) b))
  | b, [] => rfl
  | b, x :: xs => by
    simp only [List.map_cons, List.foldl_cons, foldML, hf x b, pure_bind]
    exact foldML_pure_foldl g h f₁ f₂ hf (f₁ x b) xs

private theorem list_map_take {α β : Type} (g : α → β) (n : ℕ) (xs : List α) :
    (xs.map g).take n = (xs.take n).map g := by
  rw [List.map_take]

theorem compileExpr_eval (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o x)))
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (compileExpr M e).eval (mapEnvAux M.fSort toDen aux ρ) =
      pure (toVal M.fSort toDen t (e.eval ρ)) := by
  induction e with
  | var v =>
    simp [compileExpr, Comp.eval, Expr.eval, get_mapEnvAux]
  | unit | bool _ | nat _ | none | nil => rfl
  | add a b iha ihb | sub a b iha ihb | lt a b iha ihb | eqN a b iha ihb
  | and a b iha ihb | pair a b iha ihb | cons a b iha ihb =>
    simp only [compileExpr, Comp.eval, iha ρ, pure_bind]
    rw [Comp.wk1_eval, ihb ρ]
    simp [Expr.eval, Env.get, toVal]
  | take n l ihn ihl =>
    simp only [compileExpr, Comp.eval, ihn ρ, pure_bind]
    rw [Comp.wk1_eval, ihl ρ]
    simp [Expr.eval, Env.get, toVal, List.map_take]
  | appendL K a b iha ihb =>
    simp only [compileExpr, Comp.eval, iha ρ, pure_bind]
    rw [Comp.wk1_eval, ihb ρ]
    simp [Expr.eval, Env.get, toVal, ← List.map_append, List.map_take]
  | mulK k a iha | divK k a iha | modK k a iha | not a iha | fst a iha | snd a iha
  | inl a iha | inr a iha | some a iha | len a iha | tconst a iha =>
    simp [compileExpr, Comp.eval, iha ρ, Expr.eval, Env.get, toVal]
  | ite c a b ihc iha ihb =>
    simp only [compileExpr, Comp.eval, ihc ρ, pure_bind, Expr.eval, Env.get, toVal]
    split_ifs
    · rw [Comp.wk1_eval]; exact iha ρ
    · rw [Comp.wk1_eval]; exact ihb ρ
  | caseOpt e n s ihe ihn ihs =>
    simp only [compileExpr, Comp.eval, ihe ρ, pure_bind, Expr.eval, Env.get, toVal]
    cases e.eval ρ with
    | none =>
      simp only [Option.map_none]
      rw [Comp.wk1_eval]; exact ihn ρ
    | some x =>
      simp only [Option.map_some]
      rw [Comp.renameM_liftRen_wk1_eval]
      exact ihs (.cons x ρ)
  | caseSum e l r ihe ihl ihr =>
    simp only [compileExpr, Comp.eval, ihe ρ, pure_bind, Expr.eval, Env.get, toVal]
    cases e.eval ρ with
    | inl x =>
      simp only [Sum.map_inl]
      rw [Comp.renameM_liftRen_wk1_eval]
      exact ihl (.cons x ρ)
    | inr y =>
      simp only [Sum.map_inr]
      rw [Comp.renameM_liftRen_wk1_eval]
      exact ihr (.cons y ρ)
  | letE e b ihe ihb =>
    simp only [compileExpr, Comp.eval, ihe ρ, pure_bind, Expr.eval]
    exact ihb (.cons (e.eval ρ) ρ)
  | op o a iha =>
    simp only [compileExpr, Comp.eval, iha ρ, pure_bind, Expr.eval]
    rw [callMacroAux_eval M.fSort toDen aux ρ (M.opMacro o)]
    exact hOpE o (a.eval ρ)
  | findB K l p ihl ihp =>
    simp only [compileExpr, Comp.eval, ihl ρ, pure_bind, Expr.eval, Env.get, toVal,
      list_map_take]
    refine findML_pure_map (toVal M.fSort toDen _) (fun x => p.eval (.cons x ρ)) _ (fun x => ?_)
      ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact ihp (.cons x ρ)
  | anyB K l p ihl ihp =>
    simp only [compileExpr, Comp.eval, ihl ρ, pure_bind, Expr.eval, Env.get, toVal,
      list_map_take]
    refine anyML_pure_map (toVal M.fSort toDen _) (fun x => p.eval (.cons x ρ)) _ (fun x => ?_)
      ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact ihp (.cons x ρ)
  | mapB K l f ihl ihf =>
    simp only [compileExpr, Comp.eval, ihl ρ, pure_bind, Expr.eval, Env.get, toVal,
      list_map_take]
    refine mapML_pure_map (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x => f.eval (.cons x ρ)) _ (fun x => ?_) ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact ihf (.cons x ρ)
  | foldrB K l z f ihl ihz ihf =>
    simp only [compileExpr, Comp.eval, ihl ρ, pure_bind, Expr.eval, Env.get, toVal,
      list_map_take]
    have hrev :
        foldML (fun x acc => (pure (x :: acc) : OracleComp T _)) []
          (((l.eval ρ).take K).map (toVal M.fSort toDen _)) =
          pure ((((l.eval ρ).take K).reverse).map (toVal M.fSort toDen _)) := by
      rw [foldML_rev, List.append_nil, List.map_reverse]
    rw [hrev, pure_bind, Comp.wk2_eval, ihz ρ, pure_bind]
    have htake :
        ((((l.eval ρ).take K).reverse).map (toVal M.fSort toDen _)).take K =
          (((l.eval ρ).take K).reverse).map (toVal M.fSort toDen _) := by
      apply List.take_of_length_le
      simp [List.length_take]
    simp only [htake]
    rw [foldML_pure_foldl (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ))) _ (fun x acc => ?_)
      (z.eval ρ) (((l.eval ρ).take K).reverse)]
    · rw [List.foldl_reverse]
    · rw [Comp.renameM_liftRen2_wk3_eval]
      exact ihf (.cons x (.cons acc ρ))
  | tget m i ihm ihi =>
    simp only [compileExpr, Comp.eval, ihm ρ, pure_bind]
    rw [Comp.wk1_eval, ihi ρ]
    simp [Expr.eval, Env.get, toVal]
  | tset m i a ihm ihi iha =>
    simp only [compileExpr, Comp.eval, ihm ρ, pure_bind]
    rw [Comp.wk1_eval, ihi ρ, pure_bind]
    rw [Comp.wk2_eval, iha ρ, pure_bind]
    simp only [Expr.eval, Env.get, toVal]
    congr 1; funext j
    split_ifs <;> rfl

private theorem iterM_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (f₁ : α → m α) (f₂ : β → m β)
    (hf : ∀ a, f₂ (g a) = g <$> f₁ a) :
    ∀ (n : ℕ) (a : α), iterM f₂ n (g a) = g <$> iterM f₁ n a
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, bind_map_left, map_bind]
    exact bind_congr fun a' => iterM_map_hom g f₁ f₂ hf n a'

private theorem findML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, findML p₂ (xs.map g) = Option.map g <$> findML p₁ xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    refine bind_congr fun b => ?_
    cases b with
    | true => simp
    | false => exact findML_map_hom g p₁ p₂ hp xs

private theorem anyML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (g : α → β) (p₁ : α → m Bool) (p₂ : β → m Bool)
    (hp : ∀ x, p₂ (g x) = p₁ x) :
    ∀ xs : List α, anyML p₂ (xs.map g) = anyML p₁ xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    refine bind_congr fun b => ?_
    cases b with
    | true => rfl
    | false => exact anyML_map_hom g p₁ p₂ hp xs

private theorem mapML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → m β₁) (f₂ : α₂ → m β₂)
    (hf : ∀ x, f₂ (g x) = h <$> f₁ x) :
    ∀ xs : List α₁, mapML f₂ (xs.map g) = List.map h <$> mapML f₁ xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, bind_map_left, map_bind]
    refine bind_congr fun y => ?_
    rw [mapML_map_hom g h f₁ f₂ hf xs, bind_map_left]
    simp

private theorem foldML_map_hom {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ β₁ β₂ : Type} (g : α₁ → α₂) (h : β₁ → β₂)
    (f₁ : α₁ → β₁ → m β₁) (f₂ : α₂ → β₂ → m β₂)
    (hf : ∀ x b, f₂ (g x) (h b) = h <$> f₁ x b) :
    ∀ (b : β₁) (xs : List α₁), foldML f₂ (h b) (xs.map g) = h <$> foldML f₁ b xs
  | b, [] => by simp [foldML]
  | b, x :: xs => by
    simp only [List.map_cons, foldML, hf x b, bind_map_left, map_bind]
    exact bind_congr fun b' => foldML_map_hom g h f₁ f₂ hf b' xs

private def cfStep {m : Type → Type} [Monad m] {α : Type}
    (p : α → m Bool) (mk : α → m α) (x : α) (acc : Bool × List α) : m (Bool × List α) :=
  if acc.1 then pure (true, x :: acc.2)
  else do
    let b ← p x
    if b then do
      let x' ← mk x
      pure (true, x' :: acc.2)
    else pure (false, x :: acc.2)

private theorem foldML_cfStep_true {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (p : α → m Bool) (mk : α → m α) :
    ∀ (pfx : List α) (xs : List α),
      foldML (cfStep p mk) (true, pfx) xs = pure (true, xs.reverse ++ pfx)
  | pfx, [] => by simp [foldML]
  | pfx, x :: xs => by
    simp only [foldML, cfStep, ↓reduceIte, pure_bind, foldML_cfStep_true p mk (x :: pfx) xs,
      List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem foldML_cfStep_false {m : Type → Type} [Monad m] [LawfulMonad m]
    {α₁ α₂ : Type} (g : α₁ → α₂)
    (p₁ : α₁ → m Bool) (p₂ : α₂ → m Bool)
    (mk₁ : α₁ → α₁) (mk₂ : α₂ → m α₂)
    (hp : ∀ x, p₂ (g x) = p₁ x)
    (hm : ∀ x, mk₂ (g x) = pure (g (mk₁ x))) :
    ∀ (pfx : List α₂) (xs : List α₁),
      (foldML (cfStep p₂ mk₂) (false, pfx) (xs.map g) >>= fun st =>
        pure (st.1, st.2.reverse)) =
        (fun r => (r.1, pfx.reverse ++ r.2.map g)) <$> consumeFirstML p₁ mk₁ xs
  | pfx, [] => by simp [foldML, consumeFirstML]
  | pfx, x :: xs => by
    simp only [List.map_cons, foldML, cfStep, Bool.false_eq_true, ↓reduceIte, hp x,
      consumeFirstML, bind_assoc, map_bind]
    refine bind_congr fun b => ?_
    cases b with
    | true =>
      simp only [↓reduceIte, hm x, pure_bind, foldML_cfStep_true, map_pure]
      congr 1; ext <;> simp [List.reverse_append]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
        foldML_cfStep_false g p₁ p₂ mk₁ mk₂ hp hm (g x :: pfx) xs, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc]
      refine bind_congr fun r => ?_
      simp [List.append_assoc]

private theorem foldML_cfStep_len {α : Type}
    (p : α → OracleComp T Bool) (mk : α → OracleComp T α) (xs : List α) :
    ∀ (b : Bool) (pfx : List α),
      ∀ st ∈ support (foldML (cfStep p mk) (b, pfx) xs),
        st.2.length = xs.length + pfx.length := by
  induction xs with
  | nil =>
    intro b pfx st hst
    simp only [foldML, support_pure, Set.mem_singleton_iff] at hst
    subst hst; simp
  | cons x xs ih =>
    intro b pfx st hst
    simp only [foldML, cfStep, mem_support_bind_iff] at hst
    rcases hst with ⟨st₁, hst₁, hst⟩
    cases b with
    | true =>
      simp only [↓reduceIte, support_pure, Set.mem_singleton_iff] at hst₁
      subst hst₁
      have h := ih true (x :: pfx) st hst
      simp only [List.length_cons] at h ⊢; omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hst₁
      rcases hst₁ with ⟨bv, -, hst₁⟩
      cases bv with
      | true =>
        simp only [↓reduceIte, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hst₁
        rcases hst₁ with ⟨x', -, rfl⟩
        have h := ih true (x' :: pfx) st hst
        simp only [List.length_cons] at h ⊢; omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hst₁
        subst hst₁
        have h := ih false (x :: pfx) st hst
        simp only [List.length_cons] at h ⊢; omega

theorem compileComp_eval (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hOpE : ∀ o x,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) x) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o x)))
    (hSampE : ∀ s x,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) x) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s x))
    (hQueryE : ∀ g x,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) x) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g x <$> (liftM (T.query (I₁.enc g x)) : OracleComp T _)))
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) (ρ : Env Γ) :
    (compileComp M c).eval (mapEnvAux M.fSort toDen aux ρ) =
      toVal M.fSort toDen t <$> c.eval ρ := by
  induction c with
  | ret e =>
    simp [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE e ρ]
  | bind c k ihc ihk =>
    simp only [compileComp, Comp.eval, ihc ρ, bind_map_left, map_bind]
    exact bind_congr fun x => ihk (.cons x ρ)
  | ite b c d ihc ihd =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE b ρ,
      pure_bind, Expr.eval, Env.get, toVal]
    split_ifs
    · rw [Comp.wk1_eval]; exact ihc ρ
    · rw [Comp.wk1_eval]; exact ihd ρ
  | caseOpt e n s ihn ihs =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE e ρ,
      pure_bind, Expr.eval, Env.get, toVal]
    cases e.eval ρ with
    | none =>
      simp only [Option.map_none]
      rw [Comp.wk1_eval]; exact ihn ρ
    | some x =>
      simp only [Option.map_some]
      rw [Comp.renameM_liftRen_wk1_eval]
      exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE e ρ,
      pure_bind, Expr.eval, Env.get, toVal]
    cases e.eval ρ with
    | inl x =>
      simp only [Sum.map_inl]
      rw [Comp.renameM_liftRen_wk1_eval]
      exact ihl (.cons x ρ)
    | inr y =>
      simp only [Sum.map_inr]
      rw [Comp.renameM_liftRen_wk1_eval]
      exact ihr (.cons y ρ)
  | sample s e =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE e ρ, pure_bind]
    rw [callMacroAux_eval M.fSort toDen aux ρ (M.sampMacro s)]
    exact hSampE s (e.eval ρ)
  | query g e =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE e ρ, pure_bind]
    rw [callMacroAux_eval M.fSort toDen aux ρ (M.queryMacro g)]
    exact hQueryE g (e.eval ρ)
  | iter n e body ihb =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE e ρ,
      pure_bind, Expr.eval, Env.get]
    refine iterM_map_hom (toVal M.fSort toDen _) (fun a => body.eval (.cons a ρ)) _ (fun a => ?_)
      n (e.eval ρ)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact ihb (.cons a ρ)
  | findM K l p ihp =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE l ρ,
      pure_bind, Expr.eval, Env.get, toVal, list_map_take]
    refine findML_map_hom (toVal M.fSort toDen _) (fun x => p.eval (.cons x ρ)) _ (fun x => ?_)
      ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact (ihp (.cons x ρ)).trans (id_map _)
  | anyM K l p ihp =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE l ρ,
      pure_bind, Expr.eval, Env.get, toVal, list_map_take]
    change _ = id <$> _
    rw [id_map]
    refine anyML_map_hom (toVal M.fSort toDen _) (fun x => p.eval (.cons x ρ)) _ (fun x => ?_)
      ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact (ihp (.cons x ρ)).trans (id_map _)
  | mapM K l f ihf =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE l ρ,
      pure_bind, Expr.eval, Env.get, toVal, list_map_take]
    refine mapML_map_hom (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x => f.eval (.cons x ρ)) _ (fun x => ?_) ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen_wk1_eval]
    exact ihf (.cons x ρ)
  | @consumeFirstM _ elemT K l p mk ihp =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE l ρ,
      pure_bind, Expr.eval, Env.get, toVal, list_map_take]
    set xs := (l.eval ρ).take K
    let p₂ := fun (y : (mapTy M.fSort elemT).denote) =>
      ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ (.succ v)))).eval
        (Env.cons y
          (Env.cons (t := .prod .bool (.list (mapTy M.fSort elemT))) (false, [])
            (Env.cons (t := .list (mapTy M.fSort elemT)) ((l.eval ρ).map (toVal M.fSort toDen elemT))
              (mapEnvAux M.fSort toDen aux ρ))))
    refine Eq.trans
      (congrArg (fun m => m >>= _)
        (foldML_congr
          (g := cfStep p₂
            (fun z => (compileExpr M mk).eval (.cons z (mapEnvAux M.fSort toDen aux ρ))))
          (fun y acc => ?_) (false, []) (xs.map (toVal M.fSort toDen elemT))))
      ?_
    · unfold cfStep
      split_ifs with hacc
      · rfl
      · have hp' :
            ((compileComp M p).renameM (liftRen (fun ⦃_⦄ v => .succ (.succ v)))).eval
              (Env.cons y
                (Env.cons (t := .prod .bool (.list (mapTy M.fSort elemT))) acc
                  (Env.cons (t := .list (mapTy M.fSort elemT)) ((l.eval ρ).map (toVal M.fSort toDen elemT))
                    (mapEnvAux M.fSort toDen aux ρ)))) = p₂ y := by
          dsimp only [p₂]
          rw [Comp.renameM_liftRen_wk2_eval, Comp.renameM_liftRen_wk2_eval]
        rw [hp']
        refine bind_congr fun b => ?_
        split_ifs with hb
        · exact congrArg (· >>= fun x => pure (true, x :: acc.2))
            (Comp.renameM_eval (compileExpr M mk) fun ⦃_⦄ v => by
              cases v with
              | zero => rfl
              | succ v => rfl)
        · rfl
    · have hrev_bind :
          (foldML (cfStep p₂
            (fun z => (compileExpr M mk).eval (.cons z (mapEnvAux M.fSort toDen aux ρ))))
            (false, []) (xs.map (toVal M.fSort toDen elemT)) >>= fun st =>
            foldML (fun x l => pure (x :: l)) [] (st.2.take K) >>= fun outL =>
              pure (st.1, outL)) =
          (foldML (cfStep p₂
            (fun z => (compileExpr M mk).eval (.cons z (mapEnvAux M.fSort toDen aux ρ))))
            (false, []) (xs.map (toVal M.fSort toDen elemT)) >>= fun st =>
            pure (st.1, st.2.reverse)) := by
        refine OracleComp.bind_congr_of_forall_mem_support _ fun st hst => ?_
        have hlen := foldML_cfStep_len (T := T) p₂
          (fun z => (compileExpr M mk).eval (.cons z (mapEnvAux M.fSort toDen aux ρ)))
          (xs.map (toVal M.fSort toDen elemT)) false [] st hst
        have htk : st.2.take K = st.2 := by
          apply List.take_of_length_le
          have hxs : xs.length ≤ K := List.length_take_le K (l.eval ρ)
          simp only [List.length_map, List.length_nil, add_zero] at hlen
          omega
        rw [htk, foldML_rev, List.append_nil, pure_bind]
      rw [hrev_bind]
      have hp_hom : ∀ x, p₂ (toVal M.fSort toDen elemT x) = p.eval (.cons x ρ) := by
        intro x
        dsimp only [p₂]
        rw [Comp.renameM_liftRen_wk2_eval]
        exact (ihp (.cons x ρ)).trans (id_map _)
      have hmk_hom : ∀ x,
          (compileExpr M mk).eval
            (.cons (toVal M.fSort toDen elemT x) (mapEnvAux M.fSort toDen aux ρ)) =
            pure (toVal M.fSort toDen elemT (mk.eval (.cons x ρ))) :=
        fun x => compileExpr_eval M toDen aux hOpE mk (.cons x ρ)
      rw [foldML_cfStep_false (toVal M.fSort toDen elemT) _ p₂
        (fun x => mk.eval (.cons x ρ)) _ hp_hom hmk_hom [] xs]
      simp
  | foldM K l z f ihf =>
    simp only [compileComp, Comp.eval, compileExpr_eval M toDen aux hOpE l ρ,
      pure_bind, Expr.eval, Env.get, toVal, list_map_take]
    rw [Comp.wk1_eval, compileExpr_eval M toDen aux hOpE z ρ, pure_bind]
    refine foldML_map_hom (toVal M.fSort toDen _) (toVal M.fSort toDen _)
      (fun x acc => f.eval (.cons x (.cons acc ρ))) _ (fun x acc => ?_)
      (z.eval ρ) ((l.eval ρ).take K)
    rw [Comp.renameM_liftRen2_wk2_eval]
    exact ihf (.cons x (.cons acc ρ))

end Compile

/-! ## Reduction compiler and length-guarded wrappers -/

section CompileRed

variable {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
  {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
  {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
  {C₁ : GameCodec S₁ G} {C₂ : GameCodec S₂ G} {auxT : Ty S₂}

/-- Adapter expressions reshaping source/target reduction boundary types and game codecs. -/
structure RedAdapters (fSort : S₁.Base → Ty S₂) (O₂ : Ops S₂)
    (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G) (auxT : Ty S₂)
    (rIn₁ aIn₁ aOut₁ out₁ : Ty S₁) (rIn₂ aIn₂ aOut₂ out₂ : Ty S₂) where
  splitIn : Expr O₂ [rIn₂] (.prod (mapTy fSort rIn₁) auxT)
  adaptAIn : Expr O₂ [mapTy fSort aIn₁] aIn₂
  adaptQ : Expr O₂ [C₂.Q] (mapTy fSort C₁.Q)
  adaptR : Expr O₂ [mapTy fSort C₁.R] C₂.R
  adaptAOut : Expr O₂ [aOut₂] (mapTy fSort aOut₁)
  adaptOut : Expr O₂ [mapTy fSort out₁] out₂

/-- Compile `R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁` into
`CostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ out₂` with state `.prod (mapTy M.fSort R.σ) auxT`. -/
def compileRed (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : RedAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁) :
    CostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ out₂ where
  σ := .prod (mapTy M.fSort R.σ) auxT
  init :=
    .bind (.ret A.splitIn)
      (.bind (.ret (.snd (.var .zero)))
        (.bind (.ret (.fst (.var (.succ .zero))))
          (.bind
            (Comp.wkTop2 (compileComp M R.init))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptAIn))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ .zero)))))))))
  handle :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.handle))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ (.succ .zero))))))))))
  finish :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptAOut)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.finish))
            (.ret
              (.letE (.var .zero) (Expr.wkTop1 A.adaptOut))))))

theorem compileRed_totalQueries_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : RedAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    (q : ℕ) :
    (compileRed M A R).totalQueries w₂ ws₂ q ≤ R.totalQueries w₁ ws₁ q := by
  have hi := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.init
  have hh := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.handle
  have hf := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.finish
  have hmul : q * (compileComp M R.handle).queries w₂ ws₂ ≤ q * R.handle.queries w₁ ws₁ :=
    Nat.mul_le_mul_left q hh
  simp only [CostedReduction.totalQueries, compileRed, Comp.queries, Comp.renameM_queries,
    zero_add, add_zero]
  omega

theorem compileRed_totalCost_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : RedAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (C_0 : ℕ) (hC0 : 32 ≤ C_0)
    (hOpC : ∀ o, (M.opMacro o).cost + 1 ≤ C_0 * O₁.cost o)
    (hSampC : ∀ s, (M.sampMacro s).cost + 1 ≤ C_0 * max 1 (I₁.smp.sCost s))
    (hQueryC : ∀ g, (M.queryMacro g).cost + 1 ≤ C_0 * max 1 (I₁.qCost g))
    (q : ℕ) :
    (compileRed M A R).totalCost q ≤
      (2 * C_0) * R.init.cost + A.splitIn.cost + A.adaptAIn.cost + 24 +
      q * max I₂.uCost
        ((2 * C_0) * R.handle.cost + A.adaptQ.cost + A.adaptR.cost + C₂.codecCost + 28) +
      ((2 * C_0) * R.finish.cost + A.adaptAOut.cost + A.adaptOut.cost + 22) := by
  have hi := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.init
  have hh := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.handle
  have hf := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.finish
  have hinit :
      (compileRed M A R).init.cost ≤ (2 * C_0) * R.init.cost + A.splitIn.cost + A.adaptAIn.cost + 24 := by
    simp only [compileRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hhandle :
      (compileRed M A R).handle.cost ≤ (2 * C_0) * R.handle.cost + A.adaptQ.cost + A.adaptR.cost + 28 := by
    simp only [compileRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hfinish :
      (compileRed M A R).finish.cost ≤ (2 * C_0) * R.finish.cost + A.adaptAOut.cost + A.adaptOut.cost + 22 := by
    simp only [compileRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hmax :
      max I₂.uCost ((compileRed M A R).handle.cost + C₂.codecCost) ≤
      max I₂.uCost ((2 * C_0) * R.handle.cost + A.adaptQ.cost + A.adaptR.cost + C₂.codecCost + 28) :=
    max_le_max le_rfl (by omega)
  have hmul := Nat.mul_le_mul_left q hmax
  dsimp only [CostedReduction.totalCost]
  omega

theorem compileRed_size_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : RedAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (C_0 : ℕ) (hC0 : 32 ≤ C_0)
    (hOpS : ∀ o, (M.opMacro o).size + 1 ≤ C_0)
    (hSampS : ∀ s, (M.sampMacro s).size + 1 ≤ C_0)
    (hQueryS : ∀ g, (M.queryMacro g).size + 1 ≤ C_0) :
    (compileRed M A R).size ≤
      (2 * C_0) * R.size + A.splitIn.size + A.adaptAIn.size +
      A.adaptQ.size + A.adaptR.size + A.adaptAOut.size + A.adaptOut.size + 74 := by
  have hi := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.init
  have hh := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.handle
  have hf := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.finish
  have hinit :
      (compileRed M A R).init.size ≤
        (2 * C_0) * R.init.size + A.splitIn.size + A.adaptAIn.size + 24 := by
    simp only [compileRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hhandle :
      (compileRed M A R).handle.size ≤
        (2 * C_0) * R.handle.size + A.adaptQ.size + A.adaptR.size + 28 := by
    simp only [compileRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hfinish :
      (compileRed M A R).finish.size ≤
        (2 * C_0) * R.finish.size + A.adaptAOut.size + A.adaptOut.size + 22 := by
    simp only [compileRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  dsimp only [CostedReduction.size]
  nlinarith

private theorem simulateQ_state_hom
    {σ₁ σ₂ : Type} (proj : σ₁ → σ₂)
    {impl₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T))}
    {impl₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T))}
    (hStep : ∀ q s₁, (impl₂ q).run (proj s₁) = Prod.map id proj <$> (impl₁ q).run s₁)
    {α : Type} (oa : OracleComp (unifSpec + G) α) :
    ∀ s₁ : σ₁,
      (simulateQ impl₂ oa).run (proj s₁) = Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s₁
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    intro s₁
    simp only [simulateQ_query_bind, StateT.run_bind]
    change
      (do let p ← (impl₂ q).run (proj s₁); (simulateQ impl₂ (mx p.1)).run p.2) =
        Prod.map id proj <$>
          (do let p ← (impl₁ q).run s₁; (simulateQ impl₁ (mx p.1)).run p.2)
    rw [hStep q s₁, bind_map_left, map_bind]
    exact bind_congr fun p => ih p.1 p.2

theorem compileRed_eval (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (Ad : RedAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₂ : rIn₂.denote) (x₁ : rIn₁.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o z)))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) .nil)) = C₁.rdec t r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + G) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + G) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)) = toOut <$> adv₁ a₁)
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ y₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ y₁) .nil) = outEq y₁) :
    (compileRed M Ad R).eval adv₂ x₂ = outEq <$> R.eval adv₁ x₁ := by
  let mkSt : R.σ.denote → (compileRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  have hInit :
      (compileRed M Ad R).init.eval (.cons x₂ .nil) =
        (fun (p : (aIn₁.prod R.σ).denote) =>
          ((Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ p.1) .nil),
            mkSt p.2) : (aIn₂.prod (compileRed M Ad R).σ).denote)) <$>
          R.init.eval (.cons x₁ .nil) := by
    simp only [compileRed, Comp.eval, pure_bind, Expr.eval, Env.get, hSplit]
    rw [Comp.wkTop2_eval]
    change (do
      let x ← (compileComp M R.init).eval (mapEnvAux M.fSort toDen aux (.cons x₁ .nil))
      _) = _
    rw [compileComp_eval M toDen aux hOpE hSampE hQueryE R.init (.cons x₁ .nil),
      bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun p => ?_
    congr 1; congr 1
    dsimp only [toVal]
    exact Expr.wkTop1_eval Ad.adaptAIn _ _
  have hStep :
      ∀ (q : (unifSpec + G).Domain) (s₁ : R.σ.denote),
        ((compileRed M Ad R).impl q).run (mkSt s₁) =
          Prod.map id mkSt <$> (R.impl q).run s₁ := by
    intro q s₁
    rcases q with n | t
    · change
        (StateT.lift (I₂.fwdU n)).run (mkSt s₁) =
          Prod.map id mkSt <$> (StateT.lift (I₁.fwdU n)).run s₁
      rw [StateT.run_lift, StateT.run_lift, hFwdU n]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
    · simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, compileRed,
        Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
      have hq' :
          (Expr.wkTop1 Ad.adaptQ).eval
            (Env.cons (C₂.qenc t)
              (Env.cons aux
                (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                  (toVal M.fSort toDen R.σ s₁, aux) (Env.cons (C₂.qenc t) Env.nil)))) =
            toVal M.fSort toDen C₁.Q (C₁.qenc t) := by
        rw [Expr.wkTop1_eval]
        exact hQ t
      rw [hq', Comp.wkTop3_eval]
      have hm :
          Env.cons (toVal M.fSort toDen R.σ s₁)
            (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t)) (Env.cons aux Env.nil)) =
            mapEnvAux M.fSort toDen aux (.cons s₁ (.cons (C₁.qenc t) .nil)) := rfl
      dsimp only [compileRed, Ty.denote]
      rw [hm, compileComp_eval M toDen aux hOpE hSampE hQueryE R.handle
        (.cons s₁ (.cons (C₁.qenc t) .nil)), bind_map_left, bind_assoc, map_bind]
      refine OracleComp.bind_congr' rfl fun p => ?_
      simp only [pure_bind, map_pure, Prod.map, id_eq, toVal]
      congr 1; congr 1
      rw [Expr.wkTop1_eval]
      exact hR t p.1
  unfold CostedReduction.eval
  rw [hInit, bind_map_left, map_bind]
  refine OracleComp.bind_congr' rfl fun p => ?_
  rcases p with ⟨a₁, s₁⟩
  dsimp only
  rw [hAdv a₁, simulateQ_map, StateT.run_map,
    simulateQ_state_hom mkSt hStep (adv₁ a₁) s₁]
  simp only [bind_map_left, map_bind, Prod.map, id_eq]
  refine OracleComp.bind_congr' rfl fun p' => ?_
  rcases p' with ⟨b₁, s₁'⟩
  dsimp only
  simp only [compileRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt]
  have hb' :
      (Expr.wkTop1 Ad.adaptAOut).eval
        (Env.cons (toOut b₁)
          (Env.cons aux
            (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
              (toVal M.fSort toDen R.σ s₁', aux) (Env.cons (toOut b₁) Env.nil)))) =
        toVal M.fSort toDen aOut₁ b₁ := by
    rw [Expr.wkTop1_eval]
    exact hAOut b₁
  rw [hb', Comp.wkTop3_eval]
  have hm' :
      Env.cons (toVal M.fSort toDen R.σ s₁')
        (Env.cons (toVal M.fSort toDen aOut₁ b₁) (Env.cons aux Env.nil)) =
        mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil)) := rfl
  rw [hm', compileComp_eval M toDen aux hOpE hSampE hQueryE R.finish (.cons s₁' (.cons b₁ .nil)),
    bind_map_left, map_eq_bind_pure_comp, Function.comp_def]
  refine OracleComp.bind_congr' rfl fun y₁ => ?_
  congr 1
  rw [Expr.wkTop1_eval, hOut y₁]

def dummyRed {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    CostedReduction O I G C rIn aIn aOut out where
  σ := .unit
  init := .ret (.pair (Expr.wkClosed dfltAIn) .unit)
  handle := .ret (.pair (Expr.wkClosed dfltR) .unit)
  finish := .ret (Expr.wkClosed dfltOut)

@[simp] theorem dummyRed_totalQueries {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (q : ℕ) :
    (dummyRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) dfltAIn dfltR dfltOut).totalQueries
      w ws q = 0 := by
  simp [CostedReduction.totalQueries, dummyRed, Comp.queries]

theorem dummyRed_totalCost {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) (q : ℕ) :
    (dummyRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) dfltAIn dfltR dfltOut).totalCost q =
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 3 + C.codecCost) + (dfltOut.cost + 1) := by
  simp [CostedReduction.totalCost, dummyRed, Expr.wkClosed, Comp.cost, Expr.cost]

theorem dummyRed_size {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    (dummyRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) dfltAIn dfltR dfltOut).size =
      (dfltAIn.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) := by
  simp [CostedReduction.size, dummyRed, Expr.wkClosed, Comp.size, Expr.size]

/-- Guard `realR` behind proposition `P` (`[Decidable P]`), falling back to `dummyRed` when `¬ P`. -/
def guardRed (P : Prop) [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (realR : CostedReduction O I G C rIn aIn aOut out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    CostedReduction O I G C rIn aIn aOut out :=
  if P then realR else dummyRed dfltAIn dfltR dfltOut

@[simp] theorem guardRed_pos {P : Prop} [Decidable P] (hP : P)
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (realR : CostedReduction O I G C rIn aIn aOut out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out) :
    guardRed P realR dfltAIn dfltR dfltOut = realR := by
  simp [guardRed, hP]

theorem guardRed_gRedBounded {P : Prop} [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (realR : CostedReduction O I G C rIn aIn aOut out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R) (dfltOut : Expr O [] out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCostPos : P → realR.totalCost q ≤ costBudget)
    (hCostNeg :
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 3 + C.codecCost) + (dfltOut.cost + 1) ≤
        costBudget)
    (hSizePos : P → realR.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hSizeNeg :
      (dfltAIn.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) ≤ reductionSizeBudget)
    (hQueriesPos : P → realR.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GRedBounded (guardRed P realR dfltAIn dfltR dfltOut) wTag wSamp q qOut costBudget := by
  unfold guardRed
  split_ifs with hP
  · exact gRedBounded_of_bounds realR wTag wSamp q qOut costBudget
      (hCostPos hP) (hSizePos hP) (hQueriesPos hP) hO hS
  · apply gRedBounded_of_bounds
    · rw [dummyRed_totalCost]; exact hCostNeg
    · rw [dummyRed_size]; exact Nat.le_trans hSizeNeg (Nat.le_add_right _ _)
    · rw [dummyRed_totalQueries]; exact Nat.zero_le qOut
    · exact hO
    · exact hS

private theorem comp_one_le_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : 1 ≤ c.cost := by
  cases c with
  | sample _ a | query _ a =>
    have := CryptoVerification.E2E.Costed.Expr.one_le_cost a
    simp only [Comp.cost]; omega
  | _ =>
    simp only [Comp.cost]; omega

/-- Construct `GTwoStageBounded` from static cost, AST size, query, and size-honesty bounds. -/
theorem gTwoStageBounded_of_bounds {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hQueries : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GTwoStageBounded R wTag wSamp q qOut costBudget := by
  refine ⟨hCost, hSize, hQueries,
    CryptoVerification.E2E.Costed.costedOpsSizeHonest_of_opsSizeHonest hO,
    CryptoVerification.E2E.Costed.costedSampSizeHonest_of_sampSizeHonest hS,
    fun B hA A hfit x hx dflt => ?_⟩
  let widthB := 2 * (costBudget + 2 * q + 1) * (B + 1)
  have hWidthRing : widthB = (2 * costBudget + 4 * q + 2) * B + (2 * costBudget + 4 * q + 2) := by
    dsimp only [widthB]; ring
  have hA' : ∀ v : aOut.denote, aOut.Fits B v :=
    fun v => (CryptoVerification.E2E.Costed.costedFits_iff_fits B aOut v).1 (hA v)
  have hx' : rIn.Fits B x := (CryptoVerification.E2E.Costed.costedFits_iff_fits B rIn x).1 hx
  have hnq : R.nq q ≤ costBudget :=
    le_trans (CryptoVerification.E2E.Costed.TwoStageCostedReduction.nq_le_totalCost R q) hCost
  have hInitOne : 1 ≤ R.init.cost := comp_one_le_cost R.init
  have hFinOne : 1 ≤ R.finish.cost := comp_one_le_cost R.finish
  have hBudgetGe2 : 2 ≤ costBudget := by
    have := hCost
    dsimp only [TwoStageCostedReduction.totalCost] at this
    omega
  have hPreCost :
      q * R.handlePre.cost ≤
        q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q
      (le_trans (le_trans (le_max_left _ _) (Nat.le_add_right _ _)) (le_max_right _ _))
  have hPostCost :
      q * R.handlePost.cost ≤
        q * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left q
      (le_trans (le_trans (le_max_right _ _) (Nat.le_add_right _ _)) (le_max_right _ _))
  have hResCost : R.resume.cost ≤ max R.chDone.cost R.resume.cost := le_max_right _ _
  have hPreNq : q * R.handlePre.nq ≤ q * max R.handlePre.nq R.handlePost.nq :=
    Nat.mul_le_mul_left q (le_max_left _ _)
  have hPostNq : q * R.handlePost.nq ≤ q * max R.handlePre.nq R.handlePost.nq :=
    Nat.mul_le_mul_left q (le_max_right _ _)
  have hResNq : R.resume.nq ≤ max R.chDone.nq R.resume.nq := le_max_right _ _
  have hSumCost :
      R.init.cost + q * R.handlePre.cost + R.resume.cost + q * R.handlePost.cost + R.finish.cost ≤
        2 * costBudget := by
    have := hCost
    dsimp only [TwoStageCostedReduction.totalCost] at this
    omega
  have hSumNq1 : R.init.nq + q * R.handlePre.nq + R.resume.nq + R.finish.nq ≤ costBudget := by
    have := hnq
    dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq]
      at hPreNq hResNq this ⊢
    omega
  have hSumNqPost : q * R.handlePost.nq ≤ costBudget := by
    have := hnq
    dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq]
      at hPostNq this ⊢
    omega
  have hCoeffB :
      R.init.nq + q * R.handlePre.nq + R.resume.nq + R.finish.nq + q * R.handlePost.nq +
        2 * q + 3 ≤ 2 * costBudget + 4 * q + 2 := by
    cases q with
    | zero => simp only [Nat.zero_mul, mul_zero, add_zero] at hSumNq1 ⊢; omega
    | succ _ => omega
  dsimp only
  intro cm hcm
  obtain ⟨hChFits, hMidFits⟩ := R.fits_eval1_when hO hS B B B hA' A hfit q B x hx' dflt cm hcm
  have hB1_le :
      B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) ≤
        widthB := by
    have hL :
        B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) =
          (R.init.nq + q * R.handlePre.nq + q + 1) * B + (R.init.cost + q * R.handlePre.cost) := by
      ring
    have hMul := Nat.mul_le_mul_right B (show R.init.nq + q * R.handlePre.nq + q + 1 ≤
      2 * costBudget + 4 * q + 2 by omega)
    omega
  refine ⟨?_, ?_, fun y hy z hz => ?_⟩
  · refine (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB ch cm.1).2
      (Ty.fits_mono ?_ ch cm.1 hChFits)
    have hL :
        B + B + q * B + R.totalCost q + R.nq q * B = (R.nq q + q + 2) * B + R.totalCost q := by
      ring
    have hMul := Nat.mul_le_mul_right B (show R.nq q + q + 2 ≤ 2 * costBudget + 4 * q + 2 by omega)
    omega
  · cases hcm2 : cm.2 with
    | done a s =>
      rw [hcm2] at hMidFits
      exact (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB R.σ s).2
        (Ty.fits_mono hB1_le R.σ s hMidFits)
    | paused t c p s k =>
      rw [hcm2] at hMidFits
      exact ⟨(CryptoVerification.E2E.Costed.costedFits_iff_fits widthB ch c).2
          (Ty.fits_mono hB1_le ch c hMidFits.1),
        (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB R.π p).2
          (Ty.fits_mono hB1_le R.π p hMidFits.2.1),
        (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB R.σ s).2
          (Ty.fits_mono hB1_le R.σ s hMidFits.2.2.1)⟩
  · have hy' : rIn2.Fits B y := (CryptoVerification.E2E.Costed.costedFits_iff_fits B rIn2 y).1 hy
    have hz' := R.fits_eval2_when hO hS B B B hA' cm.2 _ hMidFits y B hy' q dflt z hz
    refine (CryptoVerification.E2E.Costed.costedFits_iff_fits widthB out z).2
      (Ty.fits_mono ?_ out z hz')
    have hL :
        B + R.init.cost + R.init.nq * B + q * (B + R.handlePre.cost + R.handlePre.nq * B) +
          B + B + q * B + (R.resume.cost + q * R.handlePost.cost + R.finish.cost) +
          (R.resume.nq + q * R.handlePost.nq + R.finish.nq) * B =
          (R.init.nq + q * R.handlePre.nq + R.resume.nq + R.finish.nq + q * R.handlePost.nq +
            2 * q + 3) * B +
          (R.init.cost + q * R.handlePre.cost + R.resume.cost + q * R.handlePost.cost +
            R.finish.cost) := by
      ring
    have hMul := Nat.mul_le_mul_right B hCoeffB
    omega

/-- Adapter expressions reshaping source/target two-stage reduction boundary types and game codecs. -/
structure TwoStageRedAdapters (fSort : S₁.Base → Ty S₂) (O₂ : Ops S₂)
    (C₁ : GameCodec S₁ G) (C₂ : GameCodec S₂ G) (auxT : Ty S₂)
    (rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁)
    (rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂) where
  splitIn : Expr O₂ [rIn₂] (.prod (mapTy fSort rIn₁) auxT)
  adaptAIn : Expr O₂ [mapTy fSort aIn₁] aIn₂
  adaptQ : Expr O₂ [C₂.Q] (mapTy fSort C₁.Q)
  adaptR : Expr O₂ [mapTy fSort C₁.R] C₂.R
  adaptAOut : Expr O₂ [aOut₂] (mapTy fSort aOut₁)
  adaptCh : Expr O₂ [mapTy fSort ch₁] ch₂
  adaptRIn2 : Expr O₂ [rIn2₂] (mapTy fSort rIn2₁)
  adaptOut : Expr O₂ [mapTy fSort out₁] out₂

/-- Compile `R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁` into
`TwoStageCostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂` with state
`.prod (mapTy M.fSort R.σ) auxT` and pause payload `mapTy M.fSort R.π`. -/
def compileTwoStageRed (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (A : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁) :
    TwoStageCostedReduction O₂ I₂ G C₂ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ where
  σ := .prod (mapTy M.fSort R.σ) auxT
  π := mapTy M.fSort R.π
  init :=
    .bind (.ret A.splitIn)
      (.bind (.ret (.snd (.var .zero)))
        (.bind (.ret (.fst (.var (.succ .zero))))
          (.bind
            (Comp.wkTop2 (compileComp M R.init))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptAIn))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ .zero)))))))))
  handlePre :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.handlePre))
            (.ret
              (.caseSum (.var .zero)
                (.inl
                  (.pair
                    (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                    (.pair (.snd (.var .zero))
                      (.var (.succ (.succ (.succ (.succ .zero))))))))
                (.inr
                  (.pair
                    (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptCh))
                    (.pair (.fst (.snd (.var .zero)))
                      (.pair (.snd (.snd (.var .zero)))
                        (.var (.succ (.succ (.succ (.succ .zero))))))))))))))
  chDone :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptAOut)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.chDone))
            (.ret
              (.letE (.var .zero) (Expr.wkTop1 A.adaptCh))))))
  resume :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ (.succ .zero)))) (Expr.wkTop1 A.adaptRIn2)))
        (.bind (.ret (.var (.succ (.succ (.succ .zero)))))
          (.bind (.ret (.fst (.var (.succ (.succ (.succ .zero))))))
            (.bind
              (Comp.wkTop4 (compileComp M R.resume))
              (.ret
                (.pair
                  (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                  (.pair (.snd (.var .zero))
                    (.var (.succ (.succ (.succ (.succ .zero))))))))))))
  handlePost :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ .zero))) (Expr.wkTop1 A.adaptQ)))
        (.bind (.ret (.fst (.var (.succ (.succ .zero)))))
          (.bind
            (Comp.wkTop3 (compileComp M R.handlePost))
            (.ret
              (.pair
                (.letE (.fst (.var .zero)) (Expr.wkTop1 A.adaptR))
                (.pair (.snd (.var .zero)) (.var (.succ (.succ (.succ .zero))))))))))
  finish :=
    .bind (.ret (.snd (.var .zero)))
      (.bind
        (.ret (.letE (.var (.succ (.succ (.succ .zero)))) (Expr.wkTop1 A.adaptRIn2)))
        (.bind
          (.ret (.letE (.var (.succ (.succ (.succ .zero)))) (Expr.wkTop1 A.adaptAOut)))
          (.bind (.ret (.fst (.var (.succ (.succ (.succ .zero))))))
            (.bind
              (Comp.wkTop4 (compileComp M R.finish))
              (.ret
                (.letE (.var .zero) (Expr.wkTop1 A.adaptOut)))))))

theorem compileTwoStageRed_totalQueries_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (A : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (w₁ : I₁.Tag → ℕ) (ws₁ : I₁.smp.Samp → ℕ)
    (w₂ : I₂.Tag → ℕ) (ws₂ : I₂.smp.Samp → ℕ)
    (hOpQ : ∀ o, (M.opMacro o).queries w₂ ws₂ = 0)
    (hSampQ : ∀ s, (M.sampMacro s).queries w₂ ws₂ ≤ ws₁ s)
    (hQueryQ : ∀ g, (M.queryMacro g).queries w₂ ws₂ ≤ w₁ g)
    (q : ℕ) :
    (compileTwoStageRed M A R).totalQueries w₂ ws₂ q ≤ R.totalQueries w₁ ws₁ q := by
  have hi := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.init
  have hpre := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.handlePre
  have hpost := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.handlePost
  have hch := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.chDone
  have hres := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.resume
  have hf := compileComp_queries_le M w₁ ws₁ w₂ ws₂ hOpQ hSampQ hQueryQ R.finish
  have hmaxH : max ((compileComp M R.handlePre).queries w₂ ws₂)
      ((compileComp M R.handlePost).queries w₂ ws₂) ≤
      max (R.handlePre.queries w₁ ws₁) (R.handlePost.queries w₁ ws₁) :=
    max_le_max hpre hpost
  have hmul := Nat.mul_le_mul_left q hmaxH
  have hmaxC : max ((compileComp M R.chDone).queries w₂ ws₂)
      ((compileComp M R.resume).queries w₂ ws₂) ≤
      max (R.chDone.queries w₁ ws₁) (R.resume.queries w₁ ws₁) :=
    max_le_max hch hres
  simp only [TwoStageCostedReduction.totalQueries, compileTwoStageRed, Comp.queries,
    Comp.renameM_queries, zero_add, add_zero]
  omega

theorem compileTwoStageRed_totalCost_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (A : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (C_0 : ℕ) (hC0 : 32 ≤ C_0)
    (hOpC : ∀ o, (M.opMacro o).cost + 1 ≤ C_0 * O₁.cost o)
    (hSampC : ∀ s, (M.sampMacro s).cost + 1 ≤ C_0 * max 1 (I₁.smp.sCost s))
    (hQueryC : ∀ g, (M.queryMacro g).cost + 1 ≤ C_0 * max 1 (I₁.qCost g))
    (q : ℕ) :
    (compileTwoStageRed M A R).totalCost q ≤
      (2 * C_0) * R.init.cost + A.splitIn.cost + A.adaptAIn.cost + 24 +
      q * max I₂.uCost
        ((2 * C_0) * max R.handlePre.cost R.handlePost.cost +
          A.adaptQ.cost + A.adaptR.cost + A.adaptCh.cost + C₂.codecCost + 32) +
      ((2 * C_0) * max R.chDone.cost R.resume.cost +
        A.adaptAOut.cost + A.adaptCh.cost + A.adaptRIn2.cost + A.adaptR.cost + 32) +
      ((2 * C_0) * R.finish.cost +
        A.adaptRIn2.cost + A.adaptAOut.cost + A.adaptOut.cost + 28) := by
  have hi := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.init
  have hpre := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.handlePre
  have hpost := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.handlePost
  have hch := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.chDone
  have hres := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.resume
  have hf := compileComp_cost_le M C_0 hC0 hOpC hSampC hQueryC R.finish
  have hinit :
      (compileTwoStageRed M A R).init.cost ≤
        (2 * C_0) * R.init.cost + A.splitIn.cost + A.adaptAIn.cost + 24 := by
    simp only [compileTwoStageRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hhandlePre :
      (compileTwoStageRed M A R).handlePre.cost ≤
        (2 * C_0) * R.handlePre.cost + A.adaptQ.cost + A.adaptR.cost + A.adaptCh.cost + 32 := by
    simp only [compileTwoStageRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hhandlePost :
      (compileTwoStageRed M A R).handlePost.cost ≤
        (2 * C_0) * R.handlePost.cost + A.adaptQ.cost + A.adaptR.cost + 28 := by
    simp only [compileTwoStageRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hchDone :
      (compileTwoStageRed M A R).chDone.cost ≤
        (2 * C_0) * R.chDone.cost + A.adaptAOut.cost + A.adaptCh.cost + 22 := by
    simp only [compileTwoStageRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hresume :
      (compileTwoStageRed M A R).resume.cost ≤
        (2 * C_0) * R.resume.cost + A.adaptRIn2.cost + A.adaptR.cost + 28 := by
    simp only [compileTwoStageRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hfinish :
      (compileTwoStageRed M A R).finish.cost ≤
        (2 * C_0) * R.finish.cost + A.adaptRIn2.cost + A.adaptAOut.cost + A.adaptOut.cost + 28 := by
    simp only [compileTwoStageRed, Comp.cost, Comp.renameM_cost, Expr.renameM_cost, Expr.cost]
    omega
  have hpre_le : (2 * C_0) * R.handlePre.cost ≤
      (2 * C_0) * max R.handlePre.cost R.handlePost.cost :=
    Nat.mul_le_mul_left _ (le_max_left _ _)
  have hpost_le : (2 * C_0) * R.handlePost.cost ≤
      (2 * C_0) * max R.handlePre.cost R.handlePost.cost :=
    Nat.mul_le_mul_left _ (le_max_right _ _)
  have hch_le : (2 * C_0) * R.chDone.cost ≤ (2 * C_0) * max R.chDone.cost R.resume.cost :=
    Nat.mul_le_mul_left _ (le_max_left _ _)
  have hres_le : (2 * C_0) * R.resume.cost ≤ (2 * C_0) * max R.chDone.cost R.resume.cost :=
    Nat.mul_le_mul_left _ (le_max_right _ _)
  have hmaxH :
      max I₂.uCost
        (max (compileTwoStageRed M A R).handlePre.cost
          (compileTwoStageRed M A R).handlePost.cost + C₂.codecCost) ≤
      max I₂.uCost
        ((2 * C_0) * max R.handlePre.cost R.handlePost.cost +
          A.adaptQ.cost + A.adaptR.cost + A.adaptCh.cost + C₂.codecCost + 32) :=
    max_le_max le_rfl (by omega)
  have hmul := Nat.mul_le_mul_left q hmaxH
  dsimp only [TwoStageCostedReduction.totalCost]
  omega

theorem compileTwoStageRed_size_le (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (A : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (C_0 : ℕ) (hC0 : 32 ≤ C_0)
    (hOpS : ∀ o, (M.opMacro o).size + 1 ≤ C_0)
    (hSampS : ∀ s, (M.sampMacro s).size + 1 ≤ C_0)
    (hQueryS : ∀ g, (M.queryMacro g).size + 1 ≤ C_0) :
    (compileTwoStageRed M A R).size ≤
      (2 * C_0) * R.size + A.splitIn.size + A.adaptAIn.size +
      2 * A.adaptQ.size + 3 * A.adaptR.size + 2 * A.adaptAOut.size +
      2 * A.adaptCh.size + 2 * A.adaptRIn2.size + A.adaptOut.size + 200 := by
  have hi := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.init
  have hpre := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.handlePre
  have hch := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.chDone
  have hres := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.resume
  have hpost := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.handlePost
  have hf := compileComp_size_le M C_0 hC0 hOpS hSampS hQueryS R.finish
  have hinit :
      (compileTwoStageRed M A R).init.size ≤
        (2 * C_0) * R.init.size + A.splitIn.size + A.adaptAIn.size + 24 := by
    simp only [compileTwoStageRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hhandlePre :
      (compileTwoStageRed M A R).handlePre.size ≤
        (2 * C_0) * R.handlePre.size + A.adaptQ.size + A.adaptR.size + A.adaptCh.size + 58 := by
    simp only [compileTwoStageRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hchDone :
      (compileTwoStageRed M A R).chDone.size ≤
        (2 * C_0) * R.chDone.size + A.adaptAOut.size + A.adaptCh.size + 22 := by
    simp only [compileTwoStageRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hresume :
      (compileTwoStageRed M A R).resume.size ≤
        (2 * C_0) * R.resume.size + A.adaptRIn2.size + A.adaptR.size + 38 := by
    simp only [compileTwoStageRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hhandlePost :
      (compileTwoStageRed M A R).handlePost.size ≤
        (2 * C_0) * R.handlePost.size + A.adaptQ.size + A.adaptR.size + 28 := by
    simp only [compileTwoStageRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hfinish :
      (compileTwoStageRed M A R).finish.size ≤
        (2 * C_0) * R.finish.size + A.adaptRIn2.size + A.adaptAOut.size + A.adaptOut.size + 28 := by
    simp only [compileTwoStageRed, Comp.size, Comp.renameM_size, Expr.renameM_size, Expr.size]
    omega
  have hdist :
      (2 * C_0) * R.init.size + (2 * C_0) * R.handlePre.size + (2 * C_0) * R.chDone.size +
        (2 * C_0) * R.resume.size + (2 * C_0) * R.handlePost.size + (2 * C_0) * R.finish.size =
        (2 * C_0) * R.size := by
    dsimp only [TwoStageCostedReduction.size]; ring
  dsimp only [TwoStageCostedReduction.size] at hdist ⊢
  omega

def compileTwoStageMid (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (Ad : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    {α₁ α₂ : Type} (fα : α₁ → α₂) (fch : ch₁.denote → ch₂.denote) :
    Mid G α₁ R.π.denote R.σ.denote ch₁.denote →
      Mid G α₂ (compileTwoStageRed M Ad R).π.denote
        (compileTwoStageRed M Ad R).σ.denote ch₂.denote
  | .done a s =>
    .done (fα a) ((toVal M.fSort toDen R.σ s, aux) : (compileTwoStageRed M Ad R).σ.denote)
  | .paused t c p s k =>
    .paused t (fch c)
      (toVal M.fSort toDen R.π p : (compileTwoStageRed M Ad R).π.denote)
      ((toVal M.fSort toDen R.σ s, aux) : (compileTwoStageRed M Ad R).σ.denote)
      (fun r => fα <$> k r)

private theorem runFuel_state_hom {α₁ α₂ : Type} (fα : α₁ → α₂)
    {σ₁ : Ty S₁} {σ₂ : Ty S₂} (proj : σ₁.denote → σ₂.denote)
    {h₁ : Comp O₁ I₁ [σ₁, C₁.Q] (.prod C₁.R σ₁)}
    {h₂ : Comp O₂ I₂ [σ₂, C₂.Q] (.prod C₂.R σ₂)}
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hStep : ∀ (t : κ) (s₁ : σ₁.denote),
      (do let p ← h₂.eval (.cons (proj s₁) (.cons (C₂.qenc t) .nil))
          pure (C₂.rdec t p.1, p.2)) =
        Prod.map id proj <$>
          (do let p ← h₁.eval (.cons s₁ (.cons (C₁.qenc t) .nil))
              pure (C₁.rdec t p.1, p.2)))
    (dflt₁ : α₁) (oa : OracleComp (unifSpec + G) α₁) :
    ∀ (fuel : ℕ) (s₁ : σ₁.denote),
      runFuel (C := C₂) h₂ (fα dflt₁) (fα <$> oa) fuel (proj s₁) =
        Prod.map fα proj <$> runFuel (C := C₁) h₁ dflt₁ oa fuel s₁ := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro fuel s₁
    simp [runFuel, construct_pure, Prod.map]
  | query_bind q mx ih =>
    intro fuel s₁
    rcases q with n | t
    · simp only [map_bind, runFuel, construct_query_bind]
      rw [hFwdU n]
      exact bind_congr fun u => ih u fuel s₁
    · cases fuel with
      | zero => simp [runFuel, construct_query_bind, Prod.map]
      | succ f =>
        rw [map_bind]
        simp only [runFuel, construct_query_bind]
        change
          (do let p ← h₂.eval (.cons (proj s₁) (.cons (C₂.qenc t) .nil))
              runFuel (C := C₂) h₂ (fα dflt₁) (fα <$> mx (C₂.rdec t p.1)) f p.2) =
          Prod.map fα proj <$>
            (do let p ← h₁.eval (.cons s₁ (.cons (C₁.qenc t) .nil))
                runFuel (C := C₁) h₁ dflt₁ (mx (C₁.rdec t p.1)) f p.2)
        have hLHS :
            (do let p ← h₂.eval (.cons (proj s₁) (.cons (C₂.qenc t) .nil))
                runFuel (C := C₂) h₂ (fα dflt₁) (fα <$> mx (C₂.rdec t p.1)) f p.2) =
            ((do let p ← h₂.eval (.cons (proj s₁) (.cons (C₂.qenc t) .nil))
                 pure (C₂.rdec t p.1, p.2)) >>= fun rs =>
              runFuel (C := C₂) h₂ (fα dflt₁) (fα <$> mx rs.1) f rs.2) := by
          simp
        have hRHS :
            (do let p ← h₁.eval (.cons s₁ (.cons (C₁.qenc t) .nil))
                runFuel (C := C₁) h₁ dflt₁ (mx (C₁.rdec t p.1)) f p.2) =
            ((do let p ← h₁.eval (.cons s₁ (.cons (C₁.qenc t) .nil))
                 pure (C₁.rdec t p.1, p.2)) >>= fun rs =>
              runFuel (C := C₁) h₁ dflt₁ (mx rs.1) f rs.2) := by
          simp
        rw [hLHS, hRHS, hStep t s₁, bind_map_left, map_bind]
        refine bind_congr fun rs => ?_
        simp only [Prod.map, id_eq]
        exact ih rs.1 f rs.2

private theorem compileTwoStageRed_run1 (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (Ad : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o z)))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) .nil)) = C₁.rdec t r₁)
    {chEq : ch₁.denote → ch₂.denote}
    (hCh : ∀ c₁ : ch₁.denote,
      Ad.adaptCh.eval (.cons (toVal M.fSort toDen ch₁ c₁) .nil) = chEq c₁)
    {α₁ α₂ : Type} (toOut : α₁ → α₂)
    (dflt₁ : α₁) (oa : OracleComp (unifSpec + G) α₁) :
    ∀ (fuel : ℕ) (s₁ : R.σ.denote),
      (compileTwoStageRed M Ad R).run1 (toOut dflt₁) (toOut <$> oa) fuel
        ((toVal M.fSort toDen R.σ s₁, aux) : (compileTwoStageRed M Ad R).σ.denote) =
        compileTwoStageMid M Ad R toDen aux toOut chEq <$> R.run1 dflt₁ oa fuel s₁ := by
  let mkSt : R.σ.denote → (compileTwoStageRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  let mkPi : R.π.denote → (compileTwoStageRed M Ad R).π.denote :=
    toVal M.fSort toDen R.π
  have hHandlePre : ∀ (t : κ) (s₁ : R.σ.denote),
      (compileTwoStageRed M Ad R).handlePre.eval (.cons (mkSt s₁) (.cons (C₂.qenc t) .nil)) =
        (fun res : (Ty.sum (.prod C₁.R R.σ) (.prod ch₁ (.prod R.π R.σ))).denote =>
          match res with
          | .inl (v₁, s₁') =>
            .inl (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R v₁) .nil), mkSt s₁')
          | .inr (c₁, p₁, s₁') =>
            .inr (chEq c₁, mkPi p₁, mkSt s₁')) <$>
          R.handlePre.eval (.cons s₁ (.cons (C₁.qenc t) .nil)) := by
    intro t s₁
    simp only [compileTwoStageRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt, mkPi]
    have hq' :
        (Expr.wkTop1 Ad.adaptQ).eval
          (Env.cons (C₂.qenc t)
            (Env.cons aux
              (Env.cons (t := .prod (mapTy M.fSort R.σ) auxT)
                (toVal M.fSort toDen R.σ s₁, aux) (Env.cons (C₂.qenc t) Env.nil)))) =
          toVal M.fSort toDen C₁.Q (C₁.qenc t) := by
      rw [Expr.wkTop1_eval]; exact hQ t
    rw [hq', Comp.wkTop3_eval]
    have hm :
        Env.cons (toVal M.fSort toDen R.σ s₁)
          (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t)) (Env.cons aux Env.nil)) =
          mapEnvAux M.fSort toDen aux (.cons s₁ (.cons (C₁.qenc t) .nil)) := rfl
    dsimp only [Ty.denote]
    rw [hm, compileComp_eval M toDen aux hOpE hSampE hQueryE R.handlePre
      (.cons s₁ (.cons (C₁.qenc t) .nil)), bind_map_left, map_eq_bind_pure_comp,
      Function.comp_def]
    refine OracleComp.bind_congr' rfl fun res => ?_
    rcases res with ⟨v₁, s₁'⟩ | ⟨c₁, p₁, s₁'⟩
    · simp only [toVal, Sum.map_inl, Expr.wkTop1_eval]
    · simp only [toVal, Sum.map_inr, Expr.wkTop1_eval, hCh c₁]
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro fuel s₁
    simp [TwoStageCostedReduction.run1, construct_pure, compileTwoStageMid]
  | query_bind q mx ih =>
    intro fuel s₁
    rcases q with n | t
    · simp only [map_bind, TwoStageCostedReduction.run1, construct_query_bind]
      rw [hFwdU n]
      exact bind_congr fun u => ih u fuel s₁
    · cases fuel with
      | zero => simp [TwoStageCostedReduction.run1, construct_query_bind, compileTwoStageMid]
      | succ f =>
        rw [map_bind]
        simp only [TwoStageCostedReduction.run1, construct_query_bind]
        rw [hHandlePre t s₁, bind_map_left, map_bind]
        refine bind_congr fun res => ?_
        rcases res with ⟨v₁, s₁'⟩ | ⟨c₁, p₁, s₁'⟩
        · dsimp only
          rw [hR t v₁]
          exact ih (C₁.rdec t v₁) f s₁'
        · simp [compileTwoStageMid, mkSt, mkPi]

private theorem compileTwoStageRed_eval1 (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (Ad : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₂ : rIn₂.denote) (x₁ : rIn₁.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o z)))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) .nil)) = C₁.rdec t r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + G) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + G) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)) = toOut <$> adv₁ a₁)
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {chEq : ch₁.denote → ch₂.denote}
    (hCh : ∀ c₁ : ch₁.denote,
      Ad.adaptCh.eval (.cons (toVal M.fSort toDen ch₁ c₁) .nil) = chEq c₁)
    (fuel : ℕ) (dflt₁ : aOut₁.denote) :
    (compileTwoStageRed M Ad R).eval1 adv₂ x₂ fuel (toOut dflt₁) =
      Prod.map chEq (compileTwoStageMid M Ad R toDen aux toOut chEq) <$>
        R.eval1 adv₁ x₁ fuel dflt₁ := by
  let mkSt : R.σ.denote → (compileTwoStageRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  have hInit :
      (compileTwoStageRed M Ad R).init.eval (.cons x₂ .nil) =
        (fun (p : (aIn₁.prod R.σ).denote) =>
          ((Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ p.1) .nil),
            mkSt p.2) : (aIn₂.prod (compileTwoStageRed M Ad R).σ).denote)) <$>
          R.init.eval (.cons x₁ .nil) := by
    simp only [compileTwoStageRed, Comp.eval, pure_bind, Expr.eval, Env.get, hSplit]
    rw [Comp.wkTop2_eval]
    change (do
      let x ← (compileComp M R.init).eval (mapEnvAux M.fSort toDen aux (.cons x₁ .nil))
      _) = _
    rw [compileComp_eval M toDen aux hOpE hSampE hQueryE R.init (.cons x₁ .nil),
      bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun p => ?_
    congr 1; congr 1
    dsimp only [toVal]
    exact Expr.wkTop1_eval Ad.adaptAIn _ _
  unfold TwoStageCostedReduction.eval1
  rw [hInit, bind_map_left, map_bind]
  refine bind_congr fun ⟨a₁, s₁⟩ => ?_
  dsimp only [mkSt]
  rw [hAdv a₁, compileTwoStageRed_run1 M Ad R toDen aux hFwdU hOpE hSampE hQueryE hQ hR hCh
    toOut dflt₁ (adv₁ a₁) fuel s₁, bind_map_left, map_bind]
  refine bind_congr fun m₁ => ?_
  cases m₁ with
  | done b₁ s₁' =>
    dsimp only [compileTwoStageMid]
    simp only [compileTwoStageRed, Comp.eval, pure_bind, Expr.eval, Env.get,
      Expr.wkTop1_eval, hAOut b₁, Comp.wkTop3_eval]
    have hm' :
        Env.cons (toVal M.fSort toDen R.σ s₁')
          (Env.cons (toVal M.fSort toDen aOut₁ b₁) (Env.cons aux Env.nil)) =
          mapEnvAux M.fSort toDen aux (.cons s₁' (.cons b₁ .nil)) := rfl
    rw [hm', compileComp_eval M toDen aux hOpE hSampE hQueryE R.chDone
      (.cons s₁' (.cons b₁ .nil)), bind_map_left, bind_assoc, map_bind]
    refine OracleComp.bind_congr' rfl fun c₁ => ?_
    simp only [pure_bind, map_pure, hCh c₁, Prod.map, compileTwoStageMid]
    rfl
  | paused t c₁ p₁ s₁' k =>
    simp [compileTwoStageMid, Prod.map]

private theorem compileTwoStageRed_eval2 (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂ : Ty S₂}
    (Ad : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁ rIn₂ aIn₂ aOut₂ ch₂ rIn2₂ out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ ch₁ rIn2₁ out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote) (aux : auxT.denote)
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o z)))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) .nil)) = C₁.rdec t r₁)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {chEq : ch₁.denote → ch₂.denote}
    (y₂ : rIn2₂.denote) (y₁ : rIn2₁.denote)
    (hRIn2 : Ad.adaptRIn2.eval (.cons y₂ .nil) = toVal M.fSort toDen rIn2₁ y₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ z₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ z₁) .nil) = outEq z₁)
    (m₁ : Mid G aOut₁.denote R.π.denote R.σ.denote ch₁.denote)
    (fuel : ℕ) (dflt₁ : aOut₁.denote) :
    (compileTwoStageRed M Ad R).eval2
        (compileTwoStageMid M Ad R toDen aux toOut chEq m₁) y₂ fuel (toOut dflt₁) =
      outEq <$> R.eval2 m₁ y₁ fuel dflt₁ := by
  let mkSt : R.σ.denote → (compileTwoStageRed M Ad R).σ.denote :=
    fun s => (toVal M.fSort toDen R.σ s, aux)
  let mkPi : R.π.denote → (compileTwoStageRed M Ad R).π.denote :=
    toVal M.fSort toDen R.π
  have hFin : ∀ (b₁ : aOut₁.denote) (s₁ : R.σ.denote),
      (compileTwoStageRed M Ad R).finish.eval
        (.cons (mkSt s₁) (.cons (toOut b₁) (.cons y₂ .nil))) =
        outEq <$> R.finish.eval (.cons s₁ (.cons b₁ (.cons y₁ .nil))) := by
    intro b₁ s₁
    simp only [compileTwoStageRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt,
      Expr.wkTop1_eval, hRIn2, hAOut b₁, Comp.wkTop4_eval]
    have hm' :
        Env.cons (toVal M.fSort toDen R.σ s₁)
          (Env.cons (toVal M.fSort toDen aOut₁ b₁)
            (Env.cons (toVal M.fSort toDen rIn2₁ y₁) (Env.cons aux Env.nil))) =
          mapEnvAux M.fSort toDen aux (.cons s₁ (.cons b₁ (.cons y₁ .nil))) := rfl
    rw [hm', compileComp_eval M toDen aux hOpE hSampE hQueryE R.finish
      (.cons s₁ (.cons b₁ (.cons y₁ .nil))), bind_map_left, map_eq_bind_pure_comp,
      Function.comp_def]
    refine OracleComp.bind_congr' rfl fun z₁ => ?_
    simp [hOut z₁]
  unfold TwoStageCostedReduction.eval2
  cases m₁ with
  | done b₁ s₁ =>
    simp only [compileTwoStageMid, pure_bind]
    exact hFin b₁ s₁
  | paused t c₁ p₁ s₁ k =>
    simp only [compileTwoStageMid]
    have hRes :
        (compileTwoStageRed M Ad R).resume.eval
          (.cons (mkSt s₁) (.cons (mkPi p₁) (.cons y₂ .nil))) =
          (fun p : (C₁.R.prod R.σ).denote =>
            (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R p.1) .nil), mkSt p.2)) <$>
            R.resume.eval (.cons s₁ (.cons p₁ (.cons y₁ .nil))) := by
      simp only [compileTwoStageRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt, mkPi,
        Expr.wkTop1_eval, hRIn2, Comp.wkTop4_eval]
      have hm' :
          Env.cons (toVal M.fSort toDen R.σ s₁)
            (Env.cons (toVal M.fSort toDen R.π p₁)
              (Env.cons (toVal M.fSort toDen rIn2₁ y₁) (Env.cons aux Env.nil))) =
            mapEnvAux M.fSort toDen aux (.cons s₁ (.cons p₁ (.cons y₁ .nil))) := rfl
      rw [hm', compileComp_eval M toDen aux hOpE hSampE hQueryE R.resume
        (.cons s₁ (.cons p₁ (.cons y₁ .nil))), bind_map_left, map_eq_bind_pure_comp,
        Function.comp_def]
      refine OracleComp.bind_congr' rfl fun ⟨v₁, s₁'⟩ => ?_
      simp [toVal]
    have hPostStep : ∀ (t' : κ) (st₁ : R.σ.denote),
        (do let p ← (compileTwoStageRed M Ad R).handlePost.eval
              (.cons (mkSt st₁) (.cons (C₂.qenc t') .nil))
            pure (C₂.rdec t' p.1, p.2)) =
          Prod.map id mkSt <$>
            (do let p ← R.handlePost.eval (.cons st₁ (.cons (C₁.qenc t') .nil))
                pure (C₁.rdec t' p.1, p.2)) := by
      intro t' st₁
      simp only [compileTwoStageRed, Comp.eval, pure_bind, Expr.eval, Env.get, mkSt,
        Expr.wkTop1_eval, hQ t', Comp.wkTop3_eval]
      have hm' :
          Env.cons (toVal M.fSort toDen R.σ st₁)
            (Env.cons (toVal M.fSort toDen C₁.Q (C₁.qenc t')) (Env.cons aux Env.nil)) =
            mapEnvAux M.fSort toDen aux (.cons st₁ (.cons (C₁.qenc t') .nil)) := rfl
      dsimp only [Ty.denote]
      rw [hm', compileComp_eval M toDen aux hOpE hSampE hQueryE R.handlePost
        (.cons st₁ (.cons (C₁.qenc t') .nil)), bind_map_left, bind_assoc, map_bind]
      refine bind_congr fun ⟨v₁, st₁'⟩ => ?_
      simp [toVal, hR t' v₁, Prod.map]
    change
      (do
        let (v, s') ← (compileTwoStageRed M Ad R).resume.eval
          (.cons (mkSt s₁) (.cons (mkPi p₁) (.cons y₂ .nil)))
        let (b, s) ← runFuel (compileTwoStageRed M Ad R).handlePost (toOut dflt₁)
          (toOut <$> k (C₂.rdec t v)) fuel s'
        (compileTwoStageRed M Ad R).finish.eval (.cons s (.cons b (.cons y₂ .nil)))) = _
    rw [hRes, bind_map_left, map_bind]
    refine bind_congr fun ⟨v₁, s₁'⟩ => ?_
    dsimp only
    rw [hR t v₁, runFuel_state_hom toOut mkSt hFwdU hPostStep dflt₁ (k (C₁.rdec t v₁)) fuel s₁',
      bind_map_left, map_bind]
    refine bind_congr fun ⟨b₁, s₁''⟩ => ?_
    dsimp only [Prod.map]
    exact hFin b₁ s₁''

theorem compileTwoStageRed_evalTwoStage1 (M : MacroBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁}
    {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (Ad : TwoStageRedAdapters M.fSort O₂ C₁ C₂ auxT
      rIn₁ aIn₁ aOut₁ .unit .unit out₁ rIn₂ aIn₂ aOut₂ .unit .unit out₂)
    (R : TwoStageCostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ .unit .unit out₁)
    (toDen : (b : S₁.Base) → S₁.den b → (M.fSort b).denote)
    (x₂ : rIn₂.denote) (x₁ : rIn₁.denote) (aux : auxT.denote)
    (hSplit : Ad.splitIn.eval (.cons x₂ .nil) = (toVal M.fSort toDen rIn₁ x₁, aux))
    (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    (hOpE : ∀ o z,
      (M.opMacro o).eval (.cons (toVal M.fSort toDen (O₁.dom o) z) (.cons aux .nil)) =
        pure (toVal M.fSort toDen (O₁.cod o) (O₁.eval o z)))
    (hSampE : ∀ s z,
      (M.sampMacro s).eval (.cons (toVal M.fSort toDen (I₁.smp.sDom s) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.smp.sTy s) <$> I₁.liftP (I₁.smp.samp s z))
    (hQueryE : ∀ g z,
      (M.queryMacro g).eval (.cons (toVal M.fSort toDen (I₁.dom g) z) (.cons aux .nil)) =
        toVal M.fSort toDen (I₁.cod g) <$>
          (I₁.dec g z <$> (liftM (T.query (I₁.enc g z)) : OracleComp T _)))
    (hQ : ∀ t : κ,
      Ad.adaptQ.eval (.cons (C₂.qenc t) .nil) = toVal M.fSort toDen C₁.Q (C₁.qenc t))
    (hR : ∀ (t : κ) (r₁ : C₁.R.denote),
      C₂.rdec t (Ad.adaptR.eval (.cons (toVal M.fSort toDen C₁.R r₁) .nil)) = C₁.rdec t r₁)
    (adv₁ : aIn₁.denote → OracleComp (unifSpec + G) aOut₁.denote)
    (adv₂ : aIn₂.denote → OracleComp (unifSpec + G) aOut₂.denote)
    (toOut : aOut₁.denote → aOut₂.denote)
    (hAdv : ∀ a₁ : aIn₁.denote,
      adv₂ (Ad.adaptAIn.eval (.cons (toVal M.fSort toDen aIn₁ a₁) .nil)) = toOut <$> adv₁ a₁)
    (hAOut : ∀ b₁ : aOut₁.denote,
      Ad.adaptAOut.eval (.cons (toOut b₁) .nil) = toVal M.fSort toDen aOut₁ b₁)
    {outEq : out₁.denote → out₂.denote}
    (hOut : ∀ z₁ : out₁.denote,
      Ad.adaptOut.eval (.cons (toVal M.fSort toDen out₁ z₁) .nil) = outEq z₁)
    (fuel : ℕ) (dflt₁ : aOut₁.denote) :
    evalTwoStage1 (compileTwoStageRed M Ad R) fuel (toOut dflt₁) adv₂ x₂ =
      outEq <$> evalTwoStage1 R fuel dflt₁ adv₁ x₁ := by
  unfold evalTwoStage1
  have hCh : ∀ c₁ : Ty.denote (S := S₁) .unit,
      Ad.adaptCh.eval (.cons (toVal M.fSort toDen .unit c₁) .nil) = () := fun _ => rfl
  have hRIn2 : Ad.adaptRIn2.eval (.cons () .nil) = toVal M.fSort toDen .unit () := rfl
  rw [compileTwoStageRed_eval1 M Ad R toDen x₂ x₁ aux hSplit hFwdU hOpE hSampE hQueryE hQ hR
    adv₁ adv₂ toOut hAdv hAOut hCh fuel dflt₁, bind_map_left, map_bind]
  refine bind_congr fun ⟨_, m₁⟩ => ?_
  exact compileTwoStageRed_eval2 M Ad R toDen aux hFwdU hOpE hSampE hQueryE hQ hR toOut hAOut
    () () hRIn2 hOut m₁ fuel dflt₁

def dummyTwoStageRed {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out where
  σ := .unit
  π := .unit
  init := .ret (.pair (Expr.wkClosed dfltAIn) .unit)
  handlePre := .ret (.inl (.pair (Expr.wkClosed dfltR) .unit))
  chDone := .ret (Expr.wkClosed dfltCh)
  resume := .ret (.pair (Expr.wkClosed dfltR) .unit)
  handlePost := .ret (.pair (Expr.wkClosed dfltR) .unit)
  finish := .ret (Expr.wkClosed dfltOut)

@[simp] theorem dummyTwoStageRed_totalQueries {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (q : ℕ) :
    (dummyTwoStageRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) (rIn2 := rIn2)
      dfltAIn dfltR dfltCh dfltOut).totalQueries w ws q = 0 := by
  simp [TwoStageCostedReduction.totalQueries, dummyTwoStageRed, Comp.queries]

theorem dummyTwoStageRed_totalCost {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) (q : ℕ) :
    (dummyTwoStageRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) (rIn2 := rIn2)
      dfltAIn dfltR dfltCh dfltOut).totalCost q =
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 4 + C.codecCost) +
        max (dfltCh.cost + 1) (dfltR.cost + 3) + (dfltOut.cost + 1) := by
  have hmax : max (dfltR.cost + 4) (dfltR.cost + 3) = dfltR.cost + 4 := by omega
  simp only [TwoStageCostedReduction.totalCost, dummyTwoStageRed, Expr.wkClosed, Comp.cost,
    Expr.cost, Expr.renameM_cost]
  rw [show dfltR.cost + 1 + 1 + 1 + 1 = dfltR.cost + 4 by omega,
    show dfltR.cost + 1 + 1 + 1 = dfltR.cost + 3 by omega, hmax]

theorem dummyTwoStageRed_size {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    (dummyTwoStageRed (I := I) (C := C) (rIn := rIn) (aOut := aOut) (rIn2 := rIn2)
      dfltAIn dfltR dfltCh dfltOut).size =
      (dfltAIn.size + 3) + (dfltR.size + 4) + (dfltCh.size + 1) +
        (dfltR.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) := by
  simp [TwoStageCostedReduction.size, dummyTwoStageRed, Expr.wkClosed, Comp.size, Expr.size]

/-- Guard `realR` behind proposition `P` (`[Decidable P]`), falling back to `dummyTwoStageRed`
when `¬ P`. -/
def guardTwoStageRed (P : Prop) [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (realR : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out :=
  if P then realR else dummyTwoStageRed dfltAIn dfltR dfltCh dfltOut

@[simp] theorem guardTwoStageRed_pos {P : Prop} [Decidable P] (hP : P)
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (realR : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out) :
    guardTwoStageRed P realR dfltAIn dfltR dfltCh dfltOut = realR := by
  simp [guardTwoStageRed, hP]

theorem guardTwoStageRed_gTwoStageBounded {P : Prop} [Decidable P]
    {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (realR : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (dfltAIn : Expr O [] aIn) (dfltR : Expr O [] C.R)
    (dfltCh : Expr O [] ch) (dfltOut : Expr O [] out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCostPos : P → realR.totalCost q ≤ costBudget)
    (hCostNeg :
      (dfltAIn.cost + 3) + q * max I.uCost (dfltR.cost + 4 + C.codecCost) +
        max (dfltCh.cost + 1) (dfltR.cost + 3) + (dfltOut.cost + 1) ≤ costBudget)
    (hSizePos : P → realR.size ≤ reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hSizeNeg :
      (dfltAIn.size + 3) + (dfltR.size + 4) + (dfltCh.size + 1) +
        (dfltR.size + 3) + (dfltR.size + 3) + (dfltOut.size + 1) ≤ reductionSizeBudget)
    (hQueriesPos : P → realR.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GTwoStageBounded (guardTwoStageRed P realR dfltAIn dfltR dfltCh dfltOut)
      wTag wSamp q qOut costBudget := by
  unfold guardTwoStageRed
  split_ifs with hP
  · exact gTwoStageBounded_of_bounds realR wTag wSamp q qOut costBudget
      (hCostPos hP) (hSizePos hP) (hQueriesPos hP) hO hS
  · apply gTwoStageBounded_of_bounds
    · rw [dummyTwoStageRed_totalCost]; exact hCostNeg
    · rw [dummyTwoStageRed_size]; exact Nat.le_trans hSizeNeg (Nat.le_add_right _ _)
    · rw [dummyTwoStageRed_totalQueries]; exact Nat.zero_le qOut
    · exact hO
    · exact hS

end CompileRed

/-! ## Retagging ASTs across `Ops` tables -/

section RetagOps

def retagExpr {S : Sig} {O₀ O₁ : Ops S}
    (fOp : O₀.Op → O₁.Op)
    (hDom : ∀ o, O₀.dom o = O₁.dom (fOp o))
    (hCod : ∀ o, O₀.cod o = O₁.cod (fOp o)) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O₀ Γ t → Expr O₁ Γ t
  | _, _, .var v => .var v
  | _, _, .unit => .unit
  | _, _, .bool b => .bool b
  | _, _, .nat n => .nat n
  | _, _, .add a b => .add (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .sub a b => .sub (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .mulK k a => .mulK k (retagExpr fOp hDom hCod a)
  | _, _, .divK k a => .divK k (retagExpr fOp hDom hCod a)
  | _, _, .modK k a => .modK k (retagExpr fOp hDom hCod a)
  | _, _, .lt a b => .lt (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .eqN a b => .eqN (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .not a => .not (retagExpr fOp hDom hCod a)
  | _, _, .and a b => .and (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .ite c a b =>
    .ite (retagExpr fOp hDom hCod c) (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .pair a b => .pair (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .fst a => .fst (retagExpr fOp hDom hCod a)
  | _, _, .snd a => .snd (retagExpr fOp hDom hCod a)
  | _, _, .inl a => .inl (retagExpr fOp hDom hCod a)
  | _, _, .inr a => .inr (retagExpr fOp hDom hCod a)
  | _, _, .none => .none
  | _, _, .some a => .some (retagExpr fOp hDom hCod a)
  | _, _, .caseOpt e n s =>
    .caseOpt (retagExpr fOp hDom hCod e) (retagExpr fOp hDom hCod n) (retagExpr fOp hDom hCod s)
  | _, _, .caseSum e l r =>
    .caseSum (retagExpr fOp hDom hCod e) (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod r)
  | _, _, .letE e b => .letE (retagExpr fOp hDom hCod e) (retagExpr fOp hDom hCod b)
  | _, _, .op o a => hCod o ▸ .op (fOp o) (hDom o ▸ retagExpr fOp hDom hCod a)
  | _, _, .nil => .nil
  | _, _, .cons x l => .cons (retagExpr fOp hDom hCod x) (retagExpr fOp hDom hCod l)
  | _, _, .len l => .len (retagExpr fOp hDom hCod l)
  | _, _, .take n l => .take (retagExpr fOp hDom hCod n) (retagExpr fOp hDom hCod l)
  | _, _, .appendL K a b =>
    .appendL K (retagExpr fOp hDom hCod a) (retagExpr fOp hDom hCod b)
  | _, _, .findB K l p => .findB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod p)
  | _, _, .anyB K l p => .anyB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod p)
  | _, _, .mapB K l f => .mapB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod f)
  | _, _, .foldrB K l z f =>
    .foldrB K (retagExpr fOp hDom hCod l) (retagExpr fOp hDom hCod z) (retagExpr fOp hDom hCod f)
  | _, _, .tconst a => .tconst (retagExpr fOp hDom hCod a)
  | _, _, .tget m i => .tget (retagExpr fOp hDom hCod m) (retagExpr fOp hDom hCod i)
  | _, _, .tset m i a =>
    .tset (retagExpr fOp hDom hCod m) (retagExpr fOp hDom hCod i) (retagExpr fOp hDom hCod a)

private theorem cast_expr_size {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t u : Ty S}
    (h : t = u) (e : Expr O Γ t) : (h ▸ e).size = e.size := by
  cases h; rfl

theorem retagExpr_size {S : Sig} {O₀ O₁ : Ops S}
    (fOp : O₀.Op → O₁.Op)
    (hDom : ∀ o, O₀.dom o = O₁.dom (fOp o))
    (hCod : ∀ o, O₀.cod o = O₁.cod (fOp o))
    (hOpSize : ∀ o, O₁.opSize (fOp o) = O₀.opSize o)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O₀ Γ t) :
    (retagExpr fOp hDom hCod e).size = e.size := by
  induction e with
  | op o a iha =>
    simp only [retagExpr, cast_expr_size, Expr.size, iha, hOpSize o]
  | _ => simp only [retagExpr, Expr.size, *]

end RetagOps

end Computational.Proofs.ReductionDsl.MacroLift
