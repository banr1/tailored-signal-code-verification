/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.Core

/-!
# Monadic Peeling and Bounded List-Loop Lemmas for `ReductionDsl`

Congruence lemmas peeling monadic binds and branches across `F <$> ·`, removing non-truncating
`List.take K` bounds, and commuting `ReductionDsl` monadic list loops with value encodings.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.ReductionDsl.PeelSim

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Env Ops Expr iterM findML anyML mapML consumeFirstML foldML)

section MonadPeel

theorem peel_bind {m : Type → Type} [Monad m] [LawfulMonad m] {α α' γ δ : Type}
    (F : γ → δ) {x : m α} {x' : m α'} (h : α' → α) {g : α → m δ} {g' : α' → m γ}
    (hx : x = h <$> x') (hg : ∀ a, g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  simp only [bind_map_left, map_bind, hg]

theorem peel_bind_same {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x x' : m α} {g : α → m δ} {g' : α → m γ}
    (hx : x = x') (hg : ∀ a, g a = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  rw [map_bind]
  exact congrArg _ (funext hg)

theorem peel_bind_support {ι : Type} {T : OracleSpec.{0, 0} ι} {α α' γ δ : Type}
    (F : γ → δ) {x : OracleComp T α} {x' : OracleComp T α'} (h : α' → α)
    {g : α → OracleComp T δ} {g' : α' → OracleComp T γ}
    (hx : x = h <$> x') (hg : ∀ a ∈ support x', g (h a) = F <$> g' a) :
    x >>= g = F <$> (x' >>= g') := by
  subst hx
  rw [bind_map_left, map_bind]
  exact bind_congr_of_forall_mem_support x' hg

theorem peel_ite {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ) {c c' : Prop}
    [Decidable c] [Decidable c'] {a b : m δ} {a' b' : m γ} (hc : c ↔ c')
    (h1 : c' → a = F <$> a') (h2 : ¬ c' → b = F <$> b') :
    (if c then a else b) = F <$> (if c' then a' else b') := by
  by_cases h : c'
  · simp only [hc.mpr h, h, ↓reduceIte]; exact h1 h
  · have h' : ¬ c := fun h' => h (hc.mp h')
    simp only [h, h', ↓reduceIte]; exact h2 h

theorem peel_ite_bool {m : Type → Type} [Functor m] {γ δ : Type} (F : γ → δ)
    {b b' : Bool} {t e : m δ} {t' e' : m γ} (hb : b = b')
    (ht : b' = true → t = F <$> t') (he : b' = false → e = F <$> e') :
    (if b then t else e) = F <$> (if b' then t' else e') := by
  subst hb
  cases b
  · simpa using he rfl
  · simpa using ht rfl

theorem peel_opt {m : Type → Type} [Functor m] {α α' γ δ : Type}
    (F : γ → δ) (h : α' → α) {o : Option α} {o' : Option α'}
    {n : m δ} {n' : m γ} {s : α → m δ} {s' : α' → m γ}
    (ho : o = o'.map h) (hn : n = F <$> n') (hs : ∀ a, s (h a) = F <$> s' a) :
    (match o with | none => n | some x => s x) =
      F <$> (match o' with | none => n' | some x => s' x) := by
  subst ho
  cases o'
  · exact hn
  · exact hs _

theorem peel_sum {m : Type → Type} [Functor m] {α α' β β' γ δ : Type}
    (F : γ → δ) (hl : α' → α) (hr : β' → β) {e : α ⊕ β} {e' : α' ⊕ β'}
    {l : α → m δ} {l' : α' → m γ} {r : β → m δ} {r' : β' → m γ}
    (he : e = Sum.map hl hr e')
    (hL : ∀ a, l (hl a) = F <$> l' a) (hR : ∀ b, r (hr b) = F <$> r' b) :
    (match e with | .inl x => l x | .inr y => r y) =
      F <$> (match e' with | .inl x => l' x | .inr y => r' y) := by
  subst he
  cases e'
  · exact hL _
  · exact hR _

theorem peel_pure {m : Type → Type} [Monad m] [LawfulMonad m] {γ δ : Type}
    (F : γ → δ) {a : δ} {a' : γ} (h : a = F a') :
    (pure a : m δ) = F <$> pure a' := by
  rw [map_pure, h]

theorem peel_pure_bind {m : Type → Type} [Monad m] [LawfulMonad m] {α γ δ : Type}
    (F : γ → δ) {x : m α} {y : α} {g : α → m δ} {z : γ}
    (hx : x = pure y) (hg : g y = pure (F z)) :
    x >>= g = F <$> pure z := by
  rw [hx, pure_bind, hg, map_pure]

theorem ite_bind {m : Type → Type} [Monad m] {α β : Type} {c : Prop} [Decidable c]
    (x y : m α) (f : α → m β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

end MonadPeel

section BoundedLoops

variable {S : Sig} {O : Ops S}

theorem take_map_of_le {α β : Type} {K : ℕ} (f : α → β) (l : List α) (h : l.length ≤ K) :
    List.take K (l.map f) = l.map f :=
  List.take_of_length_le (by simpa using h)

theorem eval_findB_of_le {Γ : List (Ty S)} {t : Ty S} (K : ℕ)
    (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) (ρ : Env Γ)
    (hle : (l.eval ρ).length ≤ K) :
    (Expr.findB K l p).eval ρ = (l.eval ρ).find? fun x => p.eval (.cons x ρ) := by
  simp only [Expr.eval, List.take_of_length_le hle]

theorem eval_anyB_of_le {Γ : List (Ty S)} {t : Ty S} (K : ℕ)
    (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) (ρ : Env Γ)
    (hle : (l.eval ρ).length ≤ K) :
    (Expr.anyB K l p).eval ρ = (l.eval ρ).any fun x => p.eval (.cons x ρ) := by
  simp only [Expr.eval, List.take_of_length_le hle]

theorem eval_mapB_of_le {Γ : List (Ty S)} {t u : Ty S} (K : ℕ)
    (l : Expr O Γ (.list t)) (f : Expr O (t :: Γ) u) (ρ : Env Γ)
    (hle : (l.eval ρ).length ≤ K) :
    (Expr.mapB K l f).eval ρ = (l.eval ρ).map fun x => f.eval (.cons x ρ) := by
  simp only [Expr.eval, List.take_of_length_le hle]

theorem eval_foldrB_of_le {Γ : List (Ty S)} {t u : Ty S} (K : ℕ)
    (l : Expr O Γ (.list t)) (z : Expr O Γ u) (f : Expr O (t :: u :: Γ) u) (ρ : Env Γ)
    (hle : (l.eval ρ).length ≤ K) :
    (Expr.foldrB K l z f).eval ρ =
      (l.eval ρ).foldr (fun x acc => f.eval (.cons x (.cons acc ρ))) (z.eval ρ) := by
  simp only [Expr.eval, List.take_of_length_le hle]

theorem iterM_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (enc : α → β) (f : β → m β) (f' : α → m α)
    (hf : ∀ a, f (enc a) = enc <$> f' a) :
    ∀ (n : ℕ) (a : α), iterM f n (enc a) = enc <$> iterM f' n a
  | 0, a => by simp [iterM]
  | n + 1, a => by
    simp only [iterM, hf a, bind_map_left, map_bind]
    exact congrArg _ (funext fun a' => iterM_map enc f f' hf n a')

theorem findML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (enc : α → β) (p : β → m Bool) (p' : α → m Bool)
    (hp : ∀ a, p (enc a) = p' a) :
    ∀ xs : List α, findML p (xs.map enc) = Option.map enc <$> findML p' xs
  | [] => by simp [findML]
  | x :: xs => by
    simp only [List.map_cons, findML, hp x, map_bind]
    refine congrArg _ (funext fun b => ?_)
    cases b
    · simpa using findML_map enc p p' hp xs
    · simp

theorem anyML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (enc : α → β) (p : β → m Bool) (p' : α → m Bool)
    (hp : ∀ a, p (enc a) = p' a) :
    ∀ xs : List α, anyML p (xs.map enc) = anyML p' xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, anyML, hp x]
    refine congrArg _ (funext fun b => ?_)
    cases b
    · exact anyML_map enc p p' hp xs
    · rfl

theorem mapML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α α' β β' : Type}
    (enc₁ : α → α') (enc₂ : β → β') (f : α' → m β') (f' : α → m β)
    (hf : ∀ a, f (enc₁ a) = enc₂ <$> f' a) :
    ∀ xs : List α, mapML f (xs.map enc₁) = List.map enc₂ <$> mapML f' xs
  | [] => by simp [mapML]
  | x :: xs => by
    simp only [List.map_cons, mapML, hf x, bind_map_left, map_bind]
    refine congrArg _ (funext fun y => ?_)
    rw [mapML_map enc₁ enc₂ f f' hf xs, bind_map_left]
    simp

theorem consumeFirstML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (enc : α → β) (p : β → m Bool) (p' : α → m Bool) (mk : β → β) (mk' : α → α)
    (hp : ∀ a, p (enc a) = p' a) (hmk : ∀ a, mk (enc a) = enc (mk' a)) :
    ∀ xs : List α,
      consumeFirstML p mk (xs.map enc) =
        Prod.map id (List.map enc) <$> consumeFirstML p' mk' xs
  | [] => by simp [consumeFirstML]
  | x :: xs => by
    simp only [List.map_cons, consumeFirstML, hp x, map_bind]
    refine congrArg _ (funext fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, consumeFirstML_map enc p p' mk mk' hp hmk xs,
        bind_map_left, map_bind, map_pure, Prod.map, id_eq, List.map_cons]
    · simp [hmk x, Prod.map]

theorem foldML_map {m : Type → Type} [Monad m] [LawfulMonad m] {α α' β β' : Type}
    (enc₁ : α → α') (enc₂ : β → β') (f : α' → β' → m β') (f' : α → β → m β)
    (hf : ∀ a acc, f (enc₁ a) (enc₂ acc) = enc₂ <$> f' a acc) :
    ∀ (acc : β) (xs : List α), foldML f (enc₂ acc) (xs.map enc₁) = enc₂ <$> foldML f' acc xs
  | acc, [] => by simp [foldML]
  | acc, x :: xs => by
    simp only [List.map_cons, foldML, hf x acc, bind_map_left, map_bind]
    exact congrArg _ (funext fun acc' => foldML_map enc₁ enc₂ f f' hf acc' xs)

end BoundedLoops

end Computational.Proofs.GameHop.ReductionDsl.PeelSim
