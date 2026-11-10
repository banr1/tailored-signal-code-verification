/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.KindedQueries
public import Computational.Proofs.ReductionDsl.Size

/-!
# Per-Query-Kind Cost, Target-Query, and Block-Size Bounds

Soundness and static-dominance lemmas for input-specialized costs (`Expr.costAt`, `Comp.costAt`,
`CostBoundedByKind`), target-query counts (`Comp.queriesAt`, `QueriesBoundedByKind`), and run-local
block-size bounds (`Fits`) on one-stage and two-stage `ReductionDsl` reductions.
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleComp

section Pointwise

variable {S : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem Expr.one_le_costAt :
    ∀ {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) (ρ : Env Γ), 1 ≤ e.costAt ρ
  | _, _, .var _, _ | _, _, .unit, _ | _, _, .bool _, _ | _, _, .none, _ | _, _, .nil, _ => le_rfl
  | _, _, .nat n, _ => one_le_bits n
  | _, _, .mulK _ a, ρ | _, _, .divK _ a, ρ | _, _, .modK _ a, ρ => by
    have := Expr.one_le_costAt a ρ; simp only [Expr.costAt]; omega
  | _, _, .op _ a, ρ => by
    have := Expr.one_le_costAt a ρ; simp only [Expr.costAt]; omega
  | _, _, .add a _, ρ | _, _, .sub a _, ρ | _, _, .lt a _, ρ | _, _, .eqN a _, ρ
  | _, _, .not a, ρ | _, _, .and a _, ρ | _, _, .ite a _ _, ρ | _, _, .pair a _, ρ
  | _, _, .fst a, ρ | _, _, .snd a, ρ | _, _, .inl a, ρ | _, _, .inr a, ρ
  | _, _, .some a, ρ | _, _, .caseOpt a _ _, ρ | _, _, .caseSum a _ _, ρ
  | _, _, .letE a _, ρ | _, _, .cons a _, ρ | _, _, .len a, ρ
  | _, _, .take a _, ρ | _, _, .appendL _ a _, ρ | _, _, .findB _ a _, ρ
  | _, _, .anyB _ a _, ρ | _, _, .mapB _ a _, ρ | _, _, .foldrB _ a _ _, ρ
  | _, _, .tconst a, ρ | _, _, .tget a _, ρ | _, _, .tset a _ _, ρ => by
    simp only [Expr.costAt]; omega

theorem Expr.costAt_le_cost :
    ∀ {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) (ρ : Env Γ), e.costAt ρ ≤ e.cost
  | _, _, .var _, _ | _, _, .unit, _ | _, _, .bool _, _ | _, _, .nat _, _
  | _, _, .none, _ | _, _, .nil, _ => le_rfl
  | _, _, .add a b, ρ | _, _, .sub a b, ρ | _, _, .lt a b, ρ | _, _, .eqN a b, ρ
  | _, _, .and a b, ρ | _, _, .pair a b, ρ | _, _, .cons a b, ρ | _, _, .take a b, ρ
  | _, _, .appendL _ a b, ρ | _, _, .tget a b, ρ => by
    have ha := Expr.costAt_le_cost a ρ; have hb := Expr.costAt_le_cost b ρ
    simp only [Expr.costAt, Expr.cost]; omega
  | _, _, .mulK _ a, ρ | _, _, .divK _ a, ρ | _, _, .modK _ a, ρ
  | _, _, .not a, ρ | _, _, .fst a, ρ | _, _, .snd a, ρ | _, _, .inl a, ρ
  | _, _, .inr a, ρ | _, _, .some a, ρ | _, _, .op _ a, ρ | _, _, .len a, ρ
  | _, _, .findB _ a _, ρ | _, _, .anyB _ a _, ρ | _, _, .mapB _ a _, ρ
  | _, _, .tconst a, ρ => by
    have ha := Expr.costAt_le_cost a ρ; simp only [Expr.costAt, Expr.cost]; omega
  | _, _, .foldrB _ l z _, ρ => by
    have hl := Expr.costAt_le_cost l ρ; have hz := Expr.costAt_le_cost z ρ
    simp only [Expr.costAt, Expr.cost]; omega
  | _, _, .tset m i a, ρ => by
    have hm := Expr.costAt_le_cost m ρ; have hi := Expr.costAt_le_cost i ρ
    have ha := Expr.costAt_le_cost a ρ; simp only [Expr.costAt, Expr.cost]; omega
  | _, _, .ite c a b, ρ => by
    have hc := Expr.costAt_le_cost c ρ
    have ha := Expr.costAt_le_cost a ρ; have hb := Expr.costAt_le_cost b ρ
    simp only [Expr.costAt, Expr.cost]; split <;> omega
  | _, _, .caseOpt e n s, ρ => by
    have he := Expr.costAt_le_cost e ρ; have hn := Expr.costAt_le_cost n ρ
    simp only [Expr.costAt, Expr.cost]
    rcases e.eval ρ with _ | x <;> dsimp only
    · omega
    · have hs := Expr.costAt_le_cost s (.cons x ρ); omega
  | _, _, .caseSum e l r, ρ => by
    have he := Expr.costAt_le_cost e ρ
    simp only [Expr.costAt, Expr.cost]
    rcases e.eval ρ with x | y <;> dsimp only
    · have hl := Expr.costAt_le_cost l (.cons x ρ); omega
    · have hr := Expr.costAt_le_cost r (.cons y ρ); omega
  | _, _, .letE e b, ρ => by
    have he := Expr.costAt_le_cost e ρ
    have hb := Expr.costAt_le_cost b (.cons (e.eval ρ) ρ)
    simp only [Expr.costAt, Expr.cost]; omega

theorem Comp.eval_eq_pure_of_pureEval? :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) (ρ : Env Γ) {x : t.denote},
      c.pureEval? ρ = some x → c.eval ρ = pure x
  | _, _, .ret e, ρ, _, h => by
    simp only [Comp.pureEval?, Option.some.injEq] at h
    subst h; rfl
  | _, _, .bind c k, ρ, _, h => by
    simp only [Comp.pureEval?, Option.bind_eq_some_iff] at h
    obtain ⟨y, hc, hk⟩ := h
    simp only [Comp.eval, Comp.eval_eq_pure_of_pureEval? c ρ hc, pure_bind,
      Comp.eval_eq_pure_of_pureEval? k (.cons y ρ) hk]
  | _, _, .ite b c d, ρ, _, h => by
    simp only [Comp.pureEval?, Comp.eval] at h ⊢
    cases hb : b.eval ρ <;> simp only [hb] at h ⊢
    · exact Comp.eval_eq_pure_of_pureEval? d ρ h
    · exact Comp.eval_eq_pure_of_pureEval? c ρ h
  | _, _, .caseOpt e n s, ρ, _, h => by
    simp only [Comp.pureEval?, Comp.eval] at h ⊢
    rcases he : e.eval ρ with _ | y <;> simp only [he] at h ⊢
    · exact Comp.eval_eq_pure_of_pureEval? n ρ h
    · exact Comp.eval_eq_pure_of_pureEval? s (.cons y ρ) h
  | _, _, .caseSum e l r, ρ, _, h => by
    simp only [Comp.pureEval?, Comp.eval] at h ⊢
    rcases he : e.eval ρ with y | y <;> simp only [he] at h ⊢
    · exact Comp.eval_eq_pure_of_pureEval? l (.cons y ρ) h
    · exact Comp.eval_eq_pure_of_pureEval? r (.cons y ρ) h
  | _, _, .sample _ _, _, _, h | _, _, .query _ _, _, _, h | _, _, .iter _ _ _, _, _, h
  | _, _, .findM _ _ _, _, _, h | _, _, .anyM _ _ _, _, _, h | _, _, .mapM _ _ _, _, _, h
  | _, _, .consumeFirstM _ _ _ _, _, _, h | _, _, .foldM _ _ _ _, _, _, h => by
    simp [Comp.pureEval?] at h

theorem Comp.queriesAt_eq_zero_of_pureEval? (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) (ρ : Env Γ) {x : t.denote},
      c.pureEval? ρ = some x → c.queriesAt w ws ρ = 0
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .bind c k, ρ, _, h => by
    simp only [Comp.pureEval?, Option.bind_eq_some_iff] at h
    obtain ⟨y, hc, hk⟩ := h
    simp only [Comp.queriesAt, hc, Comp.queriesAt_eq_zero_of_pureEval? w ws c ρ hc,
      Comp.queriesAt_eq_zero_of_pureEval? w ws k (.cons y ρ) hk]
  | _, _, .ite b c d, ρ, _, h => by
    simp only [Comp.pureEval?, Comp.queriesAt] at h ⊢
    cases hb : b.eval ρ <;> simp only [hb] at h ⊢
    · exact Comp.queriesAt_eq_zero_of_pureEval? w ws d ρ h
    · exact Comp.queriesAt_eq_zero_of_pureEval? w ws c ρ h
  | _, _, .caseOpt e n s, ρ, _, h => by
    simp only [Comp.pureEval?, Comp.queriesAt] at h ⊢
    rcases he : e.eval ρ with _ | y <;> simp only [he] at h ⊢
    · exact Comp.queriesAt_eq_zero_of_pureEval? w ws n ρ h
    · exact Comp.queriesAt_eq_zero_of_pureEval? w ws s (.cons y ρ) h
  | _, _, .caseSum e l r, ρ, _, h => by
    simp only [Comp.pureEval?, Comp.queriesAt] at h ⊢
    rcases he : e.eval ρ with y | y <;> simp only [he] at h ⊢
    · exact Comp.queriesAt_eq_zero_of_pureEval? w ws l (.cons y ρ) h
    · exact Comp.queriesAt_eq_zero_of_pureEval? w ws r (.cons y ρ) h
  | _, _, .sample _ _, _, _, h | _, _, .query _ _, _, _, h | _, _, .iter _ _ _, _, _, h
  | _, _, .findM _ _ _, _, _, h | _, _, .anyM _ _ _, _, _, h | _, _, .mapM _ _ _, _, _, h
  | _, _, .consumeFirstM _ _ _ _, _, _, h | _, _, .foldM _ _ _ _, _, _, h => by
    simp [Comp.pureEval?] at h

theorem Comp.costAt_le_cost :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) (ρ : Env Γ), c.costAt ρ ≤ c.cost
  | _, _, .ret e, ρ => by
    have he := e.costAt_le_cost ρ; simp only [Comp.costAt, Comp.cost]; omega
  | _, _, .bind c k, ρ => by
    have hc := c.costAt_le_cost ρ
    simp only [Comp.costAt, Comp.cost]
    rcases c.pureEval? ρ with _ | x <;> dsimp only
    · omega
    · have hk := k.costAt_le_cost (.cons x ρ); omega
  | _, _, .ite b c d, ρ => by
    have hb := b.costAt_le_cost ρ
    have hc := c.costAt_le_cost ρ; have hd := d.costAt_le_cost ρ
    simp only [Comp.costAt, Comp.cost]; split <;> omega
  | _, _, .caseOpt e n s, ρ => by
    have he := e.costAt_le_cost ρ; have hn := n.costAt_le_cost ρ
    simp only [Comp.costAt, Comp.cost]
    rcases e.eval ρ with _ | x <;> dsimp only
    · omega
    · have hs := s.costAt_le_cost (.cons x ρ); omega
  | _, _, .caseSum e l r, ρ => by
    have he := e.costAt_le_cost ρ
    simp only [Comp.costAt, Comp.cost]
    rcases e.eval ρ with x | y <;> dsimp only
    · have hl := l.costAt_le_cost (.cons x ρ); omega
    · have hr := r.costAt_le_cost (.cons y ρ); omega
  | _, _, .sample _ e, ρ | _, _, .query _ e, ρ | _, _, .iter _ e _, ρ
  | _, _, .findM _ e _, ρ | _, _, .anyM _ e _, ρ | _, _, .mapM _ e _, ρ
  | _, _, .consumeFirstM _ e _ _, ρ => by
    have he := e.costAt_le_cost ρ; simp only [Comp.costAt, Comp.cost]; omega
  | _, _, .foldM _ l z _, ρ => by
    have hl := l.costAt_le_cost ρ; have hz := z.costAt_le_cost ρ
    simp only [Comp.costAt, Comp.cost]; omega

theorem Comp.queriesAt_le_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) (ρ : Env Γ),
      c.queriesAt w ws ρ ≤ c.queries w ws
  | _, _, .ret _, _ | _, _, .sample _ _, _ | _, _, .query _ _, _
  | _, _, .iter _ _ _, _ | _, _, .findM _ _ _, _ | _, _, .anyM _ _ _, _
  | _, _, .mapM _ _ _, _ | _, _, .consumeFirstM _ _ _ _, _ | _, _, .foldM _ _ _ _, _ => le_rfl
  | _, _, .bind c k, ρ => by
    have hc := c.queriesAt_le_queries w ws ρ
    simp only [Comp.queriesAt, Comp.queries]
    rcases c.pureEval? ρ with _ | x <;> dsimp only
    · omega
    · have hk := k.queriesAt_le_queries w ws (.cons x ρ); omega
  | _, _, .ite _ c d, ρ => by
    have hc := c.queriesAt_le_queries w ws ρ; have hd := d.queriesAt_le_queries w ws ρ
    simp only [Comp.queriesAt, Comp.queries]; split <;> omega
  | _, _, .caseOpt e n s, ρ => by
    have hn := n.queriesAt_le_queries w ws ρ
    simp only [Comp.queriesAt, Comp.queries]
    rcases e.eval ρ with _ | x <;> dsimp only
    · omega
    · have hs := s.queriesAt_le_queries w ws (.cons x ρ); omega
  | _, _, .caseSum e l r, ρ => by
    simp only [Comp.queriesAt, Comp.queries]
    rcases e.eval ρ with x | y <;> dsimp only
    · have hl := l.queriesAt_le_queries w ws (.cons x ρ); omega
    · have hr := r.queriesAt_le_queries w ws (.cons y ρ); omega

theorem Comp.costAt_caseSum_inl {Γ : List (Ty S)} {t u v : Ty S}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v)
    (ρ : Env Γ) {x : t.denote} (h : e.eval ρ = .inl x) :
    (Comp.caseSum e l r).costAt ρ = e.costAt ρ + l.costAt (.cons x ρ) + 1 := by
  simp [Comp.costAt, h]

theorem Comp.costAt_caseSum_inr {Γ : List (Ty S)} {t u v : Ty S}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v)
    (ρ : Env Γ) {y : u.denote} (h : e.eval ρ = .inr y) :
    (Comp.caseSum e l r).costAt ρ = e.costAt ρ + r.costAt (.cons y ρ) + 1 := by
  simp [Comp.costAt, h]

theorem Comp.queriesAt_caseSum_inl (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty S)} {t u v : Ty S}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v)
    (ρ : Env Γ) {x : t.denote} (h : e.eval ρ = .inl x) :
    (Comp.caseSum e l r).queriesAt w ws ρ = l.queriesAt w ws (.cons x ρ) := by
  simp [Comp.queriesAt, h]

theorem Comp.queriesAt_caseSum_inr (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List (Ty S)} {t u v : Ty S}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v)
    (ρ : Env Γ) {y : u.denote} (h : e.eval ρ = .inr y) :
    (Comp.caseSum e l r).queriesAt w ws ρ = r.queriesAt w ws (.cons y ρ) := by
  simp [Comp.queriesAt, h]

theorem Comp.costAt_bind_of_pureEval? {Γ : List (Ty S)} {t u : Ty S}
    (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) {x : t.denote}
    (h : c.pureEval? ρ = some x) :
    (Comp.bind c k).costAt ρ = c.costAt ρ + k.costAt (.cons x ρ) + 1 := by
  simp [Comp.costAt, h]

end Pointwise

section FinSum

theorem list_ofFn_sum_mul_le : ∀ {n : ℕ} (qKind f : Fin n → ℕ) (M q : ℕ),
    (∀ i, f i ≤ M) → (List.ofFn qKind).sum ≤ q →
    (List.ofFn fun i => qKind i * f i).sum ≤ q * M
  | 0, _, _, _, _, _, _ => by simp
  | n + 1, qKind, f, M, q, hf, hq => by
    simp only [List.ofFn_succ, List.sum_cons] at hq ⊢
    have h0 : qKind 0 * f 0 ≤ qKind 0 * M := Nat.mul_le_mul_left _ (hf 0)
    have hrec := list_ofFn_sum_mul_le (fun i => qKind i.succ) (fun i => f i.succ) M
      (List.ofFn fun i => qKind i.succ).sum (fun i => hf i.succ) le_rfl
    have htot : (qKind 0 + (List.ofFn fun i => qKind i.succ).sum) * M ≤ q * M :=
      Nat.mul_le_mul_right M hq
    rw [Nat.add_mul] at htot
    omega

theorem list_ofFn_sum_mul_mono_right : ∀ {n : ℕ} (qKind f g : Fin n → ℕ),
    (∀ i, f i ≤ g i) →
    (List.ofFn fun i => qKind i * f i).sum ≤ (List.ofFn fun i => qKind i * g i).sum
  | 0, _, _, _, _ => le_rfl
  | n + 1, qKind, f, g, hfg => by
    simp only [List.ofFn_succ, List.sum_cons]
    have h0 := Nat.mul_le_mul_left (qKind 0) (hfg 0)
    have hrec := list_ofFn_sum_mul_mono_right (fun i => qKind i.succ) (fun i => f i.succ)
      (fun i => g i.succ) (fun i => hfg i.succ)
    omega

theorem list_ofFn_sum_mul_add_right : ∀ {n : ℕ} (qKind f g : Fin n → ℕ),
    (List.ofFn fun i => qKind i * (f i + g i)).sum =
      (List.ofFn fun i => qKind i * f i).sum + (List.ofFn fun i => qKind i * g i).sum
  | 0, _, _, _ => rfl
  | n + 1, qKind, f, g => by
    simp only [List.ofFn_succ, List.sum_cons, Nat.mul_add]
    have hrec := list_ofFn_sum_mul_add_right (fun i => qKind i.succ) (fun i => f i.succ)
      (fun i => g i.succ)
    simp only [Nat.mul_add] at hrec
    omega

theorem list_ofFn_sum_mul_const : ∀ {n : ℕ} (qKind : Fin n → ℕ) (c : ℕ),
    (List.ofFn fun i => qKind i * c).sum = (List.ofFn qKind).sum * c
  | 0, _, _ => by simp
  | n + 1, qKind, c => by
    simp only [List.ofFn_succ, List.sum_cons, Nat.add_mul,
      list_ofFn_sum_mul_const (fun i => qKind i.succ)]

theorem list_ofFn_sum_sub_add_mul : ∀ {n : ℕ} (qKind qRem D : Fin n → ℕ),
    (∀ i, qRem i ≤ qKind i) →
    (List.ofFn fun i => (qKind i - qRem i) * D i).sum +
      (List.ofFn fun i => qRem i * D i).sum =
      (List.ofFn fun i => qKind i * D i).sum
  | 0, _, _, _, _ => rfl
  | n + 1, qKind, qRem, D, hle => by
    simp only [List.ofFn_succ, List.sum_cons]
    have h0 : (qKind 0 - qRem 0) * D 0 + qRem 0 * D 0 = qKind 0 * D 0 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (hle 0)]
    have hrec := list_ofFn_sum_sub_add_mul (fun i => qKind i.succ) (fun i => qRem i.succ)
      (fun i => D i.succ) (fun i => hle i.succ)
    omega

theorem list_ofFn_sum_zero : ∀ (n : ℕ), (List.ofFn fun _ : Fin n => 0).sum = 0
  | 0 => rfl
  | n + 1 => by simp [List.ofFn_succ]

theorem add_list_ofFn_update_pred_mul : ∀ {n : ℕ} (qKind f : Fin n → ℕ) (i₀ : Fin n),
    0 < qKind i₀ →
    f i₀ + (List.ofFn fun i => Function.update qKind i₀ (qKind i₀ - 1) i * f i).sum =
      (List.ofFn fun i => qKind i * f i).sum
  | 0, _, _, i₀, _ => i₀.elim0
  | n + 1, qKind, f, i₀, hpos => by
    cases i₀ using Fin.cases with
    | zero =>
      simp only [List.ofFn_succ, List.sum_cons, Function.update_self]
      have hupd : (fun i : Fin n => Function.update qKind 0 (qKind 0 - 1) i.succ * f i.succ) =
          fun i : Fin n => qKind i.succ * f i.succ := by
        ext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
      rw [hupd]
      obtain ⟨m, hm⟩ : ∃ m, qKind 0 = m + 1 := ⟨qKind 0 - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, Nat.succ_mul]
      omega
    | succ j =>
      simp only [List.ofFn_succ, List.sum_cons]
      have h0 : Function.update qKind j.succ (qKind j.succ - 1) 0 = qKind 0 := by
        rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
      have hsucc : (fun i : Fin n =>
          Function.update qKind j.succ (qKind j.succ - 1) i.succ * f i.succ) =
          fun i : Fin n =>
            Function.update (fun k : Fin n => qKind k.succ) j (qKind j.succ - 1) i * f i.succ := by
        ext i
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne (Fin.succ_inj.ne.mpr hij), Function.update_of_ne hij]
      rw [h0, hsucc]
      have hrec := add_list_ofFn_update_pred_mul (fun k : Fin n => qKind k.succ)
        (fun k : Fin n => f k.succ) j hpos
      omega

end FinSum

/-! ## Per-kind dominance -/

section Dominance

variable {S : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}
  {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}

theorem CostedReduction.validKindCosts_const (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (kind : κ → Fin n) :
    R.ValidKindCosts kind (fun _ => R.handle.cost) :=
  fun s t => R.handle.costAt_le_cost (.cons s (.cons (C.qenc t) .nil))

theorem CostedReduction.totalCostByKind_le_totalCost (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (hCost qKind : Fin n → ℕ) (q : ℕ)
    (hh : ∀ i, hCost i ≤ R.handle.cost) (hq : (List.ofFn qKind).sum ≤ q) :
    R.totalCostByKind hCost qKind ≤ R.totalCost q := by
  unfold CostedReduction.totalCostByKind CostedReduction.totalCost
  have hstep : ∀ i, max I.uCost (hCost i + C.codecCost) ≤
      max I.uCost (R.handle.cost + C.codecCost) := fun i => by
    have := hh i; omega
  have hsum := list_ofFn_sum_mul_le qKind (fun i => max I.uCost (hCost i + C.codecCost))
    (max I.uCost (R.handle.cost + C.codecCost)) q hstep hq
  omega

theorem CostedReduction.costBoundedByKind_of_totalCost_le
    (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) {q B : ℕ}
    (hq : (List.ofFn qKind).sum ≤ q) (hB : R.totalCost q ≤ B) :
    R.CostBoundedByKind kind qKind B :=
  ⟨fun _ => R.handle.cost, R.validKindCosts_const kind,
    le_trans (R.totalCostByKind_le_totalCost _ qKind q (fun _ => le_rfl) hq) hB⟩

theorem CostedReduction.validKindQueries_const (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) :
    R.ValidKindQueries w ws kind (fun _ => R.handle.queries w ws) :=
  fun s t => R.handle.queriesAt_le_queries w ws (.cons s (.cons (C.qenc t) .nil))

theorem CostedReduction.totalQueriesByKind_le_totalQueries
    (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (hQ qKind : Fin n → ℕ) (q : ℕ)
    (hh : ∀ i, hQ i ≤ R.handle.queries w ws) (hq : (List.ofFn qKind).sum ≤ q) :
    R.totalQueriesByKind w ws hQ qKind ≤ R.totalQueries w ws q := by
  unfold CostedReduction.totalQueriesByKind CostedReduction.totalQueries
  have hsum := list_ofFn_sum_mul_le qKind hQ (R.handle.queries w ws) q hh hq
  omega

theorem CostedReduction.queriesBoundedByKind_of_totalQueries_le
    (R : CostedReduction O I G C rIn aIn aOut out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ)
    {q Q : ℕ} (hq : (List.ofFn qKind).sum ≤ q) (hQ : R.totalQueries w ws q ≤ Q) :
    R.QueriesBoundedByKind w ws kind qKind Q :=
  ⟨fun _ => R.handle.queries w ws, R.validKindQueries_const w ws kind,
    le_trans (R.totalQueriesByKind_le_totalQueries w ws _ qKind q (fun _ => le_rfl) hq) hQ⟩

theorem TwoStageCostedReduction.validKindCosts_const
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) :
    R.ValidKindCosts kind (fun _ => max R.handlePre.cost R.handlePost.cost) :=
  fun s t => ⟨le_trans (R.handlePre.costAt_le_cost (.cons s (.cons (C.qenc t) .nil)))
      (le_max_left _ _),
    le_trans (R.handlePost.costAt_le_cost (.cons s (.cons (C.qenc t) .nil)))
      (le_max_right _ _)⟩

theorem TwoStageCostedReduction.totalCostByKind_le_totalCost
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (hCost qKind : Fin n → ℕ) (q : ℕ)
    (hh : ∀ i, hCost i ≤ max R.handlePre.cost R.handlePost.cost)
    (hq : (List.ofFn qKind).sum ≤ q) :
    R.totalCostByKind hCost qKind ≤ R.totalCost q := by
  unfold TwoStageCostedReduction.totalCostByKind TwoStageCostedReduction.totalCost
  have hstep : ∀ i, max I.uCost (hCost i + C.codecCost) ≤
      max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) := fun i => by
    have := hh i; omega
  have hsum := list_ofFn_sum_mul_le qKind (fun i => max I.uCost (hCost i + C.codecCost))
    (max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost)) q hstep hq
  omega

theorem TwoStageCostedReduction.costBoundedByKind_of_totalCost_le
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) {q B : ℕ}
    (hq : (List.ofFn qKind).sum ≤ q) (hB : R.totalCost q ≤ B) :
    R.CostBoundedByKind kind qKind B :=
  ⟨fun _ => max R.handlePre.cost R.handlePost.cost, R.validKindCosts_const kind,
    le_trans (R.totalCostByKind_le_totalCost _ qKind q (fun _ => le_rfl) hq) hB⟩

theorem TwoStageCostedReduction.validKindQueries_const
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) :
    R.ValidKindQueries w ws kind
      (fun _ => max (R.handlePre.queries w ws) (R.handlePost.queries w ws)) :=
  fun s t => ⟨le_trans (R.handlePre.queriesAt_le_queries w ws (.cons s (.cons (C.qenc t) .nil)))
      (le_max_left _ _),
    le_trans (R.handlePost.queriesAt_le_queries w ws (.cons s (.cons (C.qenc t) .nil)))
      (le_max_right _ _)⟩

theorem TwoStageCostedReduction.totalQueriesByKind_le_totalQueries
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (hQ qKind : Fin n → ℕ) (q : ℕ)
    (hh : ∀ i, hQ i ≤ max (R.handlePre.queries w ws) (R.handlePost.queries w ws))
    (hq : (List.ofFn qKind).sum ≤ q) :
    R.totalQueriesByKind w ws hQ qKind ≤ R.totalQueries w ws q := by
  unfold TwoStageCostedReduction.totalQueriesByKind TwoStageCostedReduction.totalQueries
  have hsum := list_ofFn_sum_mul_le qKind hQ
    (max (R.handlePre.queries w ws) (R.handlePost.queries w ws)) q hh hq
  omega

theorem TwoStageCostedReduction.queriesBoundedByKind_of_totalQueries_le
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ)
    {q Q : ℕ} (hq : (List.ofFn qKind).sum ≤ q) (hQ : R.totalQueries w ws q ≤ Q) :
    R.QueriesBoundedByKind w ws kind qKind Q :=
  ⟨fun _ => max (R.handlePre.queries w ws) (R.handlePost.queries w ws),
    R.validKindQueries_const w ws kind,
    le_trans (R.totalQueriesByKind_le_totalQueries w ws _ qKind q (fun _ => le_rfl) hq) hQ⟩

end Dominance

/-! ## Per-kind target-query soundness -/

section QuerySoundness

variable {S : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem Comp.queryBound_eval_at (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ)
    (ws : I.smp.Samp → ℕ) (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ ρ : Env Γ, (c.eval ρ).IsQueryBoundP P (c.queriesAt w ws ρ) := by
  induction c with
  | ret e => intro ρ; simp [Comp.eval, Comp.queriesAt]
  | bind c k ihc ihk =>
    intro ρ
    simp only [Comp.eval, Comp.queriesAt]
    split
    · next x hx =>
      rw [Comp.eval_eq_pure_of_pureEval? c ρ hx, pure_bind]
      exact (ihk (.cons x ρ)).mono (by omega)
    · exact isQueryBoundP_bind (ihc ρ) (fun x _ => Comp.queryBound_eval P w ws hw hU k (.cons x ρ))
  | ite b c d ihc ihd =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    split
    · exact ihc ρ
    · exact ihd ρ
  | caseOpt e n s ihn ihs =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    rcases e.eval ρ with _ | x
    · exact ihn ρ
    · exact ihs (.cons x ρ)
  | caseSum e l r ihl ihr =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    rcases e.eval ρ with x | y
    · exact ihl (.cons x ρ)
    · exact ihr (.cons y ρ)
  | sample s e =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact (liftP_queryBound P hU _).mono (Nat.zero_le _)
  | query g e =>
    intro ρ
    simp only [Comp.eval, Comp.queriesAt, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    intro h; have := hw g _ h; omega
  | iter n e body _ =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact iterM_queryBound _ _ (fun a => Comp.queryBound_eval P w ws hw hU body (.cons a ρ)) n _
  | findM K l p _ =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact (findML_queryBound _ (fun x => Comp.queryBound_eval P w ws hw hU p (.cons x ρ)) _).mono
      (take_mul_le _ _ _)
  | anyM K l p _ =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact (anyML_queryBound _ (fun x => Comp.queryBound_eval P w ws hw hU p (.cons x ρ)) _).mono
      (take_mul_le _ _ _)
  | mapM K l f _ =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact (mapML_queryBound _ (fun x => Comp.queryBound_eval P w ws hw hU f (.cons x ρ)) _).mono
      (take_mul_le _ _ _)
  | consumeFirstM K l p mk _ =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact (consumeFirstML_queryBound _ _
      (fun x => Comp.queryBound_eval P w ws hw hU p (.cons x ρ)) _).mono (take_mul_le _ _ _)
  | foldM K l z f _ =>
    intro ρ; simp only [Comp.eval, Comp.queriesAt]
    exact (foldML_queryBound _
      (fun x b => Comp.queryBound_eval P w ws hw hU f (.cons x (.cons b ρ))) _ _).mono
      (take_mul_le _ _ _)

/-- Predicate on `(unifSpec + G).Domain` selecting `G`-queries in bucket `i` under `kind` (coins
are never selected). -/
def isQueryKind {G : OracleSpec κ} {n : ℕ} (kind : κ → Fin n) (i : Fin n) :
    (unifSpec + G).Domain → Prop
  | .inl _ => False
  | .inr t => kind t = i

instance {G : OracleSpec κ} {n : ℕ} (kind : κ → Fin n) (i : Fin n) :
    DecidablePred (isQueryKind (G := G) kind i) := fun q =>
  match q with
  | .inl _ => isFalse id
  | .inr t => decEq (kind t) i

theorem isQueryBoundP_coin_byKind {G : OracleSpec κ} {α : Type} {n : ℕ}
    {kind : κ → Fin n} {qKind : Fin n → ℕ} {m : ℕ}
    {mx : Fin (m + 1) → OracleComp (unifSpec + G) α}
    (h : ∀ i, (liftM ((unifSpec + G).query (.inl m)) >>= mx).IsQueryBoundP
      (isQueryKind (G := G) kind i) (qKind i))
    (u : Fin (m + 1)) :
    ∀ i, (mx u).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i) := by
  intro i
  have hi := h i
  rw [isQueryBoundP_query_bind_iff] at hi
  simpa [isQueryKind] using hi.2 u

theorem isQueryBoundP_game_byKind {G : OracleSpec κ} {α : Type} {n : ℕ}
    {kind : κ → Fin n} {qKind : Fin n → ℕ} {t : κ}
    {mx : G t → OracleComp (unifSpec + G) α}
    (h : ∀ i, (liftM ((unifSpec + G).query (.inr t)) >>= mx).IsQueryBoundP
      (isQueryKind (G := G) kind i) (qKind i)) :
    0 < qKind (kind t) ∧
    ∀ (u : G t) (i : Fin n),
      (mx u).IsQueryBoundP (isQueryKind (G := G) kind i)
        (Function.update qKind (kind t) (qKind (kind t) - 1) i) := by
  have hkt := h (kind t)
  rw [isQueryBoundP_query_bind_iff] at hkt
  have h0 := hkt.1.resolve_left (by simp [isQueryKind])
  refine ⟨h0, fun u i => ?_⟩
  have hi := h i
  rw [isQueryBoundP_query_bind_iff] at hi
  have hiu := hi.2 u
  by_cases hti : kind t = i
  · subst hti
    simpa [isQueryKind] using hiu
  · have hne : i ≠ kind t := Ne.symm hti
    rw [Function.update_of_ne hne]
    simpa [isQueryKind, hti] using hiu

theorem simulateQ_run_StateT_byKind {G : OracleSpec κ} {σ α : Type}
    {P : ι → Prop} [DecidablePred P] {n : ℕ} (kind : κ → Fin n) (hQ : Fin n → ℕ)
    {impl : QueryImpl (unifSpec + G) (StateT σ (OracleComp T))}
    (hCoin : ∀ m s, ((impl (.inl m)).run s).IsQueryBoundP P 0)
    (hGame : ∀ t s, ((impl (.inr t)).run s).IsQueryBoundP P (hQ (kind t))) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qKind : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i)) →
      ∀ s, ((simulateQ impl oa).run s).IsQueryBoundP P
        (List.ofFn fun i => qKind i * hQ i).sum := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => intro qKind _ s; simp [simulateQ_pure]
  | query_bind q mx ih =>
    intro qKind hA s
    rw [simulateQ_query_bind, StateT.run_bind]
    cases q with
    | inl m =>
      have hcont := isQueryBoundP_coin_byKind hA
      exact (isQueryBoundP_bind (hCoin m s) (fun x _ => ih x.1 (hcont x.1) x.2)).mono (by omega)
    | inr t =>
      obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byKind hA
      have hbind := isQueryBoundP_bind (hGame t s) (fun x _ => ih x.1 (hcont x.1) x.2)
      exact hbind.mono (le_of_eq (add_list_ofFn_update_pred_mul qKind hQ (kind t) hpos))

theorem CostedReduction.queryBound_eval_byKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ m, (I.fwdU m).IsQueryBoundP P 0)
    {n : ℕ} (kind : κ → Fin n) (hQ qKind : Fin n → ℕ)
    (hValid : R.ValidKindQueries w ws kind hQ)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i))
    (x : rIn.denote) :
    (R.eval A x).IsQueryBoundP P (R.totalQueriesByKind w ws hQ qKind) := by
  have hCoin : ∀ m s, ((R.impl (.inl m)).run s).IsQueryBoundP P 0 := by
    intro m s
    have := isQueryBoundP_bind (n := 0) (m := 0) (hU m)
      (fun a _ => isQueryBoundP_pure (spec := T) P (a, s) 0)
    simpa [CostedReduction.impl, handlerImpl] using this
  have hGame : ∀ t s, ((R.impl (.inr t)).run s).IsQueryBoundP P (hQ (kind t)) := by
    intro t s
    have hh := (Comp.queryBound_eval_at P w ws hw hU R.handle
      (.cons s (.cons (C.qenc t) .nil))).mono (hValid s t)
    have := isQueryBoundP_bind hh
      (fun p _ => isQueryBoundP_pure (spec := T) P (C.rdec t p.1, p.2) 0)
    simpa [CostedReduction.impl, handlerImpl] using this
  unfold CostedReduction.eval CostedReduction.totalQueriesByKind
  exact (isQueryBoundP_bind (Comp.queryBound_eval P w ws hw hU R.init (.cons x .nil))
    (fun as _ => isQueryBoundP_bind
      (simulateQ_run_StateT_byKind kind hQ hCoin hGame (hA as.1) as.2)
      (fun bs _ => Comp.queryBound_eval P w ws hw hU R.finish
        (.cons bs.2 (.cons bs.1 .nil))))).mono (by omega)

/-- Corollary of `CostedReduction.queryBound_eval_byKind` packaged for `QueriesBoundedByKind`. -/
theorem CostedReduction.queriesBoundedByKind_sound {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ m, (I.fwdU m).IsQueryBoundP P 0)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ) {Q : ℕ}
    (hBnd : R.QueriesBoundedByKind w ws kind qKind Q)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i))
    (x : rIn.denote) :
    (R.eval A x).IsQueryBoundP P Q := by
  obtain ⟨hQ, hValid, hle⟩ := hBnd
  exact (R.queryBound_eval_byKind P w ws hw hU kind hQ qKind hValid A hA x).mono hle

/-- Continuation query-bound invariant on a stage-1 `Mid` result: any paused continuation makes at
most `qRem i` remaining `G`-queries of kind `i`. -/
def Mid.QueryBoundedByKind {G : OracleSpec κ} {α π σ χ : Type} {n : ℕ}
    (kind : κ → Fin n) (qRem : Fin n → ℕ) : Mid G α π σ χ → Prop
  | .done _ _ => True
  | .paused t _ _ _ k =>
    ∀ (u : G t) (i : Fin n), (k u).IsQueryBoundP (isQueryKind (G := G) kind i) (qRem i)

theorem Mid.queryBoundedByKind_mono {G : OracleSpec κ} {α π σ χ : Type} {n : ℕ}
    {kind : κ → Fin n} {q₁ q₂ : Fin n → ℕ} (hle : ∀ i, q₁ i ≤ q₂ i) :
    ∀ m : Mid G α π σ χ, Mid.QueryBoundedByKind kind q₁ m → Mid.QueryBoundedByKind kind q₂ m
  | .done _ _, _ => trivial
  | .paused _ _ _ _ _, hk => fun u i => (hk u i).mono (hle i)

theorem runFuel_queryBound_byKind {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ)) (P : ι → Prop) [DecidablePred P]
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ m, (I.fwdU m).IsQueryBoundP P 0)
    {n : ℕ} (kind : κ → Fin n) (hQ : Fin n → ℕ)
    (hh : ∀ s t, h.queriesAt w ws (.cons s (.cons (C.qenc t) .nil)) ≤ hQ (kind t))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qRem : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qRem i)) →
      ∀ (fuel : ℕ) (s : σ.denote),
        (runFuel h dflt oa fuel s).IsQueryBoundP P
          (List.ofFn fun i => qRem i * hQ i).sum := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => intro qRem _ fuel s; simp [runFuel]
  | query_bind q mx ih =>
    intro qRem hA fuel s
    cases q with
    | inl m =>
      have hcont := isQueryBoundP_coin_byKind hA
      simpa [runFuel] using isQueryBoundP_bind (hU m) (fun u _ => ih u (hcont u) fuel s)
    | inr t =>
      cases fuel with
      | zero => simp [runFuel]
      | succ f =>
        obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byKind hA
        simp only [runFuel, construct_query_bind]
        have hstep := (Comp.queryBound_eval_at P w ws hw hU h
          (.cons s (.cons (C.qenc t) .nil))).mono (hh s t)
        exact (isQueryBoundP_bind hstep (fun p _ => ih (C.rdec t p.1) (hcont _) f p.2)).mono
          (le_of_eq (add_list_ofFn_update_pred_mul qRem hQ (kind t) hpos))

theorem TwoStageCostedReduction.run1_queryBound_byKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ m, (I.fwdU m).IsQueryBoundP P 0)
    {n : ℕ} (kind : κ → Fin n) (hQ : Fin n → ℕ)
    (hh : ∀ s t, R.handlePre.queriesAt w ws (.cons s (.cons (C.qenc t) .nil)) ≤ hQ (kind t))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qKind : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i)) →
      ∀ (fuel : ℕ) (s : R.σ.denote),
        (R.run1 dflt oa fuel s).IsQueryBoundP P
          (List.ofFn fun i => qKind i * hQ i).sum := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ => intro qKind _ fuel s; simp [TwoStageCostedReduction.run1]
  | query_bind q mx ih =>
    intro qKind hA fuel s
    cases q with
    | inl m =>
      have hcont := isQueryBoundP_coin_byKind hA
      simpa [TwoStageCostedReduction.run1] using
        isQueryBoundP_bind (hU m) (fun u _ => ih u (hcont u) fuel s)
    | inr t =>
      cases fuel with
      | zero => simp [TwoStageCostedReduction.run1]
      | succ f =>
        obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byKind hA
        simp only [TwoStageCostedReduction.run1, construct_query_bind]
        have hstep := (Comp.queryBound_eval_at P w ws hw hU R.handlePre
          (.cons s (.cons (C.qenc t) .nil))).mono (hh s t)
        refine (isQueryBoundP_bind hstep
          (m := (List.ofFn fun i =>
            Function.update qKind (kind t) (qKind (kind t) - 1) i * hQ i).sum)
          fun res _ => ?_).mono
          (le_of_eq (add_list_ofFn_update_pred_mul qKind hQ (kind t) hpos))
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact ih (C.rdec t v) (hcont _) f s'
        · exact (isQueryBoundP_pure (spec := T) P (Mid.paused t c p s' mx) 0).mono (Nat.zero_le _)

theorem TwoStageCostedReduction.run1_support_queryBoundedByKind
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qKind : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i)) →
      ∀ (fuel : ℕ) (s : R.σ.denote) (m : Mid G α R.π.denote R.σ.denote ch.denote),
        m ∈ support (R.run1 dflt oa fuel s) → Mid.QueryBoundedByKind kind qKind m := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro qKind _ fuel s m hm
    simp only [TwoStageCostedReduction.run1, construct_pure, support_pure,
      Set.mem_singleton_iff] at hm
    subst hm; trivial
  | query_bind q mx ih =>
    intro qKind hA fuel s m hm
    cases q with
    | inl num =>
      simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
      obtain ⟨u, -, hm⟩ := hm
      exact ih u (isQueryBoundP_coin_byKind hA u) fuel s m hm
    | inr t =>
      cases fuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, support_pure,
          Set.mem_singleton_iff] at hm
        subst hm; trivial
      | succ f =>
        obtain ⟨_, hcont⟩ := isQueryBoundP_game_byKind hA
        have hle : ∀ i, Function.update qKind (kind t) (qKind (kind t) - 1) i ≤ qKind i := by
          intro i
          by_cases h : i = kind t
          · subst h; simp only [Function.update_self]; omega
          · simp only [Function.update_of_ne h, le_rfl]
        simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
        obtain ⟨res, -, hm⟩ := hm
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · exact Mid.queryBoundedByKind_mono hle m (ih (C.rdec t v) (hcont _) f s' m hm)
        · simp only [support_pure, Set.mem_singleton_iff] at hm
          subst hm
          exact fun u i => (hcont u i).mono (hle i)

theorem TwoStageCostedReduction.eval1_queryBound_byKind
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ m, (I.fwdU m).IsQueryBoundP P 0)
    {n : ℕ} (kind : κ → Fin n) (hQ qKind : Fin n → ℕ)
    (hValid : R.ValidKindQueries w ws kind hQ)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i))
    (x : rIn.denote) (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval1 A x fuel dflt).IsQueryBoundP P (R.totalQueriesByKind w ws hQ qKind) := by
  unfold TwoStageCostedReduction.eval1 TwoStageCostedReduction.totalQueriesByKind
  have hle := le_max_left (R.chDone.queries w ws) (R.resume.queries w ws)
  refine (isQueryBoundP_bind (Comp.queryBound_eval P w ws hw hU R.init (.cons x .nil)) fun as _ =>
    isQueryBoundP_bind
      (R.run1_queryBound_byKind P w ws hw hU kind hQ (fun s t => (hValid s t).1)
        dflt (hA as.1) fuel as.2)
      (m := R.chDone.queries w ws) fun m _ => ?_).mono (by omega)
  cases m with
  | done b s' =>
    exact isQueryBoundP_bind
      (Comp.queryBound_eval P w ws hw hU R.chDone (.cons s' (.cons b .nil)))
      (fun c _ => isQueryBoundP_pure (spec := T) P (c, Mid.done b s') 0)
  | paused t c p s' k =>
    exact (isQueryBoundP_pure (spec := T) P (c, Mid.paused t c p s' k) 0).mono (Nat.zero_le _)

theorem TwoStageCostedReduction.eval1_support_queryBoundedByKind
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (kind : κ → Fin n) (qKind : Fin n → ℕ)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i))
    (x : rIn.denote) (fuel : ℕ) (dflt : aOut.denote) :
    ∀ cm ∈ support (R.eval1 A x fuel dflt), Mid.QueryBoundedByKind kind qKind cm.2 := by
  intro cm hcm
  simp only [TwoStageCostedReduction.eval1, mem_support_bind_iff] at hcm
  obtain ⟨⟨a, s₀⟩, -, m, hm, hcm⟩ := hcm
  have hmb := R.run1_support_queryBoundedByKind kind dflt (hA a) fuel s₀ m hm
  cases m with
  | done b s' =>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hcm
    obtain ⟨c, -, rfl⟩ := hcm; exact hmb
  | paused t c p s' k =>
    simp only [support_pure, Set.mem_singleton_iff] at hcm
    subst hcm; exact hmb

theorem TwoStageCostedReduction.eval2_queryBound_byKind
    {G : OracleSpec κ} {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ m, (I.fwdU m).IsQueryBoundP P 0)
    {n : ℕ} (kind : κ → Fin n) (hQ qKind : Fin n → ℕ)
    (hValid : R.ValidKindQueries w ws kind hQ)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote)
    (hm : Mid.QueryBoundedByKind kind qKind m)
    (y : rIn2.denote) (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval2 m y fuel dflt).IsQueryBoundP P (R.totalQueriesByKind w ws hQ qKind) := by
  have hle := le_max_right (R.chDone.queries w ws) (R.resume.queries w ws)
  unfold TwoStageCostedReduction.totalQueriesByKind
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2, pure_bind]
    exact (Comp.queryBound_eval P w ws hw hU R.finish
      (.cons s (.cons b (.cons y .nil)))).mono (by omega)
  | paused t c p s k =>
    simp only [TwoStageCostedReduction.eval2]
    exact (isQueryBoundP_bind
      (Comp.queryBound_eval P w ws hw hU R.resume (.cons s (.cons p (.cons y .nil))))
      fun vs _ => isQueryBoundP_bind
        (runFuel_queryBound_byKind R.handlePost P w ws hw hU kind hQ
          (fun s' t' => (hValid s' t').2) dflt (hm (C.rdec t vs.1)) fuel vs.2)
        fun bs _ => Comp.queryBound_eval P w ws hw hU R.finish
          (.cons bs.2 (.cons bs.1 (.cons y .nil)))).mono (by omega)

end QuerySoundness

/-! ## Per-kind block-size soundness -/

section SizeSoundness

variable {S : Sig} {ι κ : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem Expr.fits_eval_at (hO : OpsSizeHonest O) {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : ∀ (B : ℕ) (ρ : Env Γ), Env.Fits B ρ → t.Fits (B + e.costAt ρ) (e.eval ρ) := by
  induction e with
  | var v =>
    intro B ρ hρ; exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (Env.fits_get ρ v hρ)
  | unit | bool | lt | eqN | not | and | none | anyB =>
    intros; simp [Ty.Fits, Expr.eval]
  | nat n => intro B ρ _; simp only [Ty.Fits, Expr.eval, Expr.costAt]; omega
  | add a b iha ihb =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have hb := ihb B ρ hρ; have := bits_add (a.eval ρ) (b.eval ρ)
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at *; omega
  | sub a b iha _ =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mono (Nat.sub_le (a.eval ρ) (b.eval ρ))
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at *; omega
  | mulK k a iha =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mul k (a.eval ρ)
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at *; omega
  | divK k a iha =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mono (Nat.div_le_self (a.eval ρ) k)
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at *; omega
  | modK k a iha =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mono (Nat.mod_le (a.eval ρ) k)
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at *; omega
  | ite c a b _ iha ihb =>
    intro B ρ hρ
    simp only [Expr.eval, Expr.costAt]
    split
    · exact Ty.fits_mono (by omega) _ _ (iha B ρ hρ)
    · exact Ty.fits_mono (by omega) _ _ (ihb B ρ hρ)
  | pair a b iha ihb =>
    intro B ρ hρ
    exact ⟨Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ),
      Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (ihb B ρ hρ)⟩
  | fst a iha =>
    intro B ρ hρ; exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ).1
  | snd a iha =>
    intro B ρ hρ; exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ).2
  | inl a iha =>
    intro B ρ hρ; exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ)
  | inr a iha =>
    intro B ρ hρ; exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ)
  | some a iha =>
    intro B ρ hρ; exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ)
  | caseOpt e n s ihe ihn ihs =>
    intro B ρ hρ
    have he := ihe B ρ hρ
    simp only [Expr.eval, Expr.costAt]
    split
    · exact Ty.fits_mono (by omega) _ _ (ihn B ρ hρ)
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by omega) _ _
        (ihs _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
  | caseSum e l r ihe ihl ihr =>
    intro B ρ hρ
    have he := ihe B ρ hρ
    simp only [Expr.eval, Expr.costAt]
    split
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by omega) _ _
        (ihl _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
    · next y hy =>
      rw [hy] at he
      exact Ty.fits_mono (by omega) _ _
        (ihr _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
  | letE e b ihe ihb =>
    intro B ρ hρ
    have he := ihe B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _
      (ihb _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
  | op o a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (hO o _ _ (iha B ρ hρ))
  | nil => intros; simp [Ty.Fits, Expr.eval]
  | cons x l ihx ihl =>
    intro B ρ hρ
    have hx := ihx B ρ hρ; have hl := ihl B ρ hρ
    simp only [Ty.Fits, Expr.eval, Expr.costAt, List.length_cons, List.mem_cons] at hl ⊢
    refine ⟨by omega, ?_⟩
    rintro y (rfl | hy)
    · exact Ty.fits_mono (by omega) _ _ hx
    · exact Ty.fits_mono (by omega) _ _ (hl.2 y hy)
  | len l ihl =>
    intro B ρ hρ
    have hl := ihl B ρ hρ; have := bits_le_succ (l.eval ρ).length
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at hl ⊢; omega
  | take n l _ ihl =>
    intro B ρ hρ
    have hl := ihl B ρ hρ
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at hl ⊢
    refine ⟨by have := List.length_take_le' (n.eval ρ) (l.eval ρ); omega, fun y hy => ?_⟩
    exact Ty.fits_mono (by omega) _ _ (hl.2 y (List.mem_of_mem_take hy))
  | appendL K a b iha ihb =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have hb := ihb B ρ hρ
    simp only [Ty.Fits, Expr.eval, Expr.costAt] at ha hb ⊢
    refine ⟨by have := List.length_take_le K (a.eval ρ ++ b.eval ρ); omega, fun y hy => ?_⟩
    rcases List.mem_append.1 (List.mem_of_mem_take hy) with hy | hy
    · exact Ty.fits_mono (by omega) _ _ (ha.2 y hy)
    · exact Ty.fits_mono (by omega) _ _ (hb.2 y hy)
  | findB K l p ihl _ =>
    intro B ρ hρ
    have hl := ihl B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Expr.eval, Expr.costAt]
    rcases hf : ((l.eval ρ).take K).find? (fun x => p.eval (.cons x ρ)) with _ | v
    · trivial
    · exact Ty.fits_mono (by omega) _ _
        (hl.2 v (List.mem_of_mem_take (List.mem_of_find?_eq_some hf)))
  | mapB K l f ihl _ =>
    intro B ρ hρ
    have hl := ihl B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Ty.Fits, Expr.eval, Expr.costAt, List.length_map, List.mem_map]
    have hK : K ≤ K * (f.cost + 1) := Nat.le_mul_of_pos_right K (by omega)
    refine ⟨by have := List.length_take_le K (l.eval ρ); omega, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | h
      · simp at hx
      · exact h
    have hfK : f.cost + 1 ≤ K * (f.cost + 1) := Nat.le_mul_of_pos_left _ hK1
    exact Ty.fits_mono (by omega) _ _ (Expr.fits_eval hO f _ _
      (Env.fits_cons (hl.2 x (List.mem_of_mem_take hx)) (Env.fits_mono (by omega) ρ hρ)))
  | foldrB K l z f ihl ihz _ =>
    intro B ρ hρ
    have hl := ihl B ρ hρ; have hz := ihz B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Expr.eval, Expr.costAt]
    have key := foldr_fits (fun A b => B + l.costAt ρ ≤ A ∧ Ty.Fits A _ b)
      (fun x => Ty.Fits (B + l.costAt ρ) _ x) (f.cost + 1)
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun A x b hx hb => ⟨by omega, Ty.fits_mono (by omega) _ _ (Expr.fits_eval hO f _ _
        (Env.fits_cons (Ty.fits_mono hb.1 _ _ hx) (Env.fits_cons hb.2
          (Env.fits_mono (by omega) ρ hρ))))⟩)
      ((l.eval ρ).take K) (B + l.costAt ρ + z.costAt ρ) (z.eval ρ)
      (fun x hx => hl.2 x (List.mem_of_mem_take hx))
      ⟨by omega, Ty.fits_mono (by omega) _ _ hz⟩
    have hlen := Nat.mul_le_mul_right (f.cost + 1) (List.length_take_le K (l.eval ρ))
    exact Ty.fits_mono (by omega) _ _ key.2
  | tconst a iha =>
    intro B ρ hρ
    exact fun _ => Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (iha B ρ hρ)
  | tget m i ihm _ =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.costAt]; omega) _ _ (ihm B ρ hρ _)
  | tset m i a ihm _ iha =>
    intro B ρ hρ j
    simp only [Expr.eval, Expr.costAt]
    split
    · exact Ty.fits_mono (by omega) _ _ (iha B ρ hρ)
    · exact Ty.fits_mono (by omega) _ _ (ihm B ρ hρ j)

abbrev Comp.nqAt {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) (ρ : Env Γ) : ℕ :=
  c.queriesAt (fun _ => 1) (fun _ => 1) ρ

theorem Comp.fits_eval_at (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ (B : ℕ) (ρ : Env Γ), Env.Fits B ρ → ∀ y ∈ support (c.eval ρ),
      t.Fits (B + c.costAt ρ + c.nqAt ρ * aB) y := by
  induction c with
  | ret e =>
    intro B ρ hρ y hy
    simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact Ty.fits_mono (by simp only [Comp.costAt, Comp.nqAt, Comp.queriesAt]; omega) _ _
      (Expr.fits_eval_at hO e B ρ hρ)
  | bind c k ihc ihk =>
    intro B ρ hρ y hy
    simp only [Comp.eval, mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    have h1 := ihc B ρ hρ x hx
    simp only [Comp.costAt, Comp.nqAt, Comp.queriesAt]
    split
    · next x₀ hp =>
      have hx₀ : x = x₀ := by
        rw [Comp.eval_eq_pure_of_pureEval? c ρ hp, support_pure, Set.mem_singleton_iff] at hx
        exact hx
      subst hx₀
      have h2 := ihk _ _ (Env.fits_cons h1 (Env.fits_mono (by omega) ρ hρ)) y hy
      refine Ty.fits_mono ?_ _ _ h2
      simp only [Comp.nqAt, Nat.add_mul, hp]; omega
    · next hp =>
      have h2 := Comp.fits_eval hO hS aB hq k _ _
        (Env.fits_cons h1 (Env.fits_mono (by omega) ρ hρ)) y hy
      refine Ty.fits_mono ?_ _ _ h2
      simp only [Comp.nq, Comp.nqAt, Nat.add_mul, hp]; omega
  | ite b c d ihc ihd =>
    intro B ρ hρ y hy
    simp only [Comp.eval, Comp.costAt, Comp.nqAt, Comp.queriesAt] at hy ⊢
    cases hb : b.eval ρ <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hy ⊢
    · exact Ty.fits_mono (by simp only [Comp.nqAt]; omega) _ _ (ihd B ρ hρ y hy)
    · exact Ty.fits_mono (by simp only [Comp.nqAt]; omega) _ _ (ihc B ρ hρ y hy)
  | caseOpt e n s ihn ihs =>
    intro B ρ hρ y hy
    have he := Expr.fits_eval_at hO e B ρ hρ
    simp only [Comp.eval, Comp.costAt, Comp.nqAt, Comp.queriesAt] at hy ⊢
    rcases hx : e.eval ρ with _ | x <;> simp only [hx] at hy ⊢
    · exact Ty.fits_mono (by simp only [Comp.nqAt]; omega) _ _ (ihn B ρ hρ y hy)
    · rw [hx] at he
      exact Ty.fits_mono (by simp only [Comp.nqAt]; omega) _ _
        (ihs _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)) y hy)
  | caseSum e l r ihl ihr =>
    intro B ρ hρ y hy
    have he := Expr.fits_eval_at hO e B ρ hρ
    simp only [Comp.eval, Comp.costAt, Comp.nqAt, Comp.queriesAt] at hy ⊢
    rcases hx : e.eval ρ with x | z <;> simp only [hx] at hy ⊢
    · rw [hx] at he
      exact Ty.fits_mono (by simp only [Comp.nqAt]; omega) _ _
        (ihl _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)) y hy)
    · rw [hx] at he
      exact Ty.fits_mono (by simp only [Comp.nqAt]; omega) _ _
        (ihr _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)) y hy)
  | sample s e =>
    intro B ρ hρ y hy
    simp only [Comp.eval] at hy
    have := hS s _ _ (Expr.fits_eval_at hO e B ρ hρ) y (I.support_liftP_subset _ hy)
    exact Ty.fits_mono (by simp only [Comp.nqAt, Comp.costAt, Comp.queriesAt]; omega) _ _ this
  | query g e =>
    intro B ρ hρ y hy
    simp only [Comp.eval, support_map, Set.mem_image] at hy
    obtain ⟨u, -, rfl⟩ := hy
    exact Ty.fits_mono (by simp only [Comp.nqAt, Comp.costAt, Comp.queriesAt]; omega) _ _
      (hq g _ u)
  | iter n e body _ =>
    intro B ρ hρ y hy
    simp only [Comp.eval] at hy
    have he := Expr.fits_eval_at hO e B ρ hρ
    have key := iterM_fits (fun A a => B ≤ A ∧ Ty.Fits A _ a) (body.cost + body.nq * aB)
      (fun a => body.eval (.cons a ρ))
      (fun A a ha y hy => ⟨by omega, Ty.fits_mono (by omega) _ _
        (Comp.fits_eval hO hS aB hq body _ _
          (Env.fits_cons ha.2 (Env.fits_mono ha.1 ρ hρ)) y hy)⟩)
      n (B + e.costAt ρ) (e.eval ρ) ⟨by omega, he⟩ y hy
    have e1 : n * (body.cost + body.nq * aB) = n * body.cost + n * body.nq * aB := by ring
    have e2 : n * (body.cost + 1) = n * body.cost + n := by ring
    exact Ty.fits_mono
      (by simp only [Comp.nqAt, Comp.nq, Comp.costAt, Comp.queriesAt] at *; omega) _ _ key.2
  | findM K l p _ =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval_at hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    rcases y with _ | v
    · trivial
    · exact Ty.fits_mono (by simp only [Comp.costAt]; omega) _ _
        (hl.2 v (List.mem_of_mem_take (findML_mem _ _ v hy)))
  | anyM => intros; trivial
  | mapM K l f _ =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval_at hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    obtain ⟨hlen, hm⟩ := mapML_mem _ _ y hy
    have := List.length_take_le' K (l.eval ρ)
    simp only [Ty.Fits]
    refine ⟨by simp only [Comp.costAt]; omega, fun z hz => ?_⟩
    obtain ⟨x, hx, hz⟩ := hm z hz
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | h
      · simp at hx
      · exact h
    have h1 : f.cost + 1 ≤ K * (f.cost + 1) := Nat.le_mul_of_pos_left _ hK1
    have h2 : f.nq * aB ≤ K * f.nq * aB := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hK1
    exact Ty.fits_mono
      (by simp only [Comp.nqAt, Comp.nq, Comp.costAt, Comp.queriesAt] at *; omega) _ _
      (Comp.fits_eval hO hS aB hq f _ _ (Env.fits_cons (hl.2 x (List.mem_of_mem_take hx))
        (Env.fits_mono (by omega) ρ hρ)) z hz)
  | consumeFirstM K l p mk _ =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval_at hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    obtain ⟨hlen, hm⟩ := consumeFirstML_mem _ _ _ y hy
    have := List.length_take_le' K (l.eval ρ)
    refine ⟨trivial, ?_⟩
    simp only [Ty.Fits]
    refine ⟨by simp only [Comp.costAt]; omega, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl | rfl⟩ := hm z hz
    · exact Ty.fits_mono (by simp only [Comp.costAt]; omega) _ _
        (hl.2 _ (List.mem_of_mem_take hx))
    · have hK1 : 1 ≤ K := by
        rcases Nat.eq_zero_or_pos K with rfl | h
        · simp at hx
        · exact h
      have h1 : p.cost + mk.cost + 1 ≤ K * (p.cost + mk.cost + 1) :=
        Nat.le_mul_of_pos_left _ hK1
      exact Ty.fits_mono (by simp only [Comp.costAt]; omega) _ _
        (Expr.fits_eval hO mk _ _ (Env.fits_cons (hl.2 x (List.mem_of_mem_take hx))
          (Env.fits_mono (by omega) ρ hρ)))
  | foldM K l z f _ =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval_at hO l B ρ hρ
    have hz := Expr.fits_eval_at hO z B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    have key := foldML_fits (fun A b => B + l.costAt ρ ≤ A ∧ Ty.Fits A _ b)
      (fun x => Ty.Fits (B + l.costAt ρ) _ x) (f.cost + f.nq * aB)
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun A x b hx hb b' hb' => ⟨by omega, Ty.fits_mono (by omega) _ _
        (Comp.fits_eval hO hS aB hq f _ _
          (Env.fits_cons (Ty.fits_mono hb.1 _ _ hx) (Env.fits_cons hb.2
            (Env.fits_mono (by omega) ρ hρ))) b' hb')⟩)
      ((l.eval ρ).take K) (B + l.costAt ρ + z.costAt ρ) (z.eval ρ)
      (fun x hx => hl.2 x (List.mem_of_mem_take hx))
      ⟨by omega, Ty.fits_mono (by omega) _ _ hz⟩ y hy
    have hK := Nat.mul_le_mul_right (f.cost + f.nq * aB) (List.length_take_le K (l.eval ρ))
    have e1 : K * (f.cost + f.nq * aB) = K * f.cost + K * f.nq * aB := by ring
    have e2 : K * (f.cost + 1) = K * f.cost + K := by ring
    exact Ty.fits_mono
      (by simp only [Comp.nqAt, Comp.nq, Comp.costAt, Comp.queriesAt] at *; omega) _ _ key.2

abbrev CostedReduction.nqByKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    {n : ℕ} (hNq qKind : Fin n → ℕ) : ℕ :=
  R.totalQueriesByKind (fun _ => 1) (fun _ => 1) hNq qKind

abbrev TwoStageCostedReduction.nqByKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    {n : ℕ} (hNq qKind : Fin n → ℕ) : ℕ :=
  R.totalQueriesByKind (fun _ => 1) (fun _ => 1) hNq qKind

theorem CostedReduction.fits_simulateQ_byKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    {n : ℕ} (kind : κ → Fin n) (hCost hNq : Fin n → ℕ)
    (hVC : R.ValidKindCosts kind hCost)
    (hVNq : R.ValidKindQueries (fun _ => 1) (fun _ => 1) kind hNq) :
    ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {qKind : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i)) →
      ∀ (B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
        ∀ r ∈ support ((simulateQ R.impl oa).run s),
          R.σ.Fits
            (B + (List.ofFn fun i => qKind i * (qB + hCost i + hNq i * aB)).sum) r.2 := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro qKind _ B s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro qKind hb B s hs r hr
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
    cases q with
    | inl num =>
      simp only [CostedReduction.impl, handlerImpl, StateT.run_lift, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨_, -, hvs⟩ := hstep
      cases hvs
      exact ih v (isQueryBoundP_coin_byKind hb v) B s hs r hr
    | inr t =>
      obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byKind hb
      simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨⟨ans, s₁⟩, hstep, hvs⟩ := hstep
      cases hvs
      have hs₁_raw := (Comp.fits_eval_at hO hS aB hq R.handle (B + qB) _
        (Env.fits_pair hs (henc t)) (ans, s₁) hstep).2
      have hs₁ : R.σ.Fits (B + (qB + hCost (kind t) + hNq (kind t) * aB)) s₁ := by
        refine Ty.fits_mono ?_ _ _ hs₁_raw
        have hc := hVC s t
        have hnq := Nat.mul_le_mul_right aB (hVNq s t)
        simp only [Comp.nqAt] at *; omega
      have hrec := ih (C.rdec t ans) (hcont _)
        (B + (qB + hCost (kind t) + hNq (kind t) * aB)) s₁ hs₁ r hr
      have heq := add_list_ofFn_update_pred_mul qKind
        (fun i => qB + hCost i + hNq i * aB) (kind t) hpos
      exact Ty.fits_mono (by omega) _ _ hrec

/-- Per-kind one-stage reduction output size bound in terms of `totalCostByKind` and `nqByKind`. -/
theorem CostedReduction.fits_eval_byKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    {n : ℕ} (kind : κ → Fin n) (hCost hNq qKind : Fin n → ℕ)
    (hVC : R.ValidKindCosts kind hCost)
    (hVNq : R.ValidKindQueries (fun _ => 1) (fun _ => 1) kind hNq)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (B : ℕ)
    (hb : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i))
    (x : rIn.denote) (hx : rIn.Fits B x) :
    ∀ y ∈ support (R.eval A x),
      out.Fits (B + aAdvB + (List.ofFn qKind).sum * qB +
        R.totalCostByKind hCost qKind + R.nqByKind hNq qKind * aB) y := by
  intro y hy
  simp only [CostedReduction.eval, mem_support_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, ⟨outAdv, s₁⟩, hs₁, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval hO hS aB hq R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have h1 := R.fits_simulateQ_byKind hO hS aB hq qB henc kind hCost hNq hVC hVNq
    (hb oAdv) _ s₀ h0 (outAdv, s₁) hs₁
  have h2 := Comp.fits_eval hO hS aB hq R.finish _ (.cons s₁ (.cons outAdv .nil))
    (Env.fits_pair h1 (hA outAdv)) y hy
  refine Ty.fits_mono ?_ _ _ h2
  have hsplit1 := list_ofFn_sum_mul_add_right qKind
    (fun i => qB + hCost i) (fun i => hNq i * aB)
  have hsplit2 := list_ofFn_sum_mul_add_right qKind (fun _ => qB) hCost
  have hqB := list_ofFn_sum_mul_const qKind qB
  have hnqMul : (List.ofFn fun i => qKind i * (hNq i * aB)).sum =
      (List.ofFn fun i => qKind i * hNq i).sum * aB := by
    have : (fun i => qKind i * (hNq i * aB)) = fun i => (qKind i * hNq i) * aB := by
      ext i; ring
    rw [this, list_ofFn_sum_mul_const]
  have hCostLe : (List.ofFn fun i => qKind i * hCost i).sum ≤
      (List.ofFn fun i => qKind i * max I.uCost (hCost i + C.codecCost)).sum :=
    list_ofFn_sum_mul_mono_right qKind hCost _
      (fun i => le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hnqTot : (R.init.nq + (List.ofFn fun i => qKind i * hNq i).sum + R.finish.nq) * aB =
      R.init.nq * aB + (List.ofFn fun i => qKind i * hNq i).sum * aB + R.finish.nq * aB := by ring
  dsimp only [CostedReduction.totalCostByKind, CostedReduction.nqByKind,
    CostedReduction.totalQueriesByKind, Comp.nq] at hnqTot ⊢
  omega

theorem runFuel_fits_byKind {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    {n : ℕ} (kind : κ → Fin n) (hCost hNq : Fin n → ℕ)
    (hVC : ∀ s t, h.costAt (.cons s (.cons (C.qenc t) .nil)) ≤ hCost (kind t))
    (hVNq : ∀ s t, h.queriesAt (fun _ => 1) (fun _ => 1) (.cons s (.cons (C.qenc t) .nil)) ≤
      hNq (kind t))
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qRem : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qRem i)) →
      ∀ (fuel B : ℕ) (s : σ.denote), σ.Fits B s →
        ∀ r ∈ support (runFuel h dflt oa fuel s),
          σ.Fits (B + (List.ofFn fun i => qRem i * (qB + hCost i + hNq i * aB)).sum) r.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro qRem _ fuel B s hs r hr
    simp only [runFuel, construct_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro qRem hb fuel B s hs r hr
    cases q with
    | inl num =>
      simp only [runFuel, construct_query_bind, mem_support_bind_iff] at hr
      obtain ⟨u, -, hr⟩ := hr
      exact ih u (isQueryBoundP_coin_byKind hb u) fuel B s hs r hr
    | inr t =>
      cases fuel with
      | zero =>
        simp only [runFuel, construct_query_bind, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact Ty.fits_mono (by omega) _ _ hs
      | succ f =>
        obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byKind hb
        simp only [runFuel, construct_query_bind, mem_support_bind_iff] at hr
        obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
        have hs'_raw := (Comp.fits_eval_at hO hS aB hq h (B + qB) _
          (Env.fits_pair hs (henc t)) (v, s') hstep).2
        have hs' : σ.Fits (B + (qB + hCost (kind t) + hNq (kind t) * aB)) s' := by
          refine Ty.fits_mono ?_ _ _ hs'_raw
          have hc := hVC s t
          have hnq := Nat.mul_le_mul_right aB (hVNq s t)
          simp only [Comp.nqAt] at *; omega
        have hrec := ih (C.rdec t v) (hcont _) f
          (B + (qB + hCost (kind t) + hNq (kind t) * aB)) s' hs' r hr
        have heq := add_list_ofFn_update_pred_mul qRem
          (fun i => qB + hCost i + hNq i * aB) (kind t) hpos
        exact Ty.fits_mono (by omega) _ _ hrec

theorem TwoStageCostedReduction.fits_run1_byKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    {n : ℕ} (kind : κ → Fin n) (hCost hNq : Fin n → ℕ)
    (hVC : R.ValidKindCosts kind hCost)
    (hVNq : R.ValidKindQueries (fun _ => 1) (fun _ => 1) kind hNq)
    {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qKind : Fin n → ℕ},
      (∀ i, oa.IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i)) →
      ∀ (fuel B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
        ∀ m ∈ support (R.run1 dflt oa fuel s),
          ∃ qRem : Fin n → ℕ, (∀ i, qRem i ≤ qKind i) ∧
            Mid.QueryBoundedByKind kind qRem m ∧
            Mid.Fits R.π R.σ ch
              (B + (List.ofFn fun i => (qKind i - qRem i) * (qB + hCost i + hNq i * aB)).sum) m := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure _ =>
    intro qKind _ fuel B s hs m hm
    simp only [TwoStageCostedReduction.run1, construct_pure, support_pure,
      Set.mem_singleton_iff] at hm
    subst hm
    refine ⟨qKind, fun _ => le_rfl, trivial, ?_⟩
    simp only [Nat.sub_self, Nat.zero_mul, list_ofFn_sum_zero, Nat.add_zero]
    exact hs
  | query_bind q mx ih =>
    intro qKind hb fuel B s hs m hm
    cases q with
    | inl num =>
      simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
      obtain ⟨u, -, hm⟩ := hm
      exact ih u (isQueryBoundP_coin_byKind hb u) fuel B s hs m hm
    | inr t =>
      cases fuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, support_pure,
          Set.mem_singleton_iff] at hm
        subst hm
        refine ⟨qKind, fun _ => le_rfl, trivial, ?_⟩
        simp only [Nat.sub_self, Nat.zero_mul, list_ofFn_sum_zero, Nat.add_zero]
        exact hs
      | succ f =>
        obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byKind hb
        simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
        obtain ⟨res, hstep, hm⟩ := hm
        let D : Fin n → ℕ := fun i => qB + hCost i + hNq i * aB
        let qKind' : Fin n → ℕ := Function.update qKind (kind t) (qKind (kind t) - 1)
        have hres_raw := Comp.fits_eval_at hO hS aB hq R.handlePre (B + qB) _
          (Env.fits_pair hs (henc t)) res hstep
        have hstepB : B + qB + R.handlePre.costAt (.cons s (.cons (C.qenc t) .nil)) +
            R.handlePre.nqAt (.cons s (.cons (C.qenc t) .nil)) * aB ≤ B + D (kind t) := by
          have hc := (hVC s t).1
          have hnq := Nat.mul_le_mul_right aB (hVNq s t).1
          dsimp only [D, Comp.nqAt] at *; omega
        have hres := Ty.fits_mono hstepB _ res hres_raw
        have hle' : ∀ i, qKind' i ≤ qKind i := by
          intro i; dsimp only [qKind']
          by_cases h : i = kind t
          · subst h; simp only [Function.update_self]; omega
          · simp only [Function.update_of_ne h, le_rfl]
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · obtain ⟨qRem, hRemLe, hRemBnd, hRemFits⟩ :=
            ih (C.rdec t v) (hcont _) f (B + D (kind t)) s' hres.2 m hm
          refine ⟨qRem, fun i => le_trans (hRemLe i) (hle' i), hRemBnd, ?_⟩
          have hposDiff : 0 < qKind (kind t) - qRem (kind t) := by
            have h1 : qRem (kind t) ≤ Function.update qKind (kind t) (qKind (kind t) - 1) (kind t) :=
              hRemLe (kind t)
            rw [Function.update_self] at h1; omega
          have hupdDiff : (fun i =>
              Function.update (fun j => qKind j - qRem j) (kind t)
                ((qKind (kind t) - qRem (kind t)) - 1) i * D i) =
              fun i => (qKind' i - qRem i) * D i := by
            ext i; dsimp only [qKind']
            by_cases h : i = kind t
            · subst h; simp only [Function.update_self]; congr 1; omega
            · simp only [Function.update_of_ne h]
          have heq := add_list_ofFn_update_pred_mul (fun j => qKind j - qRem j) D (kind t) hposDiff
          rw [hupdDiff] at heq
          exact Mid.fits_mono (by dsimp only [D, qKind'] at *; omega) m hRemFits
        · simp only [support_pure, Set.mem_singleton_iff] at hm
          subst hm
          refine ⟨qKind', hle', hcont, ?_⟩
          have hposDiff : 0 < qKind (kind t) - qKind' (kind t) := by
            dsimp only [qKind']; rw [Function.update_self]; omega
          have hupdZero : (fun i =>
              Function.update (fun j => qKind j - qKind' j) (kind t)
                ((qKind (kind t) - qKind' (kind t)) - 1) i * D i) =
              fun _ => 0 := by
            ext i; dsimp only [qKind']
            by_cases h : i = kind t
            · subst h; simp only [Function.update_self]
              have : qKind (kind t) - (qKind (kind t) - 1) - 1 = 0 := by omega
              rw [this, Nat.zero_mul]
            · simp only [Function.update_of_ne h, Nat.sub_self, Nat.zero_mul]
          have heq := add_list_ofFn_update_pred_mul (fun j => qKind j - qKind' j) D (kind t)
            hposDiff
          rw [hupdZero, list_ofFn_sum_zero, Nat.add_zero] at heq
          exact Mid.fits_mono (by dsimp only [D, qKind'] at *; omega) _ ⟨hres.1, hres.2.1, hres.2.2⟩

/-- Per-kind two-stage reduction challenge and output size bounds across both stages, independent of
`fuel` and `fuel₂`. -/
theorem TwoStageCostedReduction.fits_eval_byKind {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    {n : ℕ} (kind : κ → Fin n) (hCost hNq qKind : Fin n → ℕ)
    (hVC : R.ValidKindCosts kind hCost)
    (hVNq : R.ValidKindQueries (fun _ => 1) (fun _ => 1) kind hNq)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (qKind i))
    (x : rIn.denote) (B : ℕ) (hx : rIn.Fits B x) (fuel : ℕ) (dflt : aOut.denote) :
    ∀ cm ∈ support (R.eval1 A x fuel dflt),
      ch.Fits (B + aAdvB + (List.ofFn qKind).sum * qB +
        R.totalCostByKind hCost qKind + R.nqByKind hNq qKind * aB) cm.1 ∧
      ∀ (y : rIn2.denote) (B₂ : ℕ), rIn2.Fits B₂ y → ∀ (fuel₂ : ℕ),
        ∀ z ∈ support (R.eval2 cm.2 y fuel₂ dflt),
          out.Fits (B + B₂ + aAdvB + (List.ofFn qKind).sum * qB +
            R.totalCostByKind hCost qKind + R.nqByKind hNq qKind * aB) z := by
  intro cm hcm
  simp only [TwoStageCostedReduction.eval1, mem_support_bind_iff] at hcm
  obtain ⟨⟨oAdv, s₀⟩, hs₀, m, hm, hcm⟩ := hcm
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval hO hS aB hq R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  obtain ⟨qRem, hRemLe, hRemBnd, hmFits⟩ :=
    R.fits_run1_byKind hO hS aB hq qB henc kind hCost hNq hVC hVNq dflt (hb oAdv)
      fuel (B + R.init.cost + R.init.nq * aB) s₀ h0 m hm
  let D : Fin n → ℕ := fun i => qB + hCost i + hNq i * aB
  have hSubAdd := list_ofFn_sum_sub_add_mul qKind qRem D hRemLe
  have hsplit1 := list_ofFn_sum_mul_add_right qKind
    (fun i => qB + hCost i) (fun i => hNq i * aB)
  have hsplit2 := list_ofFn_sum_mul_add_right qKind (fun _ => qB) hCost
  have hqB := list_ofFn_sum_mul_const qKind qB
  have hnqMul : (List.ofFn fun i => qKind i * (hNq i * aB)).sum =
      (List.ofFn fun i => qKind i * hNq i).sum * aB := by
    have : (fun i => qKind i * (hNq i * aB)) = fun i => (qKind i * hNq i) * aB := by
      ext i; ring
    rw [this, list_ofFn_sum_mul_const]
  have hCostLe : (List.ofFn fun i => qKind i * hCost i).sum ≤
      (List.ofFn fun i => qKind i * max I.uCost (hCost i + C.codecCost)).sum :=
    list_ofFn_sum_mul_mono_right qKind hCost _
      (fun i => le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hleChCost1 := le_max_left R.chDone.cost R.resume.cost
  have hleChCost2 := le_max_right R.chDone.cost R.resume.cost
  have hleChNq1 := Nat.mul_le_mul_right aB (le_max_left R.chDone.nq R.resume.nq)
  have hleChNq2 := Nat.mul_le_mul_right aB (le_max_right R.chDone.nq R.resume.nq)
  have hnqTot : (R.init.nq + (List.ofFn fun i => qKind i * hNq i).sum +
      max R.chDone.nq R.resume.nq + R.finish.nq) * aB =
      R.init.nq * aB + (List.ofFn fun i => qKind i * hNq i).sum * aB +
        max R.chDone.nq R.resume.nq * aB + R.finish.nq * aB := by ring
  dsimp only [Comp.nq] at hleChNq1 hleChNq2 hnqTot
  cases m with
  | done b s' =>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hcm
    obtain ⟨c, hc, rfl⟩ := hcm
    refine ⟨?_, ?_⟩
    · have hc' := Comp.fits_eval hO hS aB hq R.chDone _ (.cons s' (.cons b .nil))
        (Env.fits_pair hmFits (hA b)) c hc
      refine Ty.fits_mono ?_ _ _ hc'
      dsimp only [D, TwoStageCostedReduction.totalCostByKind, TwoStageCostedReduction.nqByKind,
        TwoStageCostedReduction.totalQueriesByKind, Comp.nq] at *
      omega
    · intro y B₂ hy fuel₂ z hz
      simp only [TwoStageCostedReduction.eval2, pure_bind] at hz
      have hf := Comp.fits_eval hO hS aB hq R.finish _ (.cons s' (.cons b (.cons y .nil)))
        (Env.fits_triple hmFits (hA b) hy) z hz
      refine Ty.fits_mono ?_ _ _ hf
      dsimp only [D, TwoStageCostedReduction.totalCostByKind, TwoStageCostedReduction.nqByKind,
        TwoStageCostedReduction.totalQueriesByKind, Comp.nq] at *
      omega
  | paused t c p s' k =>
    simp only [support_pure, Set.mem_singleton_iff] at hcm
    subst hcm
    refine ⟨?_, ?_⟩
    · refine Ty.fits_mono ?_ _ _ hmFits.1
      dsimp only [D, TwoStageCostedReduction.totalCostByKind, TwoStageCostedReduction.nqByKind,
        TwoStageCostedReduction.totalQueriesByKind, Comp.nq] at *
      omega
    · intro y B₂ hy fuel₂ z hz
      simp only [TwoStageCostedReduction.eval2, mem_support_bind_iff] at hz
      obtain ⟨⟨v, s₁⟩, hres, ⟨b, s₂⟩, hrun, hz⟩ := hz
      have hs₁ : R.σ.Fits
          ((B + R.init.cost + R.init.nq * aB +
            (List.ofFn fun i => (qKind i - qRem i) * D i).sum) +
            B₂ + R.resume.cost + R.resume.nq * aB) s₁ := by
        have henv : Env.Fits
            ((B + R.init.cost + R.init.nq * aB +
              (List.ofFn fun i => (qKind i - qRem i) * D i).sum) + B₂)
            (.cons s' (.cons p (.cons y .nil))) :=
          ⟨Ty.fits_mono (by dsimp only [D] at *; omega) _ _ hmFits.2.2,
            Ty.fits_mono (by dsimp only [D] at *; omega) _ _ hmFits.2.1,
            Ty.fits_mono (by omega) _ _ hy, trivial⟩
        exact (Comp.fits_eval hO hS aB hq R.resume _ _ henv (v, s₁) hres).2
      have hs₂ := runFuel_fits_byKind R.handlePost hO hS aB hq qB henc kind hCost hNq
        (fun s'' t'' => (hVC s'' t'').2) (fun s'' t'' => (hVNq s'' t'').2) dflt
        (hRemBnd (C.rdec t v)) fuel₂ _ s₁ hs₁ (b, s₂) hrun
      have henv₂ : Env.Fits
          (((B + R.init.cost + R.init.nq * aB +
            (List.ofFn fun i => (qKind i - qRem i) * D i).sum) +
            B₂ + R.resume.cost + R.resume.nq * aB) +
            (List.ofFn fun i => qRem i * D i).sum + aAdvB)
          (.cons s₂ (.cons b (.cons y .nil))) :=
        ⟨Ty.fits_mono (by dsimp only [D] at *; omega) _ _ hs₂,
          Ty.fits_mono (by omega) _ _ (hA b),
          Ty.fits_mono (by omega) _ _ hy, trivial⟩
      have hf := Comp.fits_eval hO hS aB hq R.finish _ (.cons s₂ (.cons b (.cons y .nil)))
        henv₂ z hz
      refine Ty.fits_mono ?_ _ _ hf
      dsimp only [D, TwoStageCostedReduction.totalCostByKind, TwoStageCostedReduction.nqByKind,
        TwoStageCostedReduction.totalQueriesByKind, Comp.nq] at *
      omega

end SizeSoundness

end ReductionDsl
