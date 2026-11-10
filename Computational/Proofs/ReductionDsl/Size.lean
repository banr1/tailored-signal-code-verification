/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Soundness

/-!
# ReductionDsl Size Bounds

Proves size bounds (`Ty.Fits`) and cost-independent leaf-width bounds (`Ty.BaseFits`,
`Ty.treeBlocks`) for evaluated `ReductionDsl` expressions, programs, and reductions under
`OpsSizeHonest` and `SampSizeHonest`.
-/

@[expose] public section

namespace ReductionDsl

variable {S : Sig}

theorem Ty.fits_mono {B B' : ℕ} (h : B ≤ B') : ∀ (t : Ty S) (x : t.denote), t.Fits B x →
    t.Fits B' x
  | .base _, _, hx => by simp only [Ty.Fits] at hx ⊢; omega
  | .unit, _, _ => trivial
  | .bool, _, _ => trivial
  | .nat, _, hx => by simp only [Ty.Fits] at hx ⊢; omega
  | .opt _, none, _ => trivial
  | .opt t, some a, hx => Ty.fits_mono h t a hx
  | .prod t u, x, hx => ⟨Ty.fits_mono h t _ hx.1, Ty.fits_mono h u _ hx.2⟩
  | .sum t _, .inl a, hx => Ty.fits_mono h t a hx
  | .sum _ u, .inr b, hx => Ty.fits_mono h u b hx
  | .list t, l, hx => by
    simp only [Ty.Fits] at hx ⊢
    exact ⟨by omega, fun x hm => Ty.fits_mono h t x (hx.2 x hm)⟩
  | .tbl t, m, hx => fun i => Ty.fits_mono h t _ (hx i)

def Env.Fits (B : ℕ) : {Γ : List (Ty S)} → Env Γ → Prop
  | _, .nil => True
  | _, .cons (t := t) x ρ => t.Fits B x ∧ Env.Fits B ρ

theorem Env.fits_cons {B : ℕ} {Γ : List (Ty S)} {t : Ty S} {x : t.denote} {ρ : Env Γ}
    (hx : t.Fits B x) (hρ : Env.Fits B ρ) : Env.Fits B (.cons x ρ) := ⟨hx, hρ⟩

theorem Env.fits_mono {B B' : ℕ} (h : B ≤ B') : ∀ {Γ : List (Ty S)} (ρ : Env Γ),
    Env.Fits B ρ → Env.Fits B' ρ
  | _, .nil, _ => trivial
  | _, .cons (t := t) x ρ, hρ => ⟨Ty.fits_mono h t x hρ.1, Env.fits_mono h ρ hρ.2⟩

theorem Env.fits_get {B : ℕ} : ∀ {Γ : List (Ty S)} {t : Ty S} (ρ : Env Γ) (v : Var Γ t),
    Env.Fits B ρ → t.Fits B (ρ.get v)
  | _, _, .cons _ _, .zero, hρ => hρ.1
  | _, _, .cons _ ρ, .succ v, hρ => Env.fits_get ρ v hρ.2

/-! ## Bit-length arithmetic -/

theorem lt_two_pow_bits (n : ℕ) : n < 2 ^ bits n := Nat.lt_pow_succ_log_self (by norm_num) n

theorem one_le_bits (n : ℕ) : 1 ≤ bits n := by unfold bits; omega

theorem bits_le_of_lt {n k : ℕ} (h : n < 2 ^ k) (hk : 1 ≤ k) : bits n ≤ k := by
  unfold bits
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (b := 2) hn.ne' h; omega

theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := by
  unfold bits; have := Nat.log_mono_right (b := 2) h; omega

theorem bits_add (a b : ℕ) : bits (a + b) ≤ max (bits a) (bits b) + 1 := by
  apply bits_le_of_lt _ (by omega)
  have ha := lt_two_pow_bits a
  have hb := lt_two_pow_bits b
  have h1 : 2 ^ bits a ≤ 2 ^ max (bits a) (bits b) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h2 : 2 ^ bits b ≤ 2 ^ max (bits a) (bits b) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  rw [pow_succ]; omega

theorem bits_mul (k a : ℕ) : bits (k * a) ≤ bits k + bits a := by
  apply bits_le_of_lt _ (by have := one_le_bits k; omega)
  rw [pow_add]
  exact Nat.mul_lt_mul'' (lt_two_pow_bits k) (lt_two_pow_bits a)

theorem bits_le_succ (n : ℕ) : bits n ≤ n + 1 := by
  unfold bits; have := Nat.log_le_self 2 n; omega

/-! ## Expressions -/

theorem OpsSizeHonest.sum {O₁ O₂ : Ops S} (h₁ : OpsSizeHonest O₁) (h₂ : OpsSizeHonest O₂) :
    OpsSizeHonest (O₁.sum O₂)
  | .inl o, x, B, hx => h₁ o x B hx
  | .inr o, x, B, hx => h₂ o x B hx

theorem foldr_fits {α β : Type} (P : ℕ → β → Prop) (Q : α → Prop) (D : ℕ) (f : α → β → β)
    (hf : ∀ A x b, Q x → P A b → P (A + D) (f x b)) :
    ∀ (l : List α) (A : ℕ) (z : β), (∀ x ∈ l, Q x) → P A z → P (A + l.length * D) (l.foldr f z)
  | [], A, z, _, hz => by simpa using hz
  | x :: l, A, z, hl, hz => by
    have := hf _ x _ (hl x (by simp)) (foldr_fits P Q D f hf l A z (fun y hy => hl y (by simp
      [hy])) hz)
    simp only [List.foldr_cons, List.length_cons]
    rwa [show A + (l.length + 1) * D = A + l.length * D + D by ring]

theorem Expr.fits_eval {O : Ops S} (hO : OpsSizeHonest O) {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O Γ t) : ∀ (B : ℕ) (ρ : Env Γ), Env.Fits B ρ → t.Fits (B + e.cost) (e.eval ρ) := by
  induction e with
  | var v =>
    intro B ρ hρ; exact Ty.fits_mono (by omega) _ _ (Env.fits_get ρ v hρ)
  | unit | bool | lt | eqN | not | and | none | anyB =>
    intros; simp [Ty.Fits, Expr.eval]
  | nat n => intro B ρ _; simp only [Ty.Fits, Expr.eval, Expr.cost]; omega
  | add a b iha ihb =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have hb := ihb B ρ hρ; have := bits_add (a.eval ρ) (b.eval ρ)
    simp only [Ty.Fits, Expr.eval, Expr.cost] at *; omega
  | sub a b iha ihb =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mono (Nat.sub_le (a.eval ρ) (b.eval ρ))
    simp only [Ty.Fits, Expr.eval, Expr.cost] at *; omega
  | mulK k a iha =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mul k (a.eval ρ)
    simp only [Ty.Fits, Expr.eval, Expr.cost] at *; omega
  | divK k a iha =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mono (Nat.div_le_self (a.eval ρ) k)
    simp only [Ty.Fits, Expr.eval, Expr.cost] at *; omega
  | modK k a iha =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have := bits_mono (Nat.mod_le (a.eval ρ) k)
    simp only [Ty.Fits, Expr.eval, Expr.cost] at *; omega
  | ite c a b _ iha ihb =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have hb := ihb B ρ hρ
    simp only [Expr.eval, Expr.cost]
    split
    · exact Ty.fits_mono (by omega) _ _ ha
    · exact Ty.fits_mono (by omega) _ _ hb
  | pair a b iha ihb =>
    intro B ρ hρ
    exact ⟨Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ),
      Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (ihb B ρ hρ)⟩
  | fst a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ).1
  | snd a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ).2
  | inl a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ)
  | inr a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ)
  | some a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ)
  | caseOpt e n s ihe ihn ihs =>
    intro B ρ hρ
    have he := ihe B ρ hρ
    simp only [Expr.eval, Expr.cost]
    split
    · exact Ty.fits_mono (by omega) _ _ (ihn B ρ hρ)
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by omega) _ _
        (ihs _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
  | caseSum e l r ihe ihl ihr =>
    intro B ρ hρ
    have he := ihe B ρ hρ
    simp only [Expr.eval, Expr.cost]
    split
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by omega) _ _
        (ihl _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by omega) _ _
        (ihr _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
  | letE e b ihe ihb =>
    intro B ρ hρ
    have he := ihe B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _
      (ihb _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)))
  | op o a iha =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (hO o _ _ (iha B ρ hρ))
  | nil => intros; simp [Ty.Fits, Expr.eval]
  | cons x l ihx ihl =>
    intro B ρ hρ
    have hx := ihx B ρ hρ; have hl := ihl B ρ hρ
    simp only [Ty.Fits, Expr.eval, Expr.cost, List.length_cons, List.mem_cons] at hl ⊢
    refine ⟨by omega, ?_⟩
    rintro y (rfl | hy)
    · exact Ty.fits_mono (by omega) _ _ hx
    · exact Ty.fits_mono (by omega) _ _ (hl.2 y hy)
  | len l ihl =>
    intro B ρ hρ
    have hl := ihl B ρ hρ; have := bits_le_succ (l.eval ρ).length
    simp only [Ty.Fits, Expr.eval, Expr.cost] at hl ⊢; omega
  | take n l _ ihl =>
    intro B ρ hρ
    have hl := ihl B ρ hρ
    simp only [Ty.Fits, Expr.eval, Expr.cost] at hl ⊢
    refine ⟨by have := List.length_take_le' (n.eval ρ) (l.eval ρ); omega, fun y hy => ?_⟩
    exact Ty.fits_mono (by omega) _ _ (hl.2 y (List.mem_of_mem_take hy))
  | appendL K a b iha ihb =>
    intro B ρ hρ
    have ha := iha B ρ hρ; have hb := ihb B ρ hρ
    simp only [Ty.Fits, Expr.eval, Expr.cost] at ha hb ⊢
    refine ⟨by have := List.length_take_le K (a.eval ρ ++ b.eval ρ); omega, fun y hy => ?_⟩
    rcases List.mem_append.1 (List.mem_of_mem_take hy) with hy | hy
    · exact Ty.fits_mono (by omega) _ _ (ha.2 y hy)
    · exact Ty.fits_mono (by omega) _ _ (hb.2 y hy)
  | findB K l p ihl _ =>
    intro B ρ hρ
    have hl := ihl B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Expr.eval, Expr.cost]
    rcases hf : ((l.eval ρ).take K).find? (fun x => p.eval (.cons x ρ)) with _ | v
    · trivial
    · exact Ty.fits_mono (by omega) _ _
        (hl.2 v (List.mem_of_mem_take (List.mem_of_find?_eq_some hf)))
  | mapB K l f ihl ihf =>
    intro B ρ hρ
    have hl := ihl B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Ty.Fits, Expr.eval, Expr.cost, List.length_map, List.mem_map]
    have hK : K ≤ K * (f.cost + 1) := Nat.le_mul_of_pos_right K (by omega)
    refine ⟨by have := List.length_take_le K (l.eval ρ); omega, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | h
      · simp at hx
      · exact h
    have hfK : f.cost + 1 ≤ K * (f.cost + 1) := Nat.le_mul_of_pos_left _ hK1
    exact Ty.fits_mono (by omega) _ _ (ihf _ _ (Env.fits_cons (hl.2 x (List.mem_of_mem_take hx))
      (Env.fits_mono (by omega) ρ hρ)))
  | foldrB K l z f ihl ihz ihf =>
    intro B ρ hρ
    have hl := ihl B ρ hρ; have hz := ihz B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Expr.eval, Expr.cost]
    have key := foldr_fits (fun A b => B + l.cost ≤ A ∧ Ty.Fits A _ b)
      (fun x => Ty.Fits (B + l.cost) _ x) (f.cost + 1)
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun A x b hx hb => ⟨by omega, Ty.fits_mono (by omega) _ _ (ihf _ _ (Env.fits_cons
        (Ty.fits_mono hb.1 _ _ hx) (Env.fits_cons hb.2
          (Env.fits_mono (by omega) ρ hρ))))⟩)
      ((l.eval ρ).take K) (B + l.cost + z.cost) (z.eval ρ)
      (fun x hx => hl.2 x (List.mem_of_mem_take hx))
      ⟨by omega, Ty.fits_mono (by omega) _ _ hz⟩
    have hlen := Nat.mul_le_mul_right (f.cost + 1) (List.length_take_le K (l.eval ρ))
    have hK := Nat.mul_le_mul_right (f.cost + 1) (List.length_take_le' K (l.eval ρ))
    exact Ty.fits_mono (by omega) _ _ key.2
  | tconst a iha =>
    intro B ρ hρ
    exact fun _ => Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (iha B ρ hρ)
  | tget m i ihm _ =>
    intro B ρ hρ
    exact Ty.fits_mono (by simp only [Expr.cost]; omega) _ _ (ihm B ρ hρ _)
  | tset m i a ihm _ iha =>
    intro B ρ hρ j
    simp only [Expr.eval, Expr.cost]
    split
    · exact Ty.fits_mono (by omega) _ _ (iha B ρ hρ)
    · exact Ty.fits_mono (by omega) _ _ (ihm B ρ hρ j)


/-! ## Programs -/

section Loops

open OracleComp

variable {ι : Type} {T : OracleSpec ι} {α β : Type}

theorem findML_mem (p : α → OracleComp T Bool) :
    ∀ (xs : List α) (v : α), some v ∈ support (findML p xs) → v ∈ xs
  | [], v, h => by simp [findML] at h
  | x :: xs, v, h => by
    simp only [findML, mem_support_bind_iff] at h
    obtain ⟨b, -, h⟩ := h
    split at h
    · simp at h; simp [h]
    · exact List.mem_cons_of_mem _ (findML_mem p xs v h)

theorem mapML_mem (f : α → OracleComp T β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (mapML f xs) →
      ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, y ∈ support (f x)
  | [], ys, h => by simp [mapML] at h; simp [h]
  | x :: xs, ys, h => by
    simp only [mapML, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    obtain ⟨hl, hm⟩ := mapML_mem f xs ys' hys'
    refine ⟨by simp [hl], ?_⟩
    rintro z (_ | ⟨_, hz⟩)
    · exact ⟨x, by simp, hy⟩
    · obtain ⟨x', hx', hz'⟩ := hm z hz; exact ⟨x', by simp [hx'], hz'⟩

theorem consumeFirstML_mem (p : α → OracleComp T Bool) (mk : α → α) :
    ∀ (xs : List α) (r : Bool × List α), r ∈ support (consumeFirstML p mk xs) →
      r.2.length = xs.length ∧ ∀ y ∈ r.2, ∃ x ∈ xs, y = x ∨ y = mk x
  | [], r, h => by simp [consumeFirstML] at h; simp [h]
  | x :: xs, r, h => by
    simp only [consumeFirstML, mem_support_bind_iff] at h
    obtain ⟨b, -, h⟩ := h
    split at h
    · simp only [support_pure, Set.mem_singleton_iff] at h; subst h
      refine ⟨by simp, ?_⟩
      rintro y (_ | ⟨_, hy⟩)
      · exact ⟨x, by simp, Or.inr rfl⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, Or.inl rfl⟩
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
      obtain ⟨r', hr', rfl⟩ := h
      obtain ⟨hl, hm⟩ := consumeFirstML_mem p mk xs r' hr'
      refine ⟨by simp [hl], ?_⟩
      rintro y (_ | ⟨_, hy⟩)
      · exact ⟨x, by simp, Or.inl rfl⟩
      · obtain ⟨x', hx', h'⟩ := hm y hy; exact ⟨x', by simp [hx'], h'⟩

theorem foldML_fits (P : ℕ → β → Prop) (Q : α → Prop) (D : ℕ) (f : α → β → OracleComp T β)
    (hf : ∀ A x b, Q x → P A b → ∀ b' ∈ support (f x b), P (A + D) b') :
    ∀ (xs : List α) (A : ℕ) (b : β), (∀ x ∈ xs, Q x) → P A b →
      ∀ y ∈ support (foldML f b xs), P (A + xs.length * D) y
  | [], A, b, _, hb, y, hy => by simp [foldML] at hy; subst hy; simpa using hb
  | x :: xs, A, b, hxs, hb, y, hy => by
    simp only [foldML, mem_support_bind_iff] at hy
    obtain ⟨b', hb', hy⟩ := hy
    have := foldML_fits P Q D f hf xs (A + D) b' (fun z hz => hxs z (by simp [hz]))
      (hf A x b (hxs x (by simp)) hb b' hb') y hy
    simp only [List.length_cons]
    rwa [show A + (xs.length + 1) * D = A + D + xs.length * D by ring]

theorem iterM_fits (P : ℕ → α → Prop) (D : ℕ) (f : α → OracleComp T α)
    (hf : ∀ A a, P A a → ∀ y ∈ support (f a), P (A + D) y) :
    ∀ (n A : ℕ) (a : α), P A a → ∀ y ∈ support (iterM f n a), P (A + n * D) y
  | 0, A, a, ha, y, hy => by simp [iterM] at hy; subst hy; simpa using ha
  | n + 1, A, a, ha, y, hy => by
    simp only [iterM, mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have := iterM_fits P D f hf n (A + D) z (hf A a ha z hz) y hy
    rwa [show A + (n + 1) * D = A + D + n * D by ring]

end Loops

theorem SampSizeHonest.empty : SampSizeHonest (Samplers.empty (S := S)) := fun s => s.elim

theorem SampSizeHonest.sum {X₁ X₂ : Samplers S} (h₁ : SampSizeHonest X₁)
    (h₂ : SampSizeHonest X₂) : SampSizeHonest (X₁.sum X₂)
  | .inl s, x, B, hx => h₁ s x B hx
  | .inr s, x, B, hx => h₂ s x B hx

variable {ι : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem Iface.support_liftP_subset (I : Iface S T) {α : Type} (p : ProbComp α) :
    support (I.liftP p) ⊆ support p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    intro y hy
    simp only [Iface.liftP, simulateQ_query_bind, mem_support_bind_iff] at hy
    obtain ⟨u, -, hy⟩ := hy
    simp only [mem_support_bind_iff]
    exact ⟨u, (OracleComp.mem_support_liftM_iff _ _).2 ⟨u, rfl⟩, ih u hy⟩

abbrev Comp.nq {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) : ℕ :=
  c.queries (fun _ => 1) (fun _ => 1)

/-- Every value returned by `c.eval ρ` fits the input bound plus `c.cost + c.nq * aB`. -/
theorem Comp.fits_eval (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ (B : ℕ) (ρ : Env Γ), Env.Fits B ρ → ∀ y ∈ support (c.eval ρ),
      t.Fits (B + c.cost + c.nq * aB) y := by
  induction c with
  | ret e =>
    intro B ρ hρ y hy
    simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact Ty.fits_mono (by simp only [Comp.cost]; omega) _ _ (Expr.fits_eval hO e B ρ hρ)
  | bind c k ihc ihk =>
    intro B ρ hρ y hy
    simp only [Comp.eval, mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    have h1 := ihc B ρ hρ x hx
    have h2 := ihk _ _ (Env.fits_cons h1 (Env.fits_mono (by omega) ρ hρ)) y hy
    refine Ty.fits_mono ?_ _ _ h2
    simp only [Comp.nq, Comp.cost, Comp.queries, Nat.add_mul]; omega
  | ite b c d ihc ihd =>
    intro B ρ hρ y hy
    have hl := Nat.mul_le_mul_right aB (le_max_left c.nq d.nq)
    have hr := Nat.mul_le_mul_right aB (le_max_right c.nq d.nq)
    simp only [Comp.eval] at hy
    split at hy
    · exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
        (ihc B ρ hρ y hy)
    · exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
        (ihd B ρ hρ y hy)
  | caseOpt e n s ihn ihs =>
    intro B ρ hρ y hy
    have he := Expr.fits_eval hO e B ρ hρ
    have hl := Nat.mul_le_mul_right aB (le_max_left n.nq s.nq)
    have hr := Nat.mul_le_mul_right aB (le_max_right n.nq s.nq)
    simp only [Comp.eval] at hy
    split at hy
    · exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
        (ihn B ρ hρ y hy)
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
        (ihs _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)) y hy)
  | caseSum e l r ihl ihr =>
    intro B ρ hρ y hy
    have he := Expr.fits_eval hO e B ρ hρ
    have hl := Nat.mul_le_mul_right aB (le_max_left l.nq r.nq)
    have hr := Nat.mul_le_mul_right aB (le_max_right l.nq r.nq)
    simp only [Comp.eval] at hy
    split at hy
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
        (ihl _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)) y hy)
    · next x hx =>
      rw [hx] at he
      exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
        (ihr _ _ (Env.fits_cons he (Env.fits_mono (by omega) ρ hρ)) y hy)
  | sample s e =>
    intro B ρ hρ y hy
    simp only [Comp.eval] at hy
    have := hS s _ _ (Expr.fits_eval hO e B ρ hρ) y (I.support_liftP_subset _ hy)
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries]; omega) _ _ this
  | query g e =>
    intro B ρ hρ y hy
    simp only [Comp.eval, support_map, Set.mem_image] at hy
    obtain ⟨u, -, rfl⟩ := hy
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries]; omega) _ _
      (hq g _ u)
  | iter n e body ihb =>
    intro B ρ hρ y hy
    simp only [Comp.eval] at hy
    have he := Expr.fits_eval hO e B ρ hρ
    have key := iterM_fits (fun A a => B ≤ A ∧ Ty.Fits A _ a) (body.cost + body.nq * aB)
      (fun a => body.eval (.cons a ρ))
      (fun A a ha y hy => ⟨by omega, Ty.fits_mono (by omega) _ _ (ihb _ _ (Env.fits_cons ha.2
        (Env.fits_mono ha.1 ρ hρ)) y hy)⟩) n (B + e.cost) (e.eval ρ) ⟨by omega, he⟩ y hy
    have e1 : n * (body.cost + body.nq * aB) = n * body.cost + n * body.nq * aB := by ring
    have e2 : n * (body.cost + 1) = n * body.cost + n := by ring
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _ key.2
  | findM K l p _ =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    rcases y with _ | v
    · trivial
    · exact Ty.fits_mono (by simp only [Comp.cost]; omega) _ _
        (hl.2 v (List.mem_of_mem_take (findML_mem _ _ v hy)))
  | anyM => intros; trivial
  | mapM K l f ihf =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    obtain ⟨hlen, hm⟩ := mapML_mem _ _ y hy
    have := List.length_take_le' K (l.eval ρ)
    simp only [Ty.Fits]
    refine ⟨by simp only [Comp.cost]; omega, fun z hz => ?_⟩
    obtain ⟨x, hx, hz⟩ := hm z hz
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | h
      · simp at hx
      · exact h
    have h1 : f.cost + 1 ≤ K * (f.cost + 1) := Nat.le_mul_of_pos_left _ hK1
    have h2 : f.nq * aB ≤ K * f.nq * aB := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hK1
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _
      (ihf _ _ (Env.fits_cons (hl.2 x (List.mem_of_mem_take hx))
        (Env.fits_mono (by omega) ρ hρ)) z hz)
  | consumeFirstM K l p mk _ =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    obtain ⟨hlen, hm⟩ := consumeFirstML_mem _ _ _ y hy
    have := List.length_take_le' K (l.eval ρ)
    refine ⟨trivial, ?_⟩
    simp only [Ty.Fits]
    refine ⟨by simp only [Comp.cost]; omega, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl | rfl⟩ := hm z hz
    · exact Ty.fits_mono (by simp only [Comp.cost]; omega) _ _
        (hl.2 _ (List.mem_of_mem_take hx))
    · have hK1 : 1 ≤ K := by
        rcases Nat.eq_zero_or_pos K with rfl | h
        · simp at hx
        · exact h
      have h1 : p.cost + mk.cost + 1 ≤ K * (p.cost + mk.cost + 1) :=
        Nat.le_mul_of_pos_left _ hK1
      exact Ty.fits_mono (by simp only [Comp.cost]; omega) _ _
        (Expr.fits_eval hO mk _ _ (Env.fits_cons (hl.2 x (List.mem_of_mem_take hx))
          (Env.fits_mono (by omega) ρ hρ)))
  | foldM K l z f ihf =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval hO l B ρ hρ
    have hz := Expr.fits_eval hO z B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    have key := foldML_fits (fun A b => B + l.cost ≤ A ∧ Ty.Fits A _ b)
      (fun x => Ty.Fits (B + l.cost) _ x) (f.cost + f.nq * aB)
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun A x b hx hb b' hb' => ⟨by omega, Ty.fits_mono (by omega) _ _ (ihf _ _
        (Env.fits_cons (Ty.fits_mono hb.1 _ _ hx) (Env.fits_cons hb.2
          (Env.fits_mono (by omega) ρ hρ))) b' hb')⟩)
      ((l.eval ρ).take K) (B + l.cost + z.cost) (z.eval ρ)
      (fun x hx => hl.2 x (List.mem_of_mem_take hx))
      ⟨by omega, Ty.fits_mono (by omega) _ _ hz⟩ y hy
    have hK := Nat.mul_le_mul_right (f.cost + f.nq * aB) (List.length_take_le K (l.eval ρ))
    have e1 : K * (f.cost + f.nq * aB) = K * f.cost + K * f.nq * aB := by ring
    have e2 : K * (f.cost + 1) = K * f.cost + K := by ring
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries] at *; omega) _ _ key.2

/-! ## Reductions -/

section Reductions

open OracleComp

theorem Env.fits_pair {B₁ B₂ : ℕ} {t u : Ty S} {x : t.denote} {y : u.denote}
    (hx : t.Fits B₁ x) (hy : u.Fits B₂ y) :
    Env.Fits (B₁ + B₂) (.cons x (.cons y .nil)) :=
  ⟨Ty.fits_mono (by omega) _ _ hx, Ty.fits_mono (by omega) _ _ hy, trivial⟩

theorem Env.fits_triple {B₁ B₂ B₃ : ℕ} {t u v : Ty S} {x : t.denote} {y : u.denote} {z : v.denote}
    (hx : t.Fits B₁ x) (hy : u.Fits B₂ y) (hz : v.Fits B₃ z) :
    Env.Fits (B₁ + B₂ + B₃) (.cons x (.cons y (.cons z .nil))) :=
  ⟨Ty.fits_mono (by omega) _ _ hx, Ty.fits_mono (by omega) _ _ hy,
    Ty.fits_mono (by omega) _ _ hz, trivial⟩

abbrev CostedReduction.nq {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out) (qAdv : ℕ) : ℕ :=
  R.totalQueries (fun _ => 1) (fun _ => 1) qAdv

abbrev TwoStageCostedReduction.nq {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (qAdv : ℕ) : ℕ :=
  R.totalQueries (fun _ => 1) (fun _ => 1) qAdv

theorem CostedReduction.fits_simulateQ {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t)) :
    ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {qAdv : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) qAdv →
      ∀ (B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
        ∀ r ∈ support ((simulateQ R.impl oa).run s),
          R.σ.Fits (B + qAdv * (qB + R.handle.cost + R.handle.nq * aB)) r.2 := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ B s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro qAdv hb B s hs r hr
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
    cases q with
    | inl n =>
      simp only [CostedReduction.impl, handlerImpl, StateT.run_lift, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨u, -, hvs⟩ := hstep
      cases hvs
      exact ih v (hb.2 v) B s hs r hr
    | inr t =>
      have hpos : 0 < qAdv := hb.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hb.2 u
      simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨⟨ans, s₁⟩, hstep, hvs⟩ := hstep
      cases hvs
      have hs₁ : R.σ.Fits (B + qB + R.handle.cost + R.handle.nq * aB) s₁ :=
        (Comp.fits_eval hO hS aB hq R.handle (B + qB) _
          (Env.fits_pair hs (henc t)) (ans, s₁) hstep).2
      have hrec := ih (C.rdec t ans) (hqm _)
        (B + qB + R.handle.cost + R.handle.nq * aB) s₁ hs₁ r hr
      have hring : (m + 1) * (qB + R.handle.cost + R.handle.nq * aB) =
          (qB + R.handle.cost + R.handle.nq * aB) +
            m * (qB + R.handle.cost + R.handle.nq * aB) := by ring
      exact Ty.fits_mono (by omega) _ _ hrec

/-- Every output of `R.eval A x` fits `B + aAdvB + qAdv * qB + R.totalCost qAdv + R.nq qAdv * aB`. -/
theorem CostedReduction.fits_eval {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (qAdv B : ℕ)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv)
    (x : rIn.denote) (hx : rIn.Fits B x) :
    ∀ y ∈ support (R.eval A x),
      out.Fits (B + aAdvB + qAdv * qB + R.totalCost qAdv + R.nq qAdv * aB) y := by
  intro y hy
  simp only [CostedReduction.eval, mem_support_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, ⟨outAdv, s₁⟩, hs₁, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval hO hS aB hq R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have h1 := R.fits_simulateQ hO hS aB hq qB henc (hb oAdv) _ s₀ h0 (outAdv, s₁) hs₁
  have h2 := Comp.fits_eval hO hS aB hq R.finish _ (.cons s₁ (.cons outAdv .nil))
    (Env.fits_pair h1 (hA outAdv)) y hy
  refine Ty.fits_mono ?_ _ _ h2
  have hle : qAdv * R.handle.cost ≤ qAdv * max I.uCost (R.handle.cost + C.codecCost) :=
    Nat.mul_le_mul_left qAdv (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have e1 : qAdv * (qB + R.handle.cost + R.handle.nq * aB) =
      qAdv * qB + qAdv * R.handle.cost + qAdv * R.handle.nq * aB := by ring
  have e2 : (R.init.nq + qAdv * R.handle.nq + R.finish.nq) * aB =
      R.init.nq * aB + qAdv * R.handle.nq * aB + R.finish.nq * aB := by ring
  dsimp only [CostedReduction.totalCost, CostedReduction.nq, CostedReduction.totalQueries, Comp.nq] at e1 e2 ⊢
  omega

theorem runFuel_fits {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ∀ (fuel B : ℕ) (s : σ.denote), σ.Fits B s →
      ∀ r ∈ support (runFuel h dflt oa fuel s),
        σ.Fits (B + fuel * (qB + h.cost + h.nq * aB)) r.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel B s hs r hr
    simp only [runFuel, construct_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro fuel B s hs r hr
    cases q with
    | inl n =>
      simp only [runFuel, construct_query_bind, mem_support_bind_iff] at hr
      obtain ⟨u, -, hr⟩ := hr
      exact ih u fuel B s hs r hr
    | inr t =>
      cases fuel with
      | zero =>
        simp only [runFuel, construct_query_bind, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact Ty.fits_mono (by omega) _ _ hs
      | succ f =>
        simp only [runFuel, construct_query_bind, mem_support_bind_iff] at hr
        obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
        have hs' : σ.Fits (B + qB + h.cost + h.nq * aB) s' :=
          (Comp.fits_eval hO hS aB hq h (B + qB) _
            (Env.fits_pair hs (henc t)) (v, s') hstep).2
        have hrec := ih (C.rdec t v) f (B + qB + h.cost + h.nq * aB) s' hs' r hr
        have hring : (f + 1) * (qB + h.cost + h.nq * aB) =
            (qB + h.cost + h.nq * aB) + f * (qB + h.cost + h.nq * aB) := by ring
        exact Ty.fits_mono (by omega) _ _ hrec

def Mid.Fits {κ : Type} {G : OracleSpec κ} {α : Type} (π σ ch : Ty S) (B : ℕ) :
    Mid G α π.denote σ.denote ch.denote → Prop
  | .done _ s => σ.Fits B s
  | .paused _ c p s _ => ch.Fits B c ∧ π.Fits B p ∧ σ.Fits B s

theorem Mid.fits_mono {κ : Type} {G : OracleSpec κ} {α : Type} {π σ ch : Ty S} {B B' : ℕ}
    (h : B ≤ B') : ∀ m : Mid G α π.denote σ.denote ch.denote,
      Mid.Fits π σ ch B m → Mid.Fits π σ ch B' m
  | .done _ s, hs => Ty.fits_mono h _ s hs
  | .paused _ c p s _, ⟨hc, hp, hs⟩ =>
    ⟨Ty.fits_mono h _ c hc, Ty.fits_mono h _ p hp, Ty.fits_mono h _ s hs⟩

theorem TwoStageCostedReduction.fits_run1 {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ∀ (fuel B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
      ∀ m ∈ support (R.run1 dflt oa fuel s),
        Mid.Fits R.π R.σ ch (B + fuel * (qB + R.handlePre.cost + R.handlePre.nq * aB)) m := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel B s hs m hm
    simp only [TwoStageCostedReduction.run1, construct_pure, support_pure, Set.mem_singleton_iff] at hm
    subst hm
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro fuel B s hs m hm
    cases q with
    | inl n =>
      simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
      obtain ⟨u, -, hm⟩ := hm
      exact ih u fuel B s hs m hm
    | inr t =>
      cases fuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact Ty.fits_mono (by omega) _ _ hs
      | succ f =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_support_bind_iff] at hm
        obtain ⟨res, hstep, hm⟩ := hm
        have hres := Comp.fits_eval hO hS aB hq R.handlePre (B + qB) _
          (Env.fits_pair hs (henc t)) res hstep
        have hring : (f + 1) * (qB + R.handlePre.cost + R.handlePre.nq * aB) =
            (qB + R.handlePre.cost + R.handlePre.nq * aB) +
              f * (qB + R.handlePre.cost + R.handlePre.nq * aB) := by ring
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · have hrec := ih (C.rdec t v) f (B + qB + R.handlePre.cost + R.handlePre.nq * aB)
            s' hres.2 m hm
          exact Mid.fits_mono (by omega) m hrec
        · simp only [support_pure, Set.mem_singleton_iff] at hm
          subst hm
          exact Mid.fits_mono (by omega) _ ⟨hres.1, hres.2.1, hres.2.2⟩

/-- Every `(c, m)` produced by `R.eval1 A x fuel dflt` satisfies the stage-1 size bound. -/
theorem TwoStageCostedReduction.fits_eval1 {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (fuel B : ℕ)
    (x : rIn.denote) (hx : rIn.Fits B x) (dflt : aOut.denote) :
    ∀ y ∈ support (R.eval1 A x fuel dflt),
      ch.Fits (B + aAdvB + fuel * qB + R.totalCost fuel + R.nq fuel * aB) y.1 ∧
      Mid.Fits R.π R.σ ch (B + R.init.cost + R.init.nq * aB +
        fuel * (qB + R.handlePre.cost + R.handlePre.nq * aB)) y.2 := by
  intro y hy
  simp only [TwoStageCostedReduction.eval1, mem_support_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, m, hm, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval hO hS aB hq R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have hmFits := R.fits_run1 hO hS aB hq qB henc dflt (A oAdv) fuel _ s₀ h0 m hm
  have hleCost : fuel * R.handlePre.cost ≤
      fuel * max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    Nat.mul_le_mul_left fuel (le_trans (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
      (le_max_right _ _))
  have hleNq : (fuel * R.handlePre.nq) * aB ≤
      (fuel * max R.handlePre.nq R.handlePost.nq) * aB :=
    Nat.mul_le_mul_right aB (Nat.mul_le_mul_left fuel (le_max_left _ _))
  have hleChCost := le_max_left R.chDone.cost R.resume.cost
  have hleChNq := Nat.mul_le_mul_right aB (le_max_left R.chDone.nq R.resume.nq)
  have hring1 : fuel * (qB + R.handlePre.cost + R.handlePre.nq * aB) =
      fuel * qB + fuel * R.handlePre.cost + (fuel * R.handlePre.nq) * aB := by ring
  have hring2 : (R.init.nq + fuel * max R.handlePre.nq R.handlePost.nq +
      max R.chDone.nq R.resume.nq + R.finish.nq) * aB =
      R.init.nq * aB + (fuel * max R.handlePre.nq R.handlePost.nq) * aB +
        max R.chDone.nq R.resume.nq * aB + R.finish.nq * aB := by ring
  dsimp only [Comp.nq] at hleNq hleChNq hring1 hring2
  cases m with
  | done b s' =>
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := Comp.fits_eval hO hS aB hq R.chDone _ (.cons s' (.cons b .nil))
      (Env.fits_pair hmFits (hA b)) c hc
    have hc'' : ch.Fits (B + aAdvB + fuel * qB + R.totalCost fuel + R.nq fuel * aB) c := by
      refine Ty.fits_mono ?_ _ _ hc'
      dsimp only [TwoStageCostedReduction.totalCost, TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq] at *
      omega
    exact ⟨hc'', hmFits⟩
  | paused t c p s' k =>
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    have hc'' : ch.Fits (B + aAdvB + fuel * qB + R.totalCost fuel + R.nq fuel * aB) c := by
      refine Ty.fits_mono ?_ _ _ hmFits.1
      dsimp only [TwoStageCostedReduction.totalCost, TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries, Comp.nq] at *
      omega
    exact ⟨hc'', hmFits⟩

/-- Every output of `R.eval2 m y fuel₂ dflt` fits `B₁ + B₂ + aAdvB + fuel₂ * qB + stage2Cost + stage2Nq * aB`. -/
theorem TwoStageCostedReduction.fits_eval2 {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    (qB : ℕ) (henc : ∀ t, C.Q.Fits qB (C.qenc t))
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (B₁ : ℕ)
    (hm : Mid.Fits R.π R.σ ch B₁ m)
    (y : rIn2.denote) (B₂ : ℕ) (hy : rIn2.Fits B₂ y) (fuel₂ : ℕ) (dflt : aOut.denote) :
    ∀ z ∈ support (R.eval2 m y fuel₂ dflt),
      out.Fits (B₁ + B₂ + aAdvB + fuel₂ * qB +
        (R.resume.cost + fuel₂ * R.handlePost.cost + R.finish.cost) +
        (R.resume.nq + fuel₂ * R.handlePost.nq + R.finish.nq) * aB) z := by
  intro z hz
  have hring1 : fuel₂ * (qB + R.handlePost.cost + R.handlePost.nq * aB) =
      fuel₂ * qB + fuel₂ * R.handlePost.cost + fuel₂ * R.handlePost.nq * aB := by ring
  have hring2 : (R.resume.nq + fuel₂ * R.handlePost.nq + R.finish.nq) * aB =
      R.resume.nq * aB + fuel₂ * R.handlePost.nq * aB + R.finish.nq * aB := by ring
  dsimp only [Comp.nq] at hring1 hring2
  cases m with
  | done b s =>
    simp only [TwoStageCostedReduction.eval2, pure_bind] at hz
    have hf := Comp.fits_eval hO hS aB hq R.finish _ (.cons s (.cons b (.cons y .nil)))
      (Env.fits_triple hm (hA b) hy) z hz
    refine Ty.fits_mono ?_ _ _ hf
    dsimp only [Comp.nq] at *
    omega
  | paused t c p s k =>
    simp only [TwoStageCostedReduction.eval2, mem_support_bind_iff] at hz
    obtain ⟨⟨v, s₁⟩, hres, ⟨b, s₂⟩, hrun, hz⟩ := hz
    have hs₁' : R.σ.Fits (B₁ + B₂ + R.resume.cost + R.resume.nq * aB) s₁ := by
      have henv : Env.Fits (B₁ + B₂) (.cons s (.cons p (.cons y .nil))) :=
        ⟨Ty.fits_mono (by omega) _ _ hm.2.2, Ty.fits_mono (by omega) _ _ hm.2.1,
          Ty.fits_mono (by omega) _ _ hy, trivial⟩
      exact (Comp.fits_eval hO hS aB hq R.resume (B₁ + B₂) _ henv (v, s₁) hres).2
    have hs₂ := runFuel_fits R.handlePost hO hS aB hq qB henc dflt (k (C.rdec t v))
      fuel₂ _ s₁ hs₁' (b, s₂) hrun
    have henv₂ : Env.Fits
        (B₁ + B₂ + R.resume.cost + R.resume.nq * aB +
          fuel₂ * (qB + R.handlePost.cost + R.handlePost.nq * aB) + aAdvB)
        (.cons s₂ (.cons b (.cons y .nil))) :=
      ⟨Ty.fits_mono (by omega) _ _ hs₂, Ty.fits_mono (by omega) _ _ (hA b),
        Ty.fits_mono (by omega) _ _ hy, trivial⟩
    have hf := Comp.fits_eval hO hS aB hq R.finish _ (.cons s₂ (.cons b (.cons y .nil)))
      henv₂ z hz
    refine Ty.fits_mono ?_ _ _ hf
    dsimp only [Comp.nq] at *
    omega

/-! ## Input-conditioned and dual-fuel size bounds -/

/-- Every `.inr t` game query along every reachable branch of `oa` satisfies `qPred t`. -/
def AllGameQueries {κ : Type} {G : OracleSpec κ} (qPred : κ → Prop) :
    {α : Type} → OracleComp (unifSpec + G) α → Prop :=
  OracleComp.construct (C := fun _ => Prop)
    (fun _ => True)
    (fun q _ r => (match q with | .inl _ => True | .inr t => qPred t) ∧ ∀ u, r u)

theorem CostedReduction.fits_simulateQ_on {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {qPred : κ → Prop} (qB : ℕ) (henc : C.FitsOn qPred qB) :
    ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {qAdv : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) qAdv →
      AllGameQueries qPred oa →
      ∀ (B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
        ∀ r ∈ support ((simulateQ R.impl oa).run s),
          R.σ.Fits (B + qAdv * (qB + R.handle.cost + R.handle.nq * aB)) r.2 := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ _ B s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro qAdv hb hqp B s hs r hr
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [AllGameQueries, construct_query_bind] at hqp
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
    cases q with
    | inl n =>
      simp only [CostedReduction.impl, handlerImpl, StateT.run_lift, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨u, -, hvs⟩ := hstep
      cases hvs
      exact ih v (hb.2 v) (hqp.2 v) B s hs r hr
    | inr t =>
      have hpos : 0 < qAdv := hb.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hb.2 u
      simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hstep
      obtain ⟨⟨ans, s₁⟩, hstep, hvs⟩ := hstep
      cases hvs
      have hs₁ : R.σ.Fits (B + qB + R.handle.cost + R.handle.nq * aB) s₁ :=
        (Comp.fits_eval hO hS aB hq R.handle (B + qB) _
          (Env.fits_pair hs (henc t hqp.1)) (ans, s₁) hstep).2
      have hrec := ih (C.rdec t ans) (hqm _) (hqp.2 _)
        (B + qB + R.handle.cost + R.handle.nq * aB) s₁ hs₁ r hr
      have hring : (m + 1) * (qB + R.handle.cost + R.handle.nq * aB) =
          (qB + R.handle.cost + R.handle.nq * aB) +
            m * (qB + R.handle.cost + R.handle.nq * aB) := by ring
      exact Ty.fits_mono (by omega) _ _ hrec

/-- One-stage reduction size bound with the codec premise restricted to `AllGameQueries qPred`. -/
theorem CostedReduction.fits_eval_on {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {qPred : κ → Prop} (qB : ℕ) (henc : C.FitsOn qPred qB)
    (aAdvB : ℕ) (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (qAdv B : ℕ)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv)
    (hqp : ∀ a, AllGameQueries qPred (A a))
    (x : rIn.denote) (hx : rIn.Fits B x) :
    ∀ y ∈ support (R.eval A x),
      out.Fits (B + aAdvB + qAdv * qB + R.totalCost qAdv + R.nq qAdv * aB) y := by
  intro y hy
  simp only [CostedReduction.eval, mem_support_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, ⟨outAdv, s₁⟩, hs₁, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval hO hS aB hq R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have h1 := R.fits_simulateQ_on hO hS aB hq qB henc (hb oAdv) (hqp oAdv) _ s₀ h0 (outAdv, s₁) hs₁
  have h2 := Comp.fits_eval hO hS aB hq R.finish _ (.cons s₁ (.cons outAdv .nil))
    (Env.fits_pair h1 (hA outAdv)) y hy
  refine Ty.fits_mono ?_ _ _ h2
  have hle : qAdv * R.handle.cost ≤ qAdv * max I.uCost (R.handle.cost + C.codecCost) :=
    Nat.mul_le_mul_left qAdv (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have e1 : qAdv * (qB + R.handle.cost + R.handle.nq * aB) =
      qAdv * qB + qAdv * R.handle.cost + qAdv * R.handle.nq * aB := by ring
  have e2 : (R.init.nq + qAdv * R.handle.nq + R.finish.nq) * aB =
      R.init.nq * aB + qAdv * R.handle.nq * aB + R.finish.nq * aB := by ring
  dsimp only [CostedReduction.totalCost, CostedReduction.nq, CostedReduction.totalQueries, Comp.nq] at e1 e2 ⊢
  omega

theorem runFuelBounded_fits_on {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {qPred : κ → Prop} (qB : ℕ) (henc : C.FitsOn qPred qB)
    {α : Type} (dflt : α) {oa : OracleComp (unifSpec + G) α}
    (hqp : AllGameQueries qPred oa) :
    ∀ (uFuel gFuel B : ℕ) (s : σ.denote), σ.Fits B s →
      ∀ r ∈ support (runFuelBounded h dflt oa uFuel gFuel s),
        σ.Fits (B + gFuel * (qB + h.cost + h.nq * aB)) r.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro uFuel gFuel B s hs r hr
    simp only [runFuelBounded, construct_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    simp only [AllGameQueries, construct_query_bind] at hqp
    intro uFuel gFuel B s hs r hr
    cases q with
    | inl n =>
      cases uFuel with
      | zero =>
        simp only [runFuelBounded, construct_query_bind, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact Ty.fits_mono (by omega) _ _ hs
      | succ uf =>
        simp only [runFuelBounded, construct_query_bind, mem_support_bind_iff] at hr
        obtain ⟨u, -, hr⟩ := hr
        exact ih u (hqp.2 u) uf gFuel B s hs r hr
    | inr t =>
      cases gFuel with
      | zero =>
        simp only [runFuelBounded, construct_query_bind, support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact Ty.fits_mono (by omega) _ _ hs
      | succ gf =>
        simp only [runFuelBounded, construct_query_bind, mem_support_bind_iff] at hr
        obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
        have hs' : σ.Fits (B + qB + h.cost + h.nq * aB) s' :=
          (Comp.fits_eval hO hS aB hq h (B + qB) _
            (Env.fits_pair hs (henc t hqp.1)) (v, s') hstep).2
        have hrec := ih (C.rdec t v) (hqp.2 _) uFuel gf (B + qB + h.cost + h.nq * aB) s' hs' r hr
        have hring : (gf + 1) * (qB + h.cost + h.nq * aB) =
            (qB + h.cost + h.nq * aB) + gf * (qB + h.cost + h.nq * aB) := by ring
        exact Ty.fits_mono (by omega) _ _ hrec

theorem TwoStageCostedReduction.fits_run1Bounded_on {κ : Type} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    (hq : ∀ g x u, (I.cod g).Fits aB (I.dec g x u))
    {qPred : κ → Prop} (qB : ℕ) (henc : C.FitsOn qPred qB)
    {α : Type} (dflt : α) {oa : OracleComp (unifSpec + G) α}
    (hqp : AllGameQueries qPred oa) :
    ∀ (uFuel gFuel B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
      ∀ m ∈ support (R.run1Bounded dflt oa uFuel gFuel s),
        Mid.Fits R.π R.σ ch (B + gFuel * (qB + R.handlePre.cost + R.handlePre.nq * aB)) m ∧
        (match m with | .done _ _ => True | .paused _ _ _ _ k => ∀ u, AllGameQueries qPred (k u)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro uFuel gFuel B s hs m hm
    simp only [TwoStageCostedReduction.run1Bounded, construct_pure, support_pure,
      Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨Ty.fits_mono (by omega) _ _ hs, trivial⟩
  | query_bind q mx ih =>
    simp only [AllGameQueries, construct_query_bind] at hqp
    intro uFuel gFuel B s hs m hm
    cases q with
    | inl n =>
      cases uFuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind, support_pure,
          Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨Ty.fits_mono (by omega) _ _ hs, trivial⟩
      | succ uf =>
        simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind,
          mem_support_bind_iff] at hm
        obtain ⟨u, -, hm⟩ := hm
        exact ih u (hqp.2 u) uf gFuel B s hs m hm
    | inr t =>
      cases gFuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind, support_pure,
          Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨Ty.fits_mono (by omega) _ _ hs, trivial⟩
      | succ gf =>
        simp only [TwoStageCostedReduction.run1Bounded, construct_query_bind,
          mem_support_bind_iff] at hm
        obtain ⟨res, hstep, hm⟩ := hm
        have hres := Comp.fits_eval hO hS aB hq R.handlePre (B + qB) _
          (Env.fits_pair hs (henc t hqp.1)) res hstep
        have hring : (gf + 1) * (qB + R.handlePre.cost + R.handlePre.nq * aB) =
            (qB + R.handlePre.cost + R.handlePre.nq * aB) +
              gf * (qB + R.handlePre.cost + R.handlePre.nq * aB) := by ring
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · have hrec := ih (C.rdec t v) (hqp.2 _) uFuel gf
            (B + qB + R.handlePre.cost + R.handlePre.nq * aB) s' hres.2 m hm
          exact ⟨Mid.fits_mono (by omega) m hrec.1, hrec.2⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hm
          subst hm
          exact ⟨Mid.fits_mono (by omega) _ ⟨hres.1, hres.2.1, hres.2.2⟩, hqp.2⟩

end Reductions

/-! ## Cost-independent leaf block width and tree weight -/

section BaseFitsAndTreeWeight

open OracleComp

theorem Ty.baseFits_mono {W W' : ℕ} (h : W ≤ W') :
    ∀ (t : Ty S) (x : t.denote), t.BaseFits W x → t.BaseFits W' x
  | .base _, _, hx => by simp only [Ty.BaseFits] at hx ⊢; omega
  | .unit, _, _ => trivial
  | .bool, _, _ => trivial
  | .nat, _, _ => trivial
  | .opt _, none, _ => trivial
  | .opt t, some a, hx => Ty.baseFits_mono h t a hx
  | .prod t u, x, hx => ⟨Ty.baseFits_mono h t _ hx.1, Ty.baseFits_mono h u _ hx.2⟩
  | .sum t _, .inl a, hx => Ty.baseFits_mono h t a hx
  | .sum _ u, .inr b, hx => Ty.baseFits_mono h u b hx
  | .list t, l, hx => fun x hm => Ty.baseFits_mono h t x (hx x hm)
  | .tbl t, m, hx => fun i => Ty.baseFits_mono h t _ (hx i)

theorem Ty.baseFits_of_fits {B : ℕ} : ∀ (t : Ty S) (x : t.denote), t.Fits B x → t.BaseFits B x
  | .base _, _, hx => hx
  | .unit, _, _ | .bool, _, _ | .nat, _, _ | .opt _, none, _ => trivial
  | .opt t, some a, hx => Ty.baseFits_of_fits t a hx
  | .prod t u, _, hx => ⟨Ty.baseFits_of_fits t _ hx.1, Ty.baseFits_of_fits u _ hx.2⟩
  | .sum t _, .inl a, hx => Ty.baseFits_of_fits t a hx
  | .sum _ u, .inr b, hx => Ty.baseFits_of_fits u b hx
  | .list t, _, hx => fun x hm => Ty.baseFits_of_fits t x (hx.2 x hm)
  | .tbl t, _, hx => fun i => Ty.baseFits_of_fits t _ (hx i)

def Env.BaseFits (W : ℕ) : {Γ : List (Ty S)} → Env Γ → Prop
  | _, .nil => True
  | _, .cons (t := t) x ρ => t.BaseFits W x ∧ Env.BaseFits W ρ

theorem Env.baseFits_get {W : ℕ} : ∀ {Γ : List (Ty S)} {t : Ty S} (ρ : Env Γ) (v : Var Γ t),
    Env.BaseFits W ρ → t.BaseFits W (ρ.get v)
  | _, _, .cons _ _, .zero, hρ => hρ.1
  | _, _, .cons _ ρ, .succ v, hρ => Env.baseFits_get ρ v hρ.2

theorem OpsBaseBounded.sum {O₁ O₂ : Ops S} {W₁ W₂ : ℕ}
    (h₁ : OpsBaseBounded O₁ W₁) (h₂ : OpsBaseBounded O₂ W₂) :
    OpsBaseBounded (O₁.sum O₂) (max W₁ W₂)
  | .inl o, x, W, hx => Ty.baseFits_mono (by omega) _ _ (h₁ o x W hx)
  | .inr o, x, W, hx => Ty.baseFits_mono (by omega) _ _ (h₂ o x W hx)

theorem Expr.baseFits_eval_preserve {O : Ops S} {W_op W : ℕ} (hO : OpsBaseBounded O W_op)
    (hW : W_op ≤ W) {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    ∀ (ρ : Env Γ), Env.BaseFits W ρ → t.BaseFits W (e.eval ρ) := by
  have hmax : max W W_op = W := Nat.max_eq_left hW
  induction e with
  | var v => intro ρ hρ; exact Env.baseFits_get ρ v hρ
  | unit | bool | nat | add | sub | mulK | divK | modK | lt | eqN | not | and | none | len | anyB =>
    intros; trivial
  | ite c a b _ iha ihb =>
    intro ρ hρ; simp only [Expr.eval]; split
    · exact iha ρ hρ
    · exact ihb ρ hρ
  | pair a b iha ihb => intro ρ hρ; exact ⟨iha ρ hρ, ihb ρ hρ⟩
  | fst a iha => intro ρ hρ; exact (iha ρ hρ).1
  | snd a iha => intro ρ hρ; exact (iha ρ hρ).2
  | inl a iha => intro ρ hρ; exact iha ρ hρ
  | inr a iha => intro ρ hρ; exact iha ρ hρ
  | some a iha => intro ρ hρ; exact iha ρ hρ
  | caseOpt e n s ihe ihn ihs =>
    intro ρ hρ; have he := ihe ρ hρ; simp only [Expr.eval]; split
    · exact ihn ρ hρ
    · next x hx => rw [hx] at he; exact ihs (.cons x ρ) ⟨he, hρ⟩
  | caseSum e l r ihe ihl ihr =>
    intro ρ hρ; have he := ihe ρ hρ; simp only [Expr.eval]; split
    · next x hx => rw [hx] at he; exact ihl (.cons x ρ) ⟨he, hρ⟩
    · next x hx => rw [hx] at he; exact ihr (.cons x ρ) ⟨he, hρ⟩
  | letE e b ihe ihb => intro ρ hρ; exact ihb (.cons (e.eval ρ) ρ) ⟨ihe ρ hρ, hρ⟩
  | op o a iha => intro ρ hρ; have := hO o _ W (iha ρ hρ); rwa [hmax] at this
  | nil => intro _ _ x hx; simp [Expr.eval] at hx
  | cons x l ihx ihl =>
    intro ρ hρ y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ihx ρ hρ
    · exact ihl ρ hρ y hy
  | take n l _ ihl =>
    intro ρ hρ y hy; exact ihl ρ hρ y (List.mem_of_mem_take hy)
  | appendL K a b iha ihb =>
    intro ρ hρ y hy
    rcases List.mem_append.1 (List.mem_of_mem_take hy) with hy | hy
    · exact iha ρ hρ y hy
    · exact ihb ρ hρ y hy
  | findB K l p ihl _ =>
    intro ρ hρ; simp only [Expr.eval]
    rcases hf : ((l.eval ρ).take K).find? (fun x => p.eval (.cons x ρ)) with _ | v
    · trivial
    · exact ihl ρ hρ v (List.mem_of_mem_take (List.mem_of_find?_eq_some hf))
  | mapB K l f ihl ihf =>
    intro ρ hρ y hy; simp only [Expr.eval, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ihf (.cons x ρ) ⟨ihl ρ hρ x (List.mem_of_mem_take hx), hρ⟩
  | foldrB K l z f ihl ihz ihf =>
    intro ρ hρ; simp only [Expr.eval]
    have key := foldr_fits (fun _ b => Ty.BaseFits W _ b) (fun x => Ty.BaseFits W _ x) 0
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun _ x b hx hb => ihf (.cons x (.cons b ρ)) ⟨hx, hb, hρ⟩)
      ((l.eval ρ).take K) 0 (z.eval ρ)
      (fun x hx => ihl ρ hρ x (List.mem_of_mem_take hx)) (ihz ρ hρ)
    exact key
  | tconst a iha => intro ρ hρ _; exact iha ρ hρ
  | tget m i ihm _ => intro ρ hρ; exact ihm ρ hρ _
  | tset m i a ihm _ iha =>
    intro ρ hρ j; simp only [Expr.eval]; split
    · exact iha ρ hρ
    · exact ihm ρ hρ j

theorem Comp.baseFits_eval_preserve {W_op W_samp W : ℕ}
    (hO : OpsBaseBounded O W_op) (hS : SampBaseBounded I.smp W_samp)
    (hWop : W_op ≤ W) (hWsamp : W_samp ≤ W)
    (hq : ∀ g x u, (I.cod g).BaseFits W (I.dec g x u))
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ (ρ : Env Γ), Env.BaseFits W ρ → ∀ y ∈ support (c.eval ρ), t.BaseFits W y := by
  have hmaxS : max W W_samp = W := Nat.max_eq_left hWsamp
  induction c with
  | ret e =>
    intro ρ hρ y hy
    simp only [Comp.eval, support_pure, Set.mem_singleton_iff] at hy; subst hy
    exact Expr.baseFits_eval_preserve hO hWop e ρ hρ
  | bind c k ihc ihk =>
    intro ρ hρ y hy; simp only [Comp.eval, mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    exact ihk (.cons x ρ) ⟨ihc ρ hρ x hx, hρ⟩ y hy
  | ite b c d ihc ihd =>
    intro ρ hρ y hy; simp only [Comp.eval] at hy; split at hy
    · exact ihc ρ hρ y hy
    · exact ihd ρ hρ y hy
  | caseOpt e n s ihn ihs =>
    intro ρ hρ y hy
    have he := Expr.baseFits_eval_preserve hO hWop e ρ hρ
    simp only [Comp.eval] at hy; split at hy
    · exact ihn ρ hρ y hy
    · next x hx => rw [hx] at he; exact ihs (.cons x ρ) ⟨he, hρ⟩ y hy
  | caseSum e l r ihl ihr =>
    intro ρ hρ y hy
    have he := Expr.baseFits_eval_preserve hO hWop e ρ hρ
    simp only [Comp.eval] at hy; split at hy
    · next x hx => rw [hx] at he; exact ihl (.cons x ρ) ⟨he, hρ⟩ y hy
    · next x hx => rw [hx] at he; exact ihr (.cons x ρ) ⟨he, hρ⟩ y hy
  | sample s e =>
    intro ρ hρ y hy; simp only [Comp.eval] at hy
    have := hS s _ W (Expr.baseFits_eval_preserve hO hWop e ρ hρ) y (I.support_liftP_subset _ hy)
    rwa [hmaxS] at this
  | query g e =>
    intro ρ hρ y hy; simp only [Comp.eval, support_map, Set.mem_image] at hy
    obtain ⟨u, -, rfl⟩ := hy; exact hq g _ u
  | iter n e body ihb =>
    intro ρ hρ y hy; simp only [Comp.eval] at hy
    exact iterM_fits (fun _ a => Ty.BaseFits W _ a) 0 (fun a => body.eval (.cons a ρ))
      (fun _ a ha z hz => ihb (.cons a ρ) ⟨ha, hρ⟩ z hz) n 0 (e.eval ρ)
      (Expr.baseFits_eval_preserve hO hWop e ρ hρ) y hy
  | findM K l p _ =>
    intro ρ hρ y hy
    have hl := Expr.baseFits_eval_preserve hO hWop l ρ hρ
    simp only [Comp.eval] at hy
    rcases y with _ | v
    · trivial
    · exact hl v (List.mem_of_mem_take (findML_mem _ _ v hy))
  | anyM => intros; trivial
  | mapM K l f ihf =>
    intro ρ hρ y hy
    have hl := Expr.baseFits_eval_preserve hO hWop l ρ hρ
    simp only [Comp.eval] at hy
    obtain ⟨_, hm⟩ := mapML_mem _ _ y hy
    intro z hz; obtain ⟨x, hx, hz⟩ := hm z hz
    exact ihf (.cons x ρ) ⟨hl x (List.mem_of_mem_take hx), hρ⟩ z hz
  | consumeFirstM K l p mk _ =>
    intro ρ hρ y hy
    have hl := Expr.baseFits_eval_preserve hO hWop l ρ hρ
    simp only [Comp.eval] at hy
    obtain ⟨_, hm⟩ := consumeFirstML_mem _ _ _ y hy
    refine ⟨trivial, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl | rfl⟩ := hm z hz
    · exact hl _ (List.mem_of_mem_take hx)
    · exact Expr.baseFits_eval_preserve hO hWop mk (.cons x ρ)
        ⟨hl x (List.mem_of_mem_take hx), hρ⟩
  | foldM K l z f ihf =>
    intro ρ hρ y hy
    have hl := Expr.baseFits_eval_preserve hO hWop l ρ hρ
    have hz := Expr.baseFits_eval_preserve hO hWop z ρ hρ
    simp only [Comp.eval] at hy
    exact foldML_fits (fun _ b => Ty.BaseFits W _ b) (fun x => Ty.BaseFits W _ x) 0
      (fun x acc => f.eval (.cons x (.cons acc ρ)))
      (fun _ x b hx hb b' hb' => ihf (.cons x (.cons b ρ)) ⟨hx, hb, hρ⟩ b' hb')
      ((l.eval ρ).take K) 0 (z.eval ρ)
      (fun x hx => hl x (List.mem_of_mem_take hx)) hz y hy

/-- Every `.base` leaf in `R.eval A x` and in `R`'s state stays bounded by `W` independently of `R.totalCost`. -/
theorem CostedReduction.baseFits_eval_on {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    {W_op W_samp W : ℕ} (hO : OpsBaseBounded O W_op) (hS : SampBaseBounded I.smp W_samp)
    (hWop : W_op ≤ W) (hWsamp : W_samp ≤ W)
    (hq : ∀ g x u, (I.cod g).BaseFits W (I.dec g x u))
    {qPred : κ → Prop} (henc : C.BaseFitsOn qPred W)
    (hA : ∀ v : aOut.denote, aOut.BaseFits W v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hqp : ∀ a, AllGameQueries qPred (A a))
    (x : rIn.denote) (hx : rIn.BaseFits W x) :
    (∀ y ∈ support (R.eval A x), out.BaseFits W y) ∧
    (∀ r0 ∈ support (R.init.eval (.cons x .nil)),
      ∀ r1 ∈ support ((simulateQ R.impl (A r0.1)).run r0.2), R.σ.BaseFits W r1.2) := by
  have hSim : ∀ {α : Type} {oa : OracleComp (unifSpec + G) α},
      AllGameQueries qPred oa → ∀ s, R.σ.BaseFits W s →
        ∀ r ∈ support ((simulateQ R.impl oa).run s), R.σ.BaseFits W r.2 := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro _ s hs r hr
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact hs
    | query_bind q mx ih =>
      intro hqp' s hs r hr
      simp only [AllGameQueries, construct_query_bind] at hqp'
      rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
      obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
      cases q with
      | inl n =>
        simp only [CostedReduction.impl, handlerImpl, StateT.run_lift, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hstep
        obtain ⟨_, -, hvs⟩ := hstep; cases hvs
        exact ih v (hqp'.2 v) s hs r hr
      | inr t =>
        simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hstep
        obtain ⟨⟨ans, s₁⟩, hstep, hvs⟩ := hstep; cases hvs
        have hs₁ := (Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.handle
          (.cons s (.cons (C.qenc t) .nil)) ⟨hs, henc t hqp'.1, trivial⟩ (ans, s₁) hstep).2
        exact ih (C.rdec t ans) (hqp'.2 _) s₁ hs₁ r hr
  refine ⟨fun y hy => ?_, fun r0 hr0 r1 hr1 => ?_⟩
  · simp only [CostedReduction.eval, mem_support_bind_iff] at hy
    obtain ⟨⟨oAdv, s₀⟩, hs₀, ⟨outAdv, s₁⟩, hs₁, hy⟩ := hy
    have h0 := (Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.init (.cons x .nil)
      ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
    have h1 := hSim (hqp oAdv) s₀ h0 (outAdv, s₁) hs₁
    exact Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.finish
      (.cons s₁ (.cons outAdv .nil)) ⟨h1, hA outAdv, trivial⟩ y hy
  · have h0 := (Comp.baseFits_eval_preserve hO hS hWop hWsamp hq R.init (.cons x .nil)
      ⟨hx, trivial⟩ r0 hr0).2
    exact hSim (hqp r0.1) r0.2 h0 r1 hr1

def Ty.structNodes : Ty S → ℕ
  | .base _ | .unit | .bool | .nat => 1
  | .opt t | .list t | .tbl t => 1 + t.structNodes
  | .prod t u | .sum t u => 1 + t.structNodes + u.structNodes

def Ty.NatFits (N : ℕ) : (t : Ty S) → t.denote → Prop
  | .nat, n => bits n ≤ N
  | .base _, _ | .unit, _ | .bool, _ | .opt _, none => True
  | .opt t, some a => t.NatFits N a
  | .prod t u, x => t.NatFits N x.1 ∧ u.NatFits N x.2
  | .sum t _, .inl a => t.NatFits N a
  | .sum _ u, .inr b => u.NatFits N b
  | .list t, l => ∀ x ∈ l, t.NatFits N x
  | .tbl t, m => ∀ i, t.NatFits N (m i)

theorem Ty.natFits_of_fits {B : ℕ} : ∀ (t : Ty S) (x : t.denote), t.Fits B x → t.NatFits B x
  | .nat, _, hx => hx
  | .base _, _, _ | .unit, _, _ | .bool, _, _ | .opt _, none, _ => trivial
  | .opt t, some a, hx => Ty.natFits_of_fits t a hx
  | .prod t u, _, hx => ⟨Ty.natFits_of_fits t _ hx.1, Ty.natFits_of_fits u _ hx.2⟩
  | .sum t _, .inl a, hx => Ty.natFits_of_fits t a hx
  | .sum _ u, .inr b, hx => Ty.natFits_of_fits u b hx
  | .list t, _, hx => fun x hm => Ty.natFits_of_fits t x (hx.2 x hm)
  | .tbl t, _, hx => fun i => Ty.natFits_of_fits t _ (hx i)

private theorem list_sum_map_le_length_mul {α : Type} (f : α → ℕ) (M : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ M) → (l.map f).sum ≤ l.length * M
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x (by simp)
    have hxs := list_sum_map_le_length_mul f M xs (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc f x + (xs.map f).sum ≤ M + xs.length * M := Nat.add_le_add hx hxs
      _ = (xs.length + 1) * M := by ring

theorem Ty.treeBlocks_le_of_listDepth_zero {W N : ℕ} :
    ∀ (t : Ty S), t.listDepth = 0 → t.HasNoTbl = true →
      ∀ (v : t.denote), t.BaseFits W v → t.NatFits N v →
        t.treeBlocks v ≤ t.structNodes * (max W N + 1)
  | .base _, _, _, x, hW, _ => by
    simp only [Ty.treeBlocks, Ty.structNodes, Ty.BaseFits, one_mul] at hW ⊢
    have := le_max_left W N
    omega
  | .unit, _, _, _, _, _ | .bool, _, _, _, _, _ => by
    simp [Ty.treeBlocks, Ty.structNodes]
  | .nat, _, _, n, _, hN => by
    simp only [Ty.treeBlocks, Ty.structNodes, Ty.NatFits, one_mul] at hN ⊢
    have := le_max_right W N
    omega
  | .opt t, _, _, none, _, _ => by
    simp only [Ty.treeBlocks, Ty.structNodes]
    have hr : (1 + t.structNodes) * (max W N + 1) =
        (max W N + 1) + t.structNodes * (max W N + 1) := by ring
    omega
  | .opt t, hd, hnt, some a, hW, hN => by
    simp only [Ty.listDepth, Ty.HasNoTbl] at hd hnt
    have ih := Ty.treeBlocks_le_of_listDepth_zero t hd hnt a hW hN
    simp only [Ty.treeBlocks, Ty.structNodes]
    have hr : (1 + t.structNodes) * (max W N + 1) =
        (max W N + 1) + t.structNodes * (max W N + 1) := by ring
    omega
  | .prod t u, hd, hnt, x, hW, hN => by
    simp only [Ty.listDepth, Nat.max_eq_zero_iff, Ty.HasNoTbl, Bool.and_eq_true] at hd hnt
    have iht := Ty.treeBlocks_le_of_listDepth_zero t hd.1 hnt.1 x.1 hW.1 hN.1
    have ihu := Ty.treeBlocks_le_of_listDepth_zero u hd.2 hnt.2 x.2 hW.2 hN.2
    simp only [Ty.treeBlocks, Ty.structNodes]
    have hr : (1 + t.structNodes + u.structNodes) * (max W N + 1) =
        (max W N + 1) + t.structNodes * (max W N + 1) + u.structNodes * (max W N + 1) := by ring
    omega
  | .sum t u, hd, hnt, .inl a, hW, hN => by
    simp only [Ty.listDepth, Nat.max_eq_zero_iff, Ty.HasNoTbl, Bool.and_eq_true] at hd hnt
    have iht := Ty.treeBlocks_le_of_listDepth_zero t hd.1 hnt.1 a hW hN
    simp only [Ty.treeBlocks, Ty.structNodes]
    have hr : (1 + t.structNodes + u.structNodes) * (max W N + 1) =
        (max W N + 1) + t.structNodes * (max W N + 1) + u.structNodes * (max W N + 1) := by ring
    omega
  | .sum t u, hd, hnt, .inr b, hW, hN => by
    simp only [Ty.listDepth, Nat.max_eq_zero_iff, Ty.HasNoTbl, Bool.and_eq_true] at hd hnt
    have ihu := Ty.treeBlocks_le_of_listDepth_zero u hd.2 hnt.2 b hW hN
    simp only [Ty.treeBlocks, Ty.structNodes]
    have hr : (1 + t.structNodes + u.structNodes) * (max W N + 1) =
        (max W N + 1) + t.structNodes * (max W N + 1) + u.structNodes * (max W N + 1) := by ring
    omega
  | .list _, hd, _, _, _, _ => by simp [Ty.listDepth] at hd
  | .tbl _, _, hnt, _, _, _ => by simp [Ty.HasNoTbl] at hnt

/-- For table-free types without nested lists (`listDepth ≤ 1`), `treeBlocks` is bounded by `t.structNodes * (B + 1) * (max W N + 1)`. -/
theorem Ty.treeBlocks_linear_of_noNestedLists {B W N : ℕ} :
    ∀ (t : Ty S), t.NoNestedLists → t.HasNoTbl = true →
      ∀ (v : t.denote), t.Fits B v → t.BaseFits W v → t.NatFits N v →
        t.treeBlocks v ≤ t.structNodes * (B + 1) * (max W N + 1)
  | .base _, _, _, x, _, hW, _ => by
    simp only [Ty.treeBlocks, Ty.structNodes, Ty.BaseFits, one_mul] at hW ⊢
    have := le_max_left W N
    have := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    omega
  | .unit, _, _, _, _, _, _ | .bool, _, _, _, _, _, _ => by
    simp only [Ty.treeBlocks, Ty.structNodes, one_mul]
    have := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    omega
  | .nat, _, _, n, _, _, hN => by
    simp only [Ty.treeBlocks, Ty.structNodes, Ty.NatFits, one_mul] at hN ⊢
    have := le_max_right W N
    have := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    omega
  | .opt t, _, _, none, _, _, _ => by
    simp only [Ty.treeBlocks, Ty.structNodes]
    have h1 := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    have hr : (1 + t.structNodes) * (B + 1) * (max W N + 1) =
        (B + 1) * (max W N + 1) + t.structNodes * (B + 1) * (max W N + 1) := by ring
    omega
  | .opt t, hd, hnt, some a, hB, hW, hN => by
    simp only [Ty.NoNestedLists, Ty.listDepth, Ty.HasNoTbl] at hd hnt
    have ih := Ty.treeBlocks_linear_of_noNestedLists t hd hnt a hB hW hN
    simp only [Ty.treeBlocks, Ty.structNodes]
    have h1 := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    have hr : (1 + t.structNodes) * (B + 1) * (max W N + 1) =
        (B + 1) * (max W N + 1) + t.structNodes * (B + 1) * (max W N + 1) := by ring
    omega
  | .prod t u, hd, hnt, x, hB, hW, hN => by
    simp only [Ty.NoNestedLists, Ty.listDepth, Nat.max_le, Ty.HasNoTbl, Bool.and_eq_true] at hd hnt
    have iht := Ty.treeBlocks_linear_of_noNestedLists t hd.1 hnt.1 x.1 hB.1 hW.1 hN.1
    have ihu := Ty.treeBlocks_linear_of_noNestedLists u hd.2 hnt.2 x.2 hB.2 hW.2 hN.2
    simp only [Ty.treeBlocks, Ty.structNodes]
    have h1 := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    have hr : (1 + t.structNodes + u.structNodes) * (B + 1) * (max W N + 1) =
        (B + 1) * (max W N + 1) + t.structNodes * (B + 1) * (max W N + 1) +
          u.structNodes * (B + 1) * (max W N + 1) := by ring
    omega
  | .sum t u, hd, hnt, .inl a, hB, hW, hN => by
    simp only [Ty.NoNestedLists, Ty.listDepth, Nat.max_le, Ty.HasNoTbl, Bool.and_eq_true] at hd hnt
    have iht := Ty.treeBlocks_linear_of_noNestedLists t hd.1 hnt.1 a hB hW hN
    simp only [Ty.treeBlocks, Ty.structNodes]
    have h1 := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    have hr : (1 + t.structNodes + u.structNodes) * (B + 1) * (max W N + 1) =
        (B + 1) * (max W N + 1) + t.structNodes * (B + 1) * (max W N + 1) +
          u.structNodes * (B + 1) * (max W N + 1) := by ring
    omega
  | .sum t u, hd, hnt, .inr b, hB, hW, hN => by
    simp only [Ty.NoNestedLists, Ty.listDepth, Nat.max_le, Ty.HasNoTbl, Bool.and_eq_true] at hd hnt
    have ihu := Ty.treeBlocks_linear_of_noNestedLists u hd.2 hnt.2 b hB hW hN
    simp only [Ty.treeBlocks, Ty.structNodes]
    have h1 := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    have hr : (1 + t.structNodes + u.structNodes) * (B + 1) * (max W N + 1) =
        (B + 1) * (max W N + 1) + t.structNodes * (B + 1) * (max W N + 1) +
          u.structNodes * (B + 1) * (max W N + 1) := by ring
    omega
  | .list t, hd, hnt, l, hB, hW, hN => by
    simp only [Ty.NoNestedLists, Ty.listDepth, Ty.HasNoTbl] at hd hnt
    have hd0 : t.listDepth = 0 := by omega
    have hsum : (l.map t.treeBlocks).sum ≤ l.length * (t.structNodes * (max W N + 1)) :=
      list_sum_map_le_length_mul t.treeBlocks _ l fun x hx =>
        Ty.treeBlocks_le_of_listDepth_zero t hd0 hnt x (hW x hx) (hN x hx)
    have hlen : l.length ≤ B := hB.1
    have hmul : l.length * (t.structNodes * (max W N + 1)) ≤
        B * (t.structNodes * (max W N + 1)) := Nat.mul_le_mul_right _ hlen
    have h1 := Nat.le_mul_of_pos_left (max W N + 1) (by omega : 0 < B + 1)
    have hr : (1 + t.structNodes) * (B + 1) * (max W N + 1) =
        (B + 1) * (max W N + 1) + B * (t.structNodes * (max W N + 1)) +
          t.structNodes * (max W N + 1) := by ring
    simp only [Ty.treeBlocks, Ty.structNodes]
    omega
  | .tbl _, _, hnt, _, _, _, _ => by simp [Ty.HasNoTbl] at hnt

end BaseFitsAndTreeWeight

end ReductionDsl




