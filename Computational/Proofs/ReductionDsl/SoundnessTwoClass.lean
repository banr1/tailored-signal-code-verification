/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Soundness

/-!
# Two-Class Static Query Bounds

Refines `CostedReduction.queryBound_eval` by charging at most `m` heavy game queries `kH` target
queries each and all remaining game queries `kL ≤ kH`.
-/

@[expose] public section

namespace ReductionDsl

open OracleComp

theorem isQueryBoundP_of_imp {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p p' : ι → Prop} [DecidablePred p] [DecidablePred p']
    (himp : ∀ t, p' t → p t) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP p' n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp' : p' t
      · exact Or.inr (h.1.resolve_left (not_not.mpr (himp t hp')))
      · exact Or.inl hp'
    · have := ih u (h.2 u)
      by_cases hp' : p' t
      · simp only [hp', ite_true, himp t hp'] at this ⊢; exact this
      · by_cases hp : p t
        · simp only [hp', hp, ite_true, ite_false] at this ⊢; exact this.mono (Nat.sub_le _ _)
        · simp only [hp', hp, ite_false] at this ⊢; exact this

theorem isQueryBoundP_or_add {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p₁ p₂ p : ι → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p]
    (hsplit : ∀ t, p t → p₁ t ∨ p₂ t) {oa : OracleComp spec α} {n₁ n₂ : ℕ}
    (h₁ : oa.IsQueryBoundP p₁ n₁) (h₂ : oa.IsQueryBoundP p₂ n₂) :
    oa.IsQueryBoundP p (n₁ + n₂) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ with
  | pure _ => trivial
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂ ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases hp : p t
      · rcases hsplit t hp with hp1 | hp2
        · exact Or.inr (by have := h₁.1.resolve_left (not_not.mpr hp1); omega)
        · exact Or.inr (by have := h₂.1.resolve_left (not_not.mpr hp2); omega)
      · exact Or.inl hp
    · have k₁ := h₁.2 u
      have k₂ := h₂.2 u
      by_cases hp : p t
      · rcases hsplit t hp with hp1 | hp2
        · have _hpos := h₁.1.resolve_left (not_not.mpr hp1)
          simp only [hp1, ite_true] at k₁
          have k₂' : (mx u).IsQueryBoundP p₂ n₂ := k₂.mono (by split <;> omega)
          have := ih u k₁ k₂'
          simp only [hp, ite_true]
          exact this.mono (by omega)
        · have _hpos := h₂.1.resolve_left (not_not.mpr hp2)
          simp only [hp2, ite_true] at k₂
          have k₁' : (mx u).IsQueryBoundP p₁ n₁ := k₁.mono (by split <;> omega)
          have := ih u k₁' k₂
          simp only [hp, ite_true]
          exact this.mono (by omega)
      · simp only [hp, ite_false]
        exact (ih u (k₁.mono (by split <;> omega)) (k₂.mono (by split <;> omega))).mono le_rfl

variable {ι : Type} {T : OracleSpec ι}

theorem simulateQ_run_StateT_of_step_le₂ {κ : Type} {spec : OracleSpec κ} {σ α : Type}
    {p p₂ : κ → Prop} [DecidablePred p] [DecidablePred p₂] {q : ι → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp T))} {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) (himp : ∀ t, p₂ t → p t)
    (hstep : ∀ t s, ((impl t).run s).IsQueryBoundP q
      (if p₂ t then k₂ else if p t then k₁ else 0)) :
    ∀ {oa : OracleComp spec α} {n m : ℕ}, oa.IsQueryBoundP p n → oa.IsQueryBoundP p₂ m →
      ∀ s, ((simulateQ impl oa).run s).IsQueryBoundP q (n * k₁ + min n m * (k₂ - k₁)) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n m _ _ s; simp [simulateQ_pure]
  | query_bind t mx ih =>
    intro n m hn hm s
    rw [isQueryBoundP_query_bind_iff] at hn hm
    rw [simulateQ_query_bind, StateT.run_bind]
    have hbind := isQueryBoundP_bind (hstep t s) (fun x _ => ih x.1 (hn.2 x.1) (hm.2 x.1) x.2)
    refine hbind.mono ?_
    by_cases hp2 : p₂ t
    · have hp : p t := himp t hp2
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hn.1.resolve_left (not_not.mpr hp); omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hm.1.resolve_left (not_not.mpr hp2); omega⟩
      have hmin : min (n' + 1) (m' + 1) = min n' m' + 1 := by omega
      simp only [hp, hp2, ite_true, Nat.add_sub_cancel, hmin, Nat.add_mul, Nat.one_mul]
      omega
    · by_cases hp : p t
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hn.1.resolve_left (not_not.mpr hp); omega⟩
        have hmin : min n' m ≤ min (n' + 1) m := by omega
        have hmul := Nat.mul_le_mul_right (k₂ - k₁) hmin
        simp only [hp, hp2, ite_true, ite_false, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [hp, hp2, ite_false]
        omega

def onGame {κ : Type} {G : OracleSpec κ} (h : κ → Prop) : (unifSpec + G).Domain → Prop
  | .inl _ => False
  | .inr t => h t

instance {κ : Type} {G : OracleSpec κ} (h : κ → Prop) [DecidablePred h] :
    DecidablePred (onGame (G := G) h) := fun t =>
  match t with
  | .inl _ => isFalse id
  | .inr t => if ht : h t then isTrue ht else isFalse ht

variable {S : Sig} {O : Ops S} {I : Iface S T}

/-- If `A` makes at most `q` game queries, at most `m` of which satisfy `heavy`, with per-step
target query bounds `kH` and `kL ≤ kH`, then `R.eval A` makes at most
`init + q * kL + min q m * (kH - kL) + finish` target `P`-queries. -/
theorem CostedReduction.queryBound_eval₂ {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out) (P : ι → Prop)
    [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (heavy : κ → Prop) [DecidablePred heavy] {kL kH : ℕ} (hk : kL ≤ kH)
    (hH : ∀ t s, heavy t →
      (R.handle.eval (.cons s (.cons (C.qenc t) .nil))).IsQueryBoundP P kH)
    (hL : ∀ t s, ¬ heavy t →
      (R.handle.eval (.cons s (.cons (C.qenc t) .nil))).IsQueryBoundP P kL)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (q m : ℕ)
    (hA : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) q)
    (hAH : ∀ a, (A a).IsQueryBoundP (onGame (G := G) heavy) m) (x : rIn.denote) :
    (R.eval A x).IsQueryBoundP P
      (R.init.queries w ws + (q * kL + min q m * (kH - kL)) + R.finish.queries w ws) := by
  have hstep : ∀ t s, ((R.impl t).run s).IsQueryBoundP P
      (if onGame (G := G) heavy t then kH else if isGameQuery t then kL else 0) := by
    intro t s
    cases t with
    | inl n =>
      have := isQueryBoundP_bind (n := 0) (m := 0) (hU n)
        (fun a _ => isQueryBoundP_pure (spec := T) P (a, s) 0)
      simpa [CostedReduction.impl, handlerImpl, isGameQuery, onGame] using this
    | inr t =>
      by_cases ht : heavy t
      · have := isQueryBoundP_bind (hH t s ht)
          (fun x _ => isQueryBoundP_pure (spec := T) P (C.rdec t x.1, x.2) 0)
        simpa [CostedReduction.impl, handlerImpl, isGameQuery, onGame, ht] using this
      · have := isQueryBoundP_bind (hL t s ht)
          (fun x _ => isQueryBoundP_pure (spec := T) P (C.rdec t x.1, x.2) 0)
        simpa [CostedReduction.impl, handlerImpl, isGameQuery, onGame, ht] using this
  have himp : ∀ t, onGame (G := G) heavy t → isGameQuery t := by
    intro t ht
    cases t with
    | inl _ => exact ht.elim
    | inr _ => trivial
  unfold CostedReduction.eval
  have h1 := isQueryBoundP_bind (Comp.queryBound_eval P w ws hw hU R.init (.cons x .nil))
    (fun as _ => isQueryBoundP_bind
      (simulateQ_run_StateT_of_step_le₂ hk himp hstep (hA as.1) (hAH as.1) as.2)
      (fun x _ => Comp.queryBound_eval P w ws hw hU R.finish (.cons x.2 (.cons x.1 .nil))))
  exact h1.mono (by omega)

end ReductionDsl
