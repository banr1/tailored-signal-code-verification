/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Size
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
import ProofLib.Lemmas

/-!
# Generic `GRedBounded` Constructor and Run-Local Size Lemmas

**Checked by Lean.** Proves run-local size propagation under `AllGameQueriesFit` and
`supportWhen (I.AnswerFits aB)` for `Comp`, `CostedReduction`, and `TwoStageCostedReduction`, and
derives the `GRedBounded` bundle from static cost, program-size, and query bounds under size
honesty (`gRedBounded_of_bounds`).
-/

@[expose] public section

set_option autoImplicit false

namespace ReductionDsl

open OracleComp OracleSpec

section SupportWhen

variable {ι' : Type} {spec : OracleSpec ι'}

@[simp] theorem supportWhen_pure {α : Type}
    (P : (t : ι') → spec t → Prop) (a : α) :
    supportWhen P (pure a : OracleComp spec α) = {a} := rfl

@[simp] theorem mem_supportWhen_pure_iff {α : Type}
    (P : (t : ι') → spec t → Prop) (a y : α) :
    y ∈ supportWhen P (pure a : OracleComp spec α) ↔ y = a :=
  Set.mem_singleton_iff

@[simp] theorem mem_supportWhen_query_bind_iff {α : Type}
    (P : (t : ι') → spec t → Prop) (t : ι') (mx : spec t → OracleComp spec α) (y : α) :
    y ∈ supportWhen P (liftM (OracleSpec.query t) >>= mx) ↔
      ∃ u, P t u ∧ y ∈ supportWhen P (mx u) :=
  Iff.rfl

theorem mem_supportWhen_bind_iff {α β : Type}
    (P : (t : ι') → spec t → Prop) (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (y : β) :
    y ∈ supportWhen P (oa >>= ob) ↔ ∃ x ∈ supportWhen P oa, y ∈ supportWhen P (ob x) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind, supportWhen_pure, Set.mem_singleton_iff, exists_eq_left]
  | query_bind t mx ih =>
    rw [bind_assoc, mem_supportWhen_query_bind_iff]
    simp only [ih, mem_supportWhen_query_bind_iff]
    exact ⟨fun ⟨u, hu, x, hx, hy⟩ => ⟨x, ⟨u, hu, hx⟩, hy⟩,
      fun ⟨x, ⟨u, hu, hx⟩, hy⟩ => ⟨u, hu, x, hx, hy⟩⟩

theorem mem_supportWhen_query_iff
    (P : (t : ι') → spec t → Prop) (t : ι') (u : spec t) :
    u ∈ supportWhen P (liftM (OracleSpec.query t) : OracleComp spec (spec t)) ↔ P t u := by
  conv_lhs => rw [← bind_pure (liftM (OracleSpec.query t))]
  rw [mem_supportWhen_query_bind_iff]
  exact ⟨fun ⟨u', hp, h⟩ => (mem_supportWhen_pure_iff P u' u).1 h ▸ hp,
    fun hp => ⟨u, hp, (mem_supportWhen_pure_iff P u u).2 rfl⟩⟩

theorem mem_supportWhen_map_iff {α β : Type}
    (P : (t : ι') → spec t → Prop) (f : α → β) (oa : OracleComp spec α) (y : β) :
    y ∈ supportWhen P (f <$> oa) ↔ ∃ x ∈ supportWhen P oa, f x = y := by
  rw [map_eq_bind_pure_comp, mem_supportWhen_bind_iff]
  exact ⟨fun ⟨x, hx, hy⟩ => ⟨x, hx, ((mem_supportWhen_pure_iff P (f x) y).1 hy).symm⟩,
    fun ⟨x, hx, hfy⟩ => ⟨x, hx, (mem_supportWhen_pure_iff P (f x) y).2 hfy.symm⟩⟩

theorem supportWhen_subset_support {α : Type}
    (P : (t : ι') → spec t → Prop) (oa : OracleComp spec α) :
    supportWhen P oa ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro y hy
    rw [mem_supportWhen_pure_iff] at hy
    simp [hy]
  | query_bind t mx ih =>
    intro y hy
    rw [mem_supportWhen_query_bind_iff] at hy
    obtain ⟨u, _, hy⟩ := hy
    rw [mem_support_bind_iff]
    exact ⟨u, (OracleComp.mem_support_liftM_iff _ _).2 ⟨u, rfl⟩, ih u hy⟩

end SupportWhen

section AllGameQueriesFitLemmas

variable {S : Sig} {κ : Type} {G : OracleSpec κ}

@[simp] theorem allGameQueriesFit_pure (B : ℕ) (C : GameCodec S G) {α : Type} (a : α) :
    AllGameQueriesFit B C (pure a : OracleComp (unifSpec + G) α) :=
  trivial

theorem allGameQueriesFit_query_bind_inl {B : ℕ} {C : GameCodec S G} {α : Type}
    {n : unifSpec.Domain} {mx : unifSpec.Range n → OracleComp (unifSpec + G) α}
    (h : AllGameQueriesFit B C (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx))
    (u : unifSpec.Range n) :
    AllGameQueriesFit B C (mx u) := by
  unfold AllGameQueriesFit at h ⊢
  rw [construct_query_bind] at h
  exact h u

theorem allGameQueriesFit_query_bind_inr {B : ℕ} {C : GameCodec S G} {α : Type}
    {t : κ} {mx : G t → OracleComp (unifSpec + G) α}
    (h : AllGameQueriesFit B C (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx)) :
    C.Q.Fits B (C.qenc t) ∧ ∀ u, AllGameQueriesFit B C (mx u) := by
  simpa [AllGameQueriesFit, construct_query_bind] using h

end AllGameQueriesFitLemmas

section RunLocalSize

variable {S : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem mapML_mem_when {α β : Type} (P : (t : ι) → T t → Prop) (f : α → OracleComp T β) :
    ∀ (xs : List α) (ys : List β), ys ∈ supportWhen P (mapML f xs) →
      ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, y ∈ supportWhen P (f x)
  | [], ys, h => by simp [mapML] at h; simp [h]
  | x :: xs, ys, h => by
    simp only [mapML, mem_supportWhen_bind_iff, mem_supportWhen_pure_iff] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    obtain ⟨hl, hm⟩ := mapML_mem_when P f xs ys' hys'
    refine ⟨by simp [hl], ?_⟩
    rintro z (_ | ⟨_, hz⟩)
    · exact ⟨x, by simp, hy⟩
    · obtain ⟨x', hx', hz'⟩ := hm z hz; exact ⟨x', by simp [hx'], hz'⟩

theorem foldML_fits_when {α β : Type} (W : (t : ι) → T t → Prop)
    (P : ℕ → β → Prop) (Q : α → Prop) (D : ℕ) (f : α → β → OracleComp T β)
    (hf : ∀ A x b, Q x → P A b → ∀ b' ∈ supportWhen W (f x b), P (A + D) b') :
    ∀ (xs : List α) (A : ℕ) (b : β), (∀ x ∈ xs, Q x) → P A b →
      ∀ y ∈ supportWhen W (foldML f b xs), P (A + xs.length * D) y
  | [], A, b, _, hb, y, hy => by simp [foldML] at hy; subst hy; simpa using hb
  | x :: xs, A, b, hxs, hb, y, hy => by
    simp only [foldML, mem_supportWhen_bind_iff] at hy
    obtain ⟨b', hb', hy⟩ := hy
    have := foldML_fits_when W P Q D f hf xs (A + D) b' (fun z hz => hxs z (by simp [hz]))
      (hf A x b (hxs x (by simp)) hb b' hb') y hy
    simp only [List.length_cons]
    rwa [show A + (xs.length + 1) * D = A + D + xs.length * D by ring]

theorem iterM_fits_when {α : Type} (W : (t : ι) → T t → Prop)
    (P : ℕ → α → Prop) (D : ℕ) (f : α → OracleComp T α)
    (hf : ∀ A a, P A a → ∀ y ∈ supportWhen W (f a), P (A + D) y) :
    ∀ (n A : ℕ) (a : α), P A a → ∀ y ∈ supportWhen W (iterM f n a), P (A + n * D) y
  | 0, A, a, ha, y, hy => by simp [iterM] at hy; subst hy; simpa using ha
  | n + 1, A, a, ha, y, hy => by
    simp only [iterM, mem_supportWhen_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have := iterM_fits_when W P D f hf n (A + D) z (hf A a ha z hz) y hy
    rwa [show A + (n + 1) * D = A + D + n * D by ring]

/-- Run-local size bound for `Comp.eval` under `supportWhen (I.AnswerFits aB)`. -/
theorem Comp.fits_eval_when (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB : ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    ∀ (B : ℕ) (ρ : Env Γ), Env.Fits B ρ →
      ∀ y ∈ supportWhen (I.AnswerFits aB) (c.eval ρ),
        t.Fits (B + c.cost + c.nq * aB) y := by
  induction c with
  | ret e =>
    intro B ρ hρ y hy
    simp only [Comp.eval, mem_supportWhen_pure_iff] at hy; subst hy
    exact Ty.fits_mono (by simp only [Comp.cost]; omega) _ _ (Expr.fits_eval hO e B ρ hρ)
  | bind c k ihc ihk =>
    intro B ρ hρ y hy
    simp only [Comp.eval, mem_supportWhen_bind_iff] at hy
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
    have hy' := I.support_liftP_subset _ (supportWhen_subset_support _ _ hy)
    have := hS s _ _ (Expr.fits_eval hO e B ρ hρ) y hy'
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries]; omega) _ _ this
  | query g e =>
    intro B ρ hρ y hy
    simp only [Comp.eval, mem_supportWhen_map_iff, mem_supportWhen_query_iff] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact Ty.fits_mono (by simp only [Comp.nq, Comp.cost, Comp.queries]; omega) _ _
      (hu g (e.eval ρ) rfl)
  | iter n e body ihb =>
    intro B ρ hρ y hy
    simp only [Comp.eval] at hy
    have he := Expr.fits_eval hO e B ρ hρ
    have key := iterM_fits_when (I.AnswerFits aB) (fun A a => B ≤ A ∧ Ty.Fits A _ a)
      (body.cost + body.nq * aB) (fun a => body.eval (.cons a ρ))
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
        (hl.2 v (List.mem_of_mem_take (findML_mem _ _ v (supportWhen_subset_support _ _ hy))))
  | anyM => intros; trivial
  | mapM K l f ihf =>
    intro B ρ hρ y hy
    have hl := Expr.fits_eval hO l B ρ hρ
    simp only [Ty.Fits] at hl
    simp only [Comp.eval] at hy
    obtain ⟨hlen, hm⟩ := mapML_mem_when (I.AnswerFits aB) _ _ y hy
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
    obtain ⟨hlen, hm⟩ := consumeFirstML_mem _ _ _ y (supportWhen_subset_support _ _ hy)
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
    have key := foldML_fits_when (I.AnswerFits aB) (fun A b => B + l.cost ≤ A ∧ Ty.Fits A _ b)
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

theorem CostedReduction.fits_simulateQ_when {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB qB : ℕ) :
    ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {qAdv : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) qAdv →
      AllGameQueriesFit qB C oa →
      ∀ (B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
        ∀ r ∈ supportWhen (I.AnswerFits aB) ((simulateQ R.impl oa).run s),
          R.σ.Fits (B + qAdv * (qB + R.handle.cost + R.handle.nq * aB)) r.2 := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ _ B s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_supportWhen_pure_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro qAdv hb hfit B s hs r hr
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [run_simulateQ_query_bind, mem_supportWhen_bind_iff] at hr
    obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
    cases q with
    | inl n =>
      have hfit' := allGameQueriesFit_query_bind_inl hfit
      simp only [CostedReduction.impl, handlerImpl, StateT.run_lift, mem_supportWhen_bind_iff,
        mem_supportWhen_pure_iff] at hstep
      obtain ⟨u, -, hvs⟩ := hstep
      cases hvs
      exact ih v (hb.2 v) (hfit' v) B s hs r hr
    | inr t =>
      obtain ⟨htFit, hmxFit⟩ := allGameQueriesFit_query_bind_inr hfit
      have hpos : 0 < qAdv := hb.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hb.2 u
      simp only [CostedReduction.impl, handlerImpl, StateT.run_mk, mem_supportWhen_bind_iff,
        mem_supportWhen_pure_iff] at hstep
      obtain ⟨⟨ans, s₁⟩, hstep, hvs⟩ := hstep
      cases hvs
      have hs₁ : R.σ.Fits (B + qB + R.handle.cost + R.handle.nq * aB) s₁ :=
        (Comp.fits_eval_when hO hS aB R.handle (B + qB) _
          (Env.fits_pair hs htFit) (ans, s₁) hstep).2
      have hrec := ih (C.rdec t ans) (hqm _) (hmxFit _)
        (B + qB + R.handle.cost + R.handle.nq * aB) s₁ hs₁ r hr
      have hring : (m + 1) * (qB + R.handle.cost + R.handle.nq * aB) =
          (qB + R.handle.cost + R.handle.nq * aB) +
            m * (qB + R.handle.cost + R.handle.nq * aB) := by ring
      exact Ty.fits_mono (by omega) _ _ hrec

/-- Run-local output size bound for a one-stage `CostedReduction` under `AllGameQueriesFit` and
`I.AnswerFits aB`. -/
theorem CostedReduction.fits_eval_when {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB qB aAdvB : ℕ)
    (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (qAdv B : ℕ)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv)
    (hfit : ∀ a, AllGameQueriesFit qB C (A a))
    (x : rIn.denote) (hx : rIn.Fits B x) :
    ∀ y ∈ supportWhen (I.AnswerFits aB) (R.eval A x),
      out.Fits (B + aAdvB + qAdv * qB + R.totalCost qAdv + R.nq qAdv * aB) y := by
  intro y hy
  simp only [CostedReduction.eval, mem_supportWhen_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, ⟨outAdv, s₁⟩, hs₁, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval_when hO hS aB R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have h1 := R.fits_simulateQ_when hO hS aB qB (hb oAdv) (hfit oAdv) _ s₀ h0 (outAdv, s₁) hs₁
  have h2 := Comp.fits_eval_when hO hS aB R.finish _ (.cons s₁ (.cons outAdv .nil))
    (Env.fits_pair h1 (hA outAdv)) y hy
  refine Ty.fits_mono ?_ _ _ h2
  have hle : qAdv * R.handle.cost ≤ qAdv * max I.uCost (R.handle.cost + C.codecCost) :=
    Nat.mul_le_mul_left qAdv (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have e1 : qAdv * (qB + R.handle.cost + R.handle.nq * aB) =
      qAdv * qB + qAdv * R.handle.cost + qAdv * R.handle.nq * aB := by ring
  have e2 : (R.init.nq + qAdv * R.handle.nq + R.finish.nq) * aB =
      R.init.nq * aB + qAdv * R.handle.nq * aB + R.finish.nq * aB := by ring
  dsimp only [CostedReduction.totalCost, CostedReduction.nq, CostedReduction.totalQueries,
    Comp.nq] at e1 e2 ⊢
  omega

theorem runFuel_fits_when {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB qB : ℕ)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α)
    (hfit : AllGameQueriesFit qB C oa) :
    ∀ (fuel B : ℕ) (s : σ.denote), σ.Fits B s →
      ∀ r ∈ supportWhen (I.AnswerFits aB) (runFuel h dflt oa fuel s),
        σ.Fits (B + fuel * (qB + h.cost + h.nq * aB)) r.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel B s hs r hr
    simp only [runFuel, construct_pure, mem_supportWhen_pure_iff] at hr
    subst hr
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro fuel B s hs r hr
    cases q with
    | inl n =>
      have hfit' := allGameQueriesFit_query_bind_inl hfit
      simp only [runFuel, construct_query_bind, mem_supportWhen_bind_iff] at hr
      obtain ⟨u, -, hr⟩ := hr
      exact ih u (hfit' u) fuel B s hs r hr
    | inr t =>
      obtain ⟨htFit, hmxFit⟩ := allGameQueriesFit_query_bind_inr hfit
      cases fuel with
      | zero =>
        simp only [runFuel, construct_query_bind, mem_supportWhen_pure_iff] at hr
        subst hr
        exact Ty.fits_mono (by omega) _ _ hs
      | succ f =>
        simp only [runFuel, construct_query_bind, mem_supportWhen_bind_iff] at hr
        obtain ⟨⟨v, s'⟩, hstep, hr⟩ := hr
        have hs' : σ.Fits (B + qB + h.cost + h.nq * aB) s' :=
          (Comp.fits_eval_when hO hS aB h (B + qB) _
            (Env.fits_pair hs htFit) (v, s') hstep).2
        have hrec := ih (C.rdec t v) (hmxFit _) f (B + qB + h.cost + h.nq * aB) s' hs' r hr
        have hring : (f + 1) * (qB + h.cost + h.nq * aB) =
            (qB + h.cost + h.nq * aB) + f * (qB + h.cost + h.nq * aB) := by ring
        exact Ty.fits_mono (by omega) _ _ hrec

/-- Run-local size predicate on a stage-1 `Mid` state, carrying `AllGameQueriesFit qB C` on paused
continuations. -/
def Mid.FitsWhen {κ : Type} {G : OracleSpec κ} {α : Type} (C : GameCodec S G)
    (π σ ch : Ty S) (qB B : ℕ) :
    Mid G α π.denote σ.denote ch.denote → Prop
  | .done _ s => σ.Fits B s
  | .paused _ c p s k =>
    ch.Fits B c ∧ π.Fits B p ∧ σ.Fits B s ∧ ∀ u, AllGameQueriesFit qB C (k u)

theorem Mid.fitsWhen_mono {κ : Type} {G : OracleSpec κ} {α : Type} {C : GameCodec S G}
    {π σ ch : Ty S} {qB B B' : ℕ}
    (h : B ≤ B') : ∀ m : Mid G α π.denote σ.denote ch.denote,
      Mid.FitsWhen C π σ ch qB B m → Mid.FitsWhen C π σ ch qB B' m
  | .done _ s, hs => Ty.fits_mono h _ s hs
  | .paused _ c p s _, ⟨hc, hp, hs, hk⟩ =>
    ⟨Ty.fits_mono h _ c hc, Ty.fits_mono h _ p hp, Ty.fits_mono h _ s hs, hk⟩

theorem TwoStageCostedReduction.fits_run1_when {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB qB : ℕ)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α)
    (hfit : AllGameQueriesFit qB C oa) :
    ∀ (fuel B : ℕ) (s : R.σ.denote), R.σ.Fits B s →
      ∀ m ∈ supportWhen (I.AnswerFits aB) (R.run1 dflt oa fuel s),
        Mid.FitsWhen C R.π R.σ ch qB (B + fuel * (qB + R.handlePre.cost + R.handlePre.nq * aB)) m := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel B s hs m hm
    simp only [TwoStageCostedReduction.run1, construct_pure, mem_supportWhen_pure_iff] at hm
    subst hm
    exact Ty.fits_mono (by omega) _ _ hs
  | query_bind q mx ih =>
    intro fuel B s hs m hm
    cases q with
    | inl n =>
      have hfit' := allGameQueriesFit_query_bind_inl hfit
      simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_supportWhen_bind_iff] at hm
      obtain ⟨u, -, hm⟩ := hm
      exact ih u (hfit' u) fuel B s hs m hm
    | inr t =>
      obtain ⟨htFit, hmxFit⟩ := allGameQueriesFit_query_bind_inr hfit
      cases fuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_supportWhen_pure_iff] at hm
        subst hm
        exact Ty.fits_mono (by omega) _ _ hs
      | succ f =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, mem_supportWhen_bind_iff] at hm
        obtain ⟨res, hstep, hm⟩ := hm
        have hres := Comp.fits_eval_when hO hS aB R.handlePre (B + qB) _
          (Env.fits_pair hs htFit) res hstep
        have hring : (f + 1) * (qB + R.handlePre.cost + R.handlePre.nq * aB) =
            (qB + R.handlePre.cost + R.handlePre.nq * aB) +
              f * (qB + R.handlePre.cost + R.handlePre.nq * aB) := by ring
        rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩
        · have hrec := ih (C.rdec t v) (hmxFit _) f (B + qB + R.handlePre.cost + R.handlePre.nq * aB)
            s' hres.2 m hm
          exact Mid.fitsWhen_mono (by omega) m hrec
        · simp only [mem_supportWhen_pure_iff] at hm
          subst hm
          exact Mid.fitsWhen_mono (by omega) _ ⟨hres.1, hres.2.1, hres.2.2, hmxFit⟩

theorem TwoStageCostedReduction.fits_eval1_when {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB qB aAdvB : ℕ)
    (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hfit : ∀ a, AllGameQueriesFit qB C (A a))
    (fuel B : ℕ) (x : rIn.denote) (hx : rIn.Fits B x) (dflt : aOut.denote) :
    ∀ y ∈ supportWhen (I.AnswerFits aB) (R.eval1 A x fuel dflt),
      ch.Fits (B + aAdvB + fuel * qB + R.totalCost fuel + R.nq fuel * aB) y.1 ∧
      Mid.FitsWhen C R.π R.σ ch qB (B + R.init.cost + R.init.nq * aB +
        fuel * (qB + R.handlePre.cost + R.handlePre.nq * aB)) y.2 := by
  intro y hy
  simp only [TwoStageCostedReduction.eval1, mem_supportWhen_bind_iff] at hy
  obtain ⟨⟨oAdv, s₀⟩, hs₀, m, hm, hy⟩ := hy
  have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * aB) s₀ :=
    (Comp.fits_eval_when hO hS aB R.init B (.cons x .nil) ⟨hx, trivial⟩ (oAdv, s₀) hs₀).2
  have hmFits := R.fits_run1_when hO hS aB qB dflt (A oAdv) (hfit oAdv) fuel _ s₀ h0 m hm
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
    simp only [mem_supportWhen_bind_iff, mem_supportWhen_pure_iff] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := Comp.fits_eval_when hO hS aB R.chDone _ (.cons s' (.cons b .nil))
      (Env.fits_pair hmFits (hA b)) c hc
    have hc'' : ch.Fits (B + aAdvB + fuel * qB + R.totalCost fuel + R.nq fuel * aB) c := by
      refine Ty.fits_mono ?_ _ _ hc'
      dsimp only [TwoStageCostedReduction.totalCost, TwoStageCostedReduction.nq,
        TwoStageCostedReduction.totalQueries, Comp.nq] at *
      omega
    exact ⟨hc'', hmFits⟩
  | paused t c p s' k =>
    simp only [mem_supportWhen_pure_iff] at hy
    subst hy
    have hc'' : ch.Fits (B + aAdvB + fuel * qB + R.totalCost fuel + R.nq fuel * aB) c := by
      refine Ty.fits_mono ?_ _ _ hmFits.1
      dsimp only [TwoStageCostedReduction.totalCost, TwoStageCostedReduction.nq,
        TwoStageCostedReduction.totalQueries, Comp.nq] at *
      omega
    exact ⟨hc'', hmFits⟩

theorem TwoStageCostedReduction.fits_eval2_when {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (hO : OpsSizeHonest O) (hS : SampSizeHonest I.smp) (aB qB aAdvB : ℕ)
    (hA : ∀ v : aOut.denote, aOut.Fits aAdvB v)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (B₁ : ℕ)
    (hm : Mid.FitsWhen C R.π R.σ ch qB B₁ m)
    (y : rIn2.denote) (B₂ : ℕ) (hy : rIn2.Fits B₂ y) (fuel₂ : ℕ) (dflt : aOut.denote) :
    ∀ z ∈ supportWhen (I.AnswerFits aB) (R.eval2 m y fuel₂ dflt),
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
    have hf := Comp.fits_eval_when hO hS aB R.finish _ (.cons s (.cons b (.cons y .nil)))
      (Env.fits_triple hm (hA b) hy) z hz
    refine Ty.fits_mono ?_ _ _ hf
    dsimp only [Comp.nq] at *
    omega
  | paused t c p s k =>
    simp only [TwoStageCostedReduction.eval2, mem_supportWhen_bind_iff] at hz
    obtain ⟨⟨v, s₁⟩, hres, ⟨b, s₂⟩, hrun, hz⟩ := hz
    have hs₁' : R.σ.Fits (B₁ + B₂ + R.resume.cost + R.resume.nq * aB) s₁ := by
      have henv : Env.Fits (B₁ + B₂) (.cons s (.cons p (.cons y .nil))) :=
        ⟨Ty.fits_mono (by omega) _ _ hm.2.2.1, Ty.fits_mono (by omega) _ _ hm.2.1,
          Ty.fits_mono (by omega) _ _ hy, trivial⟩
      exact (Comp.fits_eval_when hO hS aB R.resume (B₁ + B₂) _ henv (v, s₁) hres).2
    have hs₂ := runFuel_fits_when R.handlePost hO hS aB qB dflt (k (C.rdec t v))
      (hm.2.2.2 (C.rdec t v)) fuel₂ _ s₁ hs₁' (b, s₂) hrun
    have henv₂ : Env.Fits
        (B₁ + B₂ + R.resume.cost + R.resume.nq * aB +
          fuel₂ * (qB + R.handlePost.cost + R.handlePost.nq * aB) + aAdvB)
        (.cons s₂ (.cons b (.cons y .nil))) :=
      ⟨Ty.fits_mono (by omega) _ _ hs₂, Ty.fits_mono (by omega) _ _ (hA b),
        Ty.fits_mono (by omega) _ _ hy, trivial⟩
    have hf := Comp.fits_eval_when hO hS aB R.finish _ (.cons s₂ (.cons b (.cons y .nil)))
      henv₂ z hz
    refine Ty.fits_mono ?_ _ _ hf
    dsimp only [Comp.nq] at *
    omega

end RunLocalSize

end ReductionDsl

namespace CryptoVerification.E2E.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.SM
open CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E

set_option linter.unusedSectionVars false

section GRedBoundedE2E

theorem costedFits_iff_fits {S : Sig} (B : ℕ) :
    ∀ (t : Ty S) (x : t.denote), CostedFits B t x ↔ t.Fits B x
  | .base _, _ => Iff.rfl
  | .unit, _ => Iff.rfl
  | .bool, _ => Iff.rfl
  | .nat, _ => Iff.rfl
  | .opt _, none => Iff.rfl
  | .opt t, some a => costedFits_iff_fits B t a
  | .prod t u, x =>
    and_congr (costedFits_iff_fits B t x.1) (costedFits_iff_fits B u x.2)
  | .sum t _, .inl a => costedFits_iff_fits B t a
  | .sum _ u, .inr b => costedFits_iff_fits B u b
  | .list t, _ =>
    and_congr Iff.rfl (forall₂_congr fun x _ => costedFits_iff_fits B t x)
  | .tbl t, m => forall_congr' fun i => costedFits_iff_fits B t (m i)

theorem costedOpsSizeHonest_of_opsSizeHonest {S : Sig} {O : Ops S}
    (h : OpsSizeHonest O) : CostedOpsSizeHonest O :=
  fun o x B hx =>
    (costedFits_iff_fits (B + O.cost o) (O.cod o) _).2
      (h o x B ((costedFits_iff_fits B (O.dom o) x).1 hx))

theorem costedSampSizeHonest_of_sampSizeHonest {S : Sig} {X : Samplers S}
    (h : SampSizeHonest X) : CostedSampSizeHonest X :=
  fun s x B hx y hy =>
    (costedFits_iff_fits (B + X.sCost s) (X.sTy s) y).2
      (h s x B ((costedFits_iff_fits B (X.sDom s) x).1 hx) y hy)

theorem Expr.one_le_cost {S : Sig} {O : Ops S} :
    ∀ {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t), 1 ≤ e.cost
  | _, _, .var _ | _, _, .unit | _, _, .bool _ => le_rfl
  | _, _, .nat n => one_le_bits n
  | _, _, .add a _ | _, _, .sub a _ | _, _, .lt a _ | _, _, .eqN a _
  | _, _, .not a | _, _, .and a _ | _, _, .ite a _ _ | _, _, .pair a _
  | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .caseOpt a _ _ | _, _, .caseSum a _ _
  | _, _, .letE a _ | _, _, .op _ a | _, _, .cons a _ | _, _, .len a
  | _, _, .take a _ | _, _, .appendL _ a _ | _, _, .findB _ a _
  | _, _, .anyB _ a _ | _, _, .mapB _ a _ | _, _, .foldrB _ a _ _
  | _, _, .tconst a | _, _, .tget a _ | _, _, .tset a _ _ => by
    have := Expr.one_le_cost a; simp only [Expr.cost]; omega
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a => by
    have := Expr.one_le_cost a; simp only [Expr.cost]; omega
  | _, _, .none | _, _, .nil => le_rfl

theorem Comp.nq_le_cost {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T} :
    ∀ {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t), c.nq ≤ c.cost
  | _, _, .ret _ => Nat.zero_le _
  | _, _, .bind m k => by
    have hm := Comp.nq_le_cost m; have hk := Comp.nq_le_cost k
    simp only [Comp.nq, Comp.cost, Comp.queries] at hm hk ⊢; omega
  | _, _, .ite _ th el => by
    have hth := Comp.nq_le_cost th; have hel := Comp.nq_le_cost el
    simp only [Comp.nq, Comp.cost, Comp.queries] at hth hel ⊢; omega
  | _, _, .caseOpt _ n s => by
    have hn := Comp.nq_le_cost n; have hs := Comp.nq_le_cost s
    simp only [Comp.nq, Comp.cost, Comp.queries] at hn hs ⊢; omega
  | _, _, .caseSum _ l r => by
    have hl := Comp.nq_le_cost l; have hr := Comp.nq_le_cost r
    simp only [Comp.nq, Comp.cost, Comp.queries] at hl hr ⊢; omega
  | _, _, .sample _ a => by
    have ha := Expr.one_le_cost a
    simp only [Comp.nq, Comp.cost, Comp.queries]; omega
  | _, _, .query _ a => by
    have ha := Expr.one_le_cost a
    simp only [Comp.nq, Comp.cost, Comp.queries]; omega
  | _, _, .iter N s step => by
    have hs := Expr.one_le_cost s
    have hst := Comp.nq_le_cost step
    simp only [Comp.nq] at hst
    have hmul : N * Comp.queries (fun _ => 1) (fun _ => 1) step ≤ N * (step.cost + 1) :=
      Nat.mul_le_mul_left N (by omega)
    simp only [Comp.nq, Comp.cost, Comp.queries]; omega
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p => by
    have hl := Expr.one_le_cost l
    have hp := Comp.nq_le_cost p
    simp only [Comp.nq] at hp
    have hmul : K * Comp.queries (fun _ => 1) (fun _ => 1) p ≤ K * (p.cost + 1) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Comp.nq, Comp.cost, Comp.queries]; omega
  | _, _, .consumeFirstM K l p mark => by
    have hl := Expr.one_le_cost l
    have hp := Comp.nq_le_cost p
    simp only [Comp.nq] at hp
    have hmul : K * Comp.queries (fun _ => 1) (fun _ => 1) p ≤ K * (p.cost + mark.cost + 1) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Comp.nq, Comp.cost, Comp.queries]; omega
  | _, _, .foldM K l _ f => by
    have hl := Expr.one_le_cost l
    have hf := Comp.nq_le_cost f
    simp only [Comp.nq] at hf
    have hmul : K * Comp.queries (fun _ => 1) (fun _ => 1) f ≤ K * (f.cost + 1) :=
      Nat.mul_le_mul_left K (by omega)
    simp only [Comp.nq, Comp.cost, Comp.queries]; omega

theorem CostedReduction.init_handle_cost_le_totalCost {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out) (q : ℕ) :
    R.init.cost + q * R.handle.cost + R.finish.cost ≤ R.totalCost q := by
  have hle : q * R.handle.cost ≤ q * max I.uCost (R.handle.cost + C.codecCost) :=
    Nat.mul_le_mul_left q (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  dsimp only [CostedReduction.totalCost]; omega

theorem CostedReduction.nq_le_totalCost {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hi := Comp.nq_le_cost R.init
  have hh := Comp.nq_le_cost R.handle
  have hf := Comp.nq_le_cost R.finish
  have hmul : q * R.handle.nq ≤ q * R.handle.cost := Nat.mul_le_mul_left q hh
  have htot := CostedReduction.init_handle_cost_le_totalCost R q
  dsimp only [CostedReduction.nq, CostedReduction.totalQueries, Comp.nq] at hi hh hf hmul ⊢
  omega

theorem TwoStageCostedReduction.nq_le_totalCost {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut ch rIn2 out : Ty S}
    (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out) (q : ℕ) :
    R.nq q ≤ R.totalCost q := by
  have hInit := Comp.nq_le_cost R.init
  have hPre := Comp.nq_le_cost R.handlePre
  have hPost := Comp.nq_le_cost R.handlePost
  have hCh := Comp.nq_le_cost R.chDone
  have hRes := Comp.nq_le_cost R.resume
  have hFin := Comp.nq_le_cost R.finish
  dsimp only [TwoStageCostedReduction.nq, TwoStageCostedReduction.totalQueries,
    TwoStageCostedReduction.totalCost, Comp.nq] at *
  have hStepNq :
      max (R.handlePre.queries (fun _ => 1) (fun _ => 1))
          (R.handlePost.queries (fun _ => 1) (fun _ => 1)) ≤
        max I.uCost (max R.handlePre.cost R.handlePost.cost + C.codecCost) :=
    le_trans (max_le_max hPre hPost) (le_trans (Nat.le_add_right _ _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left q hStepNq
  have hMid := max_le_max hCh hRes
  omega

/-- Assembles `GRedBounded` from static cost, program-size, and query bounds together with operator
and sampler size honesty. -/
theorem gRedBounded_of_bounds {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget + 2 ^ 12 * bits costBudget)
    (hQueries : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GRedBounded R wTag wSamp q qOut costBudget := by
  refine ⟨hCost, hSize, hQueries, costedOpsSizeHonest_of_opsSizeHonest hO,
    costedSampSizeHonest_of_sampSizeHonest hS, fun B hA A hb hfit x hx => ?_⟩
  have hA' : ∀ v : aOut.denote, aOut.Fits B v :=
    fun v => (costedFits_iff_fits B aOut v).1 (hA v)
  have hx' : rIn.Fits B x := (costedFits_iff_fits B rIn x).1 hx
  have hb' : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) q :=
    fun a => (hb a).of_imp (fun t ht => by cases t <;> simp_all [isGameQuery])
  have hnq : R.nq q ≤ costBudget := le_trans (CostedReduction.nq_le_totalCost R q) hCost
  have hih : R.init.cost + q * R.handle.cost + R.finish.cost ≤ costBudget :=
    le_trans (CostedReduction.init_handle_cost_le_totalCost R q) hCost
  have hinq : R.init.nq + q * R.handle.nq ≤ costBudget := by
    have := hnq
    dsimp only [CostedReduction.nq, CostedReduction.totalQueries, Comp.nq] at this ⊢
    omega
  refine ⟨fun y hy => ?_, fun r0 hr0 r1 hr1 => ?_⟩
  · have hy' := R.fits_eval_when hO hS B B B hA' A q B hb' hfit x hx' y hy
    refine (costedFits_iff_fits _ out y).2 (Ty.fits_mono ?_ out y hy')
    nlinarith
  · have h0 : R.σ.Fits (B + R.init.cost + R.init.nq * B) r0.2 :=
      (Comp.fits_eval_when hO hS B R.init B (.cons x .nil) ⟨hx', trivial⟩ r0 hr0).2
    have h1 := R.fits_simulateQ_when hO hS B B (hb' r0.1) (hfit r0.1)
      (B + R.init.cost + R.init.nq * B) r0.2 h0 r1 hr1
    refine (costedFits_iff_fits _ R.σ r1.2).2 (Ty.fits_mono ?_ R.σ r1.2 h1)
    nlinarith

theorem gRedBounded_of_bounds_const {S : Sig} {O : Ops S} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S T} {G : OracleSpec κ}
    {C : GameCodec S G} {rIn aIn aOut out : Ty S}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ)
    (q qOut costBudget : ℕ)
    (hCost : R.totalCost q ≤ costBudget)
    (hSize : R.size ≤ reductionSizeBudget)
    (hQueries : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : OpsSizeHonest O)
    (hS : SampSizeHonest I.smp) :
    GRedBounded R wTag wSamp q qOut costBudget :=
  gRedBounded_of_bounds R wTag wSamp q qOut costBudget hCost
    (Nat.le_trans hSize (Nat.le_add_right _ _)) hQueries hO hS

theorem bits_le_self_add_one (n : ℕ) : bits n ≤ n + 1 := by
  unfold bits; have := Nat.log_le_self 2 n; omega

end GRedBoundedE2E

end CryptoVerification.E2E.Costed
