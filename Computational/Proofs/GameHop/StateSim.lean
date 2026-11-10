/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.GameHop.Rnd
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Relational State Projection, Support Invariants, and Query-Bound Combinators

Defines the unary support predicate `AllSupport`, syntactic and distributional (`=ᵈ`) state
projections across `simulateQ` away from forbidden query classes, and invariant-guarded
`IsQueryBoundP` simulation bounds.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.StateSim

open OracleSpec OracleComp
open Computational.Proofs.GameHop.Rnd (evalDistEq_bind_right_of_mem_support)

section AllSupport

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- Unary support predicate asserting that every output in `support oa` satisfies `P`. -/
def AllSupport {α : Type} (P : α → Prop) (oa : OracleComp spec α) : Prop :=
  ∀ x ∈ support oa, P x

theorem isQueryBoundP_false {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    (oa : OracleComp G α) (n : ℕ) : oa.IsQueryBoundP (fun _ => False) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure _ => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl id, fun u => by simpa using ih u n⟩

namespace AllSupport

theorem pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    AllSupport P (Pure.pure a : OracleComp spec α) := by
  intro x hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact h

theorem of_forall {α : Type} {P : α → Prop} (oa : OracleComp spec α) (h : ∀ x, P x) :
    AllSupport P oa :=
  fun x _ => h x

theorem mono {α : Type} {P Q : α → Prop} {oa : OracleComp spec α}
    (h : AllSupport P oa) (hpq : ∀ x, P x → Q x) :
    AllSupport Q oa :=
  fun x hx => hpq x (h x hx)

theorem map {α β : Type} {P : α → Prop} {Q : β → Prop} {oa : OracleComp spec α}
    (f : α → β) (h : AllSupport P oa) (hf : ∀ x, P x → Q (f x)) :
    AllSupport Q (f <$> oa) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_support_map_peel f oa hy
  exact hf x (h x hx)

theorem bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {oa : OracleComp spec α} {k : α → OracleComp spec β}
    (hoa : AllSupport P oa) (hk : ∀ x, P x → AllSupport Q (k x)) :
    AllSupport Q (oa >>= k) := by
  intro y hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact hk x (hoa x hx) y hy

theorem ite {α : Type} {P : α → Prop} (c : Prop) [Decidable c]
    {t e : OracleComp spec α}
    (ht : c → AllSupport P t) (he : ¬ c → AllSupport P e) :
    AllSupport P (if c then t else e) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact ht hc
  · simp only [hc, ↓reduceIte]; exact he hc

theorem bind_congr {α β : Type} {P : α → Prop} {oa : OracleComp spec α}
    (hoa : AllSupport P oa) (f g : α → OracleComp spec β)
    (hfg : ∀ x, P x → f x = g x) :
    oa >>= f = oa >>= g :=
  bind_congr_of_forall_mem_support oa fun x hx => hfg x (hoa x hx)

theorem simulateQ_run_of_dis {κ : Type} {G : OracleSpec.{0, 0} κ} {α σ : Type}
    (impl : QueryImpl G (StateT σ (OracleComp spec)))
    (inv : σ → Prop) (dis : κ → Prop) [DecidablePred dis]
    (hstep : ∀ t s, ¬ dis t → inv s → AllSupport (fun z => inv z.2) ((impl t).run s))
    (oa : OracleComp G α) (hoa : oa.IsQueryBoundP dis 0) (s : σ) (hs : inv s) :
    AllSupport (fun z => inv z.2) ((simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simpa [AllSupport] using hs
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    obtain ⟨hdis, hk⟩ := hoa
    have hndis : ¬ dis t := by simpa using hdis
    simp only [hndis, ↓reduceIte] at hk
    rw [simulateQ_query_bind, StateT.run_bind]
    exact (hstep t s hndis hs).bind fun z hz => ih z.1 (hk z.1) z.2 hz

theorem simulateQ_run {κ : Type} {G : OracleSpec.{0, 0} κ} {α σ : Type}
    (impl : QueryImpl G (StateT σ (OracleComp spec)))
    (inv : σ → Prop)
    (hstep : ∀ t s, inv s → AllSupport (fun z => inv z.2) ((impl t).run s))
    (oa : OracleComp G α) (s : σ) (hs : inv s) :
    AllSupport (fun z => inv z.2) ((simulateQ impl oa).run s) :=
  simulateQ_run_of_dis impl inv (fun _ => False) (fun t s _ hs => hstep t s hs)
    oa (isQueryBoundP_false oa 0) s hs

end AllSupport

end AllSupport

section StateProjectionDis

variable {ι κ : Type} {spec : OracleSpec.{0, 0} κ} {spec' : OracleSpec.{0, 0} ι}

/-- Syntactic state projection across `simulateQ` under state invariant `inv` away from `dis`. -/
theorem map_run_simulateQ_eq_of_inv_dis {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (dis : κ → Prop) [DecidablePred dis]
    (hinv : ∀ t s, ¬ dis t → inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, ¬ dis t → inv s →
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (hoa : oa.IsQueryBoundP dis 0)
    (s : σ₁) (hs : inv s) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    obtain ⟨hdis, hk⟩ := hoa
    have hndis : ¬ dis t := by simpa using hdis
    simp only [hndis, ↓reduceIte] at hk
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    rw [← hproj t s hndis hs, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun x hx => by
      simpa using ih x.1 (hk x.1) x.2 (hinv t s hndis hs x hx)

theorem run'_simulateQ_eq_of_inv_dis {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (dis : κ → Prop) [DecidablePred dis]
    (hinv : ∀ t s, ¬ dis t → inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, ¬ dis t → inv s →
      Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (hoa : oa.IsQueryBoundP dis 0)
    (s : σ₁) (hs : inv s) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' (proj s) := by
  have hmap := congrArg (fun p => Prod.fst <$> p)
    (map_run_simulateQ_eq_of_inv_dis impl₁ impl₂ inv proj dis hinv hproj oa hoa s hs)
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_def] using hmap

/-- Distributional (`=ᵈ`) state projection across `simulateQ` under state invariant `inv` away
from `dis`. -/
theorem evalDistEq_map_run_simulateQ_of_inv_dis [OracleSpec.AnswerMeasure spec']
    {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (dis : κ → Prop) [DecidablePred dis]
    (hinv : ∀ t s, ¬ dis t → inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, ¬ dis t → inv s →
      Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (hoa : oa.IsQueryBoundP dis 0)
    (s : σ₁) (hs : inv s) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =ᵈ
      (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    obtain ⟨hdis, hk⟩ := hoa
    have hndis : ¬ dis t := by simpa using hdis
    simp only [hndis, ↓reduceIte] at hk
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
    have h1 :
        ((impl₁ t).run s >>= fun z => Prod.map id proj <$> (simulateQ impl₁ (k z.1)).run z.2) =ᵈ
          ((impl₁ t).run s >>= fun z => (simulateQ impl₂ (k z.1)).run (proj z.2)) :=
      evalDistEq_bind_right_of_mem_support ((impl₁ t).run s) fun z hz =>
        ih z.1 (hk z.1) z.2 (hinv t s hndis hs z hz)
    have h2 :
        ((impl₁ t).run s >>= fun z => (simulateQ impl₂ (k z.1)).run (proj z.2)) =
          ((Prod.map id proj <$> (impl₁ t).run s) >>= fun w => (simulateQ impl₂ (k w.1)).run w.2) := by
      rw [bind_map_left]; rfl
    rw [h2] at h1
    exact h1.trans ((hproj t s hndis hs).bind_left fun w => (simulateQ impl₂ (k w.1)).run w.2)

theorem evalDistEq_run'_simulateQ_of_inv_dis [OracleSpec.AnswerMeasure spec']
    {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (dis : κ → Prop) [DecidablePred dis]
    (hinv : ∀ t s, ¬ dis t → inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, ¬ dis t → inv s →
      Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (hoa : oa.IsQueryBoundP dis 0)
    (s : σ₁) (hs : inv s) :
    (simulateQ impl₁ oa).run' s =ᵈ (simulateQ impl₂ oa).run' (proj s) := by
  have hmap :=
    (evalDistEq_map_run_simulateQ_of_inv_dis impl₁ impl₂ inv proj dis hinv hproj oa hoa s hs).map
      Prod.fst
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_def] using hmap

theorem evalDistEq_run'_simulateQ_of_inv [OracleSpec.AnswerMeasure spec']
    {α σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hinv : ∀ t s, inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2)
    (hproj : ∀ t s, inv s →
      Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : inv s) :
    (simulateQ impl₁ oa).run' s =ᵈ (simulateQ impl₂ oa).run' (proj s) :=
  evalDistEq_run'_simulateQ_of_inv_dis impl₁ impl₂ inv proj (fun _ => False)
    (fun t s _ hs => hinv t s hs) (fun t s _ hs => hproj t s hs)
    oa (isQueryBoundP_false oa 0) s hs

end StateProjectionDis

section QueryBounds

variable {ι κ : Type} {spec : OracleSpec.{0, 0} κ} {spec' : OracleSpec.{0, 0} ι}

theorem isQueryBoundP_congr_pred {α : Type} {p q : κ → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ t, p t ↔ q t) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨?_, fun u => ?_⟩
    · rcases h.1 with hnp | hpos
      · exact Or.inl (fun hq => hnp ((hpq t).mpr hq))
      · exact Or.inr hpos
    · have hu := ih u (h.2 u)
      by_cases hqt : q t
      · have hpt : p t := (hpq t).mpr hqt
        simpa [hpt, hqt] using hu
      · have hpt : ¬ p t := fun hp => hqt ((hpq t).mp hp)
        simpa [hpt, hqt] using hu

theorem isQueryBoundP_of_imp {α : Type} {p q : κ → Prop} [DecidablePred p] [DecidablePred q]
    (hqp : ∀ t, q t → p t) {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) : oa.IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    refine ⟨?_, fun u => ?_⟩
    · rcases h.1 with hnp | hpos
      · exact Or.inl (fun hq => hnp (hqp t hq))
      · exact Or.inr hpos
    · have hu := ih u (h.2 u)
      by_cases hqt : q t
      · have hpt : p t := hqp t hqt
        simpa [hpt, hqt] using hu
      · by_cases hpt : p t
        · simp only [hpt, ↓reduceIte] at hu
          simp only [hqt, ↓reduceIte]
          exact hu.mono (Nat.sub_le n 1)
        · simpa [hpt, hqt] using hu

/-- Bounds target `q`-queries of `(simulateQ impl oa).run s` by `n * k` under an indexed state
invariant `inv` preserved across steps. -/
theorem isQueryBoundP_simulateQ_stateT_inv {α σ : Type}
    {p : κ → Prop} [DecidablePred p] {q : ι → Prop} [DecidablePred q]
    (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (inv : ℕ → σ → Prop) (k : ℕ)
    (hp : ∀ t m s, p t → inv (m + 1) s →
      ((impl t).run s).IsQueryBoundP q k ∧ ∀ z ∈ support ((impl t).run s), inv m z.2)
    (hnp : ∀ t n s, ¬ p t → inv n s →
      ((impl t).run s).IsQueryBoundP q 0 ∧ ∀ z ∈ support ((impl t).run s), inv n z.2)
    (oa : OracleComp spec α) (n : ℕ) (hoa : oa.IsQueryBoundP p n) (s : σ) (hs : inv n s) :
    ((simulateQ impl oa).run s).IsQueryBoundP q (n * k) := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure a =>
    simp [simulateQ_pure]
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hpt : p t
    · have hpos : 0 < n := hoa.1.resolve_left (not_not.mpr hpt)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨hqstep, hinv⟩ := hp t m s hpt hs
      have hcont : ∀ u, (cont u).IsQueryBoundP p m := fun u => by simpa [hpt] using hoa.2 u
      refine (isQueryBoundP_bind hqstep fun z hz => ih z.1 m (hcont z.1) z.2 (hinv z hz)).mono ?_
      rw [Nat.succ_mul]
      omega
    · obtain ⟨hqstep, hinv⟩ := hnp t n s hpt hs
      have hcont : ∀ u, (cont u).IsQueryBoundP p n := fun u => by simpa [hpt] using hoa.2 u
      refine (isQueryBoundP_bind hqstep fun z hz => ih z.1 n (hcont z.1) z.2 (hinv z hz)).mono ?_
      omega

end QueryBounds

end Computational.Proofs.GameHop.StateSim
