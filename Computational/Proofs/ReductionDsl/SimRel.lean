/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Simulation of a query-bounded adversary under a state encoding

Proves `simulateQ_run_enc_of_bound`: two stateful oracle implementations whose single steps agree
along an encoding `enc` on states satisfying a query-counted invariant produce equal simulations on
any adversary within the query budget.
-/

@[expose] public section

namespace ReductionDsl

open OracleComp

theorem bind_congr_of_mem_support_rel {ι : Type} {T : OracleSpec.{0, 0} ι} {α β : Type}
    (oa : OracleComp T α) (f g : α → OracleComp T β)
    (h : ∀ x ∈ support oa, f x = g x) : oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h x (by simp)
  | query_bind t mx ih =>
    simp only [bind_assoc]
    refine bind_congr fun u => ih u (fun x hx => h x ?_)
    simp only [support_bind, Set.mem_iUnion]
    exact ⟨u, by simp, hx⟩

/-- Single-step state-encoding agreement under a query-counted invariant lifts to `simulateQ` on any
query-bounded computation. -/
theorem simulateQ_run_enc_of_bound {ι κ : Type} {T : OracleSpec.{0, 0} ι}
    {spec : OracleSpec.{0, 0} κ}
    {σ₁ σ₂ : Type} (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp T)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp T))) (enc : σ₂ → σ₁)
    (p : κ → Prop) [DecidablePred p] (q : ℕ) (Inv : ℕ → σ₂ → Prop)
    (hstep : ∀ t s n, Inv n s → (p t → n < q) →
      (impl₁ t).run (enc s) = Prod.map id enc <$> (impl₂ t).run s ∧
      ∀ z ∈ support ((impl₂ t).run s), Inv (if p t then n + 1 else n) z.2) :
    ∀ {α : Type} (oa : OracleComp spec α) (m : ℕ), oa.IsQueryBoundP p m →
      ∀ s n, Inv n s → n + m ≤ q →
        (simulateQ impl₁ oa).run (enc s) = Prod.map id enc <$> (simulateQ impl₂ oa).run s := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro m _ s n _ _; simp
  | query_bind t mx ih =>
    intro m hb s n hI hq
    rw [isQueryBoundP_query_bind_iff] at hb
    have hroom : p t → n < q := fun hp => by
      have := hb.1.resolve_left (not_not.mpr hp); omega
    obtain ⟨hEq, hPres⟩ := hstep t s n hI hroom
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query,
      OracleQuery.cont_query, map_bind]
    change (impl₁ t).run (enc s) >>= _ = (impl₂ t).run s >>= _
    rw [hEq, bind_map_left]
    refine bind_congr_of_mem_support_rel _ _ _ fun z hz => ?_
    refine ih z.1 _ (hb.2 z.1) z.2 _ (hPres z hz) ?_
    by_cases hp : p t
    · have := hb.1.resolve_left (not_not.mpr hp); simp only [hp, ite_true]; omega
    · simp only [hp, ite_false]; omega

end ReductionDsl
