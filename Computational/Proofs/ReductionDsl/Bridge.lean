/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Soundness

/-!
# Bridging `ReductionDsl` reductions to `simulateQ`

Relational simulation bridges connecting `CostedReduction.eval` and fuel-bounded `runFuel` to
`simulateQ` under a game-query budget invariant.
-/

@[expose] public section

namespace ReductionDsl

open OracleComp

variable {S : Sig} {ι : Type} {T : OracleSpec ι} {O : Ops S} {I : Iface S T}

theorem bind_congr_of_mem_support' {α β : Type} (oa : OracleComp T α)
    {ob₁ ob₂ : α → OracleComp T β} (h : ∀ x ∈ support oa, ob₁ x = ob₂ x) :
    oa >>= ob₁ = oa >>= ob₂ :=
  bind_congr_of_forall_mem_support oa h

/-- Simulating a `qAdv`-bounded computation commutes with `abs` when `so₁` and `so₂` agree under `Inv`. -/
theorem simulateQ_run_abs_of_bound {κ : Type} {G : OracleSpec κ} {σ₁ σ₂ : Type}
    (so₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (so₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T)))
    (abs : σ₁ → σ₂) (Inv : ℕ → σ₁ → Prop)
    (hU : ∀ q n s, Inv q s →
      (Prod.map id abs <$> (so₁ (.inl n)).run s) = (so₂ (.inl n)).run (abs s) ∧
      ∀ r ∈ support ((so₁ (.inl n)).run s), Inv q r.2)
    (hstep : ∀ m t s, Inv (m + 1) s →
      (Prod.map id abs <$> (so₁ (.inr t)).run s) = (so₂ (.inr t)).run (abs s) ∧
      ∀ r ∈ support ((so₁ (.inr t)).run s), Inv m r.2) :
    ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {qAdv : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) qAdv →
      ∀ (s : σ₁), Inv qAdv s →
        (Prod.map id abs <$> (simulateQ so₁ oa).run s) = (simulateQ so₂ oa).run (abs s) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ s _
    simp [simulateQ_pure, Prod.map]
  | query_bind q mx ih =>
    intro qAdv hb s hs
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, map_bind]
    cases q with
    | inl n =>
      obtain ⟨heq, hinv⟩ := hU qAdv n s hs
      rw [← heq, bind_map_left]
      refine bind_congr_of_mem_support' ((so₁ (.inl n)).run s) (fun ⟨u, s'⟩ hr => ?_)
      exact ih u (hb.2 u) s' (hinv (u, s') hr)
    | inr t =>
      have hpos : 0 < qAdv := hb.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hb.2 u
      obtain ⟨heq, hinv⟩ := hstep m t s hs
      rw [← heq, bind_map_left]
      refine bind_congr_of_mem_support' ((so₁ (.inr t)).run s) (fun ⟨u, s'⟩ hr => ?_)
      exact ih u (hqm u) s' (hinv (u, s') hr)

/-- Connects `R.eval` to a `simulateQ` reduction over abstract state `σ₂` via `abs` under budget invariant `Inv`. -/
theorem CostedReduction.eval_eq_simulateQ_of_abs {κ : Type} {G : OracleSpec κ} {C : GameCodec S G}
    {rIn aIn aOut out : Ty S} (R : CostedReduction O I G C rIn aIn aOut out) {σ₂ : Type}
    (abs : R.σ.denote → σ₂) (Inv : ℕ → R.σ.denote → Prop)
    (initImpl : rIn.denote → OracleComp T (aIn.denote × σ₂))
    (so : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T)))
    (finishImpl : σ₂ → aOut.denote → OracleComp T out.denote)
    (qAdv : ℕ) (x : rIn.denote)
    (hinit : (Prod.map id abs <$> R.init.eval (.cons x .nil)) = initImpl x)
    (hinitInv : ∀ r ∈ support (R.init.eval (.cons x .nil)), Inv qAdv r.2)
    (hU : ∀ n s, (so (.inl n)).run s = (StateT.lift (I.fwdU n)).run s)
    (hstep : ∀ m t s, Inv (m + 1) s →
      (Prod.map id abs <$> ((R.impl (.inr t)).run s)) = (so (.inr t)).run (abs s) ∧
      ∀ r ∈ support ((R.impl (.inr t)).run s), Inv m r.2)
    (hfin : ∀ s b, Inv 0 s → R.finish.eval (.cons s (.cons b .nil)) = finishImpl (abs s) b)
    (hmono : ∀ {m n} (s), m ≤ n → Inv n s → Inv m s)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv) :
    R.eval A x = (do
      let (a, s₀) ← initImpl x
      let (b, s₁) ← (simulateQ so (A a)).run s₀
      finishImpl s₁ b) := by
  let Inv' : ℕ → R.σ.denote → Prop := fun q s => Inv q s ∧ Inv 0 s
  have hU' : ∀ q n s, Inv' q s →
      (Prod.map id abs <$> (R.impl (.inl n)).run s) = (so (.inl n)).run (abs s) ∧
      ∀ r ∈ support ((R.impl (.inl n)).run s), Inv' q r.2 := by
    intro q n s hs
    refine ⟨?_, ?_⟩
    · simp [CostedReduction.impl, handlerImpl, hU, StateT.run_lift, Prod.map, map_eq_bind_pure_comp]
    · intro r hr
      simp only [CostedReduction.impl, handlerImpl, StateT.run_lift, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨u, -, rfl⟩ := hr
      exact hs
  have hstep' : ∀ m t s, Inv' (m + 1) s →
      (Prod.map id abs <$> (R.impl (.inr t)).run s) = (so (.inr t)).run (abs s) ∧
      ∀ r ∈ support ((R.impl (.inr t)).run s), Inv' m r.2 := by
    intro m t s hs
    obtain ⟨heq, hinv⟩ := hstep m t s hs.1
    exact ⟨heq, fun r hr => ⟨hinv r hr, hmono r.2 (Nat.zero_le m) (hinv r hr)⟩⟩
  simp only [CostedReduction.eval, ← hinit, bind_map_left]
  refine bind_congr_of_mem_support' (R.init.eval (.cons x .nil)) (fun ⟨a, s₀⟩ hr₀ => ?_)
  have hs₀ : Inv' qAdv s₀ :=
    ⟨hinitInv (a, s₀) hr₀, hmono s₀ (Nat.zero_le qAdv) (hinitInv (a, s₀) hr₀)⟩
  have hsim := simulateQ_run_abs_of_bound R.impl so abs Inv' hU' hstep' (hb a) s₀ hs₀
  have hinvEnd : ∀ r ∈ support ((simulateQ R.impl (A a)).run s₀), Inv 0 r.2 := by
    have hpreserve : ∀ {α : Type} {oa : OracleComp (unifSpec + G) α} {q : ℕ},
        oa.IsQueryBoundP (isGameQuery (G := G)) q →
        ∀ s, Inv' q s → ∀ r ∈ support ((simulateQ R.impl oa).run s), Inv 0 r.2 := by
      intro α oa
      induction oa using OracleComp.inductionOn with
      | pure b =>
        intro q _ s hs r hr
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hs.2
      | query_bind q mx ih =>
        intro qB hq s hs r hr
        rw [isQueryBoundP_query_bind_iff] at hq
        rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
        obtain ⟨⟨u, s'⟩, hst, hr⟩ := hr
        cases q with
        | inl n =>
          exact ih u (hq.2 u) s' ((hU' qB n s hs).2 (u, s') hst) r hr
        | inr t =>
          have hpos : 0 < qB := hq.1.resolve_left (by simp [isGameQuery])
          obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
          have hqm : ∀ v, (mx v).IsQueryBoundP (isGameQuery (G := G)) m := by
            intro v; simpa [isGameQuery] using hq.2 v
          exact ih u (hqm u) s' ((hstep' m t s hs).2 (u, s') hst) r hr
    exact hpreserve (hb a) s₀ hs₀
  dsimp only [Prod.map, id_eq] at hsim ⊢
  rw [← hsim, bind_map_left]
  refine bind_congr_of_mem_support' ((simulateQ R.impl (A a)).run s₀) (fun ⟨b, s₁⟩ hr₁ => ?_)
  exact hfin s₁ b (hinvEnd (b, s₁) hr₁)

theorem runFuel_eq_simulateQ {κ : Type} {G : OracleSpec κ} {C : GameCodec S G} {σ : Ty S}
    (h : Comp O I [σ, C.Q] (.prod C.R σ)) {α : Type} (dflt : α) :
    ∀ {oa : OracleComp (unifSpec + G) α} {q : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) q →
      ∀ {fuel : ℕ}, q ≤ fuel → ∀ (s : σ.denote),
        runFuel h dflt oa fuel s = (simulateQ (handlerImpl h) oa).run s := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro q _ fuel _ s
    simp [runFuel, simulateQ_pure]
  | query_bind q mx ih =>
    intro qB hq fuel hfuel s
    rw [isQueryBoundP_query_bind_iff] at hq
    cases q with
    | inl n =>
      rw [run_simulateQ_query_bind]
      simp only [runFuel, construct_query_bind, handlerImpl, StateT.run_lift, bind_assoc, pure_bind]
      refine bind_congr fun u => ih u (hq.2 u) hfuel s
    | inr t =>
      have hpos : 0 < qB := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qB = m + 1 := ⟨qB - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hle : m ≤ f := by omega
      rw [run_simulateQ_query_bind]
      simp only [runFuel, construct_query_bind, handlerImpl, StateT.run_mk, bind_assoc, pure_bind]
      refine bind_congr fun p => ih (C.rdec t p.1) (hqm _) hle p.2

end ReductionDsl
