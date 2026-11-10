/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import

/-!
# Two-Stage Forgetful Simulation Under `IsQueryBoundP` Budget Families

Extends `StepSim` to `TwoStageCostedReduction` via a between-query invariant `Inv` and stage-1
pause invariant `InvPause`. Provides `TwoStageForgetSim` and `OracleComp` evaluation equality
theorems across stage-1 `eval1`, challenger bind, stage-2 `eval2`, and `simulateQ`.
-/

public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (
  Sig Ty Var Expr Comp Env Ops Samplers Iface GameCodec Mid
  runFuel TwoStageCostedReduction isQueryKind
)
open Computational.Proofs.ReductionDsl.StepSim (
  isGamePred isGamePred_eq_isQueryKind
  bumpPred bumpPred_apply decPred decPred_apply
  bumpCount bumpPred_eq_bumpCount
  isQueryBoundP_coin_byPred isQueryBoundP_game_byPred bumpPred_add_decPred_le
  bind_congr_support mem_support_simulateQ
)

namespace Computational.Proofs.ReductionDsl.StepSimTwoStage

section TwoStage

variable {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι} {I : Iface S T}
  {G : OracleSpec κ} {C : GameCodec S G}
  {rIn aIn aOut ch rIn2 out : Ty S}

@[expose] def forgetPreOut {R_den ch_den π' π σ' σ : Type}
    (forgetπ : π' → π) (forgetσ : σ' → σ) :
    (R_den × σ') ⊕ (ch_den × (π' × σ')) → (R_den × σ) ⊕ (ch_den × (π × σ)) :=
  Sum.map (Prod.map id forgetσ) (Prod.map id (Prod.map forgetπ forgetσ))

@[expose] def forgetMid {α π' π σ' σ χ : Type}
    (forgetπ : π' → π) (forgetσ : σ' → σ) :
    Mid G α π' σ' χ → Mid G α π σ χ
  | .done a s' => .done a (forgetσ s')
  | .paused t c p' s' cont => .paused t c (forgetπ p') (forgetσ s') cont

/-- Intermediate stage-1 invariant on `Mid`: `.done` satisfies `Inv`, and `.paused` satisfies
`InvPause` with remaining continuation budgets within `B`. -/
@[expose] def MidSimInv {α π' σ' χ : Type} {m : ℕ}
    (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (Inv : (Fin m → ℕ) → σ' → Prop)
    (InvPause : (Fin m → ℕ) → π' → σ' → Prop) :
    Mid G α π' σ' χ → Prop
  | .done _ s' => ∃ c, (∀ j, c j ≤ B j) ∧ Inv c s'
  | .paused t _ p' s' cont =>
    ∃ (c qRem : Fin m → ℕ), (∀ j, c j + qRem j ≤ B j) ∧ InvPause c p' s' ∧
      ∀ (u : G t) (j : Fin m), (cont u).IsQueryBoundP (isGamePred (G := G) (P j)) (qRem j)

theorem runFuel_forget
    {σ' σ : Ty S}
    (h' : Comp O I [σ', C.Q] (.prod C.R σ'))
    (h : Comp O I [σ, C.Q] (.prod C.R σ))
    (forgetσ : σ'.denote → σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (Inv : (Fin m → ℕ) → σ'.denote → Prop)
    (hStep : ∀ (c : Fin m → ℕ) (s' : σ'.denote) (t : κ),
      (∀ j, c j ≤ B j) →
      (∀ j, P j t → c j + 1 ≤ B j) →
      Inv c s' →
      Prod.map id forgetσ <$> h'.eval (.cons s' (.cons (C.qenc t) .nil)) =
        h.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (h'.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpPred P c t) p.2)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ∀ (c qRem : Fin m → ℕ),
      (∀ j, oa.IsQueryBoundP (isGamePred (G := G) (P j)) (qRem j)) →
      (∀ j, c j + qRem j ≤ B j) →
      ∀ (fuel : ℕ) (s' : σ'.denote), Inv c s' →
        Prod.map id forgetσ <$> runFuel (C := C) h' dflt oa fuel s' =
          runFuel (C := C) h dflt oa fuel (forgetσ s') ∧
        ∀ bs' ∈ support (runFuel (C := C) h' dflt oa fuel s'),
          ∃ c', (∀ j, c' j ≤ B j) ∧ Inv c' bs'.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c qRem _ hc fuel s' hInv
    refine ⟨by simp [runFuel], ?_⟩
    intro bs' hbs'
    simp only [runFuel, construct_pure, support_pure, Set.mem_singleton_iff] at hbs'
    subst hbs'
    exact ⟨c, fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j), hInv⟩
  | query_bind q mx ih =>
    intro c qRem hA hc fuel s' hInv
    cases q with
    | inl num =>
      have hcont := isQueryBoundP_coin_byPred hA
      simp only [runFuel, construct_query_bind, map_bind]
      refine ⟨?_, ?_⟩
      · refine bind_congr fun u => (ih u c qRem (hcont u) hc fuel s' hInv).1
      · intro bs' hbs'
        rw [mem_support_bind_iff] at hbs'
        obtain ⟨u, -, hbs'⟩ := hbs'
        exact (ih u c qRem (hcont u) hc fuel s' hInv).2 bs' hbs'
    | inr t =>
      cases fuel with
      | zero =>
        simp only [runFuel, construct_query_bind, map_pure]
        refine ⟨rfl, ?_⟩
        intro bs' hbs'
        simp only [support_pure, Set.mem_singleton_iff] at hbs'
        subst hbs'
        exact ⟨c, fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j), hInv⟩
      | succ f =>
        obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byPred hA
        have hcB : ∀ j, c j ≤ B j := fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j)
        have hroom : ∀ j, P j t → c j + 1 ≤ B j := fun j hp => by
          have := hc j; have := hpos j hp; omega
        have hc' : ∀ j, bumpPred P c t j + decPred P qRem t j ≤ B j :=
          bumpPred_add_decPred_le P hc hpos
        obtain ⟨hEq, hPres⟩ := hStep c s' t hcB hroom hInv
        simp only [runFuel, construct_query_bind, map_bind]
        refine ⟨?_, ?_⟩
        · rw [← hEq, bind_map_left]
          refine bind_congr_support _ _ _ fun p hp => ?_
          exact (ih (C.rdec t p.1) (bumpPred P c t) (decPred P qRem t)
            (hcont (C.rdec t p.1)) hc' f p.2 (hPres p hp)).1
        · intro bs' hbs'
          rw [mem_support_bind_iff] at hbs'
          obtain ⟨p, hp, hbs'⟩ := hbs'
          exact (ih (C.rdec t p.1) (bumpPred P c t) (decPred P qRem t)
            (hcont (C.rdec t p.1)) hc' f p.2 (hPres p hp)).2 bs' hbs'

theorem twoStage_run1_forget
    (R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (forgetπ : R'.π.denote → R.π.denote)
    (forgetσ : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop)
    (InvPause : (Fin m → ℕ) → R'.π.denote → R'.σ.denote → Prop)
    (hPre : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ j, c j ≤ B j) →
      (∀ j, P j t → c j + 1 ≤ B j) →
      Inv c s' →
      forgetPreOut forgetπ forgetσ <$> R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePre.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      (∀ v s'₁, .inl (v, s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        Inv (bumpPred P c t) s'₁) ∧
      (∀ c_out p' s'₁,
        .inr (c_out, p', s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        InvPause (bumpPred P c t) p' s'₁))
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ∀ (c qRem : Fin m → ℕ),
      (∀ j, oa.IsQueryBoundP (isGamePred (G := G) (P j)) (qRem j)) →
      (∀ j, c j + qRem j ≤ B j) →
      ∀ (fuel : ℕ) (s' : R'.σ.denote), Inv c s' →
        forgetMid (G := G) forgetπ forgetσ <$> R'.run1 dflt oa fuel s' =
          R.run1 dflt oa fuel (forgetσ s') ∧
        ∀ m' ∈ support (R'.run1 dflt oa fuel s'), MidSimInv P B Inv InvPause m' := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c qRem _ hc fuel s' hInv
    refine ⟨by simp [TwoStageCostedReduction.run1, forgetMid], ?_⟩
    intro m' hm'
    simp only [TwoStageCostedReduction.run1, construct_pure, support_pure,
      Set.mem_singleton_iff] at hm'
    subst hm'
    exact ⟨c, fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j), hInv⟩
  | query_bind q mx ih =>
    intro c qRem hA hc fuel s' hInv
    cases q with
    | inl num =>
      have hcont := isQueryBoundP_coin_byPred hA
      simp only [TwoStageCostedReduction.run1, construct_query_bind, map_bind]
      refine ⟨?_, ?_⟩
      · refine bind_congr fun u => (ih u c qRem (hcont u) hc fuel s' hInv).1
      · intro m' hm'
        rw [mem_support_bind_iff] at hm'
        obtain ⟨u, -, hm'⟩ := hm'
        exact (ih u c qRem (hcont u) hc fuel s' hInv).2 m' hm'
    | inr t =>
      cases fuel with
      | zero =>
        simp only [TwoStageCostedReduction.run1, construct_query_bind, map_pure, forgetMid]
        refine ⟨trivial, ?_⟩
        intro m' hm'
        simp only [support_pure, Set.mem_singleton_iff] at hm'
        subst hm'
        exact ⟨c, fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j), hInv⟩
      | succ f =>
        obtain ⟨hpos, hcont⟩ := isQueryBoundP_game_byPred hA
        have hcB : ∀ j, c j ≤ B j := fun j => Nat.le_trans (Nat.le_add_right _ _) (hc j)
        have hroom : ∀ j, P j t → c j + 1 ≤ B j := fun j hp => by
          have := hc j; have := hpos j hp; omega
        have hc' : ∀ j, bumpPred P c t j + decPred P qRem t j ≤ B j :=
          bumpPred_add_decPred_le P hc hpos
        obtain ⟨hEq, hPresL, hPresR⟩ := hPre c s' t hcB hroom hInv
        simp only [TwoStageCostedReduction.run1, construct_query_bind, map_bind]
        refine ⟨?_, ?_⟩
        · rw [← hEq, bind_map_left]
          refine bind_congr_support _ _ _ fun res hres => ?_
          rcases res with ⟨v, s'₁⟩ | ⟨c_out, p', s'₁⟩
          · exact (ih (C.rdec t v) (bumpPred P c t) (decPred P qRem t)
              (hcont (C.rdec t v)) hc' f s'₁ (hPresL v s'₁ hres)).1
          · simp [forgetPreOut, forgetMid]
        · intro m' hm'
          rw [mem_support_bind_iff] at hm'
          obtain ⟨res, hres, hm'⟩ := hm'
          rcases res with ⟨v, s'₁⟩ | ⟨c_out, p', s'₁⟩
          · exact (ih (C.rdec t v) (bumpPred P c t) (decPred P qRem t)
              (hcont (C.rdec t v)) hc' f s'₁ (hPresL v s'₁ hres)).2 m' hm'
          · simp only [support_pure, Set.mem_singleton_iff] at hm'
            subst hm'
            exact ⟨bumpPred P c t, decPred P qRem t, hc', hPresR c_out p' s'₁ hres, hcont⟩

/-- Stage-1 `eval1` forgetful simulation and `MidSimInv` preservation under `IsQueryBoundP`. -/
theorem twoStage_eval1_forget
    (R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (forgetπ : R'.π.denote → R.π.denote)
    (forgetσ : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (x : rIn.denote)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop)
    (InvPause : (Fin m → ℕ) → R'.π.denote → R'.σ.denote → Prop)
    (hInit :
      Prod.map id forgetσ <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
      ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2)
    (hPre : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ j, c j ≤ B j) →
      (∀ j, P j t → c j + 1 ≤ B j) →
      Inv c s' →
      forgetPreOut forgetπ forgetσ <$> R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePre.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      (∀ v s'₁, .inl (v, s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        Inv (bumpPred P c t) s'₁) ∧
      (∀ c_out p' s'₁,
        .inr (c_out, p', s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        InvPause (bumpPred P c t) p' s'₁))
    (hChDone : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
      (∀ j, c j ≤ B j) →
      Inv c s' →
      R'.chDone.eval (.cons s' (.cons b .nil)) =
        R.chDone.eval (.cons (forgetσ s') (.cons b .nil)))
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a j, (A a).IsQueryBoundP (isGamePred (G := G) (P j)) (B j))
    (fuel1 : ℕ) (dflt : aOut.denote) :
    Prod.map id (forgetMid (G := G) forgetπ forgetσ) <$> R'.eval1 A x fuel1 dflt =
      R.eval1 A x fuel1 dflt ∧
    ∀ cm' ∈ support (R'.eval1 A x fuel1 dflt), MidSimInv P B Inv InvPause cm'.2 := by
  unfold TwoStageCostedReduction.eval1
  refine ⟨?_, ?_⟩
  · rw [map_bind, ← hInit.1, bind_map_left]
    refine bind_congr_support _ _ _ fun as' has' => ?_
    have hRun1 := twoStage_run1_forget R' R forgetπ forgetσ P B Inv InvPause hPre
      dflt (A as'.1) 0 B (hA as'.1) (fun j => by simp) fuel1 as'.2 (hInit.2 as' has')
    dsimp only [Prod.map, id_eq]
    rw [map_bind, ← hRun1.1, bind_map_left]
    refine bind_congr_support _ _ _ fun m' hm' => ?_
    have hMid := hRun1.2 m' hm'
    cases m' with
    | done b s' =>
      obtain ⟨c', hc', hInv'⟩ := hMid
      simp only [forgetMid, map_bind, map_pure, Prod.map, id_eq]
      rw [hChDone c' s' b hc' hInv']
    | paused t c_out p' s' cont =>
      simp [forgetMid, Prod.map]
  · intro cm' hcm'
    rw [mem_support_bind_iff] at hcm'
    obtain ⟨as', has', hcm'⟩ := hcm'
    rw [mem_support_bind_iff] at hcm'
    obtain ⟨m', hm', hcm'⟩ := hcm'
    have hMid := (twoStage_run1_forget R' R forgetπ forgetσ P B Inv InvPause hPre
      dflt (A as'.1) 0 B (hA as'.1) (fun j => by simp) fuel1 as'.2 (hInit.2 as' has')).2 m' hm'
    cases m' with
    | done b s' =>
      rw [mem_support_bind_iff] at hcm'
      obtain ⟨c_out, -, hcm'⟩ := hcm'
      simp only [support_pure, Set.mem_singleton_iff] at hcm'
      subst hcm'
      exact hMid
    | paused t c_out p' s' cont =>
      simp only [support_pure, Set.mem_singleton_iff] at hcm'
      subst hcm'
      exact hMid

/-- Stage-2 `eval2` forgetful simulation from any `Mid` satisfying `MidSimInv`. -/
theorem twoStage_eval2_forget
    (R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (forgetπ : R'.π.denote → R.π.denote)
    (forgetσ : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop)
    (InvPause : (Fin m → ℕ) → R'.π.denote → R'.σ.denote → Prop)
    (hResume : ∀ (c : Fin m → ℕ) (p' : R'.π.denote) (s' : R'.σ.denote) (y : rIn2.denote),
      (∀ j, c j ≤ B j) →
      InvPause c p' s' →
      Prod.map id forgetσ <$> R'.resume.eval (.cons s' (.cons p' (.cons y .nil))) =
        R.resume.eval (.cons (forgetσ s') (.cons (forgetπ p') (.cons y .nil))) ∧
      ∀ vs' ∈ support (R'.resume.eval (.cons s' (.cons p' (.cons y .nil)))),
        Inv c vs'.2)
    (hPost : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ j, c j ≤ B j) →
      (∀ j, P j t → c j + 1 ≤ B j) →
      Inv c s' →
      Prod.map id forgetσ <$> R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePost.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpPred P c t) p.2)
    (hFinish : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote) (y : rIn2.denote),
      (∀ j, c j ≤ B j) →
      Inv c s' →
      R'.finish.eval (.cons s' (.cons b (.cons y .nil))) =
        R.finish.eval (.cons (forgetσ s') (.cons b (.cons y .nil))))
    (m' : Mid G aOut.denote R'.π.denote R'.σ.denote ch.denote)
    (hm' : MidSimInv P B Inv InvPause m')
    (y : rIn2.denote) (fuel2 : ℕ) (dflt : aOut.denote) :
    R'.eval2 m' y fuel2 dflt =
      R.eval2 (forgetMid (G := G) forgetπ forgetσ m') y fuel2 dflt := by
  unfold TwoStageCostedReduction.eval2
  cases m' with
  | done b s' =>
    obtain ⟨c', hc', hInv'⟩ := hm'
    simp only [forgetMid, pure_bind]
    exact hFinish c' s' b y hc' hInv'
  | paused t c_out p' s' cont =>
    obtain ⟨c', qRem, hc', hInvP, hcont⟩ := hm'
    have hcB : ∀ j, c' j ≤ B j := fun j => Nat.le_trans (Nat.le_add_right _ _) (hc' j)
    obtain ⟨hResEq, hResPres⟩ := hResume c' p' s' y hcB hInvP
    simp only [forgetMid]
    rw [← hResEq, bind_map_left]
    refine bind_congr_support _ _ _ fun vs' hvs' => ?_
    have hRun2 := runFuel_forget R'.handlePost R.handlePost forgetσ P B Inv hPost
      dflt (cont (C.rdec t vs'.1)) c' qRem (hcont (C.rdec t vs'.1)) hc' fuel2 vs'.2
      (hResPres vs' hvs')
    dsimp only [Prod.map, id_eq]
    rw [← hRun2.1, bind_map_left]
    refine bind_congr_support _ _ _ fun bs' hbs' => ?_
    obtain ⟨c₂, hc₂, hInv₂⟩ := hRun2.2 bs' hbs'
    exact hFinish c₂ bs'.2 bs'.1 y hc₂ hInv₂

/-- Step-simulation obligations relating two `TwoStageCostedReduction`s via `(forgetπ, forgetσ)`,
between-query invariant `Inv`, and pause invariant `InvPause` under `(P, B)`. -/
structure TwoStageForgetSim
    (R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (forgetπ : R'.π.denote → R.π.denote)
    (forgetσ : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (x : rIn.denote)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop)
    (InvPause : (Fin m → ℕ) → R'.π.denote → R'.σ.denote → Prop) : Prop where
  hInit :
    Prod.map id forgetσ <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
    ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2
  hPre : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
    (∀ j, c j ≤ B j) → (∀ j, P j t → c j + 1 ≤ B j) → Inv c s' →
    forgetPreOut forgetπ forgetσ <$> R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil)) =
      R.handlePre.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
    (∀ v s'₁, .inl (v, s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
      Inv (bumpPred P c t) s'₁) ∧
    (∀ c_out p' s'₁,
      .inr (c_out, p', s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
      InvPause (bumpPred P c t) p' s'₁)
  hChDone : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
    (∀ j, c j ≤ B j) → Inv c s' →
    R'.chDone.eval (.cons s' (.cons b .nil)) =
      R.chDone.eval (.cons (forgetσ s') (.cons b .nil))
  hResume : ∀ (c : Fin m → ℕ) (p' : R'.π.denote) (s' : R'.σ.denote) (y : rIn2.denote),
    (∀ j, c j ≤ B j) → InvPause c p' s' →
    Prod.map id forgetσ <$> R'.resume.eval (.cons s' (.cons p' (.cons y .nil))) =
      R.resume.eval (.cons (forgetσ s') (.cons (forgetπ p') (.cons y .nil))) ∧
    ∀ vs' ∈ support (R'.resume.eval (.cons s' (.cons p' (.cons y .nil)))),
      Inv c vs'.2
  hPost : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
    (∀ j, c j ≤ B j) → (∀ j, P j t → c j + 1 ≤ B j) → Inv c s' →
    Prod.map id forgetσ <$> R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil)) =
      R.handlePost.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
    ∀ p ∈ support (R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil))),
      Inv (bumpPred P c t) p.2
  hFinish : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote) (y : rIn2.denote),
    (∀ j, c j ≤ B j) → Inv c s' →
    R'.finish.eval (.cons s' (.cons b (.cons y .nil))) =
      R.finish.eval (.cons (forgetσ s') (.cons b (.cons y .nil)))

/-- Constructs `TwoStageForgetSim` when stage-1 pause uses the state-only invariant
`fun c _ s' => Inv c s'`. -/
theorem TwoStageForgetSim.ofSameInv
    (R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (forgetπ : R'.π.denote → R.π.denote)
    (forgetσ : R'.σ.denote → R.σ.denote)
    {m : ℕ} (P : Fin m → κ → Prop) [∀ j, DecidablePred (P j)] (B : Fin m → ℕ)
    (x : rIn.denote)
    (Inv : (Fin m → ℕ) → R'.σ.denote → Prop)
    (hInit :
      Prod.map id forgetσ <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
      ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2)
    (hPre : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ j, c j ≤ B j) → (∀ j, P j t → c j + 1 ≤ B j) → Inv c s' →
      forgetPreOut forgetπ forgetσ <$> R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePre.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      (∀ v s'₁, .inl (v, s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        Inv (bumpPred P c t) s'₁) ∧
      (∀ c_out p' s'₁,
        .inr (c_out, p', s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        Inv (bumpPred P c t) s'₁))
    (hChDone : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
      (∀ j, c j ≤ B j) → Inv c s' →
      R'.chDone.eval (.cons s' (.cons b .nil)) =
        R.chDone.eval (.cons (forgetσ s') (.cons b .nil)))
    (hResume : ∀ (c : Fin m → ℕ) (p' : R'.π.denote) (s' : R'.σ.denote) (y : rIn2.denote),
      (∀ j, c j ≤ B j) → Inv c s' →
      Prod.map id forgetσ <$> R'.resume.eval (.cons s' (.cons p' (.cons y .nil))) =
        R.resume.eval (.cons (forgetσ s') (.cons (forgetπ p') (.cons y .nil))) ∧
      ∀ vs' ∈ support (R'.resume.eval (.cons s' (.cons p' (.cons y .nil)))),
        Inv c vs'.2)
    (hPost : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ j, c j ≤ B j) → (∀ j, P j t → c j + 1 ≤ B j) → Inv c s' →
      Prod.map id forgetσ <$> R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePost.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpPred P c t) p.2)
    (hFinish : ∀ (c : Fin m → ℕ) (s' : R'.σ.denote) (b : aOut.denote) (y : rIn2.denote),
      (∀ j, c j ≤ B j) → Inv c s' →
      R'.finish.eval (.cons s' (.cons b (.cons y .nil))) =
        R.finish.eval (.cons (forgetσ s') (.cons b (.cons y .nil)))) :
    TwoStageForgetSim R' R forgetπ forgetσ P B x Inv (fun c _ s' => Inv c s') :=
  ⟨hInit, hPre, hChDone, fun c p' s' y hc hI => hResume c p' s' y hc hI, hPost, hFinish⟩

/-- Constructs `TwoStageForgetSim` from disjoint per-kind obligations (`P i t := kind t = i`). -/
theorem TwoStageForgetSim.ofByKind
    (R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (forgetπ : R'.π.denote → R.π.denote)
    (forgetσ : R'.σ.denote → R.σ.denote)
    {k : ℕ} (kind : κ → Fin k) (counts : Fin k → ℕ)
    (x : rIn.denote)
    (Inv : (Fin k → ℕ) → R'.σ.denote → Prop)
    (InvPause : (Fin k → ℕ) → R'.π.denote → R'.σ.denote → Prop)
    (hInit :
      Prod.map id forgetσ <$> R'.init.eval (.cons x .nil) = R.init.eval (.cons x .nil) ∧
      ∀ as' ∈ support (R'.init.eval (.cons x .nil)), Inv 0 as'.2)
    (hPre : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ i, c i ≤ counts i) → c (kind t) + 1 ≤ counts (kind t) → Inv c s' →
      forgetPreOut forgetπ forgetσ <$> R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePre.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      (∀ v s'₁, .inl (v, s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        Inv (bumpCount c (kind t)) s'₁) ∧
      (∀ c_out p' s'₁,
        .inr (c_out, p', s'₁) ∈ support (R'.handlePre.eval (.cons s' (.cons (C.qenc t) .nil))) →
        InvPause (bumpCount c (kind t)) p' s'₁))
    (hChDone : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (b : aOut.denote),
      (∀ i, c i ≤ counts i) → Inv c s' →
      R'.chDone.eval (.cons s' (.cons b .nil)) =
        R.chDone.eval (.cons (forgetσ s') (.cons b .nil)))
    (hResume : ∀ (c : Fin k → ℕ) (p' : R'.π.denote) (s' : R'.σ.denote) (y : rIn2.denote),
      (∀ i, c i ≤ counts i) → InvPause c p' s' →
      Prod.map id forgetσ <$> R'.resume.eval (.cons s' (.cons p' (.cons y .nil))) =
        R.resume.eval (.cons (forgetσ s') (.cons (forgetπ p') (.cons y .nil))) ∧
      ∀ vs' ∈ support (R'.resume.eval (.cons s' (.cons p' (.cons y .nil)))),
        Inv c vs'.2)
    (hPost : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (t : κ),
      (∀ i, c i ≤ counts i) → c (kind t) + 1 ≤ counts (kind t) → Inv c s' →
      Prod.map id forgetσ <$> R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil)) =
        R.handlePost.eval (.cons (forgetσ s') (.cons (C.qenc t) .nil)) ∧
      ∀ p ∈ support (R'.handlePost.eval (.cons s' (.cons (C.qenc t) .nil))),
        Inv (bumpCount c (kind t)) p.2)
    (hFinish : ∀ (c : Fin k → ℕ) (s' : R'.σ.denote) (b : aOut.denote) (y : rIn2.denote),
      (∀ i, c i ≤ counts i) → Inv c s' →
      R'.finish.eval (.cons s' (.cons b (.cons y .nil))) =
        R.finish.eval (.cons (forgetσ s') (.cons b (.cons y .nil)))) :
    TwoStageForgetSim R' R forgetπ forgetσ (fun i t => kind t = i) counts x Inv InvPause where
  hInit := hInit
  hPre := fun c₀ s₀ t hc₀ hroom₀ hInv₀ => by
    rw [bumpPred_eq_bumpCount]; exact hPre c₀ s₀ t hc₀ (hroom₀ (kind t) rfl) hInv₀
  hChDone := hChDone
  hResume := hResume
  hPost := fun c₀ s₀ t hc₀ hroom₀ hInv₀ => by
    rw [bumpPred_eq_bumpCount]; exact hPost c₀ s₀ t hc₀ (hroom₀ (kind t) rfl) hInv₀
  hFinish := hFinish

/-- Two-stage `OracleComp` evaluation equality across `eval1`, challenger continuation `chall`, and
`eval2` under `IsQueryBoundP`. -/
theorem twoStage_eval_bind_eq_of_forgetSim
    {β : Type}
    {R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out}
    {forgetπ : R'.π.denote → R.π.denote}
    {forgetσ : R'.σ.denote → R.σ.denote}
    {m : ℕ} {P : Fin m → κ → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → ℕ}
    {x : rIn.denote}
    {Inv : (Fin m → ℕ) → R'.σ.denote → Prop}
    {InvPause : (Fin m → ℕ) → R'.π.denote → R'.σ.denote → Prop}
    (hSim : TwoStageForgetSim R' R forgetπ forgetσ P B x Inv InvPause)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a j, (A a).IsQueryBoundP (isGamePred (G := G) (P j)) (B j))
    (fuel1 fuel2 : ℕ) (dflt : aOut.denote)
    (chall : ch.denote → (rIn2.denote → OracleComp T out.denote) → OracleComp T β) :
    (R'.eval1 A x fuel1 dflt >>= fun cm =>
      chall cm.1 (fun y => R'.eval2 cm.2 y fuel2 dflt)) =
    (R.eval1 A x fuel1 dflt >>= fun cm =>
      chall cm.1 (fun y => R.eval2 cm.2 y fuel2 dflt)) := by
  have h1 := twoStage_eval1_forget R' R forgetπ forgetσ P B x Inv InvPause
    hSim.hInit hSim.hPre hSim.hChDone A hA fuel1 dflt
  rw [← h1.1, bind_map_left]
  refine bind_congr_support _ _ _ fun cm' hcm' => ?_
  dsimp only [Prod.map, id_eq]
  congr 1
  funext y
  exact twoStage_eval2_forget R' R forgetπ forgetσ P B Inv InvPause
    hSim.hResume hSim.hPost hSim.hFinish cm'.2 (h1.2 cm' hcm') y fuel2 dflt

/-- Two-stage `OracleComp` evaluation equality under `simulateQ impl` and `IsQueryBoundP`. -/
theorem twoStage_simulateQ_eval_bind_eq_of_forgetSim
    {ι' : Type} {T' : OracleSpec ι'} {β : Type}
    (impl : QueryImpl T (OracleComp T'))
    {R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out}
    {forgetπ : R'.π.denote → R.π.denote}
    {forgetσ : R'.σ.denote → R.σ.denote}
    {m : ℕ} {P : Fin m → κ → Prop} [∀ j, DecidablePred (P j)] {B : Fin m → ℕ}
    {x : rIn.denote}
    {Inv : (Fin m → ℕ) → R'.σ.denote → Prop}
    {InvPause : (Fin m → ℕ) → R'.π.denote → R'.σ.denote → Prop}
    (hSim : TwoStageForgetSim R' R forgetπ forgetσ P B x Inv InvPause)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a j, (A a).IsQueryBoundP (isGamePred (G := G) (P j)) (B j))
    (fuel1 fuel2 : ℕ) (dflt : aOut.denote)
    (chall : ch.denote → (rIn2.denote → OracleComp T' out.denote) → OracleComp T' β) :
    (simulateQ impl (R'.eval1 A x fuel1 dflt) >>= fun cm =>
      chall cm.1 (fun y => simulateQ impl (R'.eval2 cm.2 y fuel2 dflt))) =
    (simulateQ impl (R.eval1 A x fuel1 dflt) >>= fun cm =>
      chall cm.1 (fun y => simulateQ impl (R.eval2 cm.2 y fuel2 dflt))) := by
  have h1 := twoStage_eval1_forget R' R forgetπ forgetσ P B x Inv InvPause
    hSim.hInit hSim.hPre hSim.hChDone A hA fuel1 dflt
  rw [← h1.1, simulateQ_map, bind_map_left]
  refine bind_congr_support _ _ _ fun cm' hcm' => ?_
  have hcm'_supp : cm' ∈ support (R'.eval1 A x fuel1 dflt) :=
    mem_support_simulateQ impl (R'.eval1 A x fuel1 dflt) hcm'
  dsimp only [Prod.map, id_eq]
  congr 1
  funext y
  rw [twoStage_eval2_forget R' R forgetπ forgetσ P B Inv InvPause
    hSim.hResume hSim.hPost hSim.hFinish cm'.2 (h1.2 cm' hcm'_supp) y fuel2 dflt]

theorem twoStage_simulateQ_eval_bind_eq_of_forgetSim_byKind
    {ι' : Type} {T' : OracleSpec ι'} {β : Type}
    (impl : QueryImpl T (OracleComp T'))
    {R' R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out}
    {forgetπ : R'.π.denote → R.π.denote}
    {forgetσ : R'.σ.denote → R.σ.denote}
    {k : ℕ} {kind : κ → Fin k} {counts : Fin k → ℕ}
    {x : rIn.denote}
    {Inv : (Fin k → ℕ) → R'.σ.denote → Prop}
    {InvPause : (Fin k → ℕ) → R'.π.denote → R'.σ.denote → Prop}
    (hSim : TwoStageForgetSim R' R forgetπ forgetσ (fun i t => kind t = i) counts x Inv InvPause)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hA : ∀ a i, (A a).IsQueryBoundP (isQueryKind (G := G) kind i) (counts i))
    (fuel1 fuel2 : ℕ) (dflt : aOut.denote)
    (chall : ch.denote → (rIn2.denote → OracleComp T' out.denote) → OracleComp T' β) :
    (simulateQ impl (R'.eval1 A x fuel1 dflt) >>= fun cm =>
      chall cm.1 (fun y => simulateQ impl (R'.eval2 cm.2 y fuel2 dflt))) =
    (simulateQ impl (R.eval1 A x fuel1 dflt) >>= fun cm =>
      chall cm.1 (fun y => simulateQ impl (R.eval2 cm.2 y fuel2 dflt))) :=
  twoStage_simulateQ_eval_bind_eq_of_forgetSim impl hSim A
    (fun a i => by simpa [isGamePred_eq_isQueryKind] using hA a i) fuel1 fuel2 dflt chall

end TwoStage

end Computational.Proofs.ReductionDsl.StepSimTwoStage
