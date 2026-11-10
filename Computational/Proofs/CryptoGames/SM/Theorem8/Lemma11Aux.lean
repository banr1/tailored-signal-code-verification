/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Auxiliary lemmas for Lemma 11

**Checked by Lean.**

Defines the quantitative `ProbComp` coupling `LeComp`, the local `H2` reference game (`hooksLocal`,
`localAuth`, `localAuthAt`), and the session-index union bound used in ACD19 Lemma 11.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.AuthL11

open CryptoGames.SM.Construction

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## `ProbComp` and `LeComp` couplings -/

section ProbCompHelpers

variable {α β γ : Type}

theorem evalDist_le_one (x : ProbComp Bool) : 𝒟[x] {true} ≤ 1 := by
  calc 𝒟[x] {true} ≤ 𝒟[x] Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem evalDist_bind_mono (p : ProbComp α) (F₁ F₂ : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F₁ a] {true} ≤ 𝒟[F₂ a] {true}) :
    𝒟[p >>= F₁] {true} ≤ 𝒟[p >>= F₂] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
    exact lintegral_mono fun u => ih u fun a ha => h a (by
      rw [MonadAttach.mem_support_bind]
      exact ⟨u, by simp, ha⟩)

theorem evalDist_bind_congr_true (p : ProbComp α) (F₁ F₂ : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F₁ a] {true} = 𝒟[F₂ a] {true}) :
    𝒟[p >>= F₁] {true} = 𝒟[p >>= F₂] {true} :=
  le_antisymm
    (evalDist_bind_mono p F₁ F₂ fun a ha => (h a ha).le)
    (evalDist_bind_mono p F₂ F₁ fun a ha => (h a ha).ge)

theorem evalDist_bind_eq_zero (p : ProbComp α) (F : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F a] {true} = 0) :
    𝒟[p >>= F] {true} = 0 := by
  rw [evalDist_bind_congr_true p F (fun _ => pure false) (fun a ha => by simp [h a ha]),
    OracleComp.evalDist_bind_const]
  simp

theorem evalDist_bind_eq_one (p : ProbComp α) (F : α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F a] {true} = 1) :
    𝒟[p >>= F] {true} = 1 := by
  rw [evalDist_bind_congr_true p F (fun _ => pure true) (fun a ha => by simp [h a ha]),
    OracleComp.evalDist_bind_const]
  simp

theorem evalDist_bind_le_sum (p : ProbComp α) (q : ℕ) (F : α → ProbComp Bool)
    (G : ℕ → α → ProbComp Bool)
    (h : ∀ a ∈ support p, 𝒟[F a] {true} ≤ ∑ j ∈ Finset.range q, 𝒟[G j a] {true}) :
    𝒟[p >>= F] {true} ≤ ∑ j ∈ Finset.range q, 𝒟[p >>= G j] {true} := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simpa only [pure_bind] using h a (by simp)
  | query_bind t r ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable]
    calc ∫⁻ u, 𝒟[r u >>= F] {true} ∂𝒟[query t]
        ≤ ∫⁻ u, (∑ j ∈ Finset.range q, 𝒟[r u >>= G j] {true}) ∂𝒟[query t] := by
          refine lintegral_mono fun u => ih u fun a ha => h a ?_
          rw [MonadAttach.mem_support_bind]
          exact ⟨u, by simp, ha⟩
      _ = ∑ j ∈ Finset.range q, ∫⁻ u, 𝒟[r u >>= G j] {true} ∂𝒟[query t] :=
          lintegral_finsetSum _ fun _ _ => Measurable.of_discrete

/-- Relational quantitative coupling for `{true}`-probabilities on `ProbComp`. -/
def LeComp (R : α → β → Prop) (x : ProbComp α) (y : ProbComp β) : Prop :=
  ∀ (F₁ : α → ProbComp Bool) (F₂ : β → ProbComp Bool),
    (∀ a b, R a b → 𝒟[F₁ a] {true} ≤ 𝒟[F₂ b] {true}) →
    𝒟[x >>= F₁] {true} ≤ 𝒟[y >>= F₂] {true}

namespace LeComp

variable {R : α → β → Prop} {S : γ → β → Prop}

theorem pure {a : α} {b : β} (h : R a b) : LeComp R (Pure.pure a) (Pure.pure b) := by
  intro F₁ F₂ hF
  simpa only [pure_bind] using hF a b h

theorem bind {α' β' : Type} {S : α' → β' → Prop} {x : ProbComp α} {y : ProbComp β}
    {f : α → ProbComp α'} {g : β → ProbComp β'}
    (hx : LeComp R x y) (hf : ∀ a b, R a b → LeComp S (f a) (g b)) :
    LeComp S (x >>= f) (y >>= g) := by
  intro F₁ F₂ hF
  simp only [bind_assoc]
  exact hx _ _ fun a b hab => hf a b hab F₁ F₂ hF

theorem sample_bind {δ : Type} (p : ProbComp δ) {f : δ → ProbComp α} {g : δ → ProbComp β}
    (hf : ∀ d ∈ support p, LeComp R (f d) (g d)) :
    LeComp R (p >>= f) (p >>= g) := by
  intro F₁ F₂ hF
  simp only [bind_assoc]
  exact evalDist_bind_mono p _ _ fun d hd => hf d hd F₁ F₂ hF

theorem pure_left (a : α) (y : ProbComp β) (hy : ∀ b ∈ support y, R a b) :
    LeComp R (Pure.pure a) y := by
  induction y using OracleComp.inductionOn with
  | pure b => exact LeComp.pure (hy b (by simp))
  | query_bind t r ih =>
    intro F₁ F₂ hF
    rw [pure_bind, ← OracleComp.evalDist_bind_const (query t) (F₁ a), bind_assoc]
    refine evalDist_bind_mono (query t) _ _ fun u _ => ih u (fun b hb => hy b ?_) F₁ F₂ hF
    rw [MonadAttach.mem_support_bind]
    exact ⟨u, by simp, hb⟩

end LeComp

end ProbCompHelpers

/-! ## `FSAEAD.advantage` of a coin-ending adversary -/

section FSAEADCoin

variable {K SS RS AD M E : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq E]
  [SampleableType K]

abbrev implFS (fs : FSAEADScheme K SS RS AD M E) :
    QueryImpl (unifSpec + FSAEAD.spec SS RS AD M E)
      (StateT (FSAEAD.State SS RS AD M E) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (FSAEAD.State SS RS AD M E) ProbComp) + FSAEAD.oracleImpl fs

theorem simulateQ_liftM_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {σ α : Type}
    (oimpl : QueryImpl tspec (StateT σ ProbComp)) (p : ProbComp α) (st : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + oimpl)
      (liftM p : Engine.TComp tspec α)).run st =
    (p >>= fun a => pure (a, st)) := by
  rw [← liftComp_eq_liftM]
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : Engine.TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : Engine.TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT σ ProbComp) (QueryImpl.ofLift unifSpec ProbComp) + oimpl)
          (.inl t)) : StateT σ ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

theorem simulateQ_sampleT_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {σ α : Type}
    [SampleableType α] (oimpl : QueryImpl tspec (StateT σ ProbComp)) (st : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + oimpl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) :=
  simulateQ_liftM_run oimpl ($ᵗ α) st

def fsWin {α : Type} (fs : FSAEADScheme K SS RS AD M E)
    (oa : FSAEAD.AdversaryComp SS RS AD M E α) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ K
  let (_, st) ← (simulateQ (implFS fs) oa).run (FSAEAD.initState fs k b)
  return st.win

theorem evalDist_coin_or (b w : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || w)] := by
  cases w
  · cases b
    · ext s hs
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
        Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
        Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
        lintegral_fintype, lintegral_fintype, Fintype.sum_bool, Fintype.sum_bool]
      simp [add_comm]
    · simp
  · simp

theorem boolBias_bind_coin_or (m : Bool → ProbComp Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => m b >>= fun w =>
      ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)].boolBias =
    𝒟[($ᵗ Bool : ProbComp Bool) >>= m] {true} := by
  have heq : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => m b >>= fun w =>
      ($ᵗ Bool : ProbComp Bool) >>= fun b' => pure (b == b' || w)] =
    𝒟[(($ᵗ Bool : ProbComp Bool) >>= m) >>= fun w =>
      ($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || w)] := by
    rw [bind_assoc]
    refine evalDist_bind_congr ($ᵗ Bool) _ _ fun b => ?_
    refine evalDist_bind_congr (m b) _ _ fun w => evalDist_coin_or b w
  rw [heq]
  set W : ProbComp Bool := ($ᵗ Bool : ProbComp Bool) >>= m
  have hcT : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || true)] {true} = 1 := by
    simp only [Bool.or_true, OracleComp.evalDist_bind_const]
    simp
  have hcF1 : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || false)] {true} = 1 / 2 := by
    simp
  have hcT2 : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || true)] {false} = 0 := by
    simp only [Bool.or_true, OracleComp.evalDist_bind_const]
    simp
  have hcF2 : 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || false)] {false} = 1 / 2 := by
    simp
  have hT : 𝒟[W >>= fun w => ($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || w)] {true} =
      𝒟[W] {true} + 𝒟[W] {false} * (1 / 2) := by
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton true) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool, hcT, hcF1]
    ring
  have hF : 𝒟[W >>= fun w => ($ᵗ Bool : ProbComp Bool) >>= fun c => pure (c || w)] {false} =
      𝒟[W] {false} * (1 / 2) := by
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply (MeasurableSet.singleton false) Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool, hcT2, hcF2]
    ring
  rw [Measure.boolBias, hT, hF]
  have hne : 𝒟[W] {false} * (1 / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)
  rw [ENNReal.absDiff, ENNReal.add_sub_cancel_right hne, tsub_eq_zero_of_le le_add_self, add_zero]

theorem advantage_bind_sampleT_bool {α : Type} (fs : FSAEADScheme K SS RS AD M E)
    (oa : FSAEAD.AdversaryComp SS RS AD M E α) :
    FSAEAD.advantage fs (show FSAEAD.AdversaryComp SS RS AD M E Bool from oa >>= fun _ => sampleT Bool) =
      𝒟[fsWin fs oa] {true} := by
  unfold FSAEAD.advantage FSAEAD.game fsWin
  rw [← boolBias_bind_coin_or (fun b => ($ᵗ K) >>= fun k =>
    (simulateQ (implFS fs) oa).run (FSAEAD.initState fs k b) >>= fun z => pure z.2.win)]
  congr 2
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, simulateQ_sampleT_run]

end FSAEADCoin

/-! ## Game-state invariants and party helpers -/

section EraseStAndHelpers

open Engine

variable {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
  {g₁ g₁' : SM.GameState St₁ Msg C} {g₂ g₂' : SM.GameState St₂ Msg C}

def eraseSt {St Msg C : Type} (g : SM.GameState St Msg C) : SM.GameState Unit Msg C :=
  { st := fun _ => ()
    epoch := g.epoch
    idx := g.idx
    tL := g.tL
    trans := g.trans
    chall := g.chall
    comp := g.comp
    maxAcc := g.maxAcc
    b := g.b
    win := g.win
    leaks := g.leaks
    corrs := g.corrs }

theorem eraseSt_epoch (h : eraseSt g₁ = eraseSt g₂) : g₁.epoch = g₂.epoch :=
  congrArg SM.GameState.epoch h

theorem eraseSt_idx (h : eraseSt g₁ = eraseSt g₂) : g₁.idx = g₂.idx :=
  congrArg SM.GameState.idx h

theorem eraseSt_tL (h : eraseSt g₁ = eraseSt g₂) : g₁.tL = g₂.tL :=
  congrArg SM.GameState.tL h

theorem eraseSt_trans (h : eraseSt g₁ = eraseSt g₂) : g₁.trans = g₂.trans :=
  congrArg SM.GameState.trans h

theorem eraseSt_chall (h : eraseSt g₁ = eraseSt g₂) : g₁.chall = g₂.chall :=
  congrArg SM.GameState.chall h

theorem eraseSt_comp (h : eraseSt g₁ = eraseSt g₂) : g₁.comp = g₂.comp :=
  congrArg SM.GameState.comp h

theorem eraseSt_maxAcc (h : eraseSt g₁ = eraseSt g₂) : g₁.maxAcc = g₂.maxAcc :=
  congrArg SM.GameState.maxAcc h

theorem eraseSt_b (h : eraseSt g₁ = eraseSt g₂) : g₁.b = g₂.b :=
  congrArg SM.GameState.b h

theorem eraseSt_win (h : eraseSt g₁ = eraseSt g₂) : g₁.win = g₂.win :=
  congrArg SM.GameState.win h

theorem eraseSt_leaks (h : eraseSt g₁ = eraseSt g₂) : g₁.leaks = g₂.leaks :=
  congrArg SM.GameState.leaks h

theorem eraseSt_corrs (h : eraseSt g₁ = eraseSt g₂) : g₁.corrs = g₂.corrs :=
  congrArg SM.GameState.corrs h

@[simp] theorem eraseSt_update_st (g : SM.GameState St₁ Msg C) (st' : Party → St₁) :
    eraseSt { g with st := st' } = eraseSt g := rfl

theorem eraseSt_safeCh (h : eraseSt g₁ = eraseSt g₂) (Δ : ℕ) (P : Party) :
    g₁.safeCh Δ P = g₂.safeCh Δ P := by
  simp [SM.GameState.safeCh, eraseSt_tL h, eraseSt_epoch h]

theorem eraseSt_safeInj (h : eraseSt g₁ = eraseSt g₂) (Δ : ℕ) :
    g₁.safeInj Δ = g₂.safeInj Δ := by
  simp [SM.GameState.safeInj, eraseSt_tL h, eraseSt_epoch h]

theorem eraseSt_inTransit (h : eraseSt g₁ = eraseSt g₂) (Q : Party) (c : C) :
    g₁.inTransit Q c = g₂.inTransit Q c := by
  simp [SM.GameState.inTransit, eraseSt_trans h]

theorem eraseSt_trivial (h : eraseSt g₁ = eraseSt g₂) (Δ : ℕ) (pos : SM.Pos) :
    g₁.trivial Δ pos = g₂.trivial Δ pos := by
  simp [SM.GameState.trivial, eraseSt_comp h, eraseSt_trans h, eraseSt_tL h]

theorem eraseSt_corrAllowed (h : eraseSt g₁ = eraseSt g₂) (P : Party) :
    g₁.corrAllowed P = g₂.corrAllowed P := by
  simp [SM.GameState.corrAllowed, eraseSt_chall h, eraseSt_trans h, eraseSt_comp h]

theorem eraseSt_afterCorr (h : eraseSt g₁ = eraseSt g₂) (P : Party) :
    eraseSt (g₁.afterCorr P) = eraseSt (g₂.afterCorr P) := by
  simp [eraseSt, SM.GameState.afterCorr, SM.GameState.leak, eraseSt_epoch h, eraseSt_idx h,
    eraseSt_tL h, eraseSt_trans h, eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h, eraseSt_b h,
    eraseSt_win h, eraseSt_leaks h, eraseSt_corrs h]

theorem eraseSt_record (h : eraseSt g₁ = eraseSt g₂) (Δ : ℕ) (P : Party) (st₁ : St₁) (st₂ : St₂)
    (r : SM.Record Msg C) (isCh : Bool) :
    eraseSt (g₁.record Δ P st₁ r isCh) = eraseSt (g₂.record Δ P st₂ r isCh) := by
  simp [eraseSt, SM.GameState.record, eraseSt_safeCh h, eraseSt_epoch h, eraseSt_idx h,
    eraseSt_tL h, eraseSt_trans h, eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h, eraseSt_b h,
    eraseSt_win h, eraseSt_leaks h, eraseSt_corrs h]

theorem eraseSt_accept (h : eraseSt g₁ = eraseSt g₂) (P : Party) (st₁ : St₁) (st₂ : St₂)
    (pos : SM.Pos) :
    eraseSt (g₁.accept P st₁ pos) = eraseSt (g₂.accept P st₂ pos) := by
  simp [eraseSt, SM.GameState.accept, SM.GameState.delete, eraseSt_epoch h, eraseSt_idx h,
    eraseSt_tL h, eraseSt_trans h, eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h, eraseSt_b h,
    eraseSt_win h, eraseSt_leaks h, eraseSt_corrs h]

theorem eraseSt_leakDoom (h : eraseSt g₁ = eraseSt g₂) (h' : eraseSt g₁' = eraseSt g₂')
    (π : Policy) :
    π.leakDoom g₁ g₁' = π.leakDoom g₂ g₂' := by
  simp [Policy.leakDoom, eraseSt_leaks h', eraseSt_epoch h]

theorem eraseSt_corrDoom (h : eraseSt g₁ = eraseSt g₂) (π : Policy) (P : Party) :
    π.corrDoom g₁ P = π.corrDoom g₂ P := by
  simp [Policy.corrDoom, eraseSt_epoch h]

theorem eraseSt_authOK (h : eraseSt g₁ = eraseSt g₂) (Δ : ℕ) (tL : Option ℕ) (tStar : ℕ) :
    SM.authLosingConditionsAvoided Δ tL tStar g₁ = SM.authLosingConditionsAvoided Δ tL tStar g₂ := by
  simp [SM.authLosingConditionsAvoided, SM.canon, eraseSt_leaks h, eraseSt_corrs h]

theorem healedBy_leak_false (tL : Option ℕ) (l Δ e : ℕ) (h : SM.healedBy tL Δ e = false) :
    SM.healedBy (some (SM.maxOpt tL l)) Δ e = false := by
  cases tL with
  | none => simp [SM.healedBy] at h
  | some l₀ =>
    dsimp only [SM.healedBy, SM.maxOpt] at h ⊢
    rw [decide_eq_false_iff_not] at h ⊢
    omega

theorem comp_inv_record {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party)
    (st' : St) (r : SM.Record Msg C) (isCh : Bool) (hr : r.pos.epoch = g.epoch P)
    (hcomp : ∀ pos ∈ g.comp, SM.healedBy g.tL Δ pos.epoch = false) :
    ∀ pos ∈ (g.record Δ P st' r isCh).comp,
      SM.healedBy (g.record Δ P st' r isCh).tL Δ pos.epoch = false := by
  intro pos hpos
  simp only [SM.GameState.record] at hpos ⊢
  split at hpos
  · exact hcomp pos hpos
  · rename_i hns
    simp only [Bool.not_eq_true, SM.GameState.safeCh] at hns
    rcases List.mem_cons.mp hpos with rfl | hpos'
    · simpa [hr] using hns
    · exact hcomp pos hpos'

theorem comp_inv_accept {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party)
    (st' : St) (p : SM.Pos)
    (hcomp : ∀ pos ∈ g.comp, SM.healedBy g.tL Δ pos.epoch = false) :
    ∀ pos ∈ (g.accept P st' p).comp,
      SM.healedBy (g.accept P st' p).tL Δ pos.epoch = false := by
  intro pos hpos
  simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hpos ⊢
  exact hcomp pos hpos.1

theorem comp_inv_afterCorr {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (hΔ : 0 < Δ)
    (P : Party) (htrans : ∀ r ∈ g.trans, r.pos.epoch ≤ g.epoch r.pos.sender)
    (hcomp : ∀ pos ∈ g.comp, SM.healedBy g.tL Δ pos.epoch = false) :
    ∀ pos ∈ (g.afterCorr P).comp,
      SM.healedBy (g.afterCorr P).tL Δ pos.epoch = false := by
  intro pos hpos
  simp only [SM.GameState.afterCorr, SM.GameState.leak, List.mem_append, List.mem_map,
    List.mem_filter] at hpos ⊢
  rcases hpos with ⟨r, ⟨hr_mem, _⟩, rfl⟩ | hpos'
  · have hle := htrans r hr_mem
    have h_max : g.epoch r.pos.sender ≤ max (g.epoch .A) (g.epoch .B) := by
      cases r.pos.sender <;> simp
    have h_opt : max (g.epoch .A) (g.epoch .B) ≤ SM.maxOpt g.tL (max (g.epoch .A) (g.epoch .B)) := by
      cases g.tL <;> simp [SM.maxOpt]
    dsimp only [SM.healedBy]
    rw [decide_eq_false_iff_not]
    omega
  · exact healedBy_leak_false g.tL _ Δ pos.epoch (hcomp pos hpos')

theorem trivial_false_of_safeInj {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ)
    (P : Party) (i : ℕ) (hsafe : g.safeInj Δ = true)
    (hcomp : ∀ pos ∈ g.comp, SM.healedBy g.tL Δ pos.epoch = false) :
    g.trivial Δ ⟨P.other, g.epoch P + 1, i⟩ = false := by
  have hheal : SM.healedBy g.tL Δ (g.epoch P + 1) = true := by
    simp only [SM.GameState.safeInj] at hsafe
    have hmin : min (g.epoch .A) (g.epoch .B) ≤ g.epoch P := by
      cases P <;> simp
    cases htL : g.tL with
    | none => simp [SM.healedBy]
    | some l =>
      simp only [htL, SM.healedBy, decide_eq_true_eq] at hsafe ⊢
      omega
  simp only [SM.GameState.trivial, hheal, Bool.not_true, Bool.and_false, Bool.or_false,
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
  intro hmem
  have := hcomp _ hmem
  simp [hheal] at this

theorem sendsIn_senderOf (t : ℕ) : (Party.senderOf t).sendsIn t = true := by
  unfold Party.senderOf Party.sendsIn
  split <;> simp_all

theorem sendsIn_receiverOf (t : ℕ) : (Party.receiverOf t).sendsIn t = false := by
  have : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases this with h2 | h2 <;> simp [Party.receiverOf, Party.senderOf, Party.sendsIn, Party.other, h2]

theorem sendsIn_other (P : Party) (t : ℕ) : P.other.sendsIn t = !P.sendsIn t := by
  have : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases this with h2 | h2 <;> cases P <;> simp [Party.other, Party.sendsIn, h2]

theorem eq_senderOf_of_sendsIn {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    P = Party.senderOf t := by
  cases P <;> simp [Party.sendsIn, Party.senderOf] at h ⊢ <;> omega

theorem sendsIn_succ_false {P : Party} {t : ℕ} (h : P.sendsIn t = true) :
    P.sendsIn (t + 1) = false := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

@[simp] theorem senderOf_other (t : ℕ) : (Party.senderOf t).other = Party.receiverOf t := rfl

@[simp] theorem receiverOf_other (t : ℕ) : (Party.receiverOf t).other = Party.senderOf t :=
  Party.other_other _

@[simp]
lemma run_liftH {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv T Sv SSv RSv M E HS α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun rh => pure (rh.1, { es with h := rh.2 })) := rfl

end EraseStAndHelpers

/-! ## Local `H2` reference game -/

section LocalGame

open Engine

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

def nilSpec : OracleSpec.{0, 0} Empty := fun e => nomatch e

def nilImpl : QueryImpl nilSpec ProbComp := fun e => nomatch e

def lImpl : QueryImpl (unifSpec + nilSpec) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + nilImpl

@[simp]
theorem simulateQ_lImpl_liftM {α : Type} (p : ProbComp α) :
    simulateQ lImpl (liftM p : Engine.TComp nilSpec α) = p := by
  rw [← liftComp_eq_liftM]
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : Engine.TComp nilSpec _) =
        (liftM (OracleSpec.query (spec := unifSpec + nilSpec) (.inl t)) : Engine.TComp nilSpec _) := rfl
    have hrun : (liftM (lImpl (.inl t)) : ProbComp (unifSpec.Range t)) = liftM (OracleSpec.query t) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, hrun, ih]

@[simp]
theorem simulateQ_lImpl_sampleT {α : Type} [SampleableType α] :
    simulateQ lImpl (sampleT α : Engine.TComp nilSpec α) = ($ᵗ α : ProbComp α) :=
  simulateQ_lImpl_liftM ($ᵗ α)

/-- Bookkeeping state for the local `H2` game, tracking epoch-`t*` session keys and the last
accepted session index. -/
structure LState (T Sig K I : Type) where
  cache : ℕ → Option (T × Sig × K × Option ℕ) := fun _ => none
  table : List (I × K) := []
  sessions : List I := []
  lastIdx : Option ℕ := none

local notation "LHM" => HM nilSpec (LState T Sig K I)

def lookupFL (Ik : I) : LHM K := do
  match (← get).table.lookup Ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with table := (Ik, k) :: s.table }
    return k

def regSess (Ik : I) : LHM ℕ := do
  let s ← get
  if Ik ∈ s.sessions then return s.sessions.idxOf Ik
  else
    set { s with sessions := s.sessions ++ [Ik] }
    return s.sessions.length

def regSessOf (sid : Option I) : LHM (Option ℕ) :=
  match sid with
  | none => pure none
  | some Ik => some <$> regSess Ik

def rootL (t : ℕ) (Ik : I) (σ : Sig) : LHM (Sig × K × Option I) := do
  if mo.tStar < t then
    let p := prng.up σ Ik
    return (p.1, p.2, none)
  else if t = mo.tStar then
    if mo.tL.isSome && t = mo.tH then
      let Ir ← StateT.lift (sampleT I)
      let k ← StateT.lift (sampleT K)
      return ((prng.up σ Ir).1, k, some Ir)
    else
      let k ← lookupFL Ik
      return ((prng.up σ Ik).1, k, some Ik)
  else if mo.tL.isSome && t = mo.tH then
    let Ir ← StateT.lift (sampleT I)
    let p := prng.up σ Ir
    return (p.1, p.2, none)
  else
    let p := prng.up σ Ik
    return (p.1, p.2, none)

def hooksLocal : Hooks nilSpec (LState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig
    (SS × Option ℕ) (RS × Option ℕ) where
  startSend _ _ t γ σ r := do
    let coins ← match r with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    let (σ', k, sid) ← rootL prng mo t c.2.2 σ
    let idx? ← regSessOf sid
    modify fun s => { s with cache := Function.update s.cache t (some (c.2.1, σ', k, idx?)) }
    return some (c.1, c.2.1, σ', (fs.initSender k, idx?))
  startRecv _ _ t γ σ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, σc, k, idx?) => if Tc = Tn then some (σc, k, idx?) else none
      | none => none
    match honest with
    | some (σc, k, idx?) =>
      return some (some ((cka.receive γ Tn).1, σc, (fs.initReceiver k, idx?)))
    | none =>
      if mo.auth && t = mo.tStar then
        if mo.tL.isSome && mo.tStar = mo.tH then return none
        let kk := cka.receive γ Tn
        let k' ← lookupFL kk.2
        let idx ← regSess kk.2
        return some (some (kk.1, (prng.up σ kk.2).1, (fs.initReceiver k', some idx)))
      else return some none
  fsSend _ _ _ ssv h m _ := do
    let o := fs.send ssv.1 h m
    return some ((o.1, ssv.2), o.2)
  fsRecv _ _ _ rsv h e _ := do
    match fs.receive rsv.1 h e with
    | none => return some none
    | some (rs', i, m) =>
      modify fun s => { s with lastIdx := rsv.2 }
      return some (some ((rs', rsv.2), i, m))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    return some (realParty vp vp.γ vp.root (vp.vS.map Prod.fst) (fun t => (vp.vR t).map Prod.fst))

def initLocal : LHM (Option (PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) ×
    PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, k, sid) ← rootL prng mo 0 lam (prng.init kr)
  let idx? ← regSessOf sid
  return some (mkParties (cka.initA kc) (cka.initB kc) σ
    (fs.initSender k, idx?) (fs.initReceiver k, idx?))

abbrev EStateL (Γ T Sig SS RS M E K I : Type) :=
  EState (PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E) (LState T Sig K I)

abbrev EStateP (Γ T Sig SS RS M E K : Type) :=
  EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)

abbrev SMSpec (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

abbrev SMComp (Γ T Sig SS RS M CCoins E : Type) :=
  OracleComp (SMSpec Γ T Sig SS RS M CCoins E)

def pImpl :
    QueryImpl (unifSpec + PRFPRNG.spec Sig I K) (StateT (PRFPRNG.GameState Sig I K) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (PRFPRNG.GameState Sig I K) ProbComp)
    + PRFPRNG.oracleImpl prng

def stepP (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpec Γ T Sig SS RS M CCoins E).Range q × EStateP Γ T Sig SS RS M E K) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implE (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

def stepL (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpec Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implE (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run esL)

def runP (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implE (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

def runLoc (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implE (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2)

def runLocAt (j : ℕ) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implE (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))

def localAuth (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLoc cka prng fs Δcka qep mo A { g, h }

def localAuthAt (j : ℕ) (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAt cka prng fs Δcka qep mo j A { g, h }

theorem runP_pure (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    runP cka prng fs Δcka qep mo (pure b') esP sp = pure (authOut (2 + Δcka) mo.policy esP) := by
  simp [runP, map_eq_bind_pure_comp]

theorem runLoc_pure (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLoc cka prng fs Δcka qep mo (pure b') esL = pure (authOut (2 + Δcka) mo.policy esL) := by
  simp [runLoc, map_eq_bind_pure_comp]

theorem runLocAt_pure (j : ℕ) (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAt cka prng fs Δcka qep mo j (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAt, map_eq_bind_pure_comp]

theorem runP_query_bind (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runP cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepP cka prng fs Δcka qep mo q esP sp >>= fun r =>
        runP cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runP, stepP, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem runLoc_query_bind (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLoc cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esL =
      stepL cka prng fs Δcka qep mo q esL >>= fun r =>
        runLoc cka prng fs Δcka qep mo (k r.1) r.2 := by
  simp [runLoc, stepL, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem runLocAt_query_bind (j : ℕ) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAt cka prng fs Δcka qep mo j (liftM (OracleSpec.query q) >>= k) esL =
      stepL cka prng fs Δcka qep mo q esL >>= fun r =>
        runLocAt cka prng fs Δcka qep mo j (k r.1) r.2 := by
  simp [runLocAt, stepL, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem stepP_coinsE (n : unifSpec.Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepP cka prng fs Δcka qep mo (.inl n) esP sp =
      (fun u => ((u, esP), sp)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepP, implE, coinsE, pImpl, map_eq_bind_pure_comp, simulateQ_bind,
    simulateQ_query, bind_assoc]

theorem stepL_coinsE (n : unifSpec.Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    stepL cka prng fs Δcka qep mo (.inl n) esL =
      (fun u => (u, esL)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepL, implE, coinsE, lImpl, map_eq_bind_pure_comp, simulateQ_bind,
    simulateQ_query]

theorem stepP_abort (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) (hab : esP.abort = true) :
    ∀ r ∈ support (stepP cka prng fs Δcka qep mo q esP sp), r.1.2.abort = true := by
  intro r hr
  rcases q with n | ((((q | q) | q) | q) | P)
  · rw [stepP_coinsE] at hr
    rw [support_map] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact hab
  · simp only [stepP, implE, QueryImpl.add_apply, transmitE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepP, implE, QueryImpl.add_apply, challE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepP, implE, QueryImpl.add_apply, deliverE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepP, implE, QueryImpl.add_apply, injectE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepP, implE, QueryImpl.add_apply, corrE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab

theorem runP_abort (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true) :
    𝒟[runP cka prng fs Δcka qep mo oa esP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esP sp with
  | pure b' =>
    rw [runP_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runP_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepP_abort cka prng fs Δcka qep mo q esP sp hab r hr)

theorem runP_abort_le (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runP cka prng fs Δcka qep mo oa esP sp] {true} ≤ rhs := by
  rw [runP_abort cka prng fs Δcka qep mo oa hab]
  exact zero_le

/-! ### Session indexing and union bound -/

@[simp]
theorem simulateQ_lImpl_run_lift_sampleT {HS α : Type} [SampleableType α] (s : HS) :
    simulateQ lImpl ((StateT.lift (sampleT α) : StateT HS (TComp nilSpec) α).run s) =
      (($ᵗ α : ProbComp α) >>= fun a => pure (a, s)) := by
  change simulateQ lImpl (sampleT α >>= fun a => pure (a, s)) = _
  simp

theorem mem_support_lookupFL {Ik : I} {s : LState T Sig K I} {k : K} {s' : LState T Sig K I}
    (h : (k, s') ∈ support (simulateQ lImpl ((lookupFL Ik).run s))) :
    s'.sessions = s.sessions ∧ s'.cache = s.cache ∧ s'.lastIdx = s.lastIdx := by
  simp only [lookupFL, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
    injection h with _ hs; subst hs
    exact ⟨rfl, rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, simulateQ_pure,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
    rcases h with ⟨_, ⟨_, _, rfl⟩, hpair⟩
    injection hpair with _ hs; subst hs
    exact ⟨rfl, rfl, rfl⟩

theorem mem_support_regSess {Ik : I} {s : LState T Sig K I} {idx : ℕ} {s' : LState T Sig K I}
    (h : (idx, s') ∈ support (simulateQ lImpl ((regSess (T := T) (Sig := Sig) (K := K) Ik).run s))) :
    idx < s'.sessions.length ∧
    s.sessions.length ≤ s'.sessions.length ∧
    s'.sessions.length ≤ s.sessions.length + 1 ∧
    s'.cache = s.cache ∧
    s'.lastIdx = s.lastIdx := by
  unfold regSess at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · rename_i hmem
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
    injection h with h1 h2; subst h1 h2
    exact ⟨List.idxOf_lt_length_of_mem hmem, le_rfl, Nat.le_succ _, rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at h
    injection h with h1 h2; subst h1 h2
    dsimp only
    rw [List.length_append, List.length_singleton]
    exact ⟨Nat.lt_succ_self _, Nat.le_succ _, le_rfl, rfl, rfl⟩

theorem mem_support_regSessOf {sid : Option I} {s : LState T Sig K I} {idx? : Option ℕ}
    {s' : LState T Sig K I}
    (h : (idx?, s') ∈ support (simulateQ lImpl ((regSessOf (T := T) (Sig := Sig) (K := K) sid).run s))) :
    (sid = none → idx? = none ∧ s' = s) ∧
    (∀ Ik, sid = some Ik →
      (∃ idx, idx < s'.sessions.length ∧ idx? = some idx) ∧
      s.sessions.length ≤ s'.sessions.length ∧
      s'.sessions.length ≤ s.sessions.length + 1 ∧
      s'.cache = s.cache ∧
      s'.lastIdx = s.lastIdx) := by
  cases sid with
  | none =>
    simp only [regSessOf, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
    injection h with h1 h2; subst h1 h2
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ hnone => by cases hnone⟩
  | some Ik =>
    simp only [regSessOf, StateT.run_map, simulateQ_map, support_map] at h
    rcases h with ⟨⟨idx, s₁⟩, hreg, hpair⟩
    dsimp only [Prod.map, id_eq] at hpair
    injection hpair with h1 h2; subst h1 h2
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_support_regSess hreg
    constructor
    · intro hnone; cases hnone
    · intro Ik' _; exact ⟨⟨idx, h1, rfl⟩, h2, h3, h4, h5⟩

theorem mem_support_rootL {t : ℕ} {Ik : I} {σ : Sig} {s : LState T Sig K I}
    {out : Sig × K × Option I} {s' : LState T Sig K I}
    (h : (out, s') ∈ support (simulateQ lImpl ((rootL prng mo t Ik σ).run s))) :
    s'.sessions = s.sessions ∧ s'.cache = s.cache ∧ s'.lastIdx = s.lastIdx ∧
    (t = mo.tStar → ∃ Ik', out.2.2 = some Ik') ∧
    (t ≠ mo.tStar → out.2.2 = none) := by
  unfold rootL at h
  by_cases hgt : mo.tStar < t
  · simp only [hgt, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at h
    injection h with h1 h2; subst h1 h2
    exact ⟨rfl, rfl, rfl, fun heq => by omega, fun _ => rfl⟩
  · simp only [hgt, ↓reduceIte] at h
    by_cases heq : t = mo.tStar
    · simp only [heq, ↓reduceIte] at h
      split at h
      · simp only [StateT.run_bind, pure_bind, StateT.run_pure, simulateQ_bind,
          simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨_, ⟨Ir, _, rfl⟩, _, ⟨k, _, rfl⟩, hpair⟩
        injection hpair with h1 h2; subst h1 h2
        exact ⟨rfl, rfl, rfl, fun _ => ⟨Ir, rfl⟩, fun hne => (hne heq).elim⟩
      · simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨k, s₁⟩, hlk, hpair⟩
        injection hpair with h1 h2; subst h1 h2
        obtain ⟨h1, h2, h3⟩ := mem_support_lookupFL hlk
        exact ⟨h1, h2, h3, fun _ => ⟨Ik, rfl⟩, fun hne => (hne heq).elim⟩
    · simp only [heq, ↓reduceIte] at h
      split at h
      · simp only [StateT.run_bind, pure_bind, StateT.run_pure, simulateQ_bind,
          simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨_, ⟨Ir, _, rfl⟩, hpair⟩
        injection hpair with h1 h2; subst h1 h2
        exact ⟨rfl, rfl, rfl, fun h1 => (heq h1).elim, fun _ => rfl⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
        injection h with h1 h2; subst h1 h2
        exact ⟨rfl, rfl, rfl, fun h1 => (heq h1).elim, fun _ => rfl⟩

theorem mem_support_startSend_local {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {t : ℕ} {γ : Γ} {σ : Sig} {r : Option CCoins} {s : LState T Sig K I}
    {res : Option (Γ × T × Sig × (SS × Option ℕ))} {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      (((hooksLocal cka prng fs mo).startSend ctx P t γ σ r).run s)))
    (hc_inv : ∀ Tc σk kk idx?, s.cache mo.tStar = some (Tc, σk, kk, idx?) →
      ∃ idx, idx < s.sessions.length ∧ idx? = some idx) :
    s.sessions.length ≤ s'.sessions.length ∧
    s'.sessions.length ≤ s.sessions.length + 1 ∧
    (t ≠ mo.tStar → s'.sessions = s.sessions) ∧
    s'.lastIdx = s.lastIdx ∧
    (∀ Tc σk kk idx?, s'.cache mo.tStar = some (Tc, σk, kk, idx?) →
      ∃ idx, idx < s'.sessions.length ∧ idx? = some idx) := by
  have hcoins : ∃ coins, (res, s') ∈ support (simulateQ lImpl
      (((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some coins)).run s)) := by
    cases r with
    | some c => exact ⟨c, h⟩
    | none =>
      have hbind : ((hooksLocal cka prng fs mo).startSend ctx P t γ σ none).run s =
          ((StateT.lift (sampleT CCoins) : LHM CCoins).run s >>= fun p =>
            ((hooksLocal cka prng fs mo).startSend ctx P t γ σ (some p.1)).run p.2) := rfl
      rw [hbind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT] at h
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
      rcases h with ⟨_, ⟨c, _, rfl⟩, hc⟩
      exact ⟨c, hc⟩
  rcases hcoins with ⟨coins, h⟩
  simp only [hooksLocal, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
    simulateQ_bind, simulateQ_pure, MonadAttach.mem_support_bind, support_pure,
    Set.mem_singleton_iff] at h
  rcases h with ⟨⟨⟨σ', k, sid⟩, s₁⟩, hroot, ⟨idx?, s₂⟩, hreg, hpair⟩
  injection hpair with hres hs'; subst hs'
  obtain ⟨h1_sess, h1_cache, h1_last, h1_eq, h1_ne⟩ := mem_support_rootL prng mo hroot
  obtain ⟨h2_none, h2_some⟩ := mem_support_regSessOf hreg
  by_cases ht : t = mo.tStar
  · obtain ⟨Ik', hsid⟩ := h1_eq ht
    obtain ⟨⟨idx, hidx_lt, hidx_eq⟩, hlen_le, hlen_ub, _, h2_last⟩ := h2_some Ik' hsid
    rw [h1_sess] at hlen_le hlen_ub
    refine ⟨hlen_le, hlen_ub, fun hne => (hne ht).elim, h2_last.trans h1_last, ?_⟩
    intro Tc σk kk idx?' hcache
    dsimp only at hcache
    rw [← ht, Function.update_self] at hcache
    injection hcache with htuple
    injection htuple with _ htuple2
    injection htuple2 with _ htuple3
    injection htuple3 with _ hidx'
    subst hidx'
    exact ⟨idx, hidx_lt, hidx_eq⟩
  · obtain ⟨hidx_none, hs₂⟩ := h2_none (h1_ne ht)
    subst hs₂
    refine ⟨by rw [h1_sess], by rw [h1_sess]; omega, fun _ => h1_sess, h1_last, ?_⟩
    intro Tc σk kk idx?' hcache
    dsimp only at hcache
    rw [Function.update_of_ne (Ne.symm ht), h1_cache] at hcache
    obtain ⟨idx, hlt, heq⟩ := hc_inv Tc σk kk idx?' hcache
    exact ⟨idx, by rwa [h1_sess], heq⟩

theorem mem_support_vSend_local {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)} {m : M}
    {pair : Option (M × M)} {r : Option CCoins} {s : LState T Sig K I}
    {res : Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × (Header T × E))}
    {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      ((vSend (hooksLocal cka prng fs mo) ctx P vp m pair r).run s)))
    (hc_inv : ∀ Tc σk kk idx?, s.cache mo.tStar = some (Tc, σk, kk, idx?) →
      ∃ idx, idx < s.sessions.length ∧ idx? = some idx) :
    s.sessions.length ≤ s'.sessions.length ∧
    s'.sessions.length ≤ s.sessions.length + 1 ∧
    (mo.tStar = 0 → s'.sessions = s.sessions) ∧
    s'.lastIdx = s.lastIdx ∧
    (∀ Tc σk kk idx?, s'.cache mo.tStar = some (Tc, σk, kk, idx?) →
      ∃ idx, idx < s'.sessions.length ∧ idx? = some idx) ∧
    (∀ vp' c, res = some (vp', c) → vp'.id = vp.id ∧ vp'.vR = vp.vR) := by
  unfold vSend at h
  split at h
  · simp only [StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at h
    rcases h with ⟨⟨res_ss, s_ss⟩, hss, h2⟩
    obtain ⟨hl1, hl2, hne, hlast, hc'⟩ := mem_support_startSend_local cka prng fs mo hss hc_inv
    cases res_ss with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at h2
      injection h2 with hres hs'; subst hres hs'
      exact ⟨hl1, hl2, fun h0 => hne (by omega), hlast, hc', fun _ _ hnone => nomatch hnone⟩
    | some val =>
      rcases val with ⟨γ', T', σ', ss⟩
      simp only [hooksLocal, pure_bind, StateT.run_bind, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at h2
      injection h2 with hres hs'; subst hres hs'
      refine ⟨hl1, hl2, fun h0 => hne (by omega), hlast, hc', ?_⟩
      intro vp' c heq; injection heq with heq; injection heq with hvp _
      subst hvp; exact ⟨rfl, rfl⟩
  · simp only [pure_bind] at h
    cases hvS : vp.vS with
    | none =>
      simp only [hvS, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
      injection h with hres hs'; subst hres hs'
      refine ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, hc_inv, ?_⟩
      intro vp' c heq; injection heq with heq; injection heq with hvp _
      subst hvp; exact ⟨rfl, rfl⟩
    | some v =>
      simp only [hvS, hooksLocal, StateT.run_bind, StateT.run_pure, pure_bind, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at h
      injection h with hres hs'; subst hres hs'
      refine ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, hc_inv, ?_⟩
      intro vp' c heq; injection heq with heq; injection heq with hvp _
      subst hvp; exact ⟨rfl, rfl⟩

theorem mem_support_startRecv_local {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {t : ℕ} {γ : Γ} {σ : Sig} {Tn : T} {s : LState T Sig K I}
    {res : Option (Option (Γ × Sig × (RS × Option ℕ)))} {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      (((hooksLocal cka prng fs mo).startRecv ctx P t γ σ Tn).run s)))
    (hc_inv : ∀ Tc σk kk idx?, s.cache mo.tStar = some (Tc, σk, kk, idx?) →
      ∃ idx, idx < s.sessions.length ∧ idx? = some idx) :
    s.sessions.length ≤ s'.sessions.length ∧
    s'.sessions.length ≤ s.sessions.length + 1 ∧
    (t ≠ mo.tStar → s'.sessions = s.sessions) ∧
    s'.cache = s.cache ∧
    (∀ γ' σ' rsv, res = some (some (γ', σ', rsv)) → t = mo.tStar →
      ∃ idx, idx < s'.sessions.length ∧ rsv.2 = some idx) := by
  simp only [hooksLocal, StateT.run_bind, StateT.run_get, pure_bind] at h
  cases hcache : s.cache t with
  | none =>
    simp only [hcache] at h
    split at h
    · rename_i hauth_t
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hauth_t
      split at h
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
        injection h with hres hs'; subst hres hs'
        exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ hnone => nomatch hnone⟩
      · simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
        rcases h with ⟨⟨k', s₁⟩, hlk, ⟨idx, s₂⟩, hreg, hpair⟩
        injection hpair with hres hs'; subst hres hs'
        obtain ⟨h1_sess, h1_cache, _⟩ := mem_support_lookupFL hlk
        obtain ⟨h2_lt, h2_le, h2_ub, h2_cache, _⟩ := mem_support_regSess hreg
        rw [h1_sess] at h2_le h2_ub
        refine ⟨h2_le, h2_ub, fun hne => (hne hauth_t.2).elim, h2_cache.trans h1_cache, ?_⟩
        intro γ' σ' rsv heq _
        injection heq with heq; injection heq with heq; injection heq with _ heq
        injection heq with _ hrsv; subst hrsv
        exact ⟨idx, h2_lt, rfl⟩
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
      injection h with hres hs'; subst hres hs'
      exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ hnone => nomatch hnone⟩
  | some val =>
    rcases val with ⟨Tc, σc, k, idx?⟩
    simp only [hcache] at h
    by_cases hTc : Tc = Tn
    · simp only [hTc, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at h
      injection h with hres hs'; subst hres hs'
      refine ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, ?_⟩
      intro γ' σ' rsv heq ht
      injection heq with heq; injection heq with heq; injection heq with _ heq
      injection heq with _ hrsv; subst hrsv
      subst ht
      exact hc_inv Tc σc k idx? hcache
    · simp only [hTc, ↓reduceIte] at h
      split at h
      · rename_i hauth_t
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hauth_t
        split at h
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
          injection h with hres hs'; subst hres hs'
          exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ hnone => nomatch hnone⟩
        · simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
          rcases h with ⟨⟨k', s₁⟩, hlk, ⟨idx, s₂⟩, hreg, hpair⟩
          injection hpair with hres hs'; subst hres hs'
          obtain ⟨h1_sess, h1_cache, _⟩ := mem_support_lookupFL hlk
          obtain ⟨h2_lt, h2_le, h2_ub, h2_cache, _⟩ := mem_support_regSess hreg
          rw [h1_sess] at h2_le h2_ub
          refine ⟨h2_le, h2_ub, fun hne => (hne hauth_t.2).elim, h2_cache.trans h1_cache, ?_⟩
          intro γ' σ' rsv heq _
          injection heq with heq; injection heq with heq; injection heq with _ heq
          injection heq with _ hrsv; subst hrsv
          exact ⟨idx, h2_lt, rfl⟩
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
        injection h with hres hs'; subst hres hs'
        exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ hnone => nomatch hnone⟩

theorem mem_support_vRecv_local {ctx : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E}
    {P : Party} {vp : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)} {c : Header T × E}
    {rec : Option (SM.Record M (Header T × E))} {s : LState T Sig K I}
    {res : Option (Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × ℕ × ℕ × M))}
    {s' : LState T Sig K I}
    (h : (res, s') ∈ support (simulateQ lImpl
      ((vRecv (hooksLocal cka prng fs mo) ctx P vp c rec).run s)))
    (hvR_inv : ∀ rsv, vp.vR mo.tStar = some rsv →
      ∃ idx, idx < s.sessions.length ∧ rsv.2 = some idx)
    (hc_inv : ∀ Tc σk kk idx?, s.cache mo.tStar = some (Tc, σk, kk, idx?) →
      ∃ idx, idx < s.sessions.length ∧ idx? = some idx) :
    s.sessions.length ≤ s'.sessions.length ∧
    s'.sessions.length ≤ s.sessions.length + 1 ∧
    (mo.tStar = 0 → s'.sessions = s.sessions) ∧
    s'.cache = s.cache ∧
    (∀ vp' t' i' m', res = some (some (vp', t', i', m')) →
      vp'.id = vp.id ∧
      (∀ rsv, vp'.vR mo.tStar = some rsv →
        ∃ idx, idx < s'.sessions.length ∧ rsv.2 = some idx) ∧
      (t' = mo.tStar → ∃ idx, idx < s'.sessions.length ∧ s'.lastIdx = some idx)) := by
  unfold vRecv at h
  dsimp only at h
  split at h
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
    injection h with hres hs'; subst hres hs'
    exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ _ hnone => nomatch hnone⟩
  · split at h
    · rename_i h_ep1
      cases hc2 : c.1.2 with
      | none =>
        simp only [hc2, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at h
        injection h with hres hs'; subst hres hs'
        exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ _ hnone => nomatch hnone⟩
      | some Tn =>
        simp only [hc2, StateT.run_bind, simulateQ_bind, MonadAttach.mem_support_bind] at h
        rcases h with ⟨⟨res_sr, s_sr⟩, hsr, h2⟩
        obtain ⟨hl1, hl2, hne, hcache_sr, hsr_idx⟩ :=
          mem_support_startRecv_local cka prng fs mo hsr hc_inv
        have h0_sr : mo.tStar = 0 → s_sr.sessions = s.sessions := fun h0 => hne (by omega)
        cases res_sr with
        | none =>
          simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at h2
          injection h2 with hres hs'; subst hres hs'
          exact ⟨hl1, hl2, h0_sr, hcache_sr, fun _ _ _ _ hnone => nomatch hnone⟩
        | some res_sr' =>
          cases res_sr' with
          | none =>
            simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at h2
            injection h2 with hres hs'; subst hres hs'
            exact ⟨hl1, hl2, h0_sr, hcache_sr, fun _ _ _ _ hnone => nomatch hnone⟩
          | some val =>
            rcases val with ⟨γ', σ', rs⟩
            simp only [pure_bind, Function.update_self, hooksLocal] at h2
            cases hfs : fs.receive rs.1 c.1 c.2 with
            | none =>
              simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at h2
              injection h2 with hres hs'; subst hres hs'
              exact ⟨hl1, hl2, h0_sr, hcache_sr, fun _ _ _ _ hnone => nomatch hnone⟩
            | some out =>
              rcases out with ⟨rs', i, m⟩
              simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at h2
              injection h2 with hres hs'; subst hres hs'
              refine ⟨hl1, hl2, h0_sr, hcache_sr, ?_⟩
              intro vp' t' i' m' heq
              injection heq with heq; injection heq with heq; injection heq with hvp hrest
              injection hrest with ht' _
              subst hvp ht'
              refine ⟨rfl, ?_, ?_⟩
              · intro rsv hrsv
                dsimp only at hrsv
                by_cases hct : c.1.1 = mo.tStar
                · rw [← hct, Function.update_self] at hrsv
                  injection hrsv with hrsv; subst hrsv
                  exact hsr_idx γ' σ' rs rfl hct
                · rw [Function.update_of_ne (Ne.symm hct), Function.update_of_ne (Ne.symm hct)] at hrsv
                  obtain ⟨idx, hlt, heq_idx⟩ := hvR_inv rsv hrsv
                  exact ⟨idx, lt_of_lt_of_le hlt hl1, heq_idx⟩
              · intro ht'
                exact hsr_idx γ' σ' rs rfl ht'
    · simp only [pure_bind] at h
      cases hvR : vp.vR c.1.1 with
      | none =>
        simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at h
        injection h with hres hs'; subst hres hs'
        exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ _ hnone => nomatch hnone⟩
      | some v =>
        simp only [hvR, hooksLocal] at h
        cases hfs : fs.receive v.1 c.1 c.2 with
        | none =>
          simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at h
          injection h with hres hs'; subst hres hs'
          exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, fun _ _ _ _ hnone => nomatch hnone⟩
        | some out =>
          rcases out with ⟨rs', i, m⟩
          simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at h
          injection h with hres hs'; subst hres hs'
          refine ⟨le_rfl, Nat.le_succ _, fun _ => rfl, rfl, ?_⟩
          intro vp' t' i' m' heq
          injection heq with heq; injection heq with heq; injection heq with hvp hrest
          injection hrest with ht' _
          subst hvp ht'
          refine ⟨rfl, ?_, ?_⟩
          · intro rsv hrsv
            dsimp only at hrsv
            by_cases hct : c.1.1 = mo.tStar
            · rw [← hct, Function.update_self] at hrsv
              injection hrsv with hrsv; subst hrsv
              rw [hct] at hvR
              exact hvR_inv v hvR
            · rw [Function.update_of_ne (Ne.symm hct)] at hrsv
              exact hvR_inv rsv hrsv
          · intro ht'
            rw [ht'] at hvR
            exact hvR_inv v hvR

/-- Invariant on `esL` bounding the number of epoch-`t*` sessions by the query budget `q`. -/
structure SessInv (q rem : ℕ) (esL : EStateL Γ T Sig SS RS M E K I) : Prop where
  vR_idx : ∀ P rsv, (esL.g.st P).vR mo.tStar = some rsv →
    ∃ idx, idx < esL.h.sessions.length ∧ rsv.2 = some idx
  cache_idx : ∀ Tc σ k idx?, esL.h.cache mo.tStar = some (Tc, σ, k, idx?) →
    ∃ idx, idx < esL.h.sessions.length ∧ idx? = some idx
  bound :
    (esL.g.win = true ∧ ∃ j, j < q ∧ esL.h.lastIdx = some j) ∨
    (esL.g.win = false ∧
      ((mo.tStar = 0 ∧ esL.h.sessions.length ≤ 1 ∧ rem ≤ q) ∨
       (0 < mo.tStar ∧ esL.h.sessions.length + rem ≤ q)))

theorem SessInv.mono_sessions {q rem : ℕ} {esL : EStateL Γ T Sig SS RS M E K I}
    (hS : SessInv mo q rem esL) {P : Party}
    {vp' : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)} {h' : LState T Sig K I}
    (hlen : esL.h.sessions.length ≤ h'.sessions.length)
    (hvR' : ∀ rsv, vp'.vR mo.tStar = some rsv →
      ∃ idx, idx < h'.sessions.length ∧ rsv.2 = some idx)
    (Q : Party) (rsv : RS × Option ℕ)
    (hq : (Function.update esL.g.st P vp' Q).vR mo.tStar = some rsv) :
    ∃ idx, idx < h'.sessions.length ∧ rsv.2 = some idx := by
  by_cases hQP : Q = P
  · subst hQP; rw [Function.update_self] at hq; exact hvR' rsv hq
  · rw [Function.update_of_ne hQP] at hq
    obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
    exact ⟨idx, lt_of_lt_of_le hlt hlen, heq⟩

theorem stepL_sessInv (hauth : mo.auth = true) {q rem : ℕ}
    (q_sm : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    (∀ t, q_sm = .inl t →
      ∀ r ∈ support (stepL cka prng fs Δcka qep mo (.inl t) esL),
        SessInv mo q rem r.2) ∧
    (∀ q_inr, q_sm = .inr q_inr → 0 < rem →
      ∀ r ∈ support (stepL cka prng fs Δcka qep mo (.inr q_inr) esL),
        SessInv mo q (rem - 1) r.2) := by
  constructor
  · intro t ht r hr
    rw [stepL_coinsE, support_map] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact hS
  · intro q_inr hq_sm hrem r hr
    have hrem_mono :
        (esL.g.win = true ∧ ∃ j, j < q ∧ esL.h.lastIdx = some j) ∨
        (esL.g.win = false ∧
          ((mo.tStar = 0 ∧ esL.h.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
           (0 < mo.tStar ∧ esL.h.sessions.length + (rem - 1) ≤ q))) := by
      rcases hS.bound with hwin | ⟨hnw, ⟨ht0, hle1, hrem_q⟩ | hpos⟩
      · exact Or.inl hwin
      · exact Or.inr ⟨hnw, Or.inl ⟨ht0, hle1, by omega⟩⟩
      · exact Or.inr ⟨hnw, Or.inr ⟨hpos.1, by omega⟩⟩
    have hS_noop : SessInv mo q (rem - 1) esL := ⟨hS.vR_idx, hS.cache_idx, hrem_mono⟩
    rcases q_inr with ((((q1 | q2) | q3) | q4) | P)
    ·
      rcases q1 with ⟨P, m, r_coins⟩
      simp only [stepL, implE, QueryImpl.add_apply, transmitE, StateT.run_bind, StateT.run_get,
        pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_ab_win
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_ab_win
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnot_ab_win; cases hnot_ab_win.2
        · cases hep : esL.g.epMgmt (2 + Δcka) qep P r_coins.isSome with
          | none =>
            simp only [hep, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hr
            subst hr; exact hS_noop
          | some s₁ =>
            have hs₁_st : s₁.st = esL.g.st := by
              unfold SM.GameState.epMgmt at hep
              split at hep <;> split at hep
              · cases hep
              · injection hep with hep; subst hep; split <;> rfl
              · cases hep
              · injection hep with hep; subst hep; rfl
            have hs₁_win : s₁.win = esL.g.win := by
              unfold SM.GameState.epMgmt at hep
              split at hep <;> split at hep
              · cases hep
              · injection hep with hep; subst hep; split <;> rfl
              · cases hep
              · injection hep with hep; subst hep; rfl
            simp only [hep] at hr
            split at hr
            · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact ⟨hS.vR_idx, hS.cache_idx, hrem_mono⟩
            · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
                MonadAttach.mem_support_bind] at hr
              rcases hr with ⟨⟨res_vs, h'⟩, hvs, hr2⟩
              obtain ⟨hl1, hl2, h0, hlast, hc', hvp'⟩ :=
                mem_support_vSend_local cka prng fs mo hvs hS.cache_idx
              have hbound' :
                  (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
                  (esL.g.win = false ∧
                    ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                     (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
                refine Or.inr ⟨hnot_ab_win.2, ?_⟩
                rcases hlen_bound with ⟨ht0, hle1, hrem_q⟩ | ⟨htpos, hleq⟩
                · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
                · exact Or.inr ⟨htpos, by omega⟩
              cases res_vs with
              | none =>
                simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                subst hr2
                refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
              | some val =>
                rcases val with ⟨st', c⟩
                simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                subst hr2
                obtain ⟨_, hvR_st'⟩ := hvp' st' c rfl
                refine ⟨fun Q rsv hq => ?_, hc', ?_⟩
                · dsimp only [SM.GameState.record] at hq
                  rw [hs₁_st] at hq hvR_st'
                  exact hS.mono_sessions mo hl1 (fun rsv hr => by
                    rw [hvR_st'] at hr
                    obtain ⟨idx, hlt, heq⟩ := hS.vR_idx P rsv hr
                    exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩) Q rsv hq
                · dsimp only [SM.GameState.record]
                  rwa [hs₁_win]
    ·
      rcases q2 with ⟨P, m₀, m₁, r_coins⟩
      simp only [stepL, implE, QueryImpl.add_apply, challE, Mode.cfg, hauth, ↓reduceIte,
        SM.Config.auth, Bool.not_false, Bool.or_true, StateT.run_bind, StateT.run_get,
        pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · split at hr <;>
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact hS_noop
    ·
      rcases q3 with ⟨P, c⟩
      simp only [stepL, implE, QueryImpl.add_apply, deliverE, Mode.cfg, hauth, ↓reduceIte,
        SM.Config.auth, Bool.false_and, StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_ab_win
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_ab_win
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnot_ab_win; cases hnot_ab_win.2
        · split at hr
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact hS_noop
          · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
              MonadAttach.mem_support_bind] at hr
            rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
            obtain ⟨hl1, hl2, h0, hcache', hvp'⟩ :=
              mem_support_vRecv_local cka prng fs mo hvr (hS.vR_idx P) hS.cache_idx
            have hbound' :
                (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
                (esL.g.win = false ∧
                  ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                   (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
              refine Or.inr ⟨hnot_ab_win.2, ?_⟩
              rcases hlen_bound with ⟨ht0, hle1, hrem_q⟩ | ⟨htpos, hleq⟩
              · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
              · exact Or.inr ⟨htpos, by omega⟩
            have hc' : ∀ Tc σ k idx?, h'.cache mo.tStar = some (Tc, σ, k, idx?) →
                ∃ idx, idx < h'.sessions.length ∧ idx? = some idx := by
              intro Tc σ k idx? hc
              rw [hcache'] at hc
              obtain ⟨idx, hlt, heq⟩ := hS.cache_idx Tc σ k idx? hc
              exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
            cases res_vr with
            | none =>
              simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
              subst hr2
              refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
              obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
              exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
            | some res_vr' =>
              cases res_vr' with
              | none =>
                simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2
                refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
              | some val =>
                rcases val with ⟨st', t', i', m'⟩
                simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                  StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2
                obtain ⟨_, hvR_st', _⟩ := hvp' st' t' i' m' rfl
                refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                dsimp only [SM.GameState.accept, SM.GameState.delete] at hq
                rw [Function.update_idem] at hq
                exact hS.mono_sessions mo hl1 hvR_st' Q rsv hq
    ·
      rcases q4 with ⟨P, c⟩
      simp only [stepL, implE, QueryImpl.add_apply, injectE, Mode.cfg, hauth, ↓reduceIte,
        SM.Config.auth, StateT.run_bind, StateT.run_get, pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · rename_i hnot_guard
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hnot_guard
        have hnw : esL.g.win = false := hnot_guard.1.1.2
        rcases hS.bound with ⟨hwin, _⟩ | ⟨_, hlen_bound⟩
        · rw [hwin] at hnw; cases hnw
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
            MonadAttach.mem_support_bind] at hr
          rcases hr with ⟨⟨res_vr, h'⟩, hvr, hr2⟩
          obtain ⟨hl1, hl2, h0, hcache', hvp'⟩ :=
            mem_support_vRecv_local cka prng fs mo hvr (hS.vR_idx P) hS.cache_idx
          have hbound' :
              (esL.g.win = true ∧ ∃ j, j < q ∧ h'.lastIdx = some j) ∨
              (esL.g.win = false ∧
                ((mo.tStar = 0 ∧ h'.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
                 (0 < mo.tStar ∧ h'.sessions.length + (rem - 1) ≤ q))) := by
            refine Or.inr ⟨hnw, ?_⟩
            rcases hlen_bound with ⟨ht0, hle1, hrem_q⟩ | ⟨htpos, hleq⟩
            · exact Or.inl ⟨ht0, by rw [h0 ht0]; exact hle1, by omega⟩
            · exact Or.inr ⟨htpos, by omega⟩
          have hc' : ∀ Tc σ k idx?, h'.cache mo.tStar = some (Tc, σ, k, idx?) →
              ∃ idx, idx < h'.sessions.length ∧ idx? = some idx := by
            intro Tc σ k idx? hc
            rw [hcache'] at hc
            obtain ⟨idx, hlt, heq⟩ := hS.cache_idx Tc σ k idx? hc
            exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
          cases res_vr with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
            subst hr2
            refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
            obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
            exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
          | some res_vr' =>
            cases res_vr' with
            | none =>
              simp only [pure_bind, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hr2
              subst hr2
              refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
              obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
              exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
            | some val =>
              rcases val with ⟨st', t', i', m'⟩
              obtain ⟨_, hvR_st', hlast_tStar⟩ := hvp' st' t' i' m' rfl
              simp only [pure_bind] at hr2
              split at hr2
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr2
                subst hr2
                refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
              · split at hr2
                · simp only [commitE, hooksLocal, run_liftH, pure_bind, StateT.run_bind,
                    StateT.run_pure, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr2
                  subst hr2
                  refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                  dsimp only [SM.GameState.accept, SM.GameState.delete] at hq
                  rw [Function.update_idem] at hq
                  exact hS.mono_sessions mo hl1 hvR_st' Q rsv hq
                · split at hr2
                  · rename_i ht'
                    simp only [beq_iff_eq] at ht'
                    simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr2
                    subst hr2
                    obtain ⟨idx, hidx_lt, hlast_eq⟩ := hlast_tStar ht'
                    have hidx_q : idx < q := by
                      rcases hlen_bound with ⟨ht0, hle1, hrem_q⟩ | ⟨htpos, hleq⟩
                      · rw [h0 ht0] at hidx_lt; omega
                      · omega
                    refine ⟨fun Q rsv hq => ?_, hc', Or.inl ⟨rfl, ⟨idx, hidx_q, hlast_eq⟩⟩⟩
                    obtain ⟨idx', hlt, heq⟩ := hS.vR_idx Q rsv hq
                    exact ⟨idx', lt_of_lt_of_le hlt hl1, heq⟩
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hr2
                    subst hr2
                    refine ⟨fun Q rsv hq => ?_, hc', hbound'⟩
                    obtain ⟨idx, hlt, heq⟩ := hS.vR_idx Q rsv hq
                    exact ⟨idx, lt_of_lt_of_le hlt hl1, heq⟩
    ·
      simp only [stepL, implE, QueryImpl.add_apply, corrE, StateT.run_bind, StateT.run_get,
        pure_bind] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact hS_noop
      · split at hr
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨hS_noop.vR_idx, hS_noop.cache_idx, hS_noop.bound⟩
        · simp only [hooksLocal, run_liftH, pure_bind, StateT.run_bind, StateT.run_pure,
            StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact ⟨hS_noop.vR_idx, hS_noop.cache_idx, hS_noop.bound⟩

theorem runLoc_le_sum_runLocAt (hauth : mo.auth = true) {q rem : ℕ}
    {p : (SMSpec Γ T Sig SS RS M CCoins E).Domain → Prop} [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (hq : oa.IsQueryBoundP p rem)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    𝒟[runLoc cka prng fs Δcka qep mo oa esL] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[runLocAt cka prng fs Δcka qep mo j oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing rem esL with
  | pure a =>
    simp only [runLoc, runLocAt, simulateQ_pure, StateT.run_pure, pure_bind, evalDist_pure]
    by_cases hwin : authOut (2 + Δcka) mo.policy esL = true
    · rw [hwin]
      simp only [Bool.true_and, Set.mem_singleton_iff, ↓reduceIte]
      have hwin_g : esL.g.win = true := by
        unfold authOut at hwin
        simp only [Bool.and_eq_true] at hwin
        exact hwin.1.2
      rcases hS.bound with ⟨_, j, hj, hlast⟩ | ⟨hnw, _⟩
      · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr hj))
        simp [hlast]
      · rw [hwin_g] at hnw; cases hnw
    · have hfalse : authOut (2 + Δcka) mo.policy esL = false :=
        Bool.eq_false_iff.mpr hwin
      simp [hfalse]
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    dsimp only [runLoc, runLocAt]
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
      simulateQ_bind, bind_assoc]
    change 𝒟[stepL cka prng fs Δcka qep mo t esL >>= fun x =>
        runLoc cka prng fs Δcka qep mo (r x.1) x.2] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[stepL cka prng fs Δcka qep mo t esL >>= fun x =>
        runLocAt cka prng fs Δcka qep mo j (r x.1) x.2] {true}
    refine evalDist_bind_le_sum _ _ _ _ (fun x hx => ?_)
    have hstep := stepL_sessInv cka prng fs Δcka qep mo hauth t esL hS
    cases t with
    | inl c =>
      exact ih x.1 (by simpa [hp_inl c] using hq.2 x.1) x.2 (hstep.1 c rfl x hx)
    | inr q_sm =>
      have hpos : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      exact ih x.1 (by simpa [hp_inr q_sm] using hq.2 x.1) x.2 (hstep.2 q_sm rfl hpos x hx)

theorem localAuth_le_sum_localAuthAt (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) (hq : SM.MakesAtMostQueries A q) :
    𝒟[localAuth cka prng fs lam Δcka qep tL t A] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[localAuthAt cka prng fs lam Δcka qep j tL t A] {true} := by
  rw [SM.MakesAtMostQueries] at hq
  dsimp only [localAuth, localAuthAt]
  refine evalDist_bind_le_sum
    (simulateQ lImpl ((initLocal cka prng fs lam ⟨true, tL, t⟩).run {})) q
    (fun x => match x.1 with
      | none => pure false
      | some (vA, vB) =>
        runLoc cka prng fs Δcka qep ⟨true, tL, t⟩ A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun j x => match x.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocAt cka prng fs Δcka qep ⟨true, tL, t⟩ j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun x hx => ?_)
  rcases x with ⟨vs, h⟩
  cases vs with
  | none =>
    simp
  | some vAB =>
    rcases vAB with ⟨vA, vB⟩
    let mo : Mode := ⟨true, tL, t⟩
    have hS : SessInv mo q q
        ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := h } :
          EStateL Γ T Sig SS RS M E K I) := by
      simp only [initLocal, StateT.run_bind, simulateQ_bind, simulateQ_lImpl_run_lift_sampleT,
        MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨⟨kr, s1⟩, ⟨_, _, hs1⟩, ⟨kc, s2⟩, ⟨_, _, hs2⟩,
        ⟨⟨σ, k, sid⟩, s3⟩, hroot, ⟨idx?, s4⟩, hreg, hpure⟩
      injection hs1 with _ hs1; subst hs1
      injection hs2 with _ hs2; subst hs2
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hpure
      injection hpure with hvAB hh
      injection hvAB with hvAB; injection hvAB with hvA hvB
      subst hvA hvB hh
      obtain ⟨hl_r, hc_r, _, hsid_r1, hsid_r2⟩ := mem_support_rootL prng mo hroot
      obtain ⟨hnone_reg, hsome_reg⟩ := mem_support_regSessOf hreg
      refine ⟨?_, ?_, ?_⟩
      · intro P rsv hrsv
        cases P <;> dsimp only [mkParties] at hrsv
        · split at hrsv
          · rename_i ht0
            injection hrsv with hrsv; subst hrsv
            obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
            obtain ⟨⟨idx, hlt, heq⟩, _⟩ := hsome_reg I' hsid_some
            exact ⟨idx, hlt, heq⟩
          · cases hrsv
        · cases hrsv
      · intro Tc σ' k' idx' hc
        rcases sid with _ | Ik
        · obtain ⟨_, hs4⟩ := hnone_reg rfl
          rw [hs4, hc_r] at hc; cases hc
        · obtain ⟨_, _, _, hc_reg, _⟩ := hsome_reg Ik rfl
          rw [hc_reg, hc_r] at hc; cases hc
      · refine Or.inr ⟨rfl, ?_⟩
        by_cases ht0 : mo.tStar = 0
        · refine Or.inl ⟨ht0, ?_, le_rfl⟩
          obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
          obtain ⟨_, _, hl2, _, _⟩ := hsome_reg I' hsid_some
          have : h.sessions.length ≤ ({} : LState T Sig K I).sessions.length + 1 := by
            rw [← hl_r]; exact hl2
          exact this
        · have htpos : 0 < mo.tStar := Nat.pos_of_ne_zero ht0
          have hsid_none : sid = none := hsid_r2 (Ne.symm ht0)
          obtain ⟨_, hs4⟩ := hnone_reg hsid_none
          have hlen0 : h.sessions.length = 0 := by
            rw [hs4, hl_r]; rfl
          exact Or.inr ⟨htpos, by rw [hlen0, Nat.zero_add]⟩
    exact runLoc_le_sum_runLocAt cka prng fs Δcka qep mo rfl (fun _ => by simp) (fun _ => by simp)
      A hq _ hS

/-! ### Coupling `redPRNGAuth` with `localAuth` -/

@[simp]
theorem simulateQ_pImpl_sampleT {α : Type} [SampleableType α] (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (pImpl prng) (sampleT α : Engine.TComp (PRFPRNG.spec Sig I K) α)).run sp =
      (($ᵗ α : ProbComp α) >>= fun a => pure (a, sp)) :=
  simulateQ_sampleT_run _ sp

@[simp]
theorem simulateQ_pImpl_run_lift_sampleT {HS α : Type} [SampleableType α] (s : HS)
    (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (pImpl prng)
      ((StateT.lift (sampleT α) : StateT HS (TComp (PRFPRNG.spec Sig I K)) α).run s)).run sp =
      (($ᵗ α : ProbComp α) >>= fun a => pure ((a, s), sp)) := by
  change (simulateQ (pImpl prng) (sampleT α >>= fun a => pure (a, s))).run sp = _
  simp [StateT.run_bind]

@[simp]
theorem simulateQ_pImpl_liftP {α : Type} (q : PRFPRNG.AdversaryComp Sig I K α)
    (s : PRNGState T Sig K) :
    simulateQ (pImpl prng) ((liftP q).run s) =
      (simulateQ (pImpl prng) q >>= fun a => pure (a, s)) := by
  change simulateQ (pImpl prng) (q >>= fun a => pure (a, s)) = _
  simp

@[simp]
theorem simulateQ_pImpl_processQuery (Ik : Option I) :
    simulateQ (pImpl prng) (PRFPRNG.processQuery (State := Sig) (Output := K) Ik) =
      PRFPRNG.processImpl prng Ik := by
  simp [PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl]

@[simp]
theorem simulateQ_pImpl_challPrngQuery (Ik : Option I) :
    simulateQ (pImpl prng) (PRFPRNG.challPrngQuery (State := Sig) (Output := K) Ik) =
      PRFPRNG.challPrngImpl prng Ik := by
  simp [PRFPRNG.challPrngQuery, pImpl, PRFPRNG.oracleImpl]

@[simp]
theorem simulateQ_pImpl_challPrfQuery (Ik : I) :
    simulateQ (pImpl prng) (PRFPRNG.challPrfQuery (State := Sig) (Output := K) Ik) =
      PRFPRNG.challPrfImpl prng Ik := by
  simp [PRFPRNG.challPrfQuery, pImpl, PRFPRNG.oracleImpl]

@[simp]
theorem simulateQ_pImpl_corrQuery :
    simulateQ (pImpl prng) (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) =
      PRFPRNG.corrImpl () := by
  simp [PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl]

@[simp]
theorem run_processImpl_some (Ik : I) (sp : PRFPRNG.GameState Sig I K) :
    (PRFPRNG.processImpl prng (some Ik)).run sp =
      if sp.prf then pure (none, sp)
      else pure (some (prng.up sp.σ Ik).2, { sp with σ := (prng.up sp.σ Ik).1 }) := by
  unfold PRFPRNG.processImpl PRFPRNG.samIfNec
  by_cases hprf : sp.prf = true
  · simp [hprf]
  · simp [hprf, StateT.run_monadLift]

@[simp]
theorem run_processImpl_none (sp : PRFPRNG.GameState Sig I K) :
    (PRFPRNG.processImpl prng (none : Option I)).run sp =
      if sp.prf then pure (none, sp)
      else (($ᵗ I : ProbComp I) >>= fun Ir =>
        pure (some (prng.up sp.σ Ir).2, { sp with σ := (prng.up sp.σ Ir).1, corr := false })) := by
  unfold PRFPRNG.processImpl PRFPRNG.samIfNec
  by_cases hprf : sp.prf = true
  · simp [hprf]
  · simp [hprf, StateT.run_monadLift]

@[simp]
theorem run_challPrngImpl_none (sp : PRFPRNG.GameState Sig I K) :
    (PRFPRNG.challPrngImpl prng (none : Option I)).run sp =
      (($ᵗ I : ProbComp I) >>= fun Ir =>
        if sp.prf then pure (none, sp)
        else if sp.b then
          (($ᵗ K : ProbComp K) >>= fun R' =>
            pure (some R', { sp with σ := (prng.up sp.σ Ir).1, corr := false, prng := true }))
        else
          pure (some (prng.up sp.σ Ir).2,
            { sp with σ := (prng.up sp.σ Ir).1, corr := false, prng := true })) := by
  rcases sp with ⟨σ, b, corr, prng_f, prf, table⟩
  cases prf <;> cases b <;>
    simp [PRFPRNG.challPrngImpl, PRFPRNG.samIfNec, StateT.run_monadLift]

@[simp]
theorem run_challPrfImpl (Ik : I) (sp : PRFPRNG.GameState Sig I K) :
    (PRFPRNG.challPrfImpl prng Ik).run sp =
      if sp.corr || sp.prng then pure (none, sp)
      else if sp.b then
        match sp.table.lookup Ik with
        | some R' => pure (some ((prng.up sp.σ Ik).1, R'), { sp with prf := true })
        | none =>
          (($ᵗ K : ProbComp K) >>= fun R' =>
            pure (some ((prng.up sp.σ Ik).1, R'),
              { sp with prf := true, table := (Ik, R') :: sp.table }))
      else pure (some (prng.up sp.σ Ik), { sp with prf := true }) := by
  rcases sp with ⟨σ, b, corr, prng_f, prf, table⟩
  cases corr <;> cases prng_f <;> cases b <;>
    simp [PRFPRNG.challPrfImpl, StateT.run_monadLift]
  cases hlk : table.lookup Ik <;> simp [StateT.run_monadLift]

@[simp]
theorem run_corrImpl (sp : PRFPRNG.GameState Sig I K) :
    (PRFPRNG.corrImpl (State := Sig) (Input := I) (Output := K) ()).run sp =
      if sp.prf then pure (none, sp)
      else pure (some sp.σ, { sp with corr := true }) := by
  unfold PRFPRNG.corrImpl
  by_cases hprf : sp.prf = true <;> simp [hprf]

def RelCache (cP : Option (T × Option Sig × K)) (cL : Option (T × Sig × K × Option ℕ)) : Prop :=
  (cP = none ∧ cL = none) ∨
  ∃ Tc σP σL k idx?,
    cP = some (Tc, σP, k) ∧ cL = some (Tc, σL, k, idx?) ∧ (∀ s, σP = some s → s = σL)

structure RelVP (e : ℕ) (P : Party) (vpP : VP Γ T (Option Sig) SS RS)
    (vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) : Prop where
  id_P : vpP.id = P
  tcur_P : vpP.tcur = e
  id_L : vpL.id = P
  tcur_L : vpL.tcur = e
  γ_eq : vpP.γ = vpL.γ
  Tcur_eq : vpP.curCkaMsg = vpL.curCkaMsg
  vS_eq : vpP.vS = vpL.vS.map Prod.fst
  vR_eq : ∀ t, vpP.vR t = (vpL.vR t).map Prod.fst
  root_eq : ∀ s, vpP.root = some s → s = vpL.root

def RootRel (t : ℕ) (hP : PRNGState T Sig K) (sp : PRFPRNG.GameState Sig I K)
    (hL : LState T Sig K I)
    (rP : (Option (Option Sig × K) × PRNGState T Sig K) × PRFPRNG.GameState Sig I K)
    (rL : (Sig × K × Option I) × LState T Sig K I) : Prop :=
  rP.1.1 = none ∨
  ∃ σP,
    rP.1.1 = some (σP, rL.1.2.1) ∧
    rP.1.2 = hP ∧
    rP.2.b = true ∧
    rP.2.table = rL.2.table ∧
    (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
    rL.2.cache = hL.cache ∧
    rL.2.sessions = hL.sessions ∧
    (∀ s, σP = some s → s = rL.1.1) ∧
    (t < mo.tStar → rP.2.σ = rL.1.1) ∧
    (t = mo.tStar → ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → rP.2.σ = sp.σ)

theorem leComp_rootPRNG_rootL {t : ℕ} {Ik : I} {σv : Option Sig} {σ : Sig}
    {hP : PRNGState T Sig K} {sp : PRFPRNG.GameState Sig I K} {hL : LState T Sig K I}
    (hb : sp.b = true) (htable : sp.table = hL.table)
    (hcorr : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true ∨ t < mo.tH)
    (hσ_gt : mo.tStar < t → ∀ s, σv = some s → s = σ)
    (hσ_le : t ≤ mo.tStar → sp.σ = σ) :
    LeComp (RootRel mo t hP sp hL)
      ((simulateQ (pImpl prng) ((rootPRNG prng mo t Ik σv).run hP)).run sp)
      (simulateQ lImpl ((rootL prng mo t Ik σ).run hL)) := by
  unfold rootPRNG rootL
  by_cases hgt : mo.tStar < t
  · simp only [hgt, ↓reduceIte]
    rcases σv with _ | σ_P
    · simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · have hσ_eq : σ_P = σ := hσ_gt hgt σ_P rfl
      subst σ_P
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨some (prng.up σ Ik).1, rfl, rfl, hb, htable,
        (fun h1 h2 => (hcorr h1 h2).resolve_right (by omega)), rfl, rfl,
        fun _ hs => Option.some.inj hs.symm, fun hlt => by omega, fun heq => by omega⟩)
  · simp only [hgt, ↓reduceIte]
    have hle : t ≤ mo.tStar := Nat.le_of_not_lt hgt
    have hsp_σ : sp.σ = σ := hσ_le hle
    by_cases heq : t = mo.tStar
    · simp only [heq, ↓reduceIte]
      by_cases hth : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · simp only [hth, ↓reduceIte, StateT.run_bind, simulateQ_bind, simulateQ_pImpl_challPrngQuery,
          simulateQ_pImpl_liftP, simulateQ_lImpl_run_lift_sampleT, run_challPrngImpl_none,
          bind_assoc, pure_bind]
        refine LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
        by_cases hprf : sp.prf = true
        · simp only [hprf, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [hprf, Bool.false_eq_true, ↓reduceIte, hb, bind_assoc, pure_bind,
            StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pImpl_liftP,
            simulateQ_pImpl_corrQuery, simulateQ_pure, run_corrImpl]
          refine LeComp.sample_bind ($ᵗ K) fun k _ => ?_
          simp only [pure_bind, hsp_σ]
          refine LeComp.pure (Or.inr ⟨some (prng.up σ Ir).1, rfl, rfl, rfl, htable,
            fun _ _ => rfl, rfl, rfl, fun _ hs => Option.some.inj hs.symm, fun hlt => by omega, ?_⟩)
          intro _ hnot
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hth
          exact False.elim (hnot hth)
      · simp only [hth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
          simulateQ_pImpl_liftP, simulateQ_pImpl_challPrfQuery, run_challPrfImpl, bind_assoc,
          pure_bind, lookupFL, StateT.run_get]
        by_cases hcp : (sp.corr || sp.prng) = true
        · simp only [hcp, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [hcp, Bool.false_eq_true, ↓reduceIte, hb, htable, hsp_σ]
          have hcorr_absurd : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true := by
            intro h1 h2; simp [h1, h2] at hth
          cases hlk : hL.table.lookup Ik with
          | some k =>
            simp only [hlk, StateT.run_pure, simulateQ_pure, pure_bind]
            exact LeComp.pure (Or.inr ⟨some (prng.up σ Ik).1, rfl, rfl, rfl, rfl,
              hcorr_absurd, rfl, rfl, fun _ hs => Option.some.inj hs.symm, fun hlt => by omega,
              fun _ _ => hsp_σ.symm⟩)
          | none =>
            simp only [hlk, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, bind_assoc]
            refine LeComp.sample_bind ($ᵗ K) fun k _ => ?_
            exact LeComp.pure (Or.inr ⟨some (prng.up σ Ik).1, rfl, rfl, rfl, rfl,
              hcorr_absurd, rfl, rfl, fun _ hs => Option.some.inj hs.symm, fun hlt => by omega,
              fun _ _ => hsp_σ.symm⟩)
    · simp only [heq, ↓reduceIte]
      have hlt : t < mo.tStar := Nat.lt_of_le_of_ne hle heq
      by_cases hth : (mo.tL.isSome && decide (t = mo.tH)) = true
      · simp only [hth, ↓reduceIte, StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftP,
          simulateQ_pImpl_processQuery, simulateQ_lImpl_run_lift_sampleT, run_processImpl_none,
          bind_assoc, pure_bind]
        by_cases hprf : sp.prf = true
        · simp only [hprf, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [hprf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            bind_assoc, pure_bind, hsp_σ]
          refine LeComp.sample_bind ($ᵗ I) fun Ir _ => ?_
          refine LeComp.pure (Or.inr ⟨none, rfl, rfl, hb, htable, ?_, rfl, rfl,
            (by rintro _ ⟨⟩), fun _ => rfl, fun heq' => False.elim (heq heq')⟩)
          intro _ hstar_th
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hth
          omega
      · simp only [hth, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt_h : (mo.tL.isSome && decide (t < mo.tH)) = true
        · simp only [hlt_h, ↓reduceIte, processCorr, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftP, simulateQ_pImpl_processQuery, run_processImpl_some,
            bind_assoc, pure_bind]
          by_cases hprf : sp.prf = true
          · simp only [hprf, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
            exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · simp only [hprf, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
              simulateQ_bind, simulateQ_pImpl_liftP, simulateQ_pImpl_corrQuery, simulateQ_pure,
              run_corrImpl, bind_assoc, pure_bind, hsp_σ]
            exact LeComp.pure (Or.inr ⟨some (prng.up σ Ik).1, rfl, rfl, hb, htable,
              fun _ _ => rfl, rfl, rfl, fun _ hs => Option.some.inj hs.symm, fun _ => rfl,
              fun heq' => False.elim (heq heq')⟩)
        · simp only [hlt_h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_pImpl_liftP, simulateQ_pImpl_processQuery, run_processImpl_some,
            bind_assoc, pure_bind]
          by_cases hprf : sp.prf = true
          · simp only [hprf, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
            exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
          · simp only [hprf, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              pure_bind, hsp_σ]
            refine LeComp.pure (Or.inr ⟨none, rfl, rfl, hb, htable, ?_, rfl, rfl,
              (by rintro _ ⟨⟩), fun _ => rfl, fun heq' => False.elim (heq heq')⟩)
            intro h1 h2
            rcases hcorr h1 h2 with hc | hlt_th
            · exact hc
            · simp [h1, hlt_th] at hlt_h

def VSendRel (e : ℕ) (P : Party)
    (vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (hP : PRNGState T Sig K) (sp : PRFPRNG.GameState Sig I K)
    (hL : LState T Sig K I)
    (rP : (Option (VP Γ T (Option Sig) SS RS × (Header T × E)) × PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × (Header T × E)) ×
      LState T Sig K I) : Prop :=
  let e' := if P.sendsIn (e + 1) then e + 1 else e
  rP.1.1 = none ∨
  ∃ vpP' vpL' c,
    rP.1.1 = some (vpP', c) ∧
    rL.1 = some (vpL', c) ∧
    c.1.1 = e' ∧
    RelVP e' P vpP' vpL' ∧
    (∀ t', RelCache (rP.1.2.cache t') (rL.2.cache t')) ∧
    rP.2.b = true ∧
    rP.2.table = rL.2.table ∧
    (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
    (P.sendsIn (e + 1) = true →
      (∀ t', t' ≠ e + 1 → rL.2.cache t' = hL.cache t') ∧
      (e + 1 < mo.tStar → rP.2.σ = vpL'.root ∧
        ∀ Tc σc k idx?, rL.2.cache (e + 1) = some (Tc, σc, k, idx?) → σc = rP.2.σ) ∧
      (e + 1 = mo.tStar → ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → rP.2.σ = sp.σ)) ∧
    (P.sendsIn (e + 1) = false →
      rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL ∧ vpL'.root = vpL.root)

theorem leComp_startSend_PRNG_local {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS}
    {vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)}
    {r_coins : Option CCoins}
    {hP : PRNGState T Sig K} {sp : PRFPRNG.GameState Sig I K} {hL : LState T Sig K I}
    (hvp : RelVP e P vpP vpL)
    (hcache : ∀ t', RelCache (hP.cache t') (hL.cache t'))
    (hb : sp.b = true) (htable : sp.table = hL.table)
    (hcorr : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true)
    (hσ_le : e + 1 ≤ mo.tStar → sp.σ = vpL.root) :
    LeComp (fun rP rL =>
        rP.1.1 = none ∨
        ∃ γ' T' σP σL k idx?,
          rP.1.1 = some (γ', T', σP, fs.initSender k) ∧
          rL.1 = some (γ', T', σL, (fs.initSender k, idx?)) ∧
          (∀ s, σP = some s → s = σL) ∧
          (∀ t', RelCache (rP.1.2.cache t') (rL.2.cache t')) ∧
          (∀ t', t' ≠ e + 1 → rL.2.cache t' = hL.cache t') ∧
          rP.2.b = true ∧
          rP.2.table = rL.2.table ∧
          (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
          (e + 1 < mo.tStar → rP.2.σ = σL ∧
            ∀ Tc σc k' idx', rL.2.cache (e + 1) = some (Tc, σc, k', idx') → σc = rP.2.σ) ∧
          (e + 1 = mo.tStar → ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → rP.2.σ = sp.σ))
      ((simulateQ (pImpl prng)
        (((hooksPRNG cka prng fs mo).startSend gP P (e + 1) vpP.γ vpP.root r_coins).run hP)).run sp)
      (simulateQ lImpl
        (((hooksLocal cka prng fs mo).startSend gL P (e + 1) vpL.γ vpL.root r_coins).run hL)) := by
  have hbody : ∀ (coins : CCoins),
      LeComp (fun rP rL =>
          rP.1.1 = none ∨
          ∃ γ' T' σP σL k idx?,
            rP.1.1 = some (γ', T', σP, fs.initSender k) ∧
            rL.1 = some (γ', T', σL, (fs.initSender k, idx?)) ∧
            (∀ s, σP = some s → s = σL) ∧
            (∀ t', RelCache (rP.1.2.cache t') (rL.2.cache t')) ∧
            (∀ t', t' ≠ e + 1 → rL.2.cache t' = hL.cache t') ∧
            rP.2.b = true ∧
            rP.2.table = rL.2.table ∧
            (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
            (e + 1 < mo.tStar → rP.2.σ = σL ∧
              ∀ Tc σc k' idx', rL.2.cache (e + 1) = some (Tc, σc, k', idx') → σc = rP.2.σ) ∧
            (e + 1 = mo.tStar → ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → rP.2.σ = sp.σ))
        ((simulateQ (pImpl prng)
          ((do
            let c := cka.send vpP.γ coins
            match ← rootPRNG prng mo (e + 1) c.2.2 vpP.root with
            | none => return none
            | some (σ', k) =>
              modify fun s : PRNGState T Sig K =>
                { s with cache := Function.update s.cache (e + 1) (some (c.2.1, σ', k)) }
              return some (c.1, c.2.1, σ', fs.initSender k)).run hP)).run sp)
        (simulateQ lImpl
          ((do
            let c := cka.send vpL.γ coins
            let (σ', k, sid) ← rootL prng mo (e + 1) c.2.2 vpL.root
            let idx? ← regSessOf sid
            modify fun s : LState T Sig K I =>
              { s with cache := Function.update s.cache (e + 1) (some (c.2.1, σ', k, idx?)) }
            return some (c.1, c.2.1, σ', (fs.initSender k, idx?))).run hL)) := by
    intro coins
    rw [hvp.γ_eq]
    simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
    refine (leComp_rootPRNG_rootL prng mo hb htable (fun h1 h2 => Or.inl (hcorr h1 h2))
      (fun _ => hvp.root_eq) hσ_le).bind ?_
    rintro ⟨⟨res_root, hP1⟩, sp1⟩ ⟨⟨σL, kL, sid⟩, hL1⟩ hroot
    rcases hroot with hnone | ⟨σP, hres_P, hhP1, hb1, htab1, hcorr1, hc1, hsess1, hσ_rel, hlt_σ, heq_σ⟩
    · dsimp only at hnone
      subst hnone
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hres_P hhP1
      subst hres_P hhP1
      simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
      have hreg_det : ∃ (idx? : Option ℕ) (hL2 : LState T Sig K I),
          simulateQ lImpl ((regSessOf (T := T) (Sig := Sig) (K := K) sid).run hL1) =
            pure (idx?, hL2) ∧ hL2.table = hL1.table ∧ hL2.cache = hL1.cache := by
        cases sid with
        | none =>
          exact ⟨none, hL1, rfl, rfl, rfl⟩
        | some Ik =>
          unfold regSessOf regSess
          simp only [StateT.run_map, StateT.run_bind, StateT.run_get, pure_bind]
          split
          · exact ⟨some (hL1.sessions.idxOf Ik), hL1, rfl, rfl, rfl⟩
          · exact ⟨some hL1.sessions.length, { hL1 with sessions := hL1.sessions ++ [Ik] },
              rfl, rfl, rfl⟩
      obtain ⟨idx?, hL2, hreg_eq, htab2, hc2⟩ := hreg_det
      rw [hreg_eq]
      simp only [pure_bind]
      refine LeComp.pure (Or.inr ⟨(cka.send vpL.γ coins).1, (cka.send vpL.γ coins).2.1,
        σP, σL, kL, idx?, rfl, rfl, hσ_rel, ?_, ?_, hb1, (by dsimp only; rw [htab1, ← htab2]),
        hcorr1, ?_, heq_σ⟩)
      · intro t'
        dsimp only
        by_cases ht' : t' = e + 1
        · subst ht'
          simp only [Function.update_self]
          exact Or.inr ⟨_, σP, σL, kL, idx?, rfl, rfl, hσ_rel⟩
        · rw [Function.update_of_ne ht', Function.update_of_ne ht', hc2, hc1]
          exact hcache t'
      · intro t' ht'
        dsimp only
        rw [Function.update_of_ne ht', hc2, hc1]
      · intro hlt
        refine ⟨hlt_σ hlt, ?_⟩
        intro Tc σc k' idx' hc_eq
        dsimp only at hc_eq
        rw [Function.update_self] at hc_eq
        injection hc_eq with hc_eq
        injection hc_eq with _ hc_eq
        injection hc_eq with hσc _
        rw [← hσc, hlt_σ hlt]
  cases r_coins with
  | some coins =>
    simp only [hooksPRNG, hooksLocal, pure_bind]
    exact hbody coins
  | none =>
    unfold hooksPRNG hooksLocal
    dsimp only
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, simulateQ_bind,
      simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT,
      bind_assoc, bind_assoc]
    refine LeComp.sample_bind ($ᵗ CCoins) fun coins _ => ?_
    simp only [pure_bind]
    exact hbody coins

theorem leComp_vSend_PRNG_local {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS}
    {vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)}
    {m : M} {r_coins : Option CCoins}
    {hP : PRNGState T Sig K} {sp : PRFPRNG.GameState Sig I K} {hL : LState T Sig K I}
    (hvp : RelVP e P vpP vpL)
    (hcache : ∀ t', RelCache (hP.cache t') (hL.cache t'))
    (hb : sp.b = true) (htable : sp.table = hL.table)
    (hcorr : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true)
    (hσ_le : P.sendsIn (e + 1) = true → e + 1 ≤ mo.tStar → sp.σ = vpL.root) :
    LeComp (VSendRel mo e P vpL hP sp hL)
      ((simulateQ (pImpl prng)
        ((vSend (hooksPRNG cka prng fs mo) gP P vpP m none r_coins).run hP)).run sp)
      (simulateQ lImpl
        ((vSend (hooksLocal cka prng fs mo) gL P vpL m none r_coins).run hL)) := by
  unfold vSend
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hsends : P.sendsIn (e + 1) = true
  · simp only [hsends, ↓reduceIte, StateT.run_bind, simulateQ_bind, bind_assoc]
    refine (leComp_startSend_PRNG_local cka prng fs mo hvp hcache hb htable hcorr
      (hσ_le hsends)).bind ?_
    rintro ⟨⟨res_ssP, hP1⟩, sp1⟩ ⟨res_ssL, hL1⟩ hss
    rcases hss with hnone | ⟨γ', T', σP, σL, k, idx?, hP_eq, hL_eq, hσ_rel, hc_rel, hc_other,
      hb1, htab1, hcorr1, hlt_σ, heq_σ⟩
    · dsimp only at hnone
      subst hnone
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_eq hL_eq
      subst hP_eq hL_eq
      simp only [hooksPRNG, hooksLocal, pure_bind, StateT.run_pure, simulateQ_pure]
      refine LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hsends]), ?_, hc_rel, hb1, htab1,
        hcorr1, ?_, (fun hns => by rw [hsends] at hns; cases hns)⟩)
      · simp only [hsends, ↓reduceIte]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvp.vR_eq, hσ_rel⟩
      · intro _
        exact ⟨hc_other, hlt_σ, heq_σ⟩
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte, pure_bind]
    have hns : P.sendsIn (e + 1) = false := Bool.eq_false_iff.mpr hsends
    have hvS := hvp.vS_eq
    rcases hvSL : vpL.vS with _ | ⟨ss, idx?⟩
    · rw [hvSL] at hvS
      simp only [Option.map_none] at hvS
      simp only [hvS, hvSL, hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq,
        StateT.run_pure, simulateQ_pure]
      refine LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hcache, hb, htable,
        hcorr, (fun hs => by rw [hns] at hs; cases hs), (fun _ => ⟨rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact hvp
    · rw [hvSL] at hvS
      simp only [Option.map_some] at hvS
      simp only [hvS, hvSL, hooksPRNG, hooksLocal, hvp.tcur_P, hvp.tcur_L, hvp.Tcur_eq,
        pure_bind, StateT.run_pure, simulateQ_pure]
      refine LeComp.pure (Or.inr ⟨_, _, _, rfl, rfl, (by simp [hns]), ?_, hcache, hb, htable,
        hcorr, (fun hs => by rw [hns] at hs; cases hs), (fun _ => ⟨rfl, rfl, rfl, rfl⟩)⟩)
      simp only [hns, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hvp.id_P, rfl, hvp.id_L, rfl, hvp.γ_eq, rfl, rfl, hvp.vR_eq, hvp.root_eq⟩

theorem leComp_startRecv_PRNG_local {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS}
    {vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)}
    {Tn : T}
    {hP : PRNGState T Sig K} {sp : PRFPRNG.GameState Sig I K} {hL : LState T Sig K I}
    (hvp : RelVP e P vpP vpL)
    (hcache : ∀ t', RelCache (hP.cache t') (hL.cache t'))
    (hb : sp.b = true) (htable : sp.table = hL.table)
    (hcorr : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true)
    (hσ_tStar : e + 1 = mo.tStar → ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) →
      sp.σ = vpL.root) :
    LeComp (fun rP rL =>
        rP.1.1 = none ∨
        (rP.1.1 = some none ∧ rL.1 = some none ∧
          rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
        ∃ γ' σP σL k idx?,
          rP.1.1 = some (some (γ', σP, fs.initReceiver k)) ∧
          rL.1 = some (some (γ', σL, (fs.initReceiver k, idx?))) ∧
          (∀ s, σP = some s → s = σL) ∧
          rP.1.2 = hP ∧
          rL.2.cache = hL.cache ∧
          rP.2.b = true ∧
          rP.2.table = rL.2.table ∧
          (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
          rP.2.σ = sp.σ ∧
          (e + 1 ≠ mo.tStar → ∃ Tc, hL.cache (e + 1) = some (Tc, σL, k, idx?)))
      ((simulateQ (pImpl prng)
        (((hooksPRNG cka prng fs mo).startRecv gP P (e + 1) vpP.γ vpP.root Tn).run hP)).run sp)
      (simulateQ lImpl
        (((hooksLocal cka prng fs mo).startRecv gL P (e + 1) vpL.γ vpL.root Tn).run hL)) := by
  unfold hooksPRNG hooksLocal
  dsimp only
  rw [hvp.γ_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hforged :
      LeComp (fun rP rL =>
          rP.1.1 = none ∨
          (rP.1.1 = some none ∧ rL.1 = some none ∧
            rP.1.2 = hP ∧ rP.2 = sp ∧ rL.2 = hL) ∨
          ∃ γ' σP σL k idx?,
            rP.1.1 = some (some (γ', σP, fs.initReceiver k)) ∧
            rL.1 = some (some (γ', σL, (fs.initReceiver k, idx?))) ∧
            (∀ s, σP = some s → s = σL) ∧
            rP.1.2 = hP ∧
            rL.2.cache = hL.cache ∧
            rP.2.b = true ∧
            rP.2.table = rL.2.table ∧
            (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
            rP.2.σ = sp.σ ∧
            e + 1 = mo.tStar)
        ((simulateQ (pImpl prng)
          ((if mo.auth && decide (e + 1 = mo.tStar) then do
              match ← liftP (PRFPRNG.challPrfQuery (cka.receive vpL.γ Tn).2) with
              | none => return none
              | some (σ', k') =>
                return some (some ((cka.receive vpL.γ Tn).1, some σ', fs.initReceiver k'))
            else return some none : HM (PRFPRNG.spec Sig I K) (PRNGState T Sig K) _).run hP)).run sp)
        (simulateQ lImpl
          ((if mo.auth && decide (e + 1 = mo.tStar) then do
              if mo.tL.isSome && decide (mo.tStar = mo.tH) then return none
              let k' ← lookupFL (cka.receive vpL.γ Tn).2
              let idx ← regSess (cka.receive vpL.γ Tn).2
              return some (some ((cka.receive vpL.γ Tn).1,
                (prng.up vpL.root (cka.receive vpL.γ Tn).2).1, (fs.initReceiver k', some idx)))
            else return some none : HM nilSpec (LState T Sig K I) _).run hL)) := by
    by_cases hauth_t : (mo.auth && decide (e + 1 = mo.tStar)) = true
    · simp only [hauth_t, ↓reduceIte, StateT.run_bind, simulateQ_bind, simulateQ_pImpl_liftP,
        simulateQ_pImpl_challPrfQuery, run_challPrfImpl, bind_assoc, pure_bind]
      have ht_eq : e + 1 = mo.tStar := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hauth_t
        exact hauth_t.2
      by_cases hth : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
      · have hsp_corr : sp.corr = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hth
          exact hcorr hth.1 hth.2
        simp only [hth, hsp_corr, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
          pure_bind]
        exact LeComp.pure (Or.inl rfl)
      · simp only [hth, Bool.false_eq_true, ↓reduceIte]
        have hnot_th : ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
          intro h; simp [h.1, h.2] at hth
        have hsp_σ : sp.σ = vpL.root := hσ_tStar ht_eq hnot_th
        by_cases hcp : (sp.corr || sp.prng) = true
        · simp only [hcp, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · simp only [hcp, Bool.false_eq_true, ↓reduceIte, hb, htable, hsp_σ, lookupFL,
            StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind, bind_assoc]
          have hreg_det : ∀ hL1 : LState T Sig K I, ∃ (idx : ℕ) (hL2 : LState T Sig K I),
              simulateQ lImpl
                ((regSess (T := T) (Sig := Sig) (K := K) (cka.receive vpL.γ Tn).2).run hL1) =
                pure (idx, hL2) ∧ hL2.table = hL1.table ∧ hL2.cache = hL1.cache := by
            intro hL1
            unfold regSess
            simp only [StateT.run_bind, StateT.run_get, pure_bind]
            split
            · exact ⟨hL1.sessions.idxOf (cka.receive vpL.γ Tn).2, hL1, rfl, rfl, rfl⟩
            · exact ⟨hL1.sessions.length,
                { hL1 with sessions := hL1.sessions ++ [(cka.receive vpL.γ Tn).2] },
                rfl, rfl, rfl⟩
          cases hlk : hL.table.lookup (cka.receive vpL.γ Tn).2 with
          | some k' =>
            obtain ⟨idx, hL2, hreg_eq, htab2, hc2⟩ := hreg_det hL
            simp only [hlk, StateT.run_pure, simulateQ_pure, pure_bind, hreg_eq]
            refine LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ Tn).1,
              some (prng.up vpL.root (cka.receive vpL.γ Tn).2).1,
              (prng.up vpL.root (cka.receive vpL.γ Tn).2).1, k', some idx,
              rfl, rfl, fun _ hs => Option.some.inj hs.symm, rfl, hc2, rfl, htab2.symm,
              hcorr, rfl, ht_eq⟩))
          | none =>
            simp only [hlk, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_bind, simulateQ_lImpl_run_lift_sampleT, simulateQ_pure, bind_assoc]
            refine LeComp.sample_bind ($ᵗ K) fun k' _ => ?_
            obtain ⟨idx, hL2, hreg_eq, htab2, hc2⟩ :=
              hreg_det { hL with table := ((cka.receive vpL.γ Tn).2, k') :: hL.table }
            simp only [pure_bind, hreg_eq]
            refine LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ Tn).1,
              some (prng.up vpL.root (cka.receive vpL.γ Tn).2).1,
              (prng.up vpL.root (cka.receive vpL.γ Tn).2).1, k', some idx,
              rfl, rfl, fun _ hs => Option.some.inj hs.symm, rfl, hc2, rfl, htab2.symm,
              hcorr, rfl, ht_eq⟩))
    · simp only [hauth_t, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩))
  rcases hcache (e + 1) with ⟨hcP, hcL⟩ | ⟨Tc, σP, σL, k, idx?, hcP, hcL, hσ_rel⟩
  · simp only [hcP, hcL]
    intro F₁ F₂ hF
    refine hforged F₁ F₂ fun rP rL h => hF rP rL ?_
    rcases h with h1 | h2 | ⟨γ', σP, σL, k, idx?, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨γ', σP, σL, k, idx?, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        fun hne => False.elim (hne h10)⟩)
  · simp only [hcP, hcL]
    by_cases hTc : Tc = Tn
    · subst hTc
      simp only [↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨(cka.receive vpL.γ Tc).1, σP, σL, k, idx?,
        rfl, rfl, hσ_rel, rfl, rfl, hb, htable, hcorr, rfl, fun _ => ⟨Tc, rfl⟩⟩))
    · simp only [hTc, ↓reduceIte]
      intro F₁ F₂ hF
      refine hforged F₁ F₂ fun rP rL h => hF rP rL ?_
      rcases h with h1 | h2 | ⟨γ', σP', σL', k', idx', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨γ', σP', σL', k', idx', h1, h2, h3, h4, h5, h6, h7, h8, h9,
          fun hne => False.elim (hne h10)⟩)

def VRecvRel (e : ℕ) (P : Party) (c : Header T × E)
    (vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (hP : PRNGState T Sig K) (sp : PRFPRNG.GameState Sig I K)
    (hL : LState T Sig K I)
    (rP : (Option (Option (VP Γ T (Option Sig) SS RS × ℕ × ℕ × M)) × PRNGState T Sig K) ×
      PRFPRNG.GameState Sig I K)
    (rL : Option (Option (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ) × ℕ × ℕ × M)) ×
      LState T Sig K I) : Prop :=
  let t := c.1.1
  rP.1.1 = none ∨
  (rP.1.1 = some none ∧ rL.1 = some none ∧
    rP.1.2 = hP ∧ rL.2.cache = hL.cache ∧
    rP.2.b = true ∧ rP.2.table = rL.2.table ∧
    (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
    rP.2.σ = sp.σ) ∨
  ∃ vpP' vpL' i' m',
    rP.1.1 = some (some (vpP', t, i', m')) ∧
    rL.1 = some (some (vpL', t, i', m')) ∧
    t ≤ e + 1 ∧
    P.sendsIn t = false ∧
    RelVP (max e t) P vpP' vpL' ∧
    rP.1.2 = hP ∧
    rL.2.cache = hL.cache ∧
    rP.2.b = true ∧
    rP.2.table = rL.2.table ∧
    (mo.tL.isSome = true → mo.tStar = mo.tH → rP.2.corr = true) ∧
    rP.2.σ = sp.σ ∧
    (t ≤ e → vpL'.root = vpL.root) ∧
    (t = e + 1 → t ≠ mo.tStar →
      ∃ Tc k idx?, hL.cache (e + 1) = some (Tc, vpL'.root, k, idx?))

theorem leComp_vRecv_PRNG_local {e : ℕ} {P : Party}
    {gP : SM.GameState (VP Γ T (Option Sig) SS RS) M (Header T × E)}
    {gL : SM.GameState (VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) M (Header T × E)}
    {vpP : VP Γ T (Option Sig) SS RS}
    {vpL : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)}
    {c : Header T × E} {rec : Option (SM.Record M (Header T × E))}
    {hP : PRNGState T Sig K} {sp : PRFPRNG.GameState Sig I K} {hL : LState T Sig K I}
    (hvp : RelVP e P vpP vpL)
    (hcache : ∀ t', RelCache (hP.cache t') (hL.cache t'))
    (hb : sp.b = true) (htable : sp.table = hL.table)
    (hcorr : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true)
    (hσ_tStar : P.sendsIn (e + 1) = false → e + 1 = mo.tStar →
      ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → sp.σ = vpL.root) :
    LeComp (VRecvRel mo e P c vpL hP sp hL)
      ((simulateQ (pImpl prng)
        ((vRecv (hooksPRNG cka prng fs mo) gP P vpP c rec).run hP)).run sp)
      (simulateQ lImpl
        ((vRecv (hooksLocal cka prng fs mo) gL P vpL c rec).run hL)) := by
  unfold vRecv
  dsimp only
  rw [hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L]
  by_cases hguard : (P.sendsIn c.1.1 || decide (e + 1 < c.1.1)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hb, htable, hcorr, rfl⟩))
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hguard
    have hns : P.sendsIn c.1.1 = false := Bool.eq_false_iff.mpr hguard.1
    have htle : c.1.1 ≤ e + 1 := Nat.le_of_not_lt hguard.2
    by_cases hnew : c.1.1 = e + 1
    · simp only [hnew, ↓reduceIte]
      have hmax : max e (e + 1) = e + 1 := Nat.max_eq_right (Nat.le_succ e)
      cases hTn : c.1.2 with
      | none =>
        simp only [pure_bind, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hb, htable, hcorr, rfl⟩))
      | some Tn =>
        simp only [StateT.run_bind, simulateQ_bind, bind_assoc]
        have hns_e1 : P.sendsIn (e + 1) = false := hnew ▸ hns
        refine (leComp_startRecv_PRNG_local cka prng fs mo hvp hcache hb htable hcorr
          (hσ_tStar hns_e1)).bind ?_
        rintro ⟨⟨res_srP, hP1⟩, sp1⟩ ⟨res_srL, hL1⟩ hsr
        rcases hsr with hnone | ⟨hP_none, hL_none, rfl, rfl, rfl⟩ |
          ⟨γ', σP, σL, k, idx?, hP_some, hL_some, hσ_rel, hhP1, hc1, hb1, htab1, hcorr1,
            hσ1, hcache_ne⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_none hL_none; subst hP_none hL_none
          simp only [pure_bind, StateT.run_pure, simulateQ_pure]
          exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hb, htable, hcorr, rfl⟩))
        · dsimp only at hP_some hL_some hhP1; subst hP_some hL_some hhP1
          simp only [pure_bind, Function.update_self, hooksPRNG, hooksLocal]
          cases hfs : fs.receive (fs.initReceiver k) c.1 c.2 with
          | none =>
            simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, hc1, hb1, htab1, hcorr1, hσ1⟩))
          | some out =>
            rcases out with ⟨rs', i', m'⟩
            simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure]
            refine LeComp.pure ?_
            dsimp only [VRecvRel]
            rw [hnew, hmax]
            refine Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, le_rfl, hns_e1, ?_,
              rfl, hc1, hb1, htab1, hcorr1, hσ1, fun hle_e => by omega, ?_⟩)
            · refine ⟨rfl, rfl, rfl, rfl, rfl, hvp.Tcur_eq, hvp.vS_eq, ?_, hσ_rel⟩
              intro t'
              dsimp only
              rw [Function.update_idem, Function.update_idem]
              by_cases ht' : t' = e + 1
              · subst ht'; simp only [Function.update_self, Option.map_some]
              · simp only [Function.update_of_ne ht', hvp.vR_eq t']
            · intro _ hne_tStar
              obtain ⟨Tc, hc_eq⟩ := hcache_ne hne_tStar
              exact ⟨Tc, k, idx?, hc_eq⟩
    · simp only [hnew, ↓reduceIte, pure_bind]
      have htle_e : c.1.1 ≤ e := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
      have hmax : max e c.1.1 = e := Nat.max_eq_left htle_e
      have hvR := hvp.vR_eq c.1.1
      rcases hvRL : vpL.vR c.1.1 with _ | ⟨rs, idx?⟩
      · rw [hvRL] at hvR
        simp only [Option.map_none] at hvR
        simp only [hvR, hvRL, StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hb, htable, hcorr, rfl⟩))
      · rw [hvRL] at hvR
        simp only [Option.map_some] at hvR
        simp only [hvR, hvRL, hooksPRNG, hooksLocal]
        cases hfs : fs.receive rs c.1 c.2 with
        | none =>
          simp only [hfs, pure_bind, StateT.run_pure, simulateQ_pure]
          exact LeComp.pure (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hb, htable, hcorr, rfl⟩))
        | some out =>
          rcases out with ⟨rs', i', m'⟩
          simp only [hfs, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure]
          refine LeComp.pure (Or.inr (Or.inr ⟨_, _, i', m', rfl, rfl, htle, hns, ?_,
            rfl, rfl, hb, htable, hcorr, rfl, fun _ => rfl, fun heq => False.elim (hnew heq)⟩))
          rw [hmax]
          refine ⟨hvp.id_P, hvp.tcur_P, hvp.id_L, hvp.tcur_L, hvp.γ_eq, hvp.Tcur_eq, hvp.vS_eq,
            ?_, hvp.root_eq⟩
          intro t'
          dsimp only
          by_cases ht' : t' = c.1.1
          · subst ht'; simp only [Function.update_self, Option.map_some]
          · simp only [Function.update_of_ne ht', hvp.vR_eq t']

/-- Synchronized invariant between `redPRNGAuth` (at `b = true`) and `hooksLocal`. -/
structure SyncPL (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K)
    (esL : EStateL Γ T Sig SS RS M E K I) : Prop where
  abort_eq : esP.abort = esL.abort
  g_eq : eraseSt esP.g = eraseSt esL.g
  vp_rel : ∀ P, RelVP (esL.g.epoch P) P (esP.g.st P) (esL.g.st P)
  cache_rel : ∀ t', RelCache (esP.h.cache t') (esL.h.cache t')
  sp_b : sp.b = true
  table_eq : sp.table = esL.h.table
  corr_tH : mo.tL.isSome = true → mo.tStar = mo.tH → sp.corr = true
  comp_inv : ∀ pos ∈ esL.g.comp, SM.healedBy esL.g.tL (2 + Δcka) pos.epoch = false
  trans_epoch : ∀ r ∈ esL.g.trans,
    r.pos.epoch ≤ esL.g.epoch r.pos.sender ∧ r.ct.1.1 = r.pos.epoch
  epoch_le : ∀ P, esL.g.epoch P ≤ esL.g.epoch P.other + 1
  epoch_sends : ∀ P, esL.g.epoch P.other < esL.g.epoch P → P.sendsIn (esL.g.epoch P) = true
  root_max : ∀ P, esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) →
    esL.g.epoch P < mo.tStar → (esL.g.st P).root = sp.σ
  root_pred : 0 < mo.tStar → ∀ P, esL.g.epoch P = mo.tStar - 1 →
    ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → (esL.g.st P).root = sp.σ
  cache_max : ∀ Tc σc k idx?,
    esL.h.cache (max (esL.g.epoch .A) (esL.g.epoch .B)) = some (Tc, σc, k, idx?) →
    max (esL.g.epoch .A) (esL.g.epoch .B) < mo.tStar → σc = sp.σ

def StepRel {α : Type}
    (rP : (α × EStateP Γ T Sig SS RS M E K) × PRFPRNG.GameState Sig I K)
    (rL : α × EStateL Γ T Sig SS RS M E K I) : Prop :=
  rP.1.2.abort = true ∨ (rP.1.1 = rL.1 ∧ SyncPL Δcka mo rP.1.2 rP.2 rL.2)

theorem max_epoch_eq_of_eq {ep : Party → ℕ} {P : Party} (h : ep P = ep P.other) :
    max (ep .A) (ep .B) = ep P := by
  cases P <;> simp [Party.other] at h ⊢ <;> omega

theorem max_epoch_update_succ {ep : Party → ℕ} {P : Party} (h : ep P = ep P.other) :
    max (Function.update ep P (ep P + 1) .A) (Function.update ep P (ep P + 1) .B) = ep P + 1 := by
  cases P <;> simp [Party.other] at h ⊢ <;> omega

theorem max_epoch_accept_succ {ep : Party → ℕ} {P : Party} (hle : ep P.other ≤ ep P + 1)
    (hge : ep P + 1 ≤ ep P.other) :
    max (Function.update ep P (max (ep P) (ep P + 1)) .A)
      (Function.update ep P (max (ep P) (ep P + 1)) .B) = ep P + 1 := by
  have heq : ep P.other = ep P + 1 := by omega
  cases P <;> simp [Party.other] at heq ⊢ <;> omega

theorem epoch_eq_other_of_sendsIn_succ {ep : Party → ℕ} {P : Party}
    (hle : ∀ Q, ep Q ≤ ep Q.other + 1)
    (hsends_inv : ∀ Q, ep Q.other < ep Q → Q.sendsIn (ep Q) = true)
    (hsends : P.sendsIn (ep P + 1) = true) :
    ep P = ep P.other := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have heq : ep P.other = ep P + 1 := by
      have := hle P.other
      rw [Party.other_other] at this
      omega
    have hs_other := hsends_inv P.other (by rw [Party.other_other]; exact hlt)
    rw [heq, sendsIn_other, hsends] at hs_other
    cases hs_other
  · have hs_P := hsends_inv P hgt
    have := sendsIn_succ_false hs_P
    rw [hsends] at this
    cases this

theorem epMgmt_sync {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g₁ : SM.GameState St₁ Msg C}
    {g₂ : SM.GameState St₂ Msg C} (h : eraseSt g₁ = eraseSt g₂) (Δ qep : ℕ) (P : Party)
    (bad : Bool) :
    (g₁.epMgmt Δ qep P bad = none ∧ g₂.epMgmt Δ qep P bad = none) ∨
    ∃ s₁ s₂,
      g₁.epMgmt Δ qep P bad = some s₁ ∧
      g₂.epMgmt Δ qep P bad = some s₂ ∧
      eraseSt s₁ = eraseSt s₂ ∧
      s₁.st = g₁.st ∧
      s₂.st = g₂.st ∧
      s₂.trans = g₂.trans ∧
      s₂.epoch = (if P.sendsIn (g₂.epoch P + 1) then
        Function.update g₂.epoch P (g₂.epoch P + 1) else g₂.epoch) ∧
      ((∀ pos ∈ g₂.comp, SM.healedBy g₂.tL Δ pos.epoch = false) →
        ∀ pos ∈ s₂.comp, SM.healedBy s₂.tL Δ pos.epoch = false) := by
  unfold SM.GameState.epMgmt
  rw [eraseSt_epoch h, eraseSt_safeCh h]
  by_cases hsends : P.sendsIn (g₂.epoch P + 1) = true
  · simp only [hsends, ↓reduceIte]
    by_cases hqep : qep < g₂.epoch P + 1
    · simp [hqep]
    · simp only [hqep, ↓reduceIte]
      refine Or.inr ⟨_, _, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · split <;> simp [eraseSt, SM.GameState.leak, eraseSt_epoch h, eraseSt_idx h,
          eraseSt_tL h, eraseSt_trans h, eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h,
          eraseSt_b h, eraseSt_win h, eraseSt_leaks h, eraseSt_corrs h]
      · split <;> rfl
      · split <;> rfl
      · split <;> rfl
      · split <;> rfl
      · intro hcomp pos hpos
        dsimp only at hpos ⊢
        by_cases hc : (bad && !g₂.safeCh Δ P) = true <;>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
        · exact healedBy_leak_false _ _ _ _ (hcomp pos hpos)
        · exact hcomp pos hpos
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
    by_cases hqep : qep < g₂.epoch P
    · simp [hqep]
    · simp only [hqep, ↓reduceIte]
      exact Or.inr ⟨g₁, g₂, rfl, rfl, h, rfl, rfl, rfl, rfl, id⟩

theorem leComp_transmitE_PRNG_local (_hauth : mo.auth = true)
    (arg : Party × M × Option CCoins)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((transmitE (hooksPRNG cka prng fs mo) (2 + Δcka) qep mo.policy arg).run esP)).run sp)
      (simulateQ lImpl
        ((transmitE (hooksLocal cka prng fs mo) (2 + Δcka) qep mo.policy arg).run esL)) := by
  rcases arg with ⟨P, m, r_coins⟩
  unfold transmitE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq]
  by_cases habw : (esL.abort || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁P, s₁L, h1, h2, hs₁_er, hs₁P_st, hs₁L_st, hs₁_trans, hs₁_ep_fn, hs₁_comp_imp⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · simp only [h1, h2]
      rw [eraseSt_leakDoom hsync.g_eq hs₁_er mo.policy]
      by_cases hdoom : mo.policy.leakDoom esL.g s₁L = true
      · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        exact LeComp.pure (Or.inl rfl)
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, hs₁P_st, hs₁L_st,
          StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
        have hheq : P.sendsIn (esL.g.epoch P + 1) = true →
            esL.g.epoch P = esL.g.epoch P.other :=
          epoch_eq_other_of_sendsIn_succ hsync.epoch_le hsync.epoch_sends
        have hσ_le : P.sendsIn (esL.g.epoch P + 1) = true → esL.g.epoch P + 1 ≤ mo.tStar →
            sp.σ = (esL.g.st P).root := by
          intro hsends hle
          have hmax : esL.g.epoch P = max (esL.g.epoch .A) (esL.g.epoch .B) :=
            (max_epoch_eq_of_eq (hheq hsends)).symm
          exact (hsync.root_max P hmax (by omega)).symm
        refine (leComp_vSend_PRNG_local cka prng fs mo (hsync.vp_rel P) hsync.cache_rel
          hsync.sp_b hsync.table_eq hsync.corr_tH hσ_le).bind ?_
        rintro ⟨⟨res_vsP, hP1⟩, sp1⟩ ⟨res_vsL, hL1⟩ hvs
        rcases hvs with hnone | ⟨vpP', vpL', c, hP_eq, hL_eq, hc_ep, hvp', hc_rel, hb1,
          htab1, hcorr1, hsends_props, hns_props⟩
        · dsimp only at hnone; subst hnone
          simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            simulateQ_pure]
          exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
        · dsimp only at hP_eq hL_eq; subst hP_eq hL_eq
          simp only [pure_bind, StateT.run_modify, StateT.run_pure, simulateQ_pure]
          refine LeComp.pure ?_
          have hs₁_ep : s₁L.epoch P = if P.sendsIn (esL.g.epoch P + 1) then esL.g.epoch P + 1
              else esL.g.epoch P := by
            rw [hs₁_ep_fn]; split <;> simp
          have hs₁_ep_other : ∀ Q, Q ≠ P → s₁L.epoch Q = esL.g.epoch Q := by
            intro Q hQ; rw [hs₁_ep_fn]; split <;> simp [Function.update_of_ne hQ]
          have hs₁_comp := hs₁_comp_imp hsync.comp_inv
          refine Or.inr ⟨rfl, ⟨hsync.abort_eq, ?_, ?_, hc_rel, hb1, htab1, hcorr1, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_⟩⟩
          · rw [eraseSt_epoch hs₁_er, eraseSt_idx hs₁_er]
            exact eraseSt_record hs₁_er (2 + Δcka) P vpP' vpL' _ false
          · intro Q
            dsimp only [SM.GameState.record]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hs₁_ep]
              exact hvp'
            · simp only [Function.update_of_ne hQ, hs₁_ep_other Q hQ, hs₁P_st, hs₁L_st]
              exact hsync.vp_rel Q
          · exact comp_inv_record s₁L (2 + Δcka) P vpL' _ false rfl hs₁_comp
          · intro r hr
            dsimp only [SM.GameState.record] at hr ⊢
            rcases List.mem_cons.mp hr with rfl | hr'
            · refine ⟨le_rfl, ?_⟩
              dsimp only
              rw [hc_ep, hs₁_ep]
            · obtain ⟨h1, h2⟩ := hsync.trans_epoch r (hs₁_trans ▸ hr')
              refine ⟨?_, h2⟩
              by_cases hQ : r.pos.sender = P
              · rw [hQ, hs₁_ep]
                rw [hQ] at h1
                split <;> omega
              · rw [hs₁_ep_other _ hQ]
                exact h1
          · intro Q
            dsimp only [SM.GameState.record]
            rw [hs₁_ep_fn]
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte]
              cases Q <;> cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
            · simp only [hsends, Bool.false_eq_true, ↓reduceIte]
              exact hsync.epoch_le Q
          · intro Q hlt_Q
            dsimp only [SM.GameState.record] at hlt_Q ⊢
            rw [hs₁_ep_fn] at hlt_Q ⊢
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hlt_Q ⊢
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self]
                exact hsends
              · cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hlt_Q <;> omega
            · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at hlt_Q ⊢
              exact hsync.epoch_sends Q hlt_Q
          · intro Q hQ_max hQ_lt
            dsimp only [SM.GameState.record] at hQ_max hQ_lt ⊢
            rw [hs₁_ep_fn] at hQ_max hQ_lt
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hQ_max hQ_lt
              rw [max_epoch_update_succ heq_other] at hQ_max
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self] at hQ_lt ⊢
                exact ((hsends_props hsends).2.1 hQ_lt).1.symm
              · rw [Function.update_of_ne hQ] at hQ_max
                cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hQ_max <;> omega
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, hsp_eq, _, hroot_eq⟩ := hns_props hns
              dsimp only at hsp_eq
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hQ_max hQ_lt
              rw [hsp_eq]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hroot_eq]
                exact hsync.root_max P hQ_max hQ_lt
              · simp only [Function.update_of_ne hQ, hs₁L_st]
                exact hsync.root_max Q hQ_max hQ_lt
          · intro hpos Q hQ_pred hnot_th
            dsimp only [SM.GameState.record] at hQ_pred ⊢
            rw [hs₁_ep_fn] at hQ_pred
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hQ_pred
              by_cases hQ : Q = P
              · subst Q
                rw [Function.update_self] at hQ_pred ⊢
                have hlt : esL.g.epoch P + 1 < mo.tStar := by omega
                exact ((hsends_props hsends).2.1 hlt).1.symm
              · rw [Function.update_of_ne hQ] at hQ_pred ⊢
                rw [hs₁L_st]
                have hQ_eq_P : esL.g.epoch P = mo.tStar - 1 := by
                  cases Q <;> cases P <;> simp [Party.other] at hQ heq_other hQ_pred <;> omega
                have he1_eq : esL.g.epoch P + 1 = mo.tStar := by omega
                have hsp1_eq : sp1.σ = sp.σ := (hsends_props hsends).2.2 he1_eq hnot_th
                rw [hsp1_eq]
                exact hsync.root_pred hpos Q hQ_pred hnot_th
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, hsp_eq, _, hroot_eq⟩ := hns_props hns
              dsimp only at hsp_eq
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hQ_pred
              rw [hsp_eq]
              by_cases hQ : Q = P
              · subst Q
                simp only [Function.update_self, hroot_eq]
                exact hsync.root_pred hpos P hQ_pred hnot_th
              · simp only [Function.update_of_ne hQ, hs₁L_st]
                exact hsync.root_pred hpos Q hQ_pred hnot_th
          · intro Tc σc k idx? hc_max hmax_lt
            dsimp only [SM.GameState.record] at hc_max hmax_lt
            rw [hs₁_ep_fn] at hc_max hmax_lt
            by_cases hsends : P.sendsIn (esL.g.epoch P + 1) = true
            · have heq_other := hheq hsends
              simp only [hsends, ↓reduceIte] at hc_max hmax_lt
              rw [max_epoch_update_succ heq_other] at hc_max hmax_lt
              exact ((hsends_props hsends).2.1 hmax_lt).2 Tc σc k idx? hc_max
            · have hns : P.sendsIn (esL.g.epoch P + 1) = false := Bool.eq_false_iff.mpr hsends
              obtain ⟨_, hsp_eq, hhL_eq, _⟩ := hns_props hns
              dsimp only at hsp_eq hhL_eq
              simp only [hns, Bool.false_eq_true, ↓reduceIte] at hc_max hmax_lt
              rw [hhL_eq] at hc_max
              dsimp only
              rw [hsp_eq]
              exact hsync.cache_max Tc σc k idx? hc_max hmax_lt

theorem leComp_challE_PRNG_local (hauth : mo.auth = true)
    (arg : Party × M × M × Option CCoins)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((challE (hooksPRNG cka prng fs mo) (2 + Δcka) qep mo.cfg mo.policy arg).run esP)).run sp)
      (simulateQ lImpl
        ((challE (hooksLocal cka prng fs mo) (2 + Δcka) qep mo.cfg mo.policy arg).run esL)) := by
  rcases arg with ⟨P, m₀, m₁, r_coins⟩
  have hcfg : ∀ e, (mo.cfg : SM.Config M).challAllowedIn e = false := by
    intro e
    simp [Mode.cfg, hauth, SM.Config.auth]
  unfold challE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq]
  by_cases habw : (esL.abort || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    rcases epMgmt_sync hsync.g_eq (2 + Δcka) qep P r_coins.isSome with ⟨h1, h2⟩ |
      ⟨s₁P, s₁L, h1, h2, _⟩
    · simp only [h1, h2, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    · simp only [h1, h2, hcfg, Bool.not_false, Bool.or_true, ↓reduceIte,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)

@[simp] theorem run_commitE_PRNG (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : SM.Pos)
    (es : EStateP Γ T Sig SS RS M E K) :
    (commitE (hooksPRNG cka prng fs mo) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  unfold commitE
  simp only [hooksPRNG, StateT.run_bind, run_liftH, StateT.run_pure, pure_bind]
  have h : { (s.accept P new pos) with st := Function.update (s.accept P new pos).st P new } =
      s.accept P new pos := by
    simp [SM.GameState.accept]
  rw [h]

@[simp] theorem run_commitE_local (s : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E)
    (P : Party) (old new : VP Γ T Sig (SS × Option ℕ) (RS × Option ℕ)) (pos : SM.Pos)
    (es : EStateL Γ T Sig SS RS M E K I) :
    (commitE (hooksLocal cka prng fs mo) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  unfold commitE
  simp only [hooksLocal, StateT.run_bind, run_liftH, StateT.run_pure, pure_bind]
  have h : { (s.accept P new pos) with st := Function.update (s.accept P new pos).st P new } =
      s.accept P new pos := by
    simp [SM.GameState.accept]
  rw [h]

theorem leComp_deliverE_PRNG_local
    (arg : Party × (Header T × E))
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((deliverE (hooksPRNG cka prng fs mo) fs.maxSkip mo.cfg arg).run esP)).run sp)
      (simulateQ lImpl
        ((deliverE (hooksLocal cka prng fs mo) fs.maxSkip mo.cfg arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq]
  by_cases habw : (esL.abort || esL.g.win) = true
  · simp only [habw, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [habw, Bool.false_eq_true, ↓reduceIte]
    cases htr : esL.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
    | some r =>
      have hr_mem : r ∈ esL.g.trans ∧ r.pos.sender = P.other ∧ r.ct = c := by
        unfold SM.GameState.inTransit at htr
        have hfind := List.find?_some htr
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfind
        exact ⟨List.mem_of_find?_eq_some htr, hfind.1, hfind.2⟩
      have hmust_eq : esP.g.mustBeCorrect fs.maxSkip P r = esL.g.mustBeCorrect fs.maxSkip P r := by
        simp [SM.GameState.mustBeCorrect, eraseSt_comp hsync.g_eq, eraseSt_tL hsync.g_eq,
          eraseSt_epoch hsync.g_eq, eraseSt_maxAcc hsync.g_eq, eraseSt_trans hsync.g_eq]
      simp only [hmust_eq, StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
      have hσ_tStar : P.sendsIn (esL.g.epoch P + 1) = false → esL.g.epoch P + 1 = mo.tStar →
          ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → sp.σ = (esL.g.st P).root := by
        intro _ he1 hnot_th
        exact (hsync.root_pred (by omega) P (by omega) hnot_th).symm
      refine (leComp_vRecv_PRNG_local cka prng fs mo (hsync.vp_rel P) hsync.cache_rel
        hsync.sp_b hsync.table_eq hsync.corr_tH hσ_tStar).bind ?_
      rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
      rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hc1, hb1, htab1, hcorr1, hσ1⟩ |
        ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hc1, hb1, htab1, hcorr1,
          hσ1, hroot_le, hcache_e1⟩
      · dsimp only at hnone; subst hnone
        simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure]
        exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
      · dsimp only at hP_none hL_none hhP1; subst hP_none hL_none hhP1
        simp only [pure_bind]
        by_cases hmust : ((mo.cfg : SM.Config M).deliverWin && esL.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [hmust, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
            StateT.run_pure, simulateQ_pure]
          refine LeComp.pure ?_
          refine Or.inr ⟨rfl, ⟨hsync.abort_eq, ?_, hsync.vp_rel, ?_, hb1, htab1,
            hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
            fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
            fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
            fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
          · have hg := hsync.g_eq
            simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
              eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
              eraseSt_leaks hg, eraseSt_corrs hg]
          · intro t'; rw [hc1]; exact hsync.cache_rel t'
        · simp only [hmust, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
          refine LeComp.pure ?_
          refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
            htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
            fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
            fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
            fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
          intro t'; rw [hc1]; exact hsync.cache_rel t'
      · dsimp only at hP_some hL_some hhP1; subst hP_some hL_some hhP1
        simp only [pure_bind, StateT.run_bind, run_commitE_PRNG, run_commitE_local,
          StateT.run_pure, StateT.run_modify, simulateQ_pure]
        rw [eraseSt_chall hsync.g_eq]
        refine LeComp.pure (Or.inr ⟨rfl, ?_⟩)
        have hacc_er : eraseSt (esP.g.accept P vpP' r.pos) = eraseSt (esL.g.accept P vpL' r.pos) :=
          eraseSt_accept hsync.g_eq P vpP' vpL' r.pos
        have hr_ep := hsync.trans_epoch r hr_mem.1
        have hr_pos_ep : r.pos.epoch = c.1.1 := by
          rw [← hr_ep.2, hr_mem.2.2]
        have hc_le_other : c.1.1 ≤ esL.g.epoch P.other := by
          rw [← hr_pos_ep, ← hr_mem.2.1]
          exact hr_ep.1
        have hacc_ep_L : (esL.g.accept P vpL' r.pos).epoch =
            Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) := by
          dsimp only [SM.GameState.accept, SM.GameState.delete]
          rw [hr_pos_ep]
        let gP' := if ((mo.cfg : SM.Config M).deliverWin && esL.g.mustBeCorrect fs.maxSkip P r) &&
            !decide ((c.1.1, i', m') = (r.pos.epoch, r.pos.idx, r.msg)) then
            { esP.g.accept P vpP' r.pos with win := true }
          else esP.g.accept P vpP' r.pos
        let gL' := if ((mo.cfg : SM.Config M).deliverWin && esL.g.mustBeCorrect fs.maxSkip P r) &&
            !decide ((c.1.1, i', m') = (r.pos.epoch, r.pos.idx, r.msg)) then
            { esL.g.accept P vpL' r.pos with win := true }
          else esL.g.accept P vpL' r.pos
        have hg'_ep : gL'.epoch = Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) := by
          rw [← hacc_ep_L]; dsimp only [gL']; split <;> rfl
        have hg'_stP : gP'.st = (esP.g.accept P vpP' r.pos).st := by
          dsimp only [gP']; split <;> rfl
        have hg'_stL : gL'.st = (esL.g.accept P vpL' r.pos).st := by
          dsimp only [gL']; split <;> rfl
        have hg'_comp : gL'.comp = (esL.g.accept P vpL' r.pos).comp := by
          dsimp only [gL']; split <;> rfl
        have hg'_tL : gL'.tL = (esL.g.accept P vpL' r.pos).tL := by
          dsimp only [gL']; split <;> rfl
        have hg'_trans : gL'.trans = (esL.g.accept P vpL' r.pos).trans := by
          dsimp only [gL']; split <;> rfl
        refine ⟨hsync.abort_eq, ?_, ?_, ?_, hb1, htab1, hcorr1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only [gP', gL']
          split
          · simp [eraseSt, eraseSt_epoch hacc_er, eraseSt_idx hacc_er, eraseSt_tL hacc_er,
              eraseSt_trans hacc_er, eraseSt_chall hacc_er, eraseSt_comp hacc_er,
              eraseSt_maxAcc hacc_er, eraseSt_b hacc_er, eraseSt_leaks hacc_er,
              eraseSt_corrs hacc_er]
          · exact hacc_er
        · intro Q
          dsimp only
          rw [hg'_ep, hg'_stP, hg'_stL]
          dsimp only [SM.GameState.accept]
          by_cases hQ : Q = P
          · subst Q; simp only [Function.update_self]; exact hvp'
          · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
        · intro t'; rw [hc1]; exact hsync.cache_rel t'
        · dsimp only
          rw [hg'_comp, hg'_tL]
          exact comp_inv_accept esL.g (2 + Δcka) P vpL' r.pos hsync.comp_inv
        · intro r' hr'
          dsimp only at hr' ⊢
          rw [hg'_trans] at hr'
          rw [hg'_ep]
          simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr' ⊢
          obtain ⟨h1, h2⟩ := hsync.trans_epoch r' hr'.1
          refine ⟨?_, h2⟩
          by_cases hQ : r'.pos.sender = P
          · rw [hQ, Function.update_self]; rw [hQ] at h1; omega
          · rw [Function.update_of_ne hQ]; exact h1
        · intro Q
          dsimp only
          rw [hg'_ep]
          have hle_P := hsync.epoch_le P
          have hle_other := hsync.epoch_le P.other
          cases Q <;> cases P <;>
            simp [Party.other] at hc_le_other htle hle_P hle_other ⊢ <;> omega
        · intro Q hlt_Q
          dsimp only at hlt_Q ⊢
          rw [hg'_ep] at hlt_Q ⊢
          by_cases hnew : c.1.1 = esL.g.epoch P + 1
          · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
              have := hsync.epoch_le P.other
              rw [Party.other_other] at this
              omega
            cases Q <;> cases P <;> simp [Party.other, hnew] at heq_other hlt_Q <;> omega
          · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
            have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
            rw [hmax_e, Function.update_eq_self] at hlt_Q ⊢
            exact hsync.epoch_sends Q hlt_Q
        · intro Q hQ_max hQ_lt
          dsimp only at hQ_max hQ_lt ⊢
          rw [hg'_ep] at hQ_max hQ_lt
          rw [hg'_stL, hσ1]
          dsimp only [SM.GameState.accept] at hQ_max hQ_lt ⊢
          by_cases hnew : c.1.1 = esL.g.epoch P + 1
          · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
              have := hsync.epoch_le P.other
              rw [Party.other_other] at this
              omega
            have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
              cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
            have hmax_new : max (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .A)
                (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .B) =
                esL.g.epoch P + 1 := by
              rw [hnew]
              exact max_epoch_accept_succ (by omega) (by omega)
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self] at hQ_lt ⊢
              have he1_lt : esL.g.epoch P + 1 < mo.tStar := by omega
              obtain ⟨Tc, k, idx?, hc_eq⟩ := hcache_e1 hnew (by omega)
              rw [← hmax_old] at hc_eq he1_lt
              exact hsync.cache_max Tc vpL'.root k idx? hc_eq he1_lt
            · simp only [Function.update_of_ne hQ] at hQ_max hQ_lt ⊢
              have hQ_eq_max : esL.g.epoch Q = max (esL.g.epoch .A) (esL.g.epoch .B) := by
                rw [hmax_old, ← hmax_new, hQ_max]
              exact hsync.root_max Q hQ_eq_max hQ_lt
          · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
            have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
            rw [hmax_e, Function.update_eq_self] at hQ_max hQ_lt
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hroot_le htle_e]
              exact hsync.root_max P hQ_max hQ_lt
            · simp only [Function.update_of_ne hQ]
              exact hsync.root_max Q hQ_max hQ_lt
        · intro hpos Q hQ_pred hnot_th
          dsimp only at hQ_pred ⊢
          rw [hg'_ep] at hQ_pred
          rw [hg'_stL, hσ1]
          dsimp only [SM.GameState.accept] at hQ_pred ⊢
          by_cases hnew : c.1.1 = esL.g.epoch P + 1
          · have heq_other : esL.g.epoch P.other = esL.g.epoch P + 1 := by
              have := hsync.epoch_le P.other
              rw [Party.other_other] at this
              omega
            have hmax_old : max (esL.g.epoch .A) (esL.g.epoch .B) = esL.g.epoch P + 1 := by
              cases P <;> simp [Party.other] at heq_other ⊢ <;> omega
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self] at hQ_pred ⊢
              have he1_lt : esL.g.epoch P + 1 < mo.tStar := by omega
              obtain ⟨Tc, k, idx?, hc_eq⟩ := hcache_e1 hnew (by omega)
              rw [← hmax_old] at hc_eq he1_lt
              exact hsync.cache_max Tc vpL'.root k idx? hc_eq he1_lt
            · simp only [Function.update_of_ne hQ] at hQ_pred ⊢
              exact hsync.root_pred hpos Q hQ_pred hnot_th
          · have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hnew)
            have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
            rw [hmax_e, Function.update_eq_self] at hQ_pred
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hroot_le htle_e]
              exact hsync.root_pred hpos P hQ_pred hnot_th
            · simp only [Function.update_of_ne hQ]
              exact hsync.root_pred hpos Q hQ_pred hnot_th
        · intro Tc σc k idx? hc_max hmax_lt
          dsimp only at hc_max hmax_lt ⊢
          rw [hg'_ep, hc1] at hc_max
          rw [hg'_ep] at hmax_lt
          rw [hσ1]
          have hmax_eq : max (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .A)
              (Function.update esL.g.epoch P (max (esL.g.epoch P) c.1.1) .B) =
              max (esL.g.epoch .A) (esL.g.epoch .B) := by
            cases P <;> simp [Party.other] at hc_le_other ⊢ <;> omega
          rw [hmax_eq] at hc_max hmax_lt
          exact hsync.cache_max Tc σc k idx? hc_max hmax_lt

theorem leComp_injectE_PRNG_local
    (arg : Party × (Header T × E))
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((injectE (hooksPRNG cka prng fs mo) (2 + Δcka) qep mo.cfg arg).run esP)).run sp)
      (simulateQ lImpl
        ((injectE (hooksLocal cka prng fs mo) (2 + Δcka) qep mo.cfg arg).run esL)) := by
  rcases arg with ⟨P, c⟩
  unfold injectE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq, eraseSt_inTransit hsync.g_eq,
    eraseSt_safeInj hsync.g_eq]
  by_cases hguard : (esL.abort || esL.g.win || (esL.g.inTransit P.other c).isSome ||
      !esL.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, run_liftH, simulateQ_bind, bind_assoc]
    have hsafe : esL.g.safeInj (2 + Δcka) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hguard
      exact Bool.eq_true_of_not_eq_false hguard.2
    have hσ_tStar : P.sendsIn (esL.g.epoch P + 1) = false → esL.g.epoch P + 1 = mo.tStar →
        ¬ (mo.tL.isSome = true ∧ mo.tStar = mo.tH) → sp.σ = (esL.g.st P).root := by
      intro _ he1 hnot_th
      exact (hsync.root_pred (by omega) P (by omega) hnot_th).symm
    refine (leComp_vRecv_PRNG_local cka prng fs mo (hsync.vp_rel P) hsync.cache_rel
      hsync.sp_b hsync.table_eq hsync.corr_tH hσ_tStar).bind ?_
    rintro ⟨⟨res_vrP, hP1⟩, sp1⟩ ⟨res_vrL, hL1⟩ hvr
    rcases hvr with hnone | ⟨hP_none, hL_none, hhP1, hc1, hb1, htab1, hcorr1, hσ1⟩ |
      ⟨vpP', vpL', i', m', hP_some, hL_some, htle, hns, hvp', hhP1, hc1, hb1, htab1, hcorr1,
        hσ1, hroot_le, _⟩
    · dsimp only at hnone; subst hnone
      simp only [pure_bind, abortE, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        simulateQ_pure]
      exact LeComp.pure_left _ _ fun _ _ => Or.inl rfl
    · dsimp only at hP_none hL_none hhP1; subst hP_none hL_none hhP1
      simp only [pure_bind, StateT.run_pure, simulateQ_pure]
      refine LeComp.pure ?_
      refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
        htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
        fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
        fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
        fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
      intro t'; rw [hc1]; exact hsync.cache_rel t'
    · dsimp only at hP_some hL_some hhP1; subst hP_some hL_some hhP1
      simp only [StateT.run_pure, simulateQ_pure, pure_bind]
      by_cases hqep : qep + 1 < c.1.1
      · simp only [hqep, ↓reduceIte, pure_bind, StateT.run_pure, simulateQ_pure]
        refine LeComp.pure ?_
        refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
          htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
          fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
          fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
          fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
        intro t'; rw [hc1]; exact hsync.cache_rel t'
      · simp only [hqep, ↓reduceIte]
        rw [eraseSt_trivial hsync.g_eq]
        by_cases htriv : esL.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
        ·
          have hne_e1 : c.1.1 ≠ esL.g.epoch P + 1 := by
            intro heq
            rw [heq] at htriv
            have htf := trivial_false_of_safeInj esL.g (2 + Δcka) P i' hsafe hsync.comp_inv
            rw [htf] at htriv
            cases htriv
          have htle_e : c.1.1 ≤ esL.g.epoch P := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne htle hne_e1)
          have hmax_e : max (esL.g.epoch P) c.1.1 = esL.g.epoch P := Nat.max_eq_left htle_e
          simp only [htriv, ↓reduceIte, StateT.run_bind, run_commitE_PRNG, run_commitE_local,
            StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
          have hacc_ep : (esL.g.accept P vpL' ⟨P.other, c.1.1, i'⟩).epoch = esL.g.epoch := by
            dsimp only [SM.GameState.accept, SM.GameState.delete]
            rw [hmax_e, Function.update_eq_self]
          refine LeComp.pure ?_
          refine Or.inr ⟨rfl, ⟨hsync.abort_eq,
            eraseSt_accept hsync.g_eq P vpP' vpL' _, ?_, ?_, hb1, htab1, hcorr1,
            comp_inv_accept esL.g (2 + Δcka) P vpL' _ hsync.comp_inv, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
          · intro Q
            dsimp only
            rw [hacc_ep]
            dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst Q; simp only [Function.update_self]; rw [← hmax_e]; exact hvp'
            · simp only [Function.update_of_ne hQ]; exact hsync.vp_rel Q
          · intro t'; rw [hc1]; exact hsync.cache_rel t'
          · intro r hr
            dsimp only at hr ⊢
            rw [hacc_ep]
            simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
            exact hsync.trans_epoch r hr.1
          · intro Q; dsimp only; rw [hacc_ep]; exact hsync.epoch_le Q
          · intro Q; dsimp only; rw [hacc_ep]; exact hsync.epoch_sends Q
          · intro Q hQ_max hQ_lt
            dsimp only at hQ_max hQ_lt ⊢
            rw [hacc_ep] at hQ_max hQ_lt
            rw [hσ1]
            dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hroot_le htle_e]
              exact hsync.root_max P hQ_max hQ_lt
            · simp only [Function.update_of_ne hQ]
              exact hsync.root_max Q hQ_max hQ_lt
          · intro hpos Q hQ_pred hnot_th
            dsimp only at hQ_pred ⊢
            rw [hacc_ep] at hQ_pred
            rw [hσ1]
            dsimp only [SM.GameState.accept]
            by_cases hQ : Q = P
            · subst Q
              simp only [Function.update_self, hroot_le htle_e]
              exact hsync.root_pred hpos P hQ_pred hnot_th
            · simp only [Function.update_of_ne hQ]
              exact hsync.root_pred hpos Q hQ_pred hnot_th
          · intro Tc σc k idx? hc_max hmax_lt
            dsimp only at hc_max hmax_lt ⊢
            rw [hacc_ep, hc1] at hc_max
            rw [hacc_ep] at hmax_lt
            rw [hσ1]
            exact hsync.cache_max Tc σc k idx? hc_max hmax_lt
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
          by_cases hfull : (mo.cfg : SM.Config M).injectFull c.1.1 = true
          · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
              StateT.run_pure, simulateQ_pure]
            refine LeComp.pure ?_
            refine Or.inr ⟨rfl, ⟨hsync.abort_eq, ?_, hsync.vp_rel, ?_, hb1, htab1,
              hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
              fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
              fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
              fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
            · have hg := hsync.g_eq
              simp [eraseSt, eraseSt_epoch hg, eraseSt_idx hg, eraseSt_tL hg, eraseSt_trans hg,
                eraseSt_chall hg, eraseSt_comp hg, eraseSt_maxAcc hg, eraseSt_b hg,
                eraseSt_leaks hg, eraseSt_corrs hg]
            · intro t'; rw [hc1]; exact hsync.cache_rel t'
          · simp only [hfull, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, simulateQ_pure]
            refine LeComp.pure ?_
            refine Or.inr ⟨rfl, ⟨hsync.abort_eq, hsync.g_eq, hsync.vp_rel, ?_, hb1,
              htab1, hcorr1, hsync.comp_inv, hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends,
              fun Q h1 h2 => (hsync.root_max Q h1 h2).trans hσ1.symm,
              fun hpos Q h1 h2 => (hsync.root_pred hpos Q h1 h2).trans hσ1.symm,
              fun Tc σc k idx? h1 h2 => (hsync.cache_max Tc σc k idx? (hc1 ▸ h1) h2).trans hσ1.symm⟩⟩
            intro t'; rw [hc1]; exact hsync.cache_rel t'

theorem leComp_corrE_PRNG_local
    (P : Party)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((corrE (hooksPRNG cka prng fs mo) mo.policy P).run esP)).run sp)
      (simulateQ lImpl
        ((corrE (hooksLocal cka prng fs mo) mo.policy P).run esL)) := by
  unfold corrE
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq, eraseSt_corrAllowed hsync.g_eq]
  by_cases hguard : (esL.abort || esL.g.win || !esL.g.corrAllowed P) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hac_er := eraseSt_afterCorr hsync.g_eq P
    rw [eraseSt_leakDoom hsync.g_eq hac_er mo.policy, eraseSt_corrDoom hsync.g_eq mo.policy P]
    by_cases hdoom : (mo.policy.leakDoom esL.g (esL.g.afterCorr P) ||
        mo.policy.corrDoom esL.g P) = true
    · simp only [hdoom, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inl rfl)
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, run_liftH, hooksPRNG, hooksLocal]
      have hvp := hsync.vp_rel P
      rcases hrootP : (esP.g.st P).root with _ | σ
      · simp only [StateT.run_pure, pure_bind, abortE, StateT.run_bind, StateT.run_modify,
          simulateQ_pure]
        exact LeComp.pure (Or.inl rfl)
      · have hσ_eq : σ = (esL.g.st P).root := hvp.root_eq σ hrootP
        subst hσ_eq
        simp only [StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure]
        refine LeComp.pure ?_
        refine Or.inr ⟨?_, ?_⟩
        · dsimp only [realParty]
          rw [hvp.id_P, hvp.id_L, hvp.γ_eq, hvp.Tcur_eq, hvp.tcur_P, hvp.tcur_L, hvp.vS_eq]
          congr 3
          funext t'
          exact hvp.vR_eq t'
        · refine ⟨hsync.abort_eq, hac_er, hsync.vp_rel, hsync.cache_rel, hsync.sp_b,
            hsync.table_eq, hsync.corr_tH,
            comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
              (fun r hr => (hsync.trans_epoch r hr).1) hsync.comp_inv,
            hsync.trans_epoch, hsync.epoch_le, hsync.epoch_sends, hsync.root_max,
            hsync.root_pred, hsync.cache_max⟩

theorem leComp_stepP_stepL (hauth : mo.auth = true)
    (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      (stepP cka prng fs Δcka qep mo q esP sp)
      (stepL cka prng fs Δcka qep mo q esL) := by
  rcases q with n | ((((arg | arg) | arg) | arg) | P)
  · rw [stepP_coinsE, stepL_coinsE, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine LeComp.sample_bind _ fun u _ => ?_
    exact LeComp.pure (Or.inr ⟨rfl, hsync⟩)
  · exact leComp_transmitE_PRNG_local cka prng fs Δcka qep mo hauth arg hsync
  · exact leComp_challE_PRNG_local (cka := cka) (prng := prng) (fs := fs)
      Δcka qep mo hauth arg hsync
  · exact leComp_deliverE_PRNG_local (cka := cka) (prng := prng) (fs := fs)
      (Δcka := Δcka) (mo := mo) arg hsync
  · exact leComp_injectE_PRNG_local cka prng fs Δcka qep mo arg hsync
  · exact leComp_corrE_PRNG_local (cka := cka) (prng := prng) (fs := fs)
      (Δcka := Δcka) (mo := mo) P hsync

theorem runP_le_runLoc (hauth : mo.auth = true)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    𝒟[runP cka prng fs Δcka qep mo oa esP sp] {true} ≤
      𝒟[runLoc cka prng fs Δcka qep mo oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esP sp esL with
  | pure b' =>
    rw [runP_pure, runLoc_pure]
    have hout : authOut (2 + Δcka) mo.policy esP = authOut (2 + Δcka) mo.policy esL := by
      unfold authOut
      rw [hsync.abort_eq, eraseSt_win hsync.g_eq,
        eraseSt_authOK hsync.g_eq (2 + Δcka) mo.policy.tL mo.policy.tStar]
    rw [hout]
  | query_bind q k ih =>
    rw [runP_query_bind, runLoc_query_bind]
    refine leComp_stepP_stepL cka prng fs Δcka qep mo hauth q hsync _ _ ?_
    rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨rfl, hsync'⟩)
    · exact runP_abort_le cka prng fs Δcka qep mo (k uP) hab _
    · exact ih uP hsync'

theorem evalDist_runP_eq (tL : Option ℕ) (t : ℕ) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    𝒟[do
      let x ← (simulateQ (pImpl prng)
        ((simulateQ (implE (hooksPRNG cka prng fs ⟨true, tL, t⟩) (2 + Δcka) qep fs.maxSkip
          (Mode.cfg ⟨true, tL, t⟩) (Mode.policy ⟨true, tL, t⟩)) oa).run esP)).run sp
      pure (authOut (2 + Δcka) ⟨true, tL, t⟩ x.1.2)] =
    𝒟[runP cka prng fs Δcka qep ⟨true, tL, t⟩ oa esP sp] := by
  simp [runP, Mode.policy, map_eq_bind_pure_comp, Function.comp_apply]

theorem branch_redPRNGAuth_le_localAuth (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[localAuth cka prng fs lam Δcka qep tL t A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  unfold PRFPRNG.branch redPRNGAuth runPRNG engRun localAuth initPRNG initLocal
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_apply,
    StateT.run_bind, simulateQ_bind, bind_assoc,
    simulateQ_pImpl_sampleT, simulateQ_lImpl_sampleT,
    simulateQ_pImpl_run_lift_sampleT, simulateQ_lImpl_run_lift_sampleT, pure_bind]
  refine evalDist_bind_mono ($ᵗ KR) _ _ fun kr _ => ?_
  refine evalDist_bind_mono ($ᵗ KC) _ _ fun kc _ => ?_
  have hroot0 := leComp_rootPRNG_rootL prng ⟨true, tL, t⟩
    (t := 0) (Ik := lam) (σv := none) (σ := prng.init kr)
    (hP := ({} : PRNGState T Sig K)) (sp := { σ := prng.init kr, b := true })
    (hL := ({} : LState T Sig K I))
    rfl rfl (fun h1 _ => Or.inr (by cases tL <;> simp [Mode.tH, healEpoch] at h1 ⊢)) (by omega)
    (fun _ => rfl)
  refine hroot0 _ _ ?_
  rintro ⟨⟨res0, hP0⟩, sp0⟩ ⟨⟨σL, kL, sid0⟩, hL0⟩ hrel0
  rcases hrel0 with hnone | ⟨σP, hres_eq, hhP0, hb0, htab0, hcorr0', hc0, _, hσ_rel, hlt0, _⟩
  · dsimp only at hnone; subst hnone
    simp
  · dsimp only at hres_eq hhP0; subst hres_eq hhP0
    have hreg_det : ∃ (idx? : Option ℕ) (hL1 : LState T Sig K I),
        simulateQ lImpl ((regSessOf (T := T) (Sig := Sig) (K := K) sid0).run hL0) =
          pure (idx?, hL1) ∧ hL1.table = hL0.table ∧ hL1.cache = hL0.cache := by
      cases sid0 with
      | none => exact ⟨none, hL0, rfl, rfl, rfl⟩
      | some Ik =>
        unfold regSessOf regSess
        simp only [StateT.run_map, StateT.run_bind, StateT.run_get, pure_bind]
        split
        · exact ⟨some (hL0.sessions.idxOf Ik), hL0, rfl, rfl, rfl⟩
        · exact ⟨some hL0.sessions.length, { hL0 with sessions := hL0.sessions ++ [Ik] },
            rfl, rfl, rfl⟩
    obtain ⟨idx?, hL1, hreg_eq, htab1, hc1⟩ := hreg_det
    simp only [StateT.run_pure, simulateQ_pure, StateT.run_bind, simulateQ_bind, hreg_eq,
      pure_bind, bind_assoc, Function.comp_apply]
    rw [evalDist_runP_eq]
    refine runP_le_runLoc cka prng fs Δcka qep ⟨true, tL, t⟩ rfl A ?_
    refine ⟨rfl, rfl, ?_, ?_, hb0, htab0.trans htab1.symm, hcorr0', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P
      cases P with
      | A =>
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hσ_rel⟩
        intro t'
        dsimp only [mkParties]
        split <;> rfl
      | B =>
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hσ_rel⟩
        intro t'
        rfl
    · intro t'
      rw [hc1, hc0]
      exact Or.inl ⟨rfl, rfl⟩
    · intro pos hpos; cases hpos
    · intro r hr; cases hr
    · intro P; simp
    · intro P hlt; simp at hlt
    · intro P _ hlt
      cases P <;> exact (hlt0 hlt).symm
    · intro hpos P _ _
      cases P <;> exact (hlt0 hpos).symm
    · intro Tc σc k idx' hc_eq _
      rw [hc1, hc0] at hc_eq
      cases hc_eq

end LocalGame

end CryptoGames.SM.Construction.AuthL11
