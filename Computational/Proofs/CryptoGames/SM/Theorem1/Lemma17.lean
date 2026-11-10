/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17Aux
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proof of Lemma 17

**Checked by Lean.** Proves `Thm1.lemma17` (ACD19 Appendix A, Lemma 17): moving from `Config.h1`
to `Config.h2` costs twice the authenticity advantages of `challSim A` summed over admissible
guesses `(t*_L, t*)` (`DEV-SM9`, `DEV-SM19`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Thm1L17

open CryptoGames.SM.Thm1

set_option linter.unusedSectionVars false

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

local notation "Comp" => AdversaryComp St Msg Coins C
local notation "RedM" => StateT (Mirror Msg C) (AdversaryComp St Msg Coins C)

/-! ### Frozen-state lemmas -/

section Coupling

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) [SampleableType Coins]

abbrev fullImpl (cfg : Config Msg) :
    QueryImpl (unifSpec + spec St Msg Coins C) (StateT (GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) ProbComp) + oracleImpl sm Δ qep cfg

@[simp] theorem StateT_run_lift {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (x : m α) (s : σ) : (StateT.lift x).run s = (x >>= fun a => pure (a, s)) := by
  simp

private lemma mem_support_liftM_run {σ α : Type} {p : ProbComp α} {s s' : σ} {a : α}
    (h : (a, s') ∈ support ((liftM p : StateT σ ProbComp α).run s)) : s' = s := by
  rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at h
  rcases h with ⟨_, _, h2⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h2
  exact h2.2

theorem eq_of_mem_support_fullImpl_of_win_true (cfg : Config Msg)
    (t : (unifSpec + spec St Msg Coins C).Domain)
    {sa : GameState St Msg C} (hwin : sa.win = true)
    {z : (unifSpec + spec St Msg Coins C).Range t × GameState St Msg C}
    (hz : z ∈ support ((fullImpl sm Δ qep cfg t).run sa)) :
    z.2 = sa := by
  rcases t with n | ((((q | q) | q) | q) | q)
  · exact mem_support_liftM_run hz
  · change z ∈ support ((transmitImpl sm Δ qep q).run sa) at hz
    unfold transmitImpl at hz
    simp [hwin] at hz
    rw [hz]
  · change z ∈ support ((challImpl sm Δ qep cfg q).run sa) at hz
    unfold challImpl at hz
    simp [hwin] at hz
    rw [hz]
  · change z ∈ support ((deliverImpl sm cfg q).run sa) at hz
    unfold deliverImpl at hz
    simp [hwin] at hz
    rw [hz]
  · change z ∈ support ((injectImpl sm Δ qep cfg q).run sa) at hz
    unfold injectImpl at hz
    simp [hwin] at hz
    rw [hz]
  · change z ∈ support ((corrImpl q).run sa) at hz
    unfold corrImpl at hz
    simp [hwin] at hz
    rw [hz]

theorem eq_of_mem_support_simulateQ_of_win_true (cfg : Config Msg)
    {β : Type} (c : AdversaryComp St Msg Coins C β) :
    ∀ {sa : GameState St Msg C} {z : β × GameState St Msg C},
      sa.win = true →
      z ∈ support ((simulateQ (fullImpl sm Δ qep cfg) c).run sa) →
      z.2 = sa := by
  induction c using OracleComp.inductionOn with
  | pure a =>
    intro sa z _ hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t r ih =>
    intro sa z hwin hz
    rw [simulateQ_query_bind, StateT.run_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, sa₁⟩, h₁, h₂⟩
    have hsa₁ : sa₁ = sa := eq_of_mem_support_fullImpl_of_win_true sm Δ qep cfg t hwin h₁
    subst hsa₁
    exact ih u hwin h₂

theorem evalDist_simulateQ_eq_one_of_win_true (cfg : Config Msg)
    {β : Type} (c : AdversaryComp St Msg Coins C β)
    (f : β × GameState St Msg C → ProbComp Bool)
    {sa : GameState St Msg C} (hwin : sa.win = true)
    (hf : ∀ z : β × GameState St Msg C, z.2 = sa → f z = pure true) :
    𝒟[(simulateQ (fullImpl sm Δ qep cfg) c).run sa >>= f] {true} = 1 := by
  have hcongr : 𝒟[(simulateQ (fullImpl sm Δ qep cfg) c).run sa >>= f] =
      𝒟[(simulateQ (fullImpl sm Δ qep cfg) c).run sa >>= fun _ => (pure true : ProbComp Bool)] := by
    refine evalDist_bind_congr_of_support _ _ _ fun z hz => ?_
    rw [hf z (eq_of_mem_support_simulateQ_of_win_true sm Δ qep cfg c hwin hz)]
  rw [hcongr, OracleComp.evalDist_bind_const]
  simp

theorem simulateQ_fullImpl_liftM_run {α : Type} (cfg : Config Msg)
    (p : ProbComp α) (s : GameState St Msg C) :
    (simulateQ (fullImpl sm Δ qep cfg) (liftM p : AdversaryComp St Msg Coins C α)).run s =
      p >>= fun a => pure (a, s) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change (simulateQ (fullImpl sm Δ qep cfg)
      ((liftM (OracleSpec.query (spec := unifSpec + spec St Msg Coins C) (.inl t)) :
          AdversaryComp St Msg Coins C _) >>=
        fun u => (liftM (k u) : AdversaryComp St Msg Coins C α))).run s = _
    rw [simulateQ_query_bind, StateT.run_bind]
    change ((liftM (OracleSpec.query (spec := unifSpec) t) :
        StateT (GameState St Msg C) ProbComp _).run s >>=
      fun z => (simulateQ (fullImpl sm Δ qep cfg) (liftM (k z.1))).run z.2) = _
    simp only [StateT.run_monadLift, bind_assoc, pure_bind, ih]

/-! ### `CloseBySum` combinators -/

def CloseBySum (c1 c2 : ProbComp Bool) (cAuth : ℕ → Option ℕ → ProbComp Bool) : Prop :=
  ∀ ev : Set Bool,
    𝒟[c1] ev ≤ 𝒟[c2] ev +
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t, 𝒟[cAuth t tL] {true} ∧
    𝒟[c2] ev ≤ 𝒟[c1] ev +
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t, 𝒟[cAuth t tL] {true}

theorem closeBySum_of_evalDist_eq {c1 c2 : ProbComp Bool}
    {cAuth : ℕ → Option ℕ → ProbComp Bool} (h : 𝒟[c1] = 𝒟[c2]) :
    CloseBySum Δ qep c1 c2 cAuth := by
  intro ev
  rw [h]
  exact ⟨le_self_add, le_self_add⟩

theorem closeBySum_of_eq {c1 c2 : ProbComp Bool}
    {cAuth : ℕ → Option ℕ → ProbComp Bool} (h : c1 = c2) :
    CloseBySum Δ qep c1 c2 cAuth :=
  closeBySum_of_evalDist_eq Δ qep (congrArg evalDist h)

theorem closeBySum_of_evalDist_eq_one {c1 c2 : ProbComp Bool}
    {cAuth : ℕ → Option ℕ → ProbComp Bool} {t₀ : ℕ} {tL₀ : Option ℕ}
    (ht₀ : t₀ ∈ Finset.range (qep + 2)) (htL₀ : tL₀ ∈ admissibleLastLeakGuesses Δ t₀)
    (hone : 𝒟[cAuth t₀ tL₀] {true} = 1) :
    CloseBySum Δ qep c1 c2 cAuth := by
  intro ev
  have h1 : (1 : ℝ≥0∞) ≤
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t, 𝒟[cAuth t tL] {true} := by
    calc (1 : ℝ≥0∞) = 𝒟[cAuth t₀ tL₀] {true} := hone.symm
      _ ≤ ∑ tL ∈ admissibleLastLeakGuesses Δ t₀, 𝒟[cAuth t₀ tL] {true} :=
        Finset.single_le_sum (f := fun tL => 𝒟[cAuth t₀ tL] {true}) (fun _ _ => zero_le) htL₀
      _ ≤ ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t, 𝒟[cAuth t tL] {true} :=
        Finset.single_le_sum (f := fun t => ∑ tL ∈ admissibleLastLeakGuesses Δ t, 𝒟[cAuth t tL] {true})
          (fun _ _ => zero_le) ht₀
  exact ⟨(prob_le_one.trans h1).trans le_add_self, (prob_le_one.trans h1).trans le_add_self⟩

theorem closeBySum_bind {α : Type} (oa : ProbComp α)
    {f1 f2 : α → ProbComp Bool} {fAuth : ℕ → Option ℕ → α → ProbComp Bool}
    (h : ∀ a, CloseBySum Δ qep (f1 a) (f2 a) (fun t tL => fAuth t tL a)) :
    CloseBySum Δ qep (oa >>= f1) (oa >>= f2) (fun t tL => oa >>= fAuth t tL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    intro ev
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool, ∀ s : Set Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] s =
          ∫⁻ u, 𝒟[g u] s ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g s
      rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= f1) ev, h1 (fun u => k u >>= f2) ev]
    have hsum : (∑ tStar ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ tStar,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= fun x => k x >>= fAuth tStar tL] {true}) =
        ∫⁻ u, (∑ tStar ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ tStar,
          𝒟[k u >>= fAuth tStar tL] {true}) ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      rw [lintegral_finsetSum' _ (fun _ _ => Measurable.of_discrete.aemeasurable)]
      refine Finset.sum_congr rfl fun tStar _ => ?_
      rw [lintegral_finsetSum' _ (fun _ _ => Measurable.of_discrete.aemeasurable)]
      refine Finset.sum_congr rfl fun tL _ => ?_
      exact h1 (fun u => k u >>= fAuth tStar tL) {true}
    rw [hsum, ← lintegral_add_left Measurable.of_discrete,
        ← lintegral_add_left Measurable.of_discrete]
    exact ⟨lintegral_mono fun u => (ih u ev).1, lintegral_mono fun u => (ih u ev).2⟩

/-! ### Oracle step unfolding -/

@[simp] theorem toAuth_st (s : GameState St Msg C) : (toAuth s).st = s.st := rfl
@[simp] theorem toAuth_epoch (s : GameState St Msg C) : (toAuth s).epoch = s.epoch := rfl
@[simp] theorem toAuth_idx (s : GameState St Msg C) : (toAuth s).idx = s.idx := rfl
@[simp] theorem toAuth_chall (s : GameState St Msg C) : (toAuth s).chall = [] := rfl
@[simp] theorem toMirror_epoch (s : GameState St Msg C) : (toMirror s).epoch = s.epoch := rfl
@[simp] theorem toMirror_idx (s : GameState St Msg C) : (toMirror s).idx = s.idx := rfl
@[simp] theorem toMirror_b (s : GameState St Msg C) : (toMirror s).b = s.b := rfl
@[simp] theorem toMirror_chall (s : GameState St Msg C) : (toMirror s).chall = s.chall := rfl

theorem epMgmt_win {s s₁ : GameState St Msg C} {P : Party} {fresh : Bool}
    (hep : s.epMgmt Δ qep P fresh = some s₁) : s₁.win = s.win := by
  unfold GameState.epMgmt at hep
  rcases h1 : P.sendsIn (s.epoch P + 1) <;> rcases h2 : decide (qep < s.epoch P) <;>
    rcases h3 : s.safeCh Δ P <;> rcases fresh <;> simp_all [GameState.leak] <;> rw [← hep.2]

def samCoins (r_opt : Option Coins) : ProbComp Coins :=
  match r_opt with
  | none => $ᵗ Coins
  | some c => pure c

theorem samIfNec_eq (r_opt : Option Coins) :
    samIfNec r_opt = samCoins r_opt >>= fun coins => pure (coins, r_opt.isSome) := by
  cases r_opt <;> simp [samIfNec, samCoins]

theorem closeBySum_of_samCoins_const (r_opt : Option Coins)
    {c1 c2 : ProbComp Bool} {cAuth : ℕ → Option ℕ → ProbComp Bool}
    (h : CloseBySum Δ qep c1 c2 cAuth) :
    CloseBySum Δ qep (samCoins r_opt >>= fun _ => c1) (samCoins r_opt >>= fun _ => c2) cAuth := by
  intro ev
  rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const]
  exact h ev

theorem simulateQ_sim_query_bind {α : Type} (cfg : Config Msg)
    (q : (unifSpec + spec St Msg Coins C).Domain)
    (r : (unifSpec + spec St Msg Coins C).Range q → AdversaryComp St Msg Coins C α)
    (m : Mirror Msg C) (sa : GameState St Msg C) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simulateQ (simImpl Δ qep (fun _ => none) none)
        ((liftM (OracleSpec.query q) : AdversaryComp St Msg Coins C _) >>= r)).run m)).run sa =
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none q).run m)).run sa >>=
      fun z => (simulateQ (fullImpl sm Δ qep cfg)
        ((simulateQ (simImpl Δ qep (fun _ => none) none) (r z.1.1)).run z.1.2)).run z.2 := by
  rw [simulateQ_query_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]

theorem coins_step_h (cfg : Config Msg) (n : unifSpec.Domain) (s : GameState St Msg C) :
    (fullImpl sm Δ qep cfg (.inl n)).run s =
      (liftM (OracleSpec.query n) : ProbComp _) >>= fun u => pure (u, s) := by
  change (liftM (OracleSpec.query (spec := unifSpec) n) :
    StateT (GameState St Msg C) ProbComp _).run s = _
  rw [StateT.run_monadLift]

theorem coins_step_auth (cfg : Config Msg) (n : unifSpec.Domain) (s : GameState St Msg C) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none (.inl n)).run (toMirror s))).run (toAuth s) =
      (liftM (OracleSpec.query n) : ProbComp _) >>=
        fun u => pure ((u, toMirror s), toAuth s) := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simCoins n).run (toMirror s))).run (toAuth s) = _
  unfold simCoins
  simp only [StateT_run_lift, simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure]
  rw [coins_step_h]
  simp

theorem transmit_step_h (cfg : Config Msg) (P : Party) (m_msg : Msg) (r_opt : Option Coins)
    (s : GameState St Msg C) (hwin : s.win = false) :
    (fullImpl sm Δ qep cfg (.inr (.inl (.inl (.inl (.inl ⟨P, m_msg, r_opt⟩)))))).run s =
      samCoins r_opt >>= fun coins =>
        match s.epMgmt Δ qep P r_opt.isSome with
        | none => pure (none, s)
        | some s₁ =>
          let out := sm.send (s₁.st P) m_msg coins
          pure (some out.2, s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, out.2⟩ false) := by
  change (transmitImpl sm Δ qep ⟨P, m_msg, r_opt⟩).run s = _
  unfold transmitImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
    StateT.run_monadLift, monadLift_self, samIfNec_eq, bind_assoc]
  refine congrArg (samCoins r_opt >>= ·) (funext fun coins => ?_)
  cases s.epMgmt Δ qep P r_opt.isSome <;> simp [StateT.run_set]

theorem transmit_step_auth (cfg : Config Msg) (P : Party) (m_msg : Msg) (r_opt : Option Coins)
    (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inl ⟨P, m_msg, r_opt⟩)))))).run (toMirror s))).run (toAuth s) =
      samCoins r_opt >>= fun coins =>
        match s.epMgmt Δ qep P r_opt.isSome with
        | none => pure ((none, toMirror s), toAuth s)
        | some s₁ =>
          let out := sm.send (s₁.st P) m_msg coins
          let rec_r : Record Msg C := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, out.2⟩
          let s' := s₁.record Δ P out.1 rec_r false
          pure ((some out.2, toMirror s'), toAuth s') := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simTransmit Δ qep ⟨P, m_msg, r_opt⟩).run (toMirror s))).run (toAuth s) = _
  unfold simTransmit transmitQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [transmit_step_h sm Δ qep cfg P m_msg r_opt (toAuth s) hwin]
  simp only [bind_assoc]
  refine congrArg (samCoins r_opt >>= ·) (funext fun coins => ?_)
  rw [toAuth_epMgmt, toMirror_epMgmt]
  cases hep : s.epMgmt Δ qep P r_opt.isSome with
  | none =>
    simp [Option.map]
  | some s₁ =>
    simp [Option.map, StateT.run_set]
    exact ⟨toMirror_record _ _ _ _ _ _, rfl⟩

theorem chall_step_h (cfg : Config Msg) (hchallOK : cfg.challAllowedIn = fun _ => true)
    (hchallMsg : cfg.challMsg = fun _ => none)
    (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s : GameState St Msg C) (hwin : s.win = false) :
    (fullImpl sm Δ qep cfg (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run s =
      samCoins r_opt >>= fun coins =>
        match s.epMgmt Δ qep P r_opt.isSome with
        | none => pure (none, s)
        | some s₁ =>
          if !(s₁.safeCh Δ P) then pure (none, s)
          else
            let mb := if s.b then m₁ else m₀
            let out := sm.send (s₁.st P) mb coins
            pure (some out.2, s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, out.2⟩ true) := by
  change (challImpl sm Δ qep cfg ⟨P, m₀, m₁, r_opt⟩).run s = _
  unfold challImpl
  rw [hchallOK, hchallMsg]
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
    StateT.run_monadLift, monadLift_self, samIfNec_eq, bind_assoc, Bool.not_true, Bool.or_false,
    Option.getD_none]
  refine congrArg (samCoins r_opt >>= ·) (funext fun coins => ?_)
  cases s.epMgmt Δ qep P r_opt.isSome with
  | none => simp
  | some s₁ =>
    by_cases hsafe : s₁.safeCh Δ P = true <;> simp [hsafe, StateT.run_set]

theorem chall_step_auth_none (cfg : Config Msg) (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s : GameState St Msg C) (hep : s.epMgmt Δ qep P r_opt.isSome = none) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run (toMirror s))).run (toAuth s) =
      pure ((none, toMirror s), toAuth s) := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run (toMirror s))).run (toAuth s) = _
  unfold simChall
  simp [toMirror_epMgmt, hep]

theorem chall_step_auth_unsafe (cfg : Config Msg) (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s s₁ : GameState St Msg C) (hep : s.epMgmt Δ qep P r_opt.isSome = some s₁)
    (hsafe : s₁.safeCh Δ P = false) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run (toMirror s))).run (toAuth s) =
      pure ((none, toMirror s), toAuth s) := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run (toMirror s))).run (toAuth s) = _
  unfold simChall
  simp [toMirror_epMgmt, hep, hsafe]

theorem chall_step_auth_safe (cfg : Config Msg) (P : Party) (m₀ m₁ : Msg) (r_opt : Option Coins)
    (s s₁ : GameState St Msg C) (hwin : s.win = false)
    (hep : s.epMgmt Δ qep P r_opt.isSome = some s₁)
    (hsafe : s₁.safeCh Δ P = true) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inl (.inr ⟨P, m₀, m₁, r_opt⟩)))))).run (toMirror s))).run (toAuth s) =
      samCoins r_opt >>= fun coins =>
        let mb := if s.b then m₁ else m₀
        let out := sm.send (s₁.st P) mb coins
        let rec_r : Record Msg C := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, mb, out.2⟩
        let s' := s₁.record Δ P out.1 rec_r true
        pure ((some out.2, toMirror s'), toAuth s') := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simChall Δ qep (fun _ => none) none ⟨P, m₀, m₁, r_opt⟩).run (toMirror s))).run (toAuth s) = _
  unfold simChall simSend transmitQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, toMirror_epMgmt, hep, Option.map,
    toMirror_safeCh, hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT_run_lift,
    Option.getD_none, simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [transmit_step_h sm Δ qep cfg P (if (toMirror s).b then m₁ else m₀) r_opt (toAuth s) hwin]
  simp only [bind_assoc, toAuth_epMgmt, hep, Option.map]
  refine congrArg (samCoins r_opt >>= ·) (funext fun coins => ?_)
  simp [StateT.run_set]
  exact ⟨⟨rfl, toMirror_record _ _ _ _ _ _⟩, toAuth_record _ _ _ _ _ _⟩

theorem deliver_step_h (cfg : Config Msg) (hdw : cfg.deliverWin = false)
    (P : Party) (c : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (fullImpl sm Δ qep cfg (.inr (.inl (.inl (.inr ⟨P, c⟩))))).run s =
      match s.inTransit P.other c with
      | none => pure (none, s)
      | some r =>
        match sm.receive (s.st P) c with
        | none => pure (some .rejected, s)
        | some (st', t', i', m') =>
          pure (some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
                s.accept P st' r.pos) := by
  change (deliverImpl sm cfg ⟨P, c⟩).run s = _
  unfold deliverImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_eq_true, ↓reduceIte,
    hdw, Bool.false_and]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      simp [StateT.run_set]

theorem deliver_step_auth (cfg : Config Msg) (hdw : cfg.deliverWin = false)
    (P : Party) (c : C) (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inl (.inr ⟨P, c⟩))))).run (toMirror s))).run (toAuth s) =
      match s.inTransit P.other c with
      | none => pure ((none, toMirror s), toAuth s)
      | some r =>
        match sm.receive (s.st P) c with
        | none => pure ((some .rejected, toMirror s), toAuth s)
        | some (st', t', i', m') =>
          let s' := s.accept P st' r.pos
          pure ((some (.accepted t' i' (if s.chall.contains r.pos then none else some m')),
                 toMirror s'), toAuth s') := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simDeliver ⟨P, c⟩).run (toMirror s))).run (toAuth s) = _
  unfold simDeliver deliverQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [deliver_step_h sm Δ qep cfg hdw P c (toAuth s) hwin]
  rw [toAuth_inTransit, toMirror_inTransit, toAuth_st]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      simp [StateT.run_set, toAuth_accept]
      exact toMirror_accept _ _ _ _

theorem inTransit_epoch_le_max {s : GameState St Msg C} {P : Party} {c : C} {r : Record Msg C}
    (hwf : WFState Δ s) (htr : s.inTransit P.other c = some r) :
    r.pos.epoch ≤ max (s.epoch P) (s.epoch P.other) := by
  unfold GameState.inTransit at htr
  have hmem : r ∈ s.trans := List.mem_of_find?_eq_some htr
  have hpred := List.find?_some htr
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  have hle := hwf.trans_epoch_le r hmem
  rw [hpred.1] at hle
  exact hle.trans (Nat.le_max_right _ _)

theorem corr_step_h (cfg : Config Msg) (P : Party) (s : GameState St Msg C)
    (hwin : s.win = false) :
    (fullImpl sm Δ qep cfg (.inr (.inr P))).run s =
      if !(s.corrAllowed P) then pure (none, s)
      else pure (some (s.st P), s.afterCorr P) := by
  change (corrImpl P).run s = _
  unfold corrImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_or]
  split <;> simp [StateT.run_set]

theorem corr_step_auth (cfg : Config Msg) (P : Party) (s : GameState St Msg C)
    (hwf : WFState Δ s) (hwin : s.win = false) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none (.inr (.inr P))).run (toMirror s))).run (toAuth s) =
      if !(s.corrAllowed P) then pure ((none, toMirror s), toAuth s)
      else pure ((some (s.st P), toMirror (s.afterCorr P)), toAuth (s.afterCorr P)) := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simCorr P).run (toMirror s))).run (toAuth s) = _
  unfold simCorr corrQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [corr_step_h sm Δ qep cfg P (toAuth s) hwin]
  have hallow_eq : (toAuth s).corrAllowed P = s.corrAllowed P :=
    corrAllowed_eq_of_chall_in_trans P hwf.chall_in_trans rfl rfl rfl
  rw [hallow_eq]
  by_cases hallow : s.corrAllowed P = true <;>
    simp [hallow, StateT.run_set, toAuth_afterCorr, toMirror_afterCorr]

theorem inject_step_h (cfg : Config Msg) (P : Party) (c : C)
    (s : GameState St Msg C) (hwin : s.win = false) :
    (fullImpl sm Δ qep cfg (.inr (.inl (.inr ⟨P, c⟩)))).run s =
      if (s.inTransit P.other c).isSome || !(s.safeInj Δ) then pure (none, s)
      else
        match sm.receive (s.st P) c with
        | none => pure (some .rejected, s)
        | some (st', t', i', m') =>
          if qep + 1 < t' then pure (some .rejected, s)
          else
            let pos : Pos := ⟨P.other, t', i'⟩
            if s.trivial Δ pos then
              pure (some (.accepted t' i' (some m')), s.accept P st' pos)
            else
              pure (some .rejected, if cfg.injectFull t' then { s with win := true } else s) := by
  change (injectImpl sm Δ qep cfg ⟨P, c⟩).run s = _
  unfold injectImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin, Bool.false_or]
  split
  · simp
  · cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      dsimp only
      split
      · simp
      · split
        · simp [StateT.run_set]
        · split <;> simp [StateT.run_set]

theorem inject_step_auth (cfg : Config Msg) (P : Party) (c : C)
    (s : GameState St Msg C) (hwin : s.win = false) :
    (simulateQ (fullImpl sm Δ qep cfg)
      ((simImpl Δ qep (fun _ => none) none
        (.inr (.inl (.inr ⟨P, c⟩)))).run (toMirror s))).run (toAuth s) =
      if (s.inTransit P.other c).isSome || !(s.safeInj Δ) then
        pure ((none, toMirror s), toAuth s)
      else
        match sm.receive (s.st P) c with
        | none => pure ((some .rejected, toMirror s), toAuth s)
        | some (st', t', i', m') =>
          if qep + 1 < t' then pure ((some .rejected, toMirror s), toAuth s)
          else
            let pos : Pos := ⟨P.other, t', i'⟩
            if s.trivial Δ pos then
              let s' := s.accept P st' pos
              pure ((some (.accepted t' i' (some m')), toMirror s'), toAuth s')
            else
              pure ((some .rejected, toMirror s),
                if cfg.injectFull t' then { toAuth s with win := true } else toAuth s) := by
  change (simulateQ (fullImpl sm Δ qep cfg)
    ((simInject ⟨P, c⟩).run (toMirror s))).run (toAuth s) = _
  unfold simInject injectQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
    simulateQ_bind, simulateQ_HasQuery_query,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [inject_step_h sm Δ qep cfg P c (toAuth s) hwin]
  rw [toAuth_inTransit, toAuth_safeInj, toAuth_st]
  split
  · simp
  · cases sm.receive (s.st P) c with
    | none => simp
    | some res =>
      rcases res with ⟨st', t', i', m'⟩
      dsimp only
      split
      · simp
      · rw [toAuth_trivial]
        split
        · simp [StateT.run_set, toAuth_accept]
          exact toMirror_accept _ _ _ _
        · simp

/-! ### Coupling across `simulateQ` -/

theorem closeBySum_simulateQ (hΔ : 0 < Δ) {α : Type}
    (oa : AdversaryComp St Msg Coins C α)
    (f1 f2 : α × GameState St Msg C → ProbComp Bool)
    (fAuth : ℕ → Option ℕ → (α × Mirror Msg C) × GameState St Msg C → ProbComp Bool)
    (hf12 : ∀ a s, s.win = false → f1 (a, s) = f2 (a, s))
    (hfAuth : ∀ t tL (z : (α × Mirror Msg C) × GameState St Msg C),
      z.2.win = true → authLosingConditionsAvoided Δ tL t z.2 = true → fAuth t tL z = pure true) :
    ∀ {s : GameState St Msg C},
      WFState Δ s → s.win = false →
      CloseBySum Δ qep
        ((simulateQ (fullImpl sm Δ qep Config.h1) oa).run s >>= f1)
        ((simulateQ (fullImpl sm Δ qep Config.h2) oa).run s >>= f2)
        (fun t tL =>
          (simulateQ (fullImpl sm Δ qep (Config.auth t))
            ((simulateQ (simImpl Δ qep (fun _ => none) none) oa).run (toMirror s))).run
              (toAuth s) >>= fAuth t tL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s _ hwin
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact closeBySum_of_eq Δ qep (hf12 a s hwin)
  | query_bind q r ih =>
    intro s hwf hwin
    rw [simulateQ_query_bind, StateT.run_bind, simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, monadLift_self]
    simp_rw [simulateQ_sim_query_bind sm Δ qep]
    rcases q with n | ((((⟨P, m_msg, r_opt⟩ | ⟨P, m₀, m₁, r_opt⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    ·
      rw [coins_step_h, coins_step_h]
      simp_rw [coins_step_auth, bind_assoc, pure_bind]
      exact closeBySum_bind Δ qep (liftM (OracleSpec.query n)) fun u => ih u hwf hwin
    ·
      rw [transmit_step_h sm Δ qep Config.h1 P m_msg r_opt s hwin,
          transmit_step_h sm Δ qep Config.h2 P m_msg r_opt s hwin]
      simp_rw [transmit_step_auth sm Δ qep _ P m_msg r_opt s hwin, bind_assoc]
      refine closeBySum_bind Δ qep (samCoins r_opt) fun coins => ?_
      cases hep : s.epMgmt Δ qep P r_opt.isSome with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some s₁ =>
        simp only [pure_bind]
        have ⟨hwf₁, hsends₁⟩ := epMgmt_wf hwf hep
        have hs₁_win : s₁.win = false := (epMgmt_win Δ qep hep).trans hwin
        have hwf' : WFState Δ (s₁.record Δ P (sm.send (s₁.st P) m_msg coins).1
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m_msg, (sm.send (s₁.st P) m_msg coins).2⟩ false) :=
          record_wf hΔ hwf₁ rfl rfl rfl hsends₁ (by intro h; cases h)
        exact ih (some (sm.send (s₁.st P) m_msg coins).2) hwf' hs₁_win
    ·
      rw [chall_step_h sm Δ qep Config.h1 rfl rfl P m₀ m₁ r_opt s hwin,
          chall_step_h sm Δ qep Config.h2 rfl rfl P m₀ m₁ r_opt s hwin]
      cases hep : s.epMgmt Δ qep P r_opt.isSome with
      | none =>
        simp_rw [chall_step_auth_none sm Δ qep _ P m₀ m₁ r_opt s hep, bind_assoc, pure_bind]
        exact closeBySum_of_samCoins_const Δ qep r_opt (ih none hwf hwin)
      | some s₁ =>
        by_cases hsafe : s₁.safeCh Δ P = true
        · simp_rw [chall_step_auth_safe sm Δ qep _ P m₀ m₁ r_opt s s₁ hwin hep hsafe]
          simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          refine closeBySum_bind Δ qep (samCoins r_opt) fun coins => ?_
          have ⟨hwf₁, hsends₁⟩ := epMgmt_wf hwf hep
          have hs₁_win : s₁.win = false := (epMgmt_win Δ qep hep).trans hwin
          have hwf' : WFState Δ (s₁.record Δ P
              (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).1
              ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, if s.b then m₁ else m₀,
                (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).2⟩ true) :=
            record_wf hΔ hwf₁ rfl rfl rfl hsends₁ (fun _ => hsafe)
          exact ih (some (sm.send (s₁.st P) (if s.b then m₁ else m₀) coins).2) hwf' hs₁_win
        · have hsafeF : s₁.safeCh Δ P = false := Bool.eq_false_iff.mpr hsafe
          simp_rw [chall_step_auth_unsafe sm Δ qep _ P m₀ m₁ r_opt s s₁ hep hsafeF]
          simp only [hsafeF, Bool.not_false, ↓reduceIte, bind_assoc, pure_bind]
          exact closeBySum_of_samCoins_const Δ qep r_opt (ih none hwf hwin)
    ·
      rw [deliver_step_h sm Δ qep Config.h1 rfl P c s hwin,
          deliver_step_h sm Δ qep Config.h2 rfl P c s hwin]
      simp_rw [deliver_step_auth sm Δ qep (Config.auth _) rfl P c s hwin]
      cases htr : s.inTransit P.other c with
      | none =>
        simp only [pure_bind]
        exact ih none hwf hwin
      | some rec_r =>
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          simp only [pure_bind]
          exact ih (some .rejected) hwf hwin
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          simp only [pure_bind]
          have hwf' : WFState Δ (s.accept P st' rec_r.pos) :=
            accept_wf hwf (inTransit_epoch_le_max Δ hwf htr)
          exact ih (some (.accepted t' i' (if s.chall.contains rec_r.pos then none else some m')))
            hwf' hwin
    ·
      rw [inject_step_h sm Δ qep Config.h1 P c s hwin,
          inject_step_h sm Δ qep Config.h2 P c s hwin]
      simp_rw [inject_step_auth sm Δ qep (Config.auth _) P c s hwin]
      by_cases hguard : ((s.inTransit P.other c).isSome || !(s.safeInj Δ)) = true
      · simp only [hguard, ↓reduceIte, pure_bind]
        exact ih none hwf hwin
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hsafe : s.safeInj Δ = true := by
          revert hguard; cases (s.inTransit P.other c).isSome <;> cases s.safeInj Δ <;> simp
        cases hrcv : sm.receive (s.st P) c with
        | none =>
          simp only [pure_bind]
          exact ih (some .rejected) hwf hwin
        | some res =>
          rcases res with ⟨st', t', i', m'⟩
          dsimp only
          by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, pure_bind]
            exact ih (some .rejected) hwf hwin
          · simp only [hqep, ↓reduceIte]
            by_cases htriv : s.trivial Δ ⟨P.other, t', i'⟩ = true
            · simp only [htriv, ↓reduceIte, pure_bind]
              have hwf' : WFState Δ (s.accept P st' ⟨P.other, t', i'⟩) :=
                accept_wf hwf (pos_epoch_le_of_trivial hwf hsafe htriv)
              exact ih (some (.accepted t' i' (some m'))) hwf' hwin
            ·
              have htrivF : s.trivial Δ ⟨P.other, t', i'⟩ = false := Bool.eq_false_iff.mpr htriv
              simp only [htrivF, Bool.false_eq_true, ↓reduceIte, pure_bind]
              have ht' : t' ∈ Finset.range (qep + 2) := by
                rw [Finset.mem_range]; omega
              have ⟨hok, htL⟩ := authOK_of_nontrivial_inject hΔ hwf htrivF
              refine closeBySum_of_evalDist_eq_one Δ qep ht' htL ?_
              have hinj : (Config.auth (Msg := Msg) t').injectFull t' = true := by
                simp [Config.auth]
              rw [hinj]
              simp only [↓reduceIte]
              refine evalDist_simulateQ_eq_one_of_win_true sm Δ qep (Config.auth t')
                ((simulateQ (simImpl Δ qep (fun _ => none) none) (r (some .rejected))).run (toMirror s))
                (fAuth t' (canon t' s)) rfl ?_
              intro z hz
              apply hfAuth t' (canon t' s) z
              · rw [hz]
              · rw [hz, authOK_with_win, authOK_toAuth]
                exact hok
    ·
      rw [corr_step_h sm Δ qep Config.h1 P s hwin,
          corr_step_h sm Δ qep Config.h2 P s hwin]
      simp_rw [corr_step_auth sm Δ qep (Config.auth _) P s hwf hwin]
      by_cases hallow : s.corrAllowed P = true
      · simp only [hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
        exact ih (some (s.st P)) (afterCorr_wf hΔ hwf hallow) hwin
      · have hallowF : s.corrAllowed P = false := Bool.eq_false_iff.mpr hallow
        simp only [hallowF, Bool.not_false, ↓reduceIte, pure_bind]
        exact ih none hwf hwin

end Coupling

section Main

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [SampleableType Key] [SampleableType Coins]

theorem authGame_challSim_evalDist (tLStar : Option ℕ) (tStar : ℕ)
    (A : Adversary St Msg Coins C) :
    𝒟[authGame sm Δ qep tLStar tStar (challSim Δ qep A)] =
      𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
        (simulateQ (fullImpl sm Δ qep (Config.auth tStar))
          ((simulateQ (simImpl Δ qep (fun _ => none) none) A).run
            (toMirror (initState sm k b)))).run (toAuth (initState sm k b)) >>=
          fun z => pure (z.2.win && authLosingConditionsAvoided Δ tLStar tStar z.2)] := by
  unfold authGame run challSim simRun
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_bind_swap (γ := Bool) ($ᵗ Bool : ProbComp Bool) ($ᵗ Key : ProbComp Key)]
  refine congrArg evalDist (congrArg (($ᵗ Key : ProbComp Key) >>= ·) (funext fun k => ?_))
  simp only [StateT.run', map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind]
  rw [simulateQ_fullImpl_liftM_run]
  simp only [bind_assoc, pure_bind]
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, toMirror_initState, toAuth_initState]
  rfl

theorem lemma17_proof (hΔ : 0 < Δ) (A : Adversary St Msg Coins C) :
    hybridAdvantage sm Δ qep Config.h1 A ≤
      hybridAdvantage sm Δ qep Config.h2 A +
        2 * ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
          authAdvantage sm Δ qep tL t (challSim Δ qep A) := by
  let f (b : Bool) : Bool × GameState St Msg C → ProbComp Bool :=
    fun z => pure (b == z.1 || z.2.win)
  let fAuth (t : ℕ) (tL : Option ℕ) :
      (Bool × Mirror Msg C) × GameState St Msg C → ProbComp Bool :=
    fun z => pure (z.2.win && authLosingConditionsAvoided Δ tL t z.2)
  have hclose : CloseBySum Δ qep
      (game sm Δ qep Config.h1 A)
      (game sm Δ qep Config.h2 A)
      (fun t tL =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b => ($ᵗ Key : ProbComp Key) >>= fun k =>
          (simulateQ (fullImpl sm Δ qep (Config.auth t))
            ((simulateQ (simImpl Δ qep (fun _ => none) none) A).run
              (toMirror (initState sm k b)))).run (toAuth (initState sm k b)) >>=
            fAuth t tL) := by
    unfold game run
    simp only [bind_assoc]
    refine closeBySum_bind Δ qep ($ᵗ Bool : ProbComp Bool) fun b =>
      closeBySum_bind Δ qep ($ᵗ Key : ProbComp Key) fun k => ?_
    exact closeBySum_simulateQ sm Δ qep hΔ A (f b) (f b) fAuth
      (fun _ _ _ => rfl)
      (fun t tL z hwin hok => by simp [fAuth, hwin, hok])
      (wfState_init sm Δ k b) rfl
  have htr := hclose {true}
  dsimp only [fAuth] at htr
  simp_rw [← authGame_challSim_evalDist sm Δ qep _ _ A] at htr
  change 𝒟[game sm Δ qep Config.h1 A] {true} ≤
      𝒟[game sm Δ qep Config.h2 A] {true} +
        ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
          authAdvantage sm Δ qep tL t (challSim Δ qep A) ∧
    𝒟[game sm Δ qep Config.h2 A] {true} ≤
      𝒟[game sm Δ qep Config.h1 A] {true} +
        ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
          authAdvantage sm Δ qep tL t (challSim Δ qep A) at htr
  have hdiff : ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true})
      (𝒟[game sm Δ qep Config.h2 A] {true}) ≤
      ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
        authAdvantage sm Δ qep tL t (challSim Δ qep A) :=
    ENNReal.absDiff_le_iff.mpr htr
  have htri : ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true}) (1 / 2) ≤
      ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) +
        ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
          authAdvantage sm Δ qep tL t (challSim Δ qep A) := by
    calc ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true}) (1 / 2)
        ≤ ENNReal.absDiff (𝒟[game sm Δ qep Config.h1 A] {true})
            (𝒟[game sm Δ qep Config.h2 A] {true}) +
          ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) :=
          ENNReal.absDiff_triangle _ _ _
      _ ≤ (∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
            authAdvantage sm Δ qep tL t (challSim Δ qep A)) +
          ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) := by gcongr
      _ = ENNReal.absDiff (𝒟[game sm Δ qep Config.h2 A] {true}) (1 / 2) +
          ∑ t ∈ Finset.range (qep + 2), ∑ tL ∈ admissibleLastLeakGuesses Δ t,
            authAdvantage sm Δ qep tL t (challSim Δ qep A) := add_comm _ _
  unfold hybridAdvantage
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
      Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, ← mul_add]
  gcongr

end Main

end CryptoGames.SM.Thm1L17
