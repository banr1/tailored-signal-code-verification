/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game
import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Proofs of `dev6_priv_le` and `dev6_auth_le`

**Checked by Lean.** Proves the advantage bounds in `PaperCorrRule.lean` via an
identical-until-`bad` coupling between `runPaper` and `run`. Because `oracleImplPaper` lifts
`transmit`, `chall`, `deliver`, and `inject` unchanged via `liftBad` and sets `bad = true` in
`corrImplPaper` only when `corrAllowedPaper P` holds without `corrAllowed P`, the two runs agree
until `bad` becomes `true`, and `bad` is monotone.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Dev6Proof

variable {Key St Msg Coins C : Type}

def corrAllowedPaper (s : GameState St Msg C) (P : Party) : Bool :=
  !(s.chall.any (fun pos => pos.sender == P.other))

section Oracles

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

local notation "GameM" => StateT (GameState St Msg C) ProbComp
local notation "BadM" => StateT (GameState St Msg C × Bool) ProbComp

def liftBad {ι : Type} {spec' : OracleSpec.{0, 0} ι} (impl : QueryImpl spec' GameM) :
    QueryImpl spec' BadM := fun q sb =>
  (fun p => (p.1, (p.2, sb.2))) <$> impl q sb.1

def corrImplPaper : QueryImpl (Party →ₒ Option St) BadM := fun P => do
  let (s, bad) ← get
  if s.win || !(corrAllowedPaper s P) then return none
  set (s.afterCorr P, bad || !(s.corrAllowed P))
  return some (s.st P)

def oracleImplPaper : QueryImpl (spec St Msg Coins C) BadM :=
  liftBad (transmitImpl sm Δ qep + challImpl sm Δ qep cfg + deliverImpl sm cfg
    + injectImpl sm Δ qep cfg) + (corrImplPaper : QueryImpl (Party →ₒ Option St) BadM)

end Oracles

section Proof

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

local notation "GameM" => StateT (GameState St Msg C) ProbComp
local notation "BadM" => StateT (GameState St Msg C × Bool) ProbComp

abbrev implBaseFour (cfg : Config Msg) :=
  transmitImpl sm Δ qep + challImpl sm Δ qep cfg + deliverImpl sm cfg + injectImpl sm Δ qep cfg

abbrev gameImpl (cfg : Config Msg) :
    QueryImpl (unifSpec + spec St Msg Coins C) GameM :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget GameM + oracleImpl sm Δ qep cfg

abbrev gameImplPaper (cfg : Config Msg) :
    QueryImpl (unifSpec + spec St Msg Coins C) BadM :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget BadM + oracleImplPaper sm Δ qep cfg

abbrev runCfg (cfg : Config Msg) {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) : ProbComp (α × GameState St Msg C) :=
  (simulateQ (gameImpl sm Δ qep cfg) oa).run s

abbrev runPaperCfg (cfg : Config Msg) {α : Type} (oa : AdversaryComp St Msg Coins C α)
    (sb : GameState St Msg C × Bool) : ProbComp (α × (GameState St Msg C × Bool)) :=
  (simulateQ (gameImplPaper sm Δ qep cfg) oa).run sb

theorem runCfg_query_bind (cfg : Config Msg) {α : Type}
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (k : (unifSpec + spec St Msg Coins C).Range t → AdversaryComp St Msg Coins C α)
    (s : GameState St Msg C) :
    runCfg sm Δ qep cfg ((liftM (OracleSpec.query t) : AdversaryComp St Msg Coins C _) >>= k) s =
      (gameImpl sm Δ qep cfg t).run s >>= fun z => runCfg sm Δ qep cfg (k z.1) z.2 := by
  simp only [runCfg, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

theorem runPaperCfg_query_bind (cfg : Config Msg) {α : Type}
    (t : (unifSpec + spec St Msg Coins C).Domain)
    (k : (unifSpec + spec St Msg Coins C).Range t → AdversaryComp St Msg Coins C α)
    (sb : GameState St Msg C × Bool) :
    runPaperCfg sm Δ qep cfg
        ((liftM (OracleSpec.query t) : AdversaryComp St Msg Coins C _) >>= k) sb =
      (gameImplPaper sm Δ qep cfg t).run sb >>= fun z => runPaperCfg sm Δ qep cfg (k z.1) z.2 := by
  simp only [runPaperCfg, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind]

theorem gameImpl_inl_run (cfg : Config Msg) (n : unifSpec.Domain) (s : GameState St Msg C) :
    (gameImpl sm Δ qep cfg (.inl n)).run s =
      (liftM (OracleSpec.query n) : ProbComp _) >>= fun u => pure (u, s) := by
  change (StateT.lift (liftM (OracleSpec.query n) : ProbComp _)).run s = _
  simp [StateT.run_lift]

theorem gameImplPaper_inl_run (cfg : Config Msg) (n : unifSpec.Domain)
    (sb : GameState St Msg C × Bool) :
    (gameImplPaper sm Δ qep cfg (.inl n)).run sb =
      (liftM (OracleSpec.query n) : ProbComp _) >>= fun u => pure (u, sb) := by
  change (StateT.lift (liftM (OracleSpec.query n) : ProbComp _)).run sb = _
  simp [StateT.run_lift]

theorem gameImplPaper_inr_inl_run (cfg : Config Msg)
    (q : (
      ((Party × Msg × Option Coins) →ₒ Option C)
      + ((Party × Msg × Msg × Option Coins) →ₒ Option C)
      + ((Party × C) →ₒ Option (RecvResult Msg))
      + ((Party × C) →ₒ Option (RecvResult Msg))).Domain)
    (sb : GameState St Msg C × Bool) :
    (gameImplPaper sm Δ qep cfg (.inr (.inl q))).run sb =
      (implBaseFour sm Δ qep cfg q).run sb.1 >>= fun p => pure (p.1, (p.2, sb.2)) := by
  change (liftBad (implBaseFour sm Δ qep cfg) q).run sb = _
  simp only [liftBad, StateT.run, map_eq_bind_pure_comp]
  rfl

theorem mem_support_liftM_run {σ α : Type} {p : ProbComp α} {s s' : σ} {a : α}
    (h : (a, s') ∈ support ((liftM p : StateT σ ProbComp α).run s)) : s' = s := by
  rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at h
  rcases h with ⟨_, _, h2⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h2
  exact h2.2

theorem bad_true_of_mem_support_runPaperCfg (cfg : Config Msg) {α : Type}
    (oa : AdversaryComp St Msg Coins C α) :
    ∀ {s : GameState St Msg C} {z : α × (GameState St Msg C × Bool)},
      z ∈ support (runPaperCfg sm Δ qep cfg oa (s, true)) →
      z.2.2 = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz
    simp only [runPaperCfg, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t k ih =>
    intro s z hz
    rw [runPaperCfg_query_bind, MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨u, s₁, b₁⟩, h₁, h₂⟩
    rcases t with n | (q | P)
    · have hsb : (s₁, b₁) = (s, true) := mem_support_liftM_run h₁
      injection hsb with _ hb₁
      subst hb₁
      exact ih u h₂
    · rw [gameImplPaper_inr_inl_run, MonadAttach.mem_support_bind] at h₁
      rcases h₁ with ⟨p, _, hp⟩
      simp only [support_pure, Set.mem_singleton_iff, Prod.ext_iff] at hp
      rcases hp with ⟨_, _, rfl⟩
      exact ih u h₂
    · change (u, (s₁, b₁)) ∈ support ((corrImplPaper P).run (s, true)) at h₁
      simp only [corrImplPaper, StateT.run_bind, StateT.run_get, pure_bind] at h₁
      split at h₁
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        rcases h₁ with ⟨_, _, rfl⟩
        exact ih u h₂
      · simp only [Bool.true_or, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.ext_iff] at h₁
        rcases h₁ with ⟨_, _, rfl⟩
        exact ih u h₂

theorem evalDist_runPaperCfg_bad_eq_one (cfg : Config Msg) {α : Type}
    (oa : AdversaryComp St Msg Coins C α) (s : GameState St Msg C) :
    𝒟[runPaperCfg sm Δ qep cfg oa (s, true) >>= fun z => pure z.2.2] {true} = 1 := by
  have heq : 𝒟[runPaperCfg sm Δ qep cfg oa (s, true) >>= fun z => pure z.2.2] =
      𝒟[(pure true : ProbComp Bool)] := by
    rw [evalDist_bind_congr_of_support _ _ (fun _ => pure true)]
    · exact OracleComp.evalDist_bind_const _ _
    · intro z hz
      have hbad := bad_true_of_mem_support_runPaperCfg sm Δ qep cfg oa hz
      simp [hbad]
  rw [heq]
  simp

/-- Output distributions of `cR` and `cM` differ on every event by at most `𝒟[cL] {true}`. -/
def CloseBy (cR cM cL : ProbComp Bool) : Prop :=
  ∀ ev : Set Bool,
    𝒟[cR] ev ≤ 𝒟[cM] ev + 𝒟[cL] {true} ∧
    𝒟[cM] ev ≤ 𝒟[cR] ev + 𝒟[cL] {true}

theorem closeBy_of_eq {cR cM cL : ProbComp Bool} (h : cR = cM) :
    CloseBy cR cM cL := by
  intro ev
  rw [h]
  exact ⟨le_self_add, le_self_add⟩

theorem closeBy_of_evalDist_eq_one {cR cM cL : ProbComp Bool}
    (h : 𝒟[cL] {true} = 1) :
    CloseBy cR cM cL := by
  intro ev
  rw [h]
  exact ⟨prob_le_one.trans le_add_self, prob_le_one.trans le_add_self⟩

theorem closeBy_bind {α : Type}
    (oa : ProbComp α) {fR fM fL : α → ProbComp Bool}
    (h : ∀ a, CloseBy (fR a) (fM a) (fL a)) :
    CloseBy (oa >>= fR) (oa >>= fM) (oa >>= fL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    intro ev
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool, ∀ S : Set Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] S =
          ∫⁻ u, 𝒟[g u] S ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g S
      rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= fR) ev, h1 (fun u => k u >>= fM) ev, h1 (fun u => k u >>= fL) {true}]
    rw [← lintegral_add_left Measurable.of_discrete,
        ← lintegral_add_left Measurable.of_discrete]
    exact ⟨lintegral_mono fun u => (ih u ev).1, lintegral_mono fun u => (ih u ev).2⟩

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem corrAllowedPaper_of_corrAllowed {s : GameState St Msg C} {P : Party}
    (h : s.corrAllowed P = true) : corrAllowedPaper s P = true := by
  unfold GameState.corrAllowed at h
  unfold corrAllowedPaper
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem closeBy_runPaperCfg (cfg : Config Msg) {α : Type}
    (oa : AdversaryComp St Msg Coins C α)
    (f : α × GameState St Msg C → ProbComp Bool)
    (s : GameState St Msg C) :
    CloseBy
      (runPaperCfg sm Δ qep cfg oa (s, false) >>= fun z => f (z.1, z.2.1))
      (runCfg sm Δ qep cfg oa s >>= f)
      (runPaperCfg sm Δ qep cfg oa (s, false) >>= fun z => pure z.2.2) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [runPaperCfg, runCfg, simulateQ_pure, StateT.run_pure, pure_bind]
    exact closeBy_of_eq rfl
  | query_bind t k ih =>
    rw [runPaperCfg_query_bind, runCfg_query_bind]
    simp only [bind_assoc]
    rcases t with n | (q | P)
    · rw [gameImplPaper_inl_run, gameImpl_inl_run]
      simp only [bind_assoc, pure_bind]
      exact closeBy_bind (liftM (OracleSpec.query n) : ProbComp _) fun u => ih u s
    · rw [gameImplPaper_inr_inl_run]
      change CloseBy
        (((implBaseFour sm Δ qep cfg q).run s >>= fun p => pure (p.1, (p.2, false))) >>= _)
        ((implBaseFour sm Δ qep cfg q).run s >>= _)
        (((implBaseFour sm Δ qep cfg q).run s >>= fun p => pure (p.1, (p.2, false))) >>= _)
      simp only [bind_assoc, pure_bind]
      exact closeBy_bind ((implBaseFour sm Δ qep cfg q).run s) fun p => ih p.1 p.2
    · change CloseBy
        ((corrImplPaper P).run (s, false) >>= _)
        ((corrImpl P).run s >>= _)
        ((corrImplPaper P).run (s, false) >>= _)
      cases hwin : s.win with
      | true =>
        simp only [corrImplPaper, corrImpl, StateT.run_bind, StateT.run_get, pure_bind,
          hwin, Bool.true_or, ↓reduceIte, StateT.run_pure]
        exact ih none s
      | false =>
        cases hca : s.corrAllowed P with
        | true =>
          have hcap : corrAllowedPaper s P = true := corrAllowedPaper_of_corrAllowed hca
          simp only [corrImplPaper, corrImpl, StateT.run_bind, StateT.run_get, pure_bind,
            hwin, hca, hcap, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            StateT.run_set, StateT.run_pure]
          exact ih (some (s.st P)) (s.afterCorr P)
        | false =>
          cases hcap : corrAllowedPaper s P with
          | false =>
            simp only [corrImplPaper, corrImpl, StateT.run_bind, StateT.run_get, pure_bind,
              hwin, hca, hcap, Bool.not_false, Bool.or_true, ↓reduceIte, StateT.run_pure]
            exact ih none s
          | true =>
            simp only [corrImplPaper, StateT.run_bind, StateT.run_get, pure_bind,
              hwin, hca, hcap, Bool.not_true, Bool.not_false, Bool.or_false, Bool.or_true,
              Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure]
            exact closeBy_of_evalDist_eq_one
              (evalDist_runPaperCfg_bad_eq_one sm Δ qep cfg (k (some (s.st P))) (s.afterCorr P))

variable [SampleableType Key]

def runPaper (cfg : Config Msg) (b : Bool) (A : Adversary St Msg Coins C) :
    ProbComp (Bool × GameState St Msg C × Bool) := do
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C × Bool) ProbComp) + oracleImplPaper sm Δ qep cfg
  (simulateQ impl A).run (initState sm k b, false)

def authGamePaper (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    ProbComp Bool := do
  let (_, s, _) ← runPaper sm Δ qep (Config.auth tStar) false A
  return (s.win && authLosingConditionsAvoided Δ tLStar tStar s)

noncomputable def authAdvantagePaper (tLStar : Option ℕ) (tStar : ℕ)
    (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[authGamePaper sm Δ qep tLStar tStar A] {true}

def authBadPaper (tStar : ℕ) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let (_, _, bad) ← runPaper sm Δ qep (Config.auth tStar) false A
  return bad

def privGamePaper (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', s, _) ← runPaper sm Δ qep (Config.priv tStar) b A
  if lastLeakGuessAdmissible Δ tLStar tStar && canon tStar s == tLStar then return (b == b')
  else $ᵗ Bool

noncomputable def privAdvantagePaper (tLStar : Option ℕ) (tStar : ℕ)
    (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[privGamePaper sm Δ qep tLStar tStar A].boolBias

def privBadPaper (tStar : ℕ) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (_, _, bad) ← runPaper sm Δ qep (Config.priv tStar) b A
  return bad

theorem closeBy_priv (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    CloseBy
      (privGamePaper sm Δ qep tLStar tStar A)
      (privGame sm Δ qep tLStar tStar A)
      (privBadPaper sm Δ qep tStar A) := by
  unfold privGamePaper privGame privBadPaper runPaper run
  simp only [bind_assoc]
  apply closeBy_bind ($ᵗ Bool)
  intro b
  apply closeBy_bind ($ᵗ Key)
  intro k
  exact closeBy_runPaperCfg sm Δ qep (Config.priv tStar) A
    (fun z =>
      if lastLeakGuessAdmissible Δ tLStar tStar && canon tStar z.2 == tLStar then pure (b == z.1)
      else $ᵗ Bool)
    (initState sm k b)

theorem closeBy_auth (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    CloseBy
      (authGamePaper sm Δ qep tLStar tStar A)
      (authGame sm Δ qep tLStar tStar A)
      (authBadPaper sm Δ qep tStar A) := by
  unfold authGamePaper authGame authBadPaper runPaper run
  simp only [bind_assoc]
  apply closeBy_bind ($ᵗ Key)
  intro k
  exact closeBy_runPaperCfg sm Δ qep (Config.auth tStar) A
    (fun z => pure (z.2.win && authLosingConditionsAvoided Δ tLStar tStar z.2))
    (initState sm k false)

theorem dev6_priv_le_proof (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    privAdvantagePaper sm Δ qep tLStar tStar A ≤
      privAdvantage sm Δ qep tLStar tStar A + 2 * 𝒟[privBadPaper sm Δ qep tStar A] {true} := by
  have hclose := closeBy_priv sm Δ qep tLStar tStar A {true}
  unfold privAdvantagePaper privAdvantage
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
      Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
      ← mul_add]
  gcongr
  have had : (𝒟[privGamePaper sm Δ qep tLStar tStar A] {true}).absDiff
      (𝒟[privGame sm Δ qep tLStar tStar A] {true}) ≤
      𝒟[privBadPaper sm Δ qep tStar A] {true} :=
    ENNReal.absDiff_le_iff.mpr hclose
  calc (𝒟[privGamePaper sm Δ qep tLStar tStar A] {true}).absDiff (1 / 2)
      ≤ (𝒟[privGame sm Δ qep tLStar tStar A] {true}).absDiff (1 / 2) +
        (𝒟[privGamePaper sm Δ qep tLStar tStar A] {true}).absDiff
          (𝒟[privGame sm Δ qep tLStar tStar A] {true}) := by
        rw [add_comm]
        exact ENNReal.absDiff_triangle _ (𝒟[privGame sm Δ qep tLStar tStar A] {true}) _
    _ ≤ (𝒟[privGame sm Δ qep tLStar tStar A] {true}).absDiff (1 / 2) +
        𝒟[privBadPaper sm Δ qep tStar A] {true} := by
        gcongr

theorem dev6_auth_le_proof (tLStar : Option ℕ) (tStar : ℕ) (A : Adversary St Msg Coins C) :
    authAdvantagePaper sm Δ qep tLStar tStar A ≤
      authAdvantage sm Δ qep tLStar tStar A + 𝒟[authBadPaper sm Δ qep tStar A] {true} :=
  (closeBy_auth sm Δ qep tLStar tStar A {true}).1

end Proof

end CryptoGames.SM.Dev6Proof
