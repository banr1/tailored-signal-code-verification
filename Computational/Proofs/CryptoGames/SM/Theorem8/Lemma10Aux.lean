/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
import VCVio.OracleComp.EvalDist.Measure

/-!
# Step lemmas for Lemma 10

**Checked by Lean.**

Defines the synchronization invariant `Sync` between `redCKAAuth` (uniform CKA key in epoch
`t_heal`) and `redPRNGAuth` (real root RNG) for ACD19 §5.3.2 Lemma 10, and proves `Sync`
preservation for each engine oracle.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.AuthL10

open Engine

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

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

def localCKA (mo : Mode) (Δcka t : ℕ) : Bool :=
  mo.tL.isNone || decide (mo.tH + Δcka ≤ t)

def knownRoot (mo : Mode) (t : ℕ) : Bool :=
  decide (mo.tStar ≤ t) || (mo.tL.isSome && decide (t < mo.tH))

def cImpl (tH : ℕ) :
    QueryImpl (unifSpec + CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp)
    + CKA.oracleImpl cka Δcka tH

def pImpl :
    QueryImpl (unifSpec + PRFPRNG.spec Sig I K) (StateT (PRFPRNG.GameState Sig I K) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (PRFPRNG.GameState Sig I K) ProbComp)
    + PRFPRNG.oracleImpl prng

abbrev EStateC (Γ T Sig SS RS M E I : Type) :=
  EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAState T I)

abbrev EStateP (Γ T Sig SS RS M E K : Type) :=
  EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)

abbrev SMSpec (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

abbrev SMComp (Γ T Sig SS RS M CCoins E : Type) :=
  OracleComp (SMSpec Γ T Sig SS RS M CCoins E)

def stepC (mo : Mode) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    ProbComp (((SMSpec Γ T Sig SS RS M CCoins E).Range q × EStateC Γ T Sig SS RS M E I) ×
      CKA.GameState Γ T) :=
  (simulateQ (cImpl cka Δcka mo.tH)
    ((implE (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esC)).run sc

def stepP (mo : Mode) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpec Γ T Sig SS RS M CCoins E).Range q × EStateP Γ T Sig SS RS M E K) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implE (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

def runL (mo : Mode) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) : ProbComp Bool := do
  let r ← (simulateQ (cImpl cka Δcka mo.tH)
    ((simulateQ (implE (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esC)).run sc
  pure (authOut (2 + Δcka) mo.policy r.1.2)

def runR (mo : Mode) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implE (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

theorem runL_pure (mo : Mode) (b' : Bool) (esC : EStateC Γ T Sig SS RS M E I)
    (sc : CKA.GameState Γ T) :
    runL cka prng fs Δcka qep mo (pure b') esC sc = pure (authOut (2 + Δcka) mo.policy esC) := by
  simp [runL, map_eq_bind_pure_comp]

theorem runR_pure (mo : Mode) (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    runR cka prng fs Δcka qep mo (pure b') esP sp = pure (authOut (2 + Δcka) mo.policy esP) := by
  simp [runR, map_eq_bind_pure_comp]

theorem runL_query_bind (mo : Mode) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    runL cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esC sc =
      stepC cka prng fs Δcka qep mo q esC sc >>= fun r =>
        runL cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runL, stepC, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem runR_query_bind (mo : Mode) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range q → SMComp Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runR cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepP cka prng fs Δcka qep mo q esP sp >>= fun r =>
        runR cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runR, stepP, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_bind_false_of_support {α : Type} (mx : ProbComp α) (f : α → ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[(pure false : ProbComp Bool)]) :
    𝒟[mx >>= f] = 𝒟[(pure false : ProbComp Bool)] := by
  rw [evalDist_bind_congr_of_support mx f (fun _ => pure false) h,
    OracleComp.evalDist_bind_const]

theorem stepC_coinsE (mo : Mode) (n : unifSpec.Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepC cka prng fs Δcka qep mo (.inl n) esC sc =
      (fun u => ((u, esC), sc)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepC, implE, coinsE, cImpl, StateT.lift, map_eq_bind_pure_comp, simulateQ_bind,
    simulateQ_query, bind_assoc]

theorem stepP_coinsE (mo : Mode) (n : unifSpec.Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepP cka prng fs Δcka qep mo (.inl n) esP sp =
      (fun u => ((u, esP), sp)) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [stepP, implE, coinsE, pImpl, StateT.lift, map_eq_bind_pure_comp, simulateQ_bind,
    simulateQ_query, bind_assoc]

theorem stepC_abort (mo : Mode) (q : (SMSpec Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) (hab : esC.abort = true) :
    ∀ r ∈ support (stepC cka prng fs Δcka qep mo q esC sc), r.1.2.abort = true := by
  intro r hr
  rcases q with n | ((((q | q) | q) | q) | P)
  · rw [stepC_coinsE] at hr
    rw [support_map] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact hab
  · simp only [stepC, implE, QueryImpl.add_apply, transmitE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepC, implE, QueryImpl.add_apply, challE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepC, implE, QueryImpl.add_apply, deliverE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepC, implE, QueryImpl.add_apply, injectE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · simp only [stepC, implE, QueryImpl.add_apply, corrE, StateT.run_bind, StateT.run_get,
      pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact hab

theorem runL_abort (mo : Mode) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true) :
    𝒟[runL cka prng fs Δcka qep mo oa esC sc] = 𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing esC sc with
  | pure b' =>
    rw [runL_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runL_query_bind]
    exact evalDist_bind_false_of_support _ _ fun r hr =>
      ih r.1.1 (stepC_abort cka prng fs Δcka qep mo q esC sc hab r hr)

theorem runL_abort_apply_true_le (mo : Mode) (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runL cka prng fs Δcka qep mo oa esC sc] {true} ≤ rhs := by
  rw [runL_abort cka prng fs Δcka qep mo oa hab]
  simp

section EraseSt

variable {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
  {g₁ g₁' : SM.GameState St₁ Msg C} {g₂ g₂' : SM.GameState St₂ Msg C}

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

theorem eraseSt_leak (h : eraseSt g₁ = eraseSt g₂) (l : ℕ) :
    eraseSt (g₁.leak l) = eraseSt (g₂.leak l) := by
  simp [eraseSt, SM.GameState.leak, eraseSt_epoch h, eraseSt_idx h, eraseSt_tL h,
    eraseSt_trans h, eraseSt_chall h, eraseSt_comp h, eraseSt_maxAcc h, eraseSt_b h,
    eraseSt_win h, eraseSt_leaks h, eraseSt_corrs h]

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

end EraseSt

/-! ## Stateless game and policy lemmas -/

theorem knownRoot_of_not_doom {St Msg C : Type} (mo : Mode) (hauth : mo.auth = true)
    (g : SM.GameState St Msg C) (P : Party)
    (hl : mo.policy.leakDoom g (g.afterCorr P) = false)
    (hc : mo.policy.corrDoom g P = false) :
    knownRoot mo (g.epoch P) = true := by
  by_contra hnk
  simp only [Bool.not_eq_true] at hnk
  have h1 : ¬ mo.tStar ≤ g.epoch P := by
    intro hle
    simp [knownRoot, hle] at hnk
  have hlt_star : g.epoch P < mo.tStar := Nat.lt_of_not_ge h1
  have hlt_tL : SM.ltOpt mo.tL (g.epoch P) = true := by
    cases htL : mo.tL with
    | none => simp [SM.ltOpt]
    | some l =>
      have h2 : ¬ g.epoch P < mo.tH := by
        intro hlt
        simp [knownRoot, htL, hlt] at hnk
      simp only [Mode.tH, htL, healEpoch] at h2
      simp only [SM.ltOpt, decide_eq_true_eq]
      omega
  let L := SM.maxOpt g.tL (max (g.epoch .A) (g.epoch .B))
  have hP_le_max : g.epoch P ≤ max (g.epoch .A) (g.epoch .B) := by
    cases P <;> simp
  have hmax_le_L : max (g.epoch .A) (g.epoch .B) ≤ L := by
    dsimp [L, SM.maxOpt]
    cases g.tL <;> simp
  have hP_le_L : g.epoch P ≤ L := le_trans hP_le_max hmax_le_L
  have hL_ltOpt : SM.ltOpt mo.tL L = true := by
    cases htL : mo.tL with
    | none => simp [SM.ltOpt]
    | some l =>
      simp only [htL, SM.ltOpt, decide_eq_true_eq] at hlt_tL ⊢
      omega
  simp only [Policy.leakDoom, Mode.policy, SM.GameState.afterCorr, SM.GameState.leak,
    List.any_cons, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hl
  by_cases hL_star : L < mo.tStar
  · have := hl.1.1
    simp [L, hL_ltOpt, hL_star] at this
  · have hstar_le_L : mo.tStar ≤ L := Nat.le_of_not_lt hL_star
    by_cases hS : g.epoch (Party.senderOf mo.tStar) < mo.tStar
    · rcases hl.2 with h2 | h2
      · simp [L, hstar_le_L] at h2
      · simp [hS] at h2
    · have hP_ne_S : P ≠ Party.senderOf mo.tStar := by
        intro heq
        rw [heq] at hlt_star
        omega
      have hP_eq_R : P = Party.receiverOf mo.tStar := by
        unfold Party.receiverOf
        cases P <;> cases hS' : Party.senderOf mo.tStar <;>
          simp_all [Party.other]
      subst hP_eq_R
      simp [Policy.corrDoom, Mode.policy, hauth, hlt_tL] at hc

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

@[simp] theorem senderOf_other (t : ℕ) : (Party.senderOf t).other = Party.receiverOf t := rfl

@[simp] theorem receiverOf_other (t : ℕ) : (Party.receiverOf t).other = Party.senderOf t :=
  Party.other_other _

theorem party_cases_of_epoch (t : ℕ) (P : Party) :
    P = Party.senderOf t ∨ P = Party.receiverOf t := by
  unfold Party.receiverOf
  cases P <;> cases Party.senderOf t <;> simp [Party.other]

theorem epoch_eq_of_synced {ep : Party → ℕ} {m : ℕ}
    (hS : ep (Party.senderOf m) = m) (hR : ep (Party.receiverOf m) = m) (P : Party) :
    ep P = m := by
  rcases party_cases_of_epoch m P with rfl | rfl
  · exact hS
  · exact hR

/-! ## Synchronization invariant `Sync` -/

/-- Synchronization invariant between `(esC, sc)` in `CKA.branch` (`b = true`) and `(esP, sp)` in
`PRFPRNG.branch` (`b = false`) while `esC.abort = false`. -/
structure Sync (mo : Mode) (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : Prop where
  abort_C : esC.abort = false
  abort_P : esP.abort = false
  b_C : sc.b = true
  b_P : sp.b = false
  g_eq : eraseSt esP.g = eraseSt esC.g
  id_C : ∀ P, (esC.g.st P).id = P
  id_P : ∀ P, (esP.g.st P).id = P
  tcur_C : ∀ P, (esC.g.st P).tcur = esC.g.epoch P
  tcur_P : ∀ P, (esP.g.st P).tcur = esC.g.epoch P
  vS_eq : ∀ P, (esP.g.st P).vS = (esC.g.st P).vS
  vR_eq : ∀ P, (esP.g.st P).vR = (esC.g.st P).vR
  Tcur_eq : ∀ P, (esP.g.st P).curCkaMsg = (esC.g.st P).curCkaMsg
  γ_C : ∀ P, (esC.g.st P).γ =
    if localCKA mo Δcka (esC.g.epoch P) then some (esP.g.st P).γ else none
  root_P : ∀ P, (esP.g.st P).root =
    if knownRoot mo (esC.g.epoch P) then some (esC.g.st P).root else none
  cka_st : ∀ P,
    (localCKA mo Δcka (esC.g.epoch P) = false ∨ localCKA mo Δcka (esC.g.epoch P.other) = false) →
    sc.st P = (esP.g.st P).γ ∧ sc.epoch P = esC.g.epoch P
  trans_inv : ∀ r ∈ esC.g.trans,
    r.ct.1.1 = r.pos.epoch ∧
    r.pos.sender.sendsIn r.pos.epoch = true ∧
    r.pos.epoch ≤ esC.g.epoch r.pos.sender ∧
    (r.pos.epoch = esC.g.epoch r.pos.sender → r.ct.1.2 = (esC.g.st r.pos.sender).curCkaMsg)
  comp_inv : ∀ pos ∈ esC.g.comp, SM.healedBy esC.g.tL (2 + Δcka) pos.epoch = false
  epoch_S : esC.g.epoch (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) =
    max (esC.g.epoch .A) (esC.g.epoch .B)
  cache_gt : ∀ t, max (esC.g.epoch .A) (esC.g.epoch .B) < t →
    esC.h.cache t = none ∧ esP.h.cache t = none
  ping_pong :
    let m := max (esC.g.epoch .A) (esC.g.epoch .B)
    let S := Party.senderOf m
    let R := Party.receiverOf m
    (esC.g.epoch R = m ∧ (esC.g.st .A).root = (esC.g.st .B).root) ∨
    (0 < m ∧ esC.g.epoch R + 1 = m ∧
      ∃ Tm Im,
        esC.h.cache m = some (Tm, Im) ∧
        (esC.g.st S).curCkaMsg = some Tm ∧
        (esC.g.st S).root = (prng.up (esC.g.st R).root Im).1 ∧
        esP.h.cache m = some (Tm, (esP.g.st S).root, (prng.up (esC.g.st R).root Im).2) ∧
        (localCKA mo Δcka (m - 1) = false → sc.lastMsg = some Tm))
  prng_before_tH :
    let m := max (esC.g.epoch .A) (esC.g.epoch .B)
    m < mo.tStar → (mo.tL.isSome && decide (m < mo.tH)) = true →
    sp.σ = (esC.g.st (Party.senderOf m)).root ∧ sp.corr = true ∧ sp.prng = false ∧ sp.prf = false
  prng_after_tH :
    let m := max (esC.g.epoch .A) (esC.g.epoch .B)
    m < mo.tStar → (mo.tL.isSome && decide (m < mo.tH)) = false →
    sp.σ = (esC.g.st (Party.senderOf m)).root ∧ sp.corr = false ∧ sp.prng = false ∧
    (m + 1 < mo.tStar → sp.prf = false)
  prng_at_tStar :
    let m := max (esC.g.epoch .A) (esC.g.epoch .B)
    let R := Party.receiverOf mo.tStar
    m = mo.tStar → esC.g.epoch R + 1 = mo.tStar →
    (mo.tL.isSome && decide (mo.tStar = mo.tH)) = false →
    sp.σ = (esC.g.st R).root ∧ sp.corr = false ∧ sp.prng = false

@[simp]
lemma run_liftH {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv T Sv SSv RSv M E HS α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    (liftH x).run es = (x.run es.h >>= fun rh => pure (rh.1, { es with h := rh.2 })) := rfl

theorem Sync.authOut_eq {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) :
    authOut (2 + Δcka) mo.policy esC = authOut (2 + Δcka) mo.policy esP := by
  simp [authOut, hS.abort_C, hS.abort_P, eraseSt_win hS.g_eq,
    eraseSt_authOK hS.g_eq]

theorem Sync.realParty_eq {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) (γ : Γ) (σ : Sig) :
    realParty (esC.g.st P) γ σ (esC.g.st P).vS (esC.g.st P).vR =
      realParty (esP.g.st P) γ σ (esP.g.st P).vS (esP.g.st P).vR := by
  simp [realParty, hS.id_C P, hS.id_P P, hS.vS_eq P, hS.vR_eq P, hS.Tcur_eq P,
    hS.tcur_C P, hS.tcur_P P]

theorem Sync.afterCorr {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) :
    Sync prng Δcka mo { esC with g := esC.g.afterCorr P } sc
      { esP with g := esP.g.afterCorr P } sp where
  abort_C := hS.abort_C
  abort_P := hS.abort_P
  b_C := hS.b_C
  b_P := hS.b_P
  g_eq := eraseSt_afterCorr hS.g_eq P
  id_C := hS.id_C
  id_P := hS.id_P
  tcur_C := hS.tcur_C
  tcur_P := hS.tcur_P
  vS_eq := hS.vS_eq
  vR_eq := hS.vR_eq
  Tcur_eq := hS.Tcur_eq
  γ_C := hS.γ_C
  root_P := hS.root_P
  cka_st := hS.cka_st
  trans_inv := hS.trans_inv
  comp_inv := comp_inv_afterCorr esC.g (2 + Δcka) (by omega) P
    (fun r hr => (hS.trans_inv r hr).2.2.1) hS.comp_inv
  epoch_S := hS.epoch_S
  cache_gt := hS.cache_gt
  ping_pong := hS.ping_pong
  prng_before_tH := hS.prng_before_tH
  prng_after_tH := hS.prng_after_tH
  prng_at_tStar := hS.prng_at_tStar

/-! ## Step lemmas for `coinsE`, `challE`, and `corrE` -/

theorem step_pure_le {U : Type}
    {mC : ProbComp ((U × EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T)}
    {mP : ProbComp ((U × EStateP Γ T Sig SS RS M E K) × PRFPRNG.GameState Sig I K)}
    {contL : U → EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool}
    {contR : U → EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool}
    {u : U} {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T}
    {esP' : EStateP Γ T Sig SS RS M E K} {sp' : PRFPRNG.GameState Sig I K}
    (hC : mC = pure ((u, esC'), sc')) (hP : mP = pure ((u, esP'), sp'))
    (hle : 𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[mC >>= fun r => contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[mP >>= fun r => contR r.1.1 r.1.2 r.2] {true} := by
  rw [hC, hP, pure_bind, pure_bind]; exact hle

theorem step_abort_le {U : Type}
    {mC : ProbComp ((Option U × EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T)}
    {mP : ProbComp Bool}
    {contL : Option U → EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool}
    {g' : Ctx (Option Γ) T Sig SS RS M E} {h' : CKAState T I} {sc' : CKA.GameState Γ T}
    (habort : ∀ {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T} (rhs : ℝ≥0∞),
      esC'.abort = true → 𝒟[contL none esC' sc'] {true} ≤ rhs)
    (hC : mC = pure ((none, ⟨g', h', true⟩), sc')) :
    𝒟[mC >>= fun r => contL r.1.1 r.1.2 r.2] {true} ≤ 𝒟[mP] {true} := by
  rw [hC, pure_bind]; exact habort _ rfl

theorem step_coinsE_le (mo : Mode) (n : unifSpec.Domain)
    (contL : (SMSpec Γ T Sig SS RS M CCoins E).Range (.inl n) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : (SMSpec Γ T Sig SS RS M CCoins E).Range (.inl n) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inl n) esC sc >>= fun r =>
        contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inl n) esP sp >>= fun r =>
        contR r.1.1 r.1.2 r.2] {true} := by
  rw [stepC_coinsE, stepP_coinsE, bind_map_left, bind_map_left]
  exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun u _ => ih u hS

theorem stepC_challE (mo : Mode) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esC sc =
      pure ((none, esC), sc) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  simp only [stepC, implE, QueryImpl.add_apply, challE, Mode.cfg, hauth, ↓reduceIte,
    SM.Config.auth, Bool.not_false, Bool.or_true, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp
  · split <;> simp

theorem stepP_challE (mo : Mode) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esP sp =
      pure ((none, esP), sp) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  simp only [stepP, implE, QueryImpl.add_apply, challE, Mode.cfg, hauth, ↓reduceIte,
    SM.Config.auth, Bool.not_false, Bool.or_true, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · simp
  · split <;> simp

theorem step_challE_le (mo : Mode) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esC sc >>= fun r =>
        contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esP sp >>= fun r =>
        contR r.1.1 r.1.2 r.2] {true} := by
  rw [stepC_challE cka prng fs Δcka qep mo hauth, stepP_challE cka prng fs Δcka qep mo hauth,
    pure_bind, pure_bind]
  exact ih none hS

theorem step_corrE_le (mo : Mode) (hauth : mo.auth = true) (P : Party)
    (contL : Option (PartyState Γ T Sig SS RS) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (PartyState Γ T Sig SS RS) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (habort : ∀ {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T} (rhs : ℝ≥0∞),
      esC'.abort = true → 𝒟[contL none esC' sc'] {true} ≤ rhs)
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc >>= fun r =>
        contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inr P)) esP sp >>= fun r =>
        contR r.1.1 r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hca : esP.g.corrAllowed P = esC.g.corrAllowed P := eraseSt_corrAllowed hS.g_eq P
  by_cases hguard : esC.g.win || !esC.g.corrAllowed P
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    exact step_pure_le
      (by simp [-Prod.mk.injEq, stepC, implE, corrE, hS.abort_C, hguard, StateT.run_pure])
      (by simp [-Prod.mk.injEq, stepP, implE, corrE, hS.abort_P, hwin, hca, hguard, StateT.run_pure])
      (ih none hS)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hld : mo.policy.leakDoom esP.g (esP.g.afterCorr P) =
        mo.policy.leakDoom esC.g (esC.g.afterCorr P) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_afterCorr hS.g_eq P) mo.policy
    have hcd : mo.policy.corrDoom esP.g P = mo.policy.corrDoom esC.g P :=
      eraseSt_corrDoom hS.g_eq mo.policy P
    by_cases hdoom : mo.policy.leakDoom esC.g (esC.g.afterCorr P) || mo.policy.corrDoom esC.g P
    · simp only [Bool.or_eq_true] at hdoom
      exact step_abort_le habort
        (by simp [-Prod.mk.injEq, stepC, implE, corrE, abortE, hS.abort_C, hguard, hdoom, StateT.run_modify]; rfl)
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hdoom
      have hkr : knownRoot mo (esC.g.epoch P) = true :=
        knownRoot_of_not_doom mo hauth esC.g P hdoom.1 hdoom.2
      have hrootP : (esP.g.st P).root = some (esC.g.st P).root := by
        rw [hS.root_P P, hkr]
        rfl
      have hP : stepP cka prng fs Δcka qep mo (.inr (.inr P)) esP sp =
          pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
            (esC.g.st P).vS (esC.g.st P).vR), { esP with g := esP.g.afterCorr P }), sp) := by
        simp [stepP, implE, corrE, liftH, hooksPRNG, hS.abort_P, hwin, hca, hguard,
          hld, hcd, hdoom.1, hdoom.2, hrootP, StateT.run_modify, hS.realParty_eq P]
      by_cases hloc : localCKA mo Δcka (esC.g.epoch P)
      · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
          rw [hS.γ_C P, hloc]
          rfl
        exact step_pure_le
          (by simp [-Prod.mk.injEq, stepC, implE, corrE, liftH, hooksCKA, hS.abort_C, hguard, hdoom.1, hdoom.2,
            hγC, StateT.run_modify])
          hP (ih _ (hS.afterCorr P))
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esC.g.st P).γ = none := by
          rw [hS.γ_C P, hloc]
          rfl
        have hcka := (hS.cka_st P (Or.inl hloc)).1
        by_cases hcorr : sc.allowCorr mo.tH || sc.finished Δcka mo.tH P
        · simp only [Bool.or_eq_true] at hcorr
          exact step_pure_le
            (by simp [-Prod.mk.injEq, stepC, implE, corrE, hooksCKA, liftC, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, hcka, StateT.lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify])
            hP (ih _ (hS.afterCorr P))
        · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
          exact step_abort_le habort
            (by simp [-Prod.mk.injEq, stepC, implE, corrE, abortE, hooksCKA, liftC, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, StateT.lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]; rfl)

theorem eq_receiverOf_of_ne_senderOf {P : Party} {t : ℕ} (h : P ≠ Party.senderOf t) :
    P = Party.receiverOf t := by
  unfold Party.receiverOf
  cases P <;> cases hS : Party.senderOf t <;> simp_all [Party.other]

lemma estate_mk_abort_false {VPt M C HS : Type} {es : EState VPt M C HS}
    (h : es.abort = false) :
    ({ g := es.g, h := es.h, abort := false } : EState VPt M C HS) = es := by
  cases es
  simp_all

@[simp]
lemma hooksCKA_fsRecv (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t : ℕ)
    (rs : RS) (h : Header T) (e : E) (rec : Option (SM.Record M (Header T × E))) :
    (hooksCKA cka prng fs Δcka mo).fsRecv ctx P t rs h e rec =
      pure (some (fs.receive rs h e)) := rfl

@[simp]
lemma hooksPRNG_fsRecv (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t : ℕ)
    (rs : RS) (h : Header T) (e : E) (rec : Option (SM.Record M (Header T × E))) :
    (hooksPRNG cka prng fs mo).fsRecv ctx P t rs h e rec =
      pure (some (fs.receive rs h e)) := rfl

@[simp]
lemma hooksPRNG_commit (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : PartyState Γ T (Option Sig) SS RS) :
    (hooksPRNG cka prng fs mo).commit ctx P old new = pure (some new) := rfl

theorem Sync.sp_at_recv_tStar {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party)
    (htStar : esC.g.epoch P + 1 = mo.tStar)
    (hloc : localCKA mo Δcka (esC.g.epoch P) = true) :
    sp.σ = (esC.g.st P).root ∧ sp.corr = false ∧ sp.prng = false := by
  have hnot_lt : (mo.tL.isSome && decide (esC.g.epoch P < mo.tH)) = false := by
    simp only [localCKA] at hloc
    cases htL : mo.tL <;> simp_all [Mode.tH]
    omega
  rcases hS.ping_pong with ⟨hR, hrootAB⟩ | ⟨hm0, hR, _⟩
  · have hepP : esC.g.epoch P = max (esC.g.epoch .A) (esC.g.epoch .B) :=
      epoch_eq_of_synced hS.epoch_S hR P
    have hm_lt : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
    have hnot_lt' : (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = false := by
      rwa [← hepP]
    obtain ⟨hσ, hcorr, hprng, _⟩ := hS.prng_after_tH hm_lt hnot_lt'
    refine ⟨?_, hcorr, hprng⟩
    rw [hσ]
    cases P <;> cases Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) <;>
      first | rfl | exact hrootAB | exact hrootAB.symm
  · have hS_ep := hS.epoch_S
    by_cases hP : P = Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))
    · have hepP : esC.g.epoch P = max (esC.g.epoch .A) (esC.g.epoch .B) := by
        rw [hP, hS_ep]
      have hm_lt : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
      have hnot_lt' : (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = false := by
        rwa [← hepP]
      obtain ⟨hσ, hcorr, hprng, _⟩ := hS.prng_after_tH hm_lt hnot_lt'
      rw [← hP] at hσ
      exact ⟨hσ, hcorr, hprng⟩
    · have hPR : P = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) :=
        eq_receiverOf_of_ne_senderOf hP
      have hm_eq : max (esC.g.epoch .A) (esC.g.epoch .B) = mo.tStar := by
        rw [← hPR] at hR
        omega
      have hnot_eq : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = false := by
        simp only [localCKA] at hloc
        cases htL : mo.tL <;> simp_all [Mode.tH]
        omega
      have hR' : esC.g.epoch (Party.receiverOf mo.tStar) + 1 = mo.tStar := by
        simpa [hm_eq] using hR
      obtain ⟨hσ, hcorr, hprng⟩ := hS.prng_at_tStar hm_eq hR' hnot_eq
      have hPR' : P = Party.receiverOf mo.tStar := by simpa [hm_eq] using hPR
      rw [← hPR'] at hσ
      exact ⟨hσ, hcorr, hprng⟩

theorem Sync.set_prf {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (p : Bool)
    (hp : p = sp.prf ∨ (sp.corr = false ∧ max (esC.g.epoch .A) (esC.g.epoch .B) + 1 ≥ mo.tStar)) :
    Sync prng Δcka mo esC sc esP { sp with prf := p } where
  abort_C := hS.abort_C
  abort_P := hS.abort_P
  b_C := hS.b_C
  b_P := hS.b_P
  g_eq := hS.g_eq
  id_C := hS.id_C
  id_P := hS.id_P
  tcur_C := hS.tcur_C
  tcur_P := hS.tcur_P
  vS_eq := hS.vS_eq
  vR_eq := hS.vR_eq
  Tcur_eq := hS.Tcur_eq
  γ_C := hS.γ_C
  root_P := hS.root_P
  cka_st := hS.cka_st
  trans_inv := hS.trans_inv
  comp_inv := hS.comp_inv
  epoch_S := hS.epoch_S
  cache_gt := hS.cache_gt
  ping_pong := hS.ping_pong
  prng_before_tH := fun hm hlt => by
    obtain ⟨h1, h2, h3, h4⟩ := hS.prng_before_tH hm hlt
    refine ⟨h1, h2, h3, ?_⟩
    rcases hp with rfl | ⟨hcorr, _⟩
    · exact h4
    · simp [hcorr] at h2
  prng_after_tH := fun hm hlt => by
    obtain ⟨h1, h2, h3, h4⟩ := hS.prng_after_tH hm hlt
    refine ⟨h1, h2, h3, fun hm1 => ?_⟩
    rcases hp with rfl | ⟨_, hge⟩
    · exact h4 hm1
    · omega
  prng_at_tStar := hS.prng_at_tStar

theorem Sync.set_win_prf {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (w : Bool) (p : Bool)
    (hp : p = sp.prf ∨ (sp.corr = false ∧ max (esC.g.epoch .A) (esC.g.epoch .B) + 1 ≥ mo.tStar)) :
    Sync prng Δcka mo { esC with g := { esC.g with win := w } } sc
      { esP with g := { esP.g with win := w } } { sp with prf := p } where
  abort_C := hS.abort_C
  abort_P := hS.abort_P
  b_C := hS.b_C
  b_P := hS.b_P
  g_eq := by
    simp [eraseSt, eraseSt_epoch hS.g_eq, eraseSt_idx hS.g_eq, eraseSt_tL hS.g_eq,
      eraseSt_trans hS.g_eq, eraseSt_chall hS.g_eq, eraseSt_comp hS.g_eq,
      eraseSt_maxAcc hS.g_eq, eraseSt_b hS.g_eq, eraseSt_leaks hS.g_eq,
      eraseSt_corrs hS.g_eq]
  id_C := hS.id_C
  id_P := hS.id_P
  tcur_C := hS.tcur_C
  tcur_P := hS.tcur_P
  vS_eq := hS.vS_eq
  vR_eq := hS.vR_eq
  Tcur_eq := hS.Tcur_eq
  γ_C := hS.γ_C
  root_P := hS.root_P
  cka_st := hS.cka_st
  trans_inv := hS.trans_inv
  comp_inv := hS.comp_inv
  epoch_S := hS.epoch_S
  cache_gt := hS.cache_gt
  ping_pong := hS.ping_pong
  prng_before_tH := fun hm hlt => by
    obtain ⟨h1, h2, h3, h4⟩ := hS.prng_before_tH hm hlt
    refine ⟨h1, h2, h3, ?_⟩
    rcases hp with rfl | ⟨hcorr, _⟩
    · exact h4
    · simp [hcorr] at h2
  prng_after_tH := by
    dsimp only
    intro hm hlt
    obtain ⟨h1, h2, h3, h4⟩ := hS.prng_after_tH hm hlt
    refine ⟨h1, h2, h3, fun hm1 => ?_⟩
    rcases hp with rfl | ⟨_, hge⟩
    · exact h4 hm1
    · omega
  prng_at_tStar := hS.prng_at_tStar

lemma accept_epoch_of_le {St Msg C : Type} (g : SM.GameState St Msg C) (P : Party) (st' : St)
    (pos : SM.Pos) (h : pos.epoch ≤ g.epoch P) :
    (g.accept P st' pos).epoch = g.epoch := by
  ext Q
  by_cases hQP : Q = P
  · subst hQP
    simp [SM.GameState.accept, SM.GameState.delete, Nat.max_eq_left h]
  · simp [SM.GameState.accept, SM.GameState.delete, hQP]

lemma accept_st {St Msg C : Type} (g : SM.GameState St Msg C) (P : Party) (st' : St)
    (pos : SM.Pos) :
    (g.accept P st' pos).st = Function.update g.st P st' := rfl

@[simp]
lemma accept_update_self {St Msg C : Type} (g : SM.GameState St Msg C) (P : Party) (st' : St)
    (pos : SM.Pos) :
    { g.accept P st' pos with st := Function.update (g.accept P st' pos).st P st' } =
      g.accept P st' pos := by
  simp [SM.GameState.accept]

theorem Sync.accept_old {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) (vR' : ℕ → Option RS) (pos : SM.Pos)
    (hle : pos.epoch ≤ esC.g.epoch P) :
    Sync prng Δcka mo
      { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos } sc
      { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos } sp where
  abort_C := hS.abort_C
  abort_P := hS.abort_P
  b_C := hS.b_C
  b_P := hS.b_P
  g_eq := eraseSt_accept hS.g_eq P _ _ pos
  id_C := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.id_C]
    · simp [accept_st, hQP, hS.id_C]
  id_P := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.id_P]
    · simp [accept_st, hQP, hS.id_P]
  tcur_C := fun Q => by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.tcur_C]
    · simp [accept_st, hQP, hS.tcur_C]
  tcur_P := fun Q => by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.tcur_P]
    · simp [accept_st, hQP, hS.tcur_P]
  vS_eq := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.vS_eq]
    · simp [accept_st, hQP, hS.vS_eq]
  vR_eq := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st]
    · simp [accept_st, hQP, hS.vR_eq]
  Tcur_eq := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.Tcur_eq]
    · simp [accept_st, hQP, hS.Tcur_eq]
  γ_C := fun Q => by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.γ_C]
    · simp [accept_st, hQP, hS.γ_C]
  root_P := fun Q => by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.root_P]
    · simp [accept_st, hQP, hS.root_P]
  cka_st := fun Q => by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    by_cases hQP : Q = P
    · subst hQP; simpa [accept_st] using hS.cka_st Q
    · simpa [accept_st, hQP] using hS.cka_st Q
  trans_inv := fun r hr => by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hS.trans_inv r hr.1
    refine ⟨h1, h2, h3, fun hep => ?_⟩
    rw [h4 hep]
    by_cases hP : r.pos.sender = P
    · subst hP; simp [accept_st]
    · simp [accept_st, hP]
  comp_inv := comp_inv_accept esC.g (2 + Δcka) P _ pos hS.comp_inv
  epoch_S := by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    exact hS.epoch_S
  cache_gt := by
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle]
    exact hS.cache_gt
  ping_pong := by
    have hst_root : ∀ Q, ((esC.g.accept P { esC.g.st P with vR := vR' } pos).st Q).root =
        (esC.g.st Q).root := fun Q => by
      by_cases hQP : Q = P <;> simp [accept_st, hQP]
    have hst_Tcur : ∀ Q, ((esC.g.accept P { esC.g.st P with vR := vR' } pos).st Q).curCkaMsg =
        (esC.g.st Q).curCkaMsg := fun Q => by
      by_cases hQP : Q = P <;> simp [accept_st, hQP]
    have hstP_root : ∀ Q, ((esP.g.accept P { esP.g.st P with vR := vR' } pos).st Q).root =
        (esP.g.st Q).root := fun Q => by
      by_cases hQP : Q = P <;> simp [accept_st, hQP]
    dsimp only
    simp only [accept_epoch_of_le _ _ _ _ hle, hst_root, hst_Tcur, hstP_root]
    exact hS.ping_pong
  prng_before_tH := by
    have hst_root : ∀ Q, ((esC.g.accept P { esC.g.st P with vR := vR' } pos).st Q).root =
        (esC.g.st Q).root := fun Q => by
      by_cases hQP : Q = P <;> simp [accept_st, hQP]
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle, hst_root]
    exact hS.prng_before_tH
  prng_after_tH := by
    have hst_root : ∀ Q, ((esC.g.accept P { esC.g.st P with vR := vR' } pos).st Q).root =
        (esC.g.st Q).root := fun Q => by
      by_cases hQP : Q = P <;> simp [accept_st, hQP]
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle, hst_root]
    exact hS.prng_after_tH
  prng_at_tStar := by
    have hst_root : ∀ Q, ((esC.g.accept P { esC.g.st P with vR := vR' } pos).st Q).root =
        (esC.g.st Q).root := fun Q => by
      by_cases hQP : Q = P <;> simp [accept_st, hQP]
    dsimp only
    rw [accept_epoch_of_le _ _ _ _ hle, hst_root]
    exact hS.prng_at_tStar

theorem Sync.cache_at_succ {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) (t : ℕ)
    (ht : t = esC.g.epoch P + 1) :
    (esC.h.cache t = none ∧ esP.h.cache t = none) ∨
      ∃ Tm Im,
        esC.h.cache t = some (Tm, Im) ∧
        esP.h.cache t = some (Tm, (esP.g.st (Party.senderOf t)).root,
          (prng.up (esC.g.st P).root Im).2) := by
  by_cases hgt : max (esC.g.epoch .A) (esC.g.epoch .B) < t
  · exact Or.inl (hS.cache_gt t hgt)
  · rcases hS.ping_pong with ⟨hR, _⟩ | ⟨hm0, hR, Tm, Im, hcC, _, _, hcP, _⟩
    · have hepP : esC.g.epoch P = max (esC.g.epoch .A) (esC.g.epoch .B) :=
        epoch_eq_of_synced hS.epoch_S hR P
      omega
    · have hS_ep := hS.epoch_S
      have hne : P ≠ Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
        intro hPS
        rw [hPS, hS_ep] at ht
        omega
      have hPR : P = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) :=
        eq_receiverOf_of_ne_senderOf hne
      have htm : t = max (esC.g.epoch .A) (esC.g.epoch .B) := by
        rw [hPR] at ht
        omega
      right
      refine ⟨Tm, Im, ?_, ?_⟩
      · simpa [htm] using hcC
      · rw [htm, hPR]
        exact hcP

lemma startRecv_CKA_unhonest (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (t : ℕ) (γv : Option Γ) (σ : Sig) (Tn : T) (hc : CKAState T I)
    (h : ∀ Im, hc.cache t ≠ some (Tn, Im)) :
    ((hooksCKA cka prng fs Δcka mo).startRecv ctx P t γv σ Tn).run hc =
      (if mo.auth && t = mo.tStar then
        match γv with
        | some γ =>
          let k := cka.receive γ Tn
          let p := prng.up σ k.2
          pure (some (some (some k.1, p.1, fs.initReceiver p.2)), hc)
        | none => pure (none, hc)
      else pure (some none, hc)) := by
  rcases hcache : hc.cache t with _ | ⟨Tc, Ik⟩
  · simp only [hooksCKA, hcache, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · split <;> rfl
    · rfl
  · have hne : Tc ≠ Tn := fun heq => h Ik (by rw [← heq, hcache])
    simp only [hooksCKA, hcache, hne, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · split <;> rfl
    · rfl

lemma startRecv_PRNG_unhonest (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (t : ℕ) (γ : Γ) (σv : Option Sig) (Tn : T) (hp : PRNGState T Sig K)
    (h : ∀ σc k, hp.cache t ≠ some (Tn, σc, k)) :
    ((hooksPRNG cka prng fs mo).startRecv ctx P t γ σv Tn).run hp =
      (if mo.auth && t = mo.tStar then
        let kk := cka.receive γ Tn
        ((liftP (PRFPRNG.challPrfQuery kk.2)).run hp >>= fun r =>
          match r.1 with
          | none => pure (none, r.2)
          | some (σ', k') => pure (some (some (kk.1, some σ', fs.initReceiver k')), r.2))
      else pure (some none, hp)) := by
  rcases hcache : hp.cache t with _ | ⟨Tc, σc, k⟩
  · simp only [hooksPRNG, hcache, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_bind]
      congr 1; ext r; rcases r with ⟨_ | ⟨σ', k'⟩, hp'⟩ <;> rfl
    · rfl
  · have hne : Tc ≠ Tn := fun heq => h σc k (by rw [← heq, hcache])
    simp only [hooksPRNG, hcache, hne, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_bind]
      congr 1; ext r; rcases r with ⟨_ | ⟨σ', k'⟩, hp'⟩ <;> rfl
    · rfl

/-! ## Step lemma for `injectE` -/

theorem step_injectE_le (mo : Mode) (hauth : mo.auth = true)
    (q : Party × (Header T × E))
    (contL : Option (SM.RecvResult M) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (SM.RecvResult M) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (habort : ∀ {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T} (rhs : ℝ≥0∞),
      esC'.abort = true → 𝒟[contL none esC' sc'] {true} ≤ rhs)
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inr q))) esC sc >>= fun r =>
        contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inr q))) esP sp >>= fun r =>
        contR r.1.1 r.1.2 r.2] {true} := by
  rcases q with ⟨P, c⟩
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hsafe : esP.g.safeInj (2 + Δcka) = esC.g.safeInj (2 + Δcka) :=
    eraseSt_safeInj hS.g_eq (2 + Δcka)
  have hesC_eq := estate_mk_abort_false hS.abort_C
  have hesP_eq := estate_mk_abort_false hS.abort_P
  by_cases hguard : esC.g.win || (esC.g.inTransit P.other c).isSome || !esC.g.safeInj (2 + Δcka)
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    exact step_pure_le
      (by simp [-Prod.mk.injEq, stepC, implE, injectE, hS.abort_C, hguard, StateT.run_pure])
      (by simp [-Prod.mk.injEq, stepP, implE, injectE, hS.abort_P, hwin, htrans, hsafe, hguard, StateT.run_pure])
      (ih none hS)
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨⟨hwin0, htrans0⟩, hsafe0⟩
    by_cases hsend : P.sendsIn c.1.1 || decide (esC.g.epoch P + 1 < c.1.1)
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hsend
      exact step_pure_le
        (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
          hS.id_C P, hS.tcur_C P, hsend, StateT.run_pure, hesC_eq])
        (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0,
          hS.id_P P, hS.tcur_P P, hsend, StateT.run_pure, hesP_eq])
        (ih (some .rejected) hS)
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hsend
      rcases hsend with ⟨hsend0, hle⟩
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      ·
        have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        have htriv_false : ∀ i', esC.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false := by
          intro i'
          exact trivial_false_of_safeInj esC.g (2 + Δcka) P i' hsafe0 hS.comp_inv
        have htrivP_false : ∀ i', esP.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false := by
          intro i'
          rw [eraseSt_trivial hS.g_eq]
          exact htriv_false i'
        cases hTn : c.1.2 with
        | none =>
          exact step_pure_le
            (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
              hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, StateT.run_pure, hesC_eq])
            (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0,
              hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn, StateT.run_pure, hesP_eq])
            (ih (some .rejected) hS)
        | some Tn =>
          have hafter : ∀ (γC' : Option Γ) (σC' : Sig) (γP' : Γ) (σP' : Option Sig) (rs : RS)
              (sp' : PRFPRNG.GameState Sig I K)
              (hsp' : sp'.prf = sp.prf ∨
                (sp.corr = false ∧ max (esC.g.epoch .A) (esC.g.epoch .B) + 1 ≥ mo.tStar))
              (hsp_eq : sp' = { sp with prf := sp'.prf })
              (hsC : ((hooksCKA cka prng fs Δcka mo).startRecv esC.g P (esC.g.epoch P + 1)
                (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                pure (some (some (γC', σC', rs)), esC.h))
              (hsP : (simulateQ (pImpl prng)
                (((hooksPRNG cka prng fs mo).startRecv esP.g P (esC.g.epoch P + 1)
                  (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h)).run sp =
                pure ((some (some (γP', σP', rs)), esP.h), sp')),
              𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc >>= fun r =>
                  contL r.1.1 r.1.2 r.2] {true} ≤
                𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp >>= fun r =>
                  contR r.1.1 r.1.2 r.2] {true} := by
            intro γC' σC' γP' σP' rs sp' hsp' hsp_eq hsC hsP
            have hS' : Sync prng Δcka mo esC sc esP sp' := by
              rw [hsp_eq]
              exact hS.set_prf sp'.prf hsp'
            rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨v', i', m'⟩
            · exact step_pure_le
                (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesC_eq])
                (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                  hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                  StateT.run_bind, simulateQ_bind, hsP, hfs, StateT.run_pure, simulateQ_pure,
                  hesP_eq])
                (ih (some .rejected) hS')
            · by_cases hqep : qep + 1 < esC.g.epoch P + 1
              · exact step_pure_le
                  (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                    hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep,
                    StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesC_eq])
                  (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                    hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                    StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, StateT.run_pure,
                    simulateQ_pure, hesP_eq])
                  (ih (some .rejected) hS')
              · have htrivC := htriv_false i'
                have htrivP := htrivP_false i'
                by_cases hinj : (mo.cfg (M := M)).injectFull (esC.g.epoch P + 1)
                · exact step_pure_le
                    (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep, htrivC, hinj,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_bind,
                      simulateQ_pure])
                    (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                      hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                      StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, htrivP, hinj, ← hsp_eq,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure])
                    (ih (some .rejected) (hsp_eq ▸ hS.set_win_prf true sp'.prf hsp'))
                · simp only [Bool.not_eq_true] at hinj
                  exact step_pure_le
                    (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep, htrivC, hinj,
                      StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesC_eq])
                    (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                      hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                      StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, htrivP, hinj,
                      StateT.run_pure, simulateQ_pure, hesP_eq])
                    (ih (some .rejected) hS')
          have hcache := hS.cache_at_succ P c.1.1 hnew
          have hnone :
              (∀ Im, esC.h.cache (esC.g.epoch P + 1) ≠ some (Tn, Im)) →
              (∀ σc k, esP.h.cache (esC.g.epoch P + 1) ≠ some (Tn, σc, k)) →
              𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc >>= fun r =>
                  contL r.1.1 r.1.2 r.2] {true} ≤
                𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp >>= fun r =>
                  contR r.1.1 r.1.2 r.2] {true} := by
            intro hcC_none hcP_none
            have hsC_un := startRecv_CKA_unhonest cka prng fs Δcka mo esC.g P (esC.g.epoch P + 1)
              (esC.g.st P).γ (esC.g.st P).root Tn esC.h hcC_none
            have hsP_un := startRecv_PRNG_unhonest cka prng fs mo esP.g P (esC.g.epoch P + 1)
              (esP.g.st P).γ (esP.g.st P).root Tn esP.h hcP_none
            by_cases htStar : esC.g.epoch P + 1 = mo.tStar
            · by_cases hloc : localCKA mo Δcka (esC.g.epoch P)
              · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
                  simp [hS.γ_C P, hloc]
                obtain ⟨hσ, hcorr0, hprng0⟩ := hS.sp_at_recv_tStar P htStar hloc
                have hm_ge : max (esC.g.epoch .A) (esC.g.epoch .B) + 1 ≥ mo.tStar := by
                  have : esC.g.epoch P ≤ max (esC.g.epoch .A) (esC.g.epoch .B) := by
                    cases P <;> simp
                  omega
                let kk := cka.receive (esP.g.st P).γ Tn
                let p := prng.up (esC.g.st P).root kk.2
                refine hafter (some kk.1) p.1 kk.1 (some p.1) (fs.initReceiver p.2)
                  { sp with prf := true } (Or.inr ⟨hcorr0, hm_ge⟩) rfl ?_ ?_
                · rw [hsC_un]
                  simp [hauth, htStar, hγC, kk, p]
                · rw [hsP_un]
                  simp [hauth, htStar, liftP, PRFPRNG.challPrfQuery, pImpl,
                    PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl, hcorr0, hprng0, hS.b_P, hσ, kk, p,
                    StateT.lift, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
                    StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set]
              · simp only [Bool.not_eq_true] at hloc
                have hγC : (esC.g.st P).γ = none := by
                  simp [hS.γ_C P, hloc]
                have hsC_abort : ((hooksCKA cka prng fs Δcka mo).startRecv esC.g P
                    (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                    pure (none, esC.h) := by
                  rw [hsC_un]
                  simp [hauth, htStar, hγC]
                exact step_abort_le habort
                  (by simp [-Prod.mk.injEq, stepC, implE, injectE, abortE, vRecv, hS.abort_C, hwin0, htrans0,
                    hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC_abort,
                    StateT.run_bind, StateT.run_pure, StateT.run_modify,
                    simulateQ_bind, simulateQ_pure]; rfl)
            · have hsC_rej : ((hooksCKA cka prng fs Δcka mo).startRecv esC.g P
                  (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                  pure (some none, esC.h) := by
                rw [hsC_un]
                simp [hauth, htStar]
              have hsP_rej : ((hooksPRNG cka prng fs mo).startRecv esP.g P
                  (esC.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root Tn).run esP.h =
                  pure (some none, esP.h) := by
                rw [hsP_un]
                simp [hauth, htStar]
              exact step_pure_le
                (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC_rej,
                  StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesC_eq])
                (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                  hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn, hsP_rej,
                  StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesP_eq])
                (ih (some .rejected) hS)
          rcases hcache with ⟨hcC, hcP⟩ | ⟨Tm, Im, hcC, hcP⟩
          · rw [hnew] at hcC hcP
            exact hnone (by simp [hcC]) (by simp [hcP])
          · rw [hnew] at hcC hcP
            by_cases hTm : Tm = Tn
            · subst hTm
              let p := prng.up (esC.g.st P).root Im
              refine hafter ((esC.g.st P).γ.map fun γ => (cka.receive γ Tm).1) p.1
                (cka.receive (esP.g.st P).γ Tm).1 (esP.g.st (Party.senderOf (esC.g.epoch P + 1))).root
                (fs.initReceiver p.2) sp (Or.inl rfl) rfl ?_ ?_
              · simp [hooksCKA, hcC, p, StateT.run_bind, StateT.run_get, StateT.run_pure]
              · simp [hooksPRNG, hcP, p, StateT.run_bind, StateT.run_get, StateT.run_pure,
                  simulateQ_pure]
            · exact hnone (by simp [hcC, hTm]) (by simp [hcP, hTm])
      ·
        have hle_ep : c.1.1 ≤ esC.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := by rw [hS.vR_eq P]
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          exact step_pure_le
            (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
              hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_pure, hesC_eq])
            (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0,
              hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, StateT.run_pure,
              hesP_eq])
            (ih (some .rejected) hS)
        | some v =>
          rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · exact step_pure_le
              (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, StateT.run_pure, hesC_eq])
              (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR,
                hfs, StateT.run_pure, hesP_eq])
              (ih (some .rejected) hS)
          · by_cases hqep : qep + 1 < c.1.1
            · exact step_pure_le
                (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, StateT.run_pure,
                  hesC_eq])
                (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                  hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR,
                  hfs, hqep, StateT.run_pure, hesP_eq])
                (ih (some .rejected) hS)
            · let pos : SM.Pos := ⟨P.other, c.1.1, i'⟩
              have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                eraseSt_trivial hS.g_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
                have hvR'_eq : Function.update (esP.g.st P).vR c.1.1 (some v') = vR' := by
                  simp [vR', hS.vR_eq P]
                exact step_pure_le
                  (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, commitE, hooksCKA, hS.abort_C, hwin0,
                    htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                    htriv, pos, vR', StateT.run_pure, StateT.run_modify]; rfl)
                  (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, commitE, hS.abort_P, hwin,
                    htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle,
                    hnew, hvRP, hvR, hfs, hqep, htriv_eq, htriv, pos, hvR'_eq,
                    StateT.run_pure, StateT.run_modify])
                  (ih _ (hS.accept_old P vR' pos hle_ep))
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (mo.cfg (M := M)).injectFull c.1.1
                · exact step_pure_le
                    (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0,
                      hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                      htriv, hinj, pos, StateT.run_pure, StateT.run_modify])
                    (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans,
                      hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                      hvRP, hvR, hfs, hqep, htriv_eq, htriv, hinj, pos,
                      StateT.run_pure, StateT.run_modify])
                    (ih (some .rejected) (hS.set_win_prf true sp.prf (Or.inl rfl)))
                · simp only [Bool.not_eq_true] at hinj
                  exact step_pure_le
                    (by simp [-Prod.mk.injEq, stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0,
                      hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                      htriv, hinj, pos, StateT.run_pure, hesC_eq])
                    (by simp [-Prod.mk.injEq, stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans,
                      hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                      hvRP, hvR, hfs, hqep, htriv_eq, htriv, hinj, pos, StateT.run_pure, hesP_eq])
                    (ih (some .rejected) hS)

/-! ## Step lemma for `deliverE` -/

theorem party_eq_or_eq_other (Q P : Party) : Q = P ∨ Q = P.other := by
  cases Q <;> cases P <;> simp [Party.other]

@[simp]
lemma hooksCKA_commit (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (old new : VP (Option Γ) T Sig SS RS) :
    (hooksCKA cka prng fs Δcka mo).commit ctx P old new =
      (if old.tcur < new.tcur && old.γ.isNone then do
        match ← liftC (CKA.receiveQuery P) with
        | none => return none
        | some () =>
          if mo.tH + Δcka ≤ new.tcur then
            match ← liftC (CKA.corrQuery P) with
            | none => return none
            | some γ => return some { new with γ := some γ }
          else return some new
      else return some new) := rfl

lemma hooksCKA_startRecv_honest (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party)
    (t : ℕ) (γv : Option Γ) (σ : Sig) (Tm : T) (Im : I) (hc : CKAState T I)
    (hcache : hc.cache t = some (Tm, Im)) :
    ((hooksCKA cka prng fs Δcka mo).startRecv ctx P t γv σ Tm).run hc =
      pure (some (some (γv.map fun γ => (cka.receive γ Tm).1,
        (prng.up σ Im).1, fs.initReceiver (prng.up σ Im).2)), hc) := by
  simp [hooksCKA, hcache, StateT.run_bind, StateT.run_get, StateT.run_pure]

theorem inTransit_some_props {St Msg C : Type} [DecidableEq C]
    {g : SM.GameState St Msg C} {Q : Party} {c : C} {r : SM.Record Msg C}
    (h : g.inTransit Q c = some r) :
    r ∈ g.trans ∧ r.pos.sender = Q ∧ r.ct = c := by
  unfold SM.GameState.inTransit at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨hmem, hp.1, hp.2⟩

theorem accept_epoch_of_succ {St Msg C : Type} [DecidableEq C]
    (g : SM.GameState St Msg C) (P : Party) (st' : St) (pos : SM.Pos)
    (hpos : pos.epoch = g.epoch P + 1) (hother : g.epoch P.other = g.epoch P + 1) :
    (g.accept P st' pos).epoch = fun _ => g.epoch P + 1 := by
  ext Q
  simp only [SM.GameState.accept, SM.GameState.delete, Function.update_apply]
  rcases party_eq_or_eq_other Q P with hQ | hQ
  · subst hQ; simp [hpos]
  · subst hQ; simp [Party.other_ne, hother]

@[simp]
theorem accept_update_st_self {St Msg C : Type} [DecidableEq C]
    (g : SM.GameState St Msg C) (P : Party) (st₁ st₂ : St) (pos : SM.Pos) :
    { (g.accept P st₁ pos) with st := Function.update (g.accept P st₁ pos).st P st₂ } =
      g.accept P st₂ pos := by
  simp [SM.GameState.accept, SM.GameState.delete]

theorem max_epoch_of_other_succ {ep : Party → ℕ} {P : Party}
    (hother : ep P.other = ep P + 1) :
    max (ep .A) (ep .B) = ep P + 1 := by
  cases P <;> simp [Party.other] at hother ⊢ <;> omega

theorem Sync.deliver_new_info {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) {P : Party} {c : Header T × E}
    {r : SM.Record M (Header T × E)}
    (hr : esC.g.inTransit P.other c = some r) (hnew : c.1.1 = esC.g.epoch P + 1) :
    let m := esC.g.epoch P + 1
    r.pos.epoch = m ∧
    P = Party.receiverOf m ∧
    P.other = Party.senderOf m ∧
    esC.g.epoch P.other = m ∧
    max (esC.g.epoch .A) (esC.g.epoch .B) = m ∧
    ∃ Tm Im,
      c.1.2 = some Tm ∧
      esC.h.cache m = some (Tm, Im) ∧
      (esC.g.st P.other).curCkaMsg = some Tm ∧
      (esC.g.st P.other).root = (prng.up (esC.g.st P).root Im).1 ∧
      esP.h.cache m = some (Tm, (esP.g.st P.other).root, (prng.up (esC.g.st P).root Im).2) ∧
      (localCKA mo Δcka (esC.g.epoch P) = false → sc.lastMsg = some Tm) := by
  obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
  obtain ⟨ht1, hsend, hle_ep, hTcur⟩ := hS.trans_inv r hmem
  rw [hct] at ht1 hTcur
  rw [hsender] at hsend hle_ep hTcur
  have hr_ep : r.pos.epoch = esC.g.epoch P + 1 := by omega
  have hle_other : esC.g.epoch P + 1 ≤ esC.g.epoch P.other := by omega
  rcases hS.ping_pong with ⟨hR, _⟩ | ⟨hm0, hR, Tm, Im, hcC, hST, hSroot, hcP, hlast⟩
  · have hepP := epoch_eq_of_synced hS.epoch_S hR P
    have hepO := epoch_eq_of_synced hS.epoch_S hR P.other
    omega
  · have hS_ep : esC.g.epoch (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) =
        max (esC.g.epoch .A) (esC.g.epoch .B) := hS.epoch_S
    have hP_ne_S : P ≠ Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
      intro hEq
      have h1 : esC.g.epoch P = max (esC.g.epoch .A) (esC.g.epoch .B) := by rw [hEq, hS_ep]
      have h2 : esC.g.epoch P.other + 1 = max (esC.g.epoch .A) (esC.g.epoch .B) := by
        have hO : P.other = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
          rw [hEq, senderOf_other]
        rw [hO, hR]
      omega
    have hP_eq_R : P = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) :=
      eq_receiverOf_of_ne_senderOf hP_ne_S
    have hM_eq : max (esC.g.epoch .A) (esC.g.epoch .B) = esC.g.epoch P + 1 := by
      rw [← hP_eq_R] at hR
      exact hR.symm
    rw [hM_eq] at hP_eq_R hS_ep hcC hST hSroot hcP hlast
    have hO_eq_Sm : P.other = Party.senderOf (esC.g.epoch P + 1) := by
      simpa [receiverOf_other] using congrArg Party.other hP_eq_R
    have hO_ep : esC.g.epoch P.other = esC.g.epoch P + 1 := by
      rw [hO_eq_Sm, hS_ep]
    rw [← hP_eq_R] at hSroot hcP
    rw [← hO_eq_Sm] at hST hSroot hcP
    have hct2 : c.1.2 = some Tm := by
      rw [hTcur (by omega), hST]
    refine ⟨hr_ep, hP_eq_R, hO_eq_Sm, hO_ep, hM_eq, Tm, Im, hct2, hcC, hST, hSroot, hcP, ?_⟩
    intro hloc
    apply hlast
    simpa using hloc

theorem Sync.accept_new {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc sc' : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) (γP' : Γ) (vR' : ℕ → Option RS)
    (pos : SM.Pos)
    (hpos : pos.epoch = esC.g.epoch P + 1)
    (hother : esC.g.epoch P.other = esC.g.epoch P + 1)
    (hsc_b : sc'.b = true)
    (hcka' : localCKA mo Δcka (esC.g.epoch P + 1) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P + 1) :
    let m := esC.g.epoch P + 1
    let γC' := if localCKA mo Δcka m then some γP' else none
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esC.g.st P with tcur := m, γ := γC', root := (esC.g.st P.other).root, vR := vR' }
    let stP' : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
    Sync prng Δcka mo { esC with g := esC.g.accept P stC' pos } sc'
      { esP with g := esP.g.accept P stP' pos } sp where
  abort_C := hS.abort_C
  abort_P := hS.abort_P
  b_C := hsc_b
  b_P := hS.b_P
  g_eq := eraseSt_accept hS.g_eq P _ _ pos
  id_C := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.id_C]
    · simp [accept_st, hQP, hS.id_C]
  id_P := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.id_P]
    · simp [accept_st, hQP, hS.id_P]
  tcur_C := fun Q => by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    rcases party_eq_or_eq_other Q P with hQ | hQ
    · subst hQ; simp [accept_st]
    · subst hQ; simp [accept_st, Party.other_ne, hS.tcur_C, hother]
  tcur_P := fun Q => by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    rcases party_eq_or_eq_other Q P with hQ | hQ
    · subst hQ; simp [accept_st]
    · subst hQ; simp [accept_st, Party.other_ne, hS.tcur_P, hother]
  vS_eq := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.vS_eq]
    · simp [accept_st, hQP, hS.vS_eq]
  vR_eq := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st]
    · simp [accept_st, hQP, hS.vR_eq]
  Tcur_eq := fun Q => by
    by_cases hQP : Q = P
    · subst hQP; simp [accept_st, hS.Tcur_eq]
    · simp [accept_st, hQP, hS.Tcur_eq]
  γ_C := fun Q => by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    rcases party_eq_or_eq_other Q P with hQ | hQ
    · subst hQ; simp [accept_st]
    · subst hQ; simpa [accept_st, Party.other_ne, hother] using hS.γ_C P.other
  root_P := fun Q => by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    rcases party_eq_or_eq_other Q P with hQ | hQ
    · rw [hQ]; simpa [accept_st, hother] using hS.root_P P.other
    · rw [hQ]; simpa [accept_st, Party.other_ne, hother] using hS.root_P P.other
  cka_st := fun Q hloc => by
    dsimp only at hloc ⊢
    rw [accept_epoch_of_succ _ _ _ _ hpos hother] at hloc ⊢
    have hloc' : localCKA mo Δcka (esC.g.epoch P + 1) = false := by
      rcases hloc with h | h <;> exact h
    obtain ⟨h1, h2, h3, h4⟩ := hcka' hloc'
    rcases party_eq_or_eq_other Q P with hQ | hQ
    · rw [hQ]; simp [accept_st, h1, h2]
    · rw [hQ]; simp [accept_st, Party.other_ne, h3, h4]
  trans_inv := fun r hr => by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    dsimp only
    simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hS.trans_inv r hr.1
    have hle_sender : esC.g.epoch r.pos.sender ≤ esC.g.epoch P + 1 := by
      rcases party_eq_or_eq_other r.pos.sender P with hP | hO
      · rw [hP]; omega
      · rw [hO]; omega
    refine ⟨h1, h2, by omega, fun hep => ?_⟩
    have hneP : r.pos.sender ≠ P := by
      intro hP
      rw [hP] at h3
      omega
    have hO : r.pos.sender = P.other := by
      rcases party_eq_or_eq_other r.pos.sender P with hP | hO
      · exact False.elim (hneP hP)
      · exact hO
    have hep' : r.pos.epoch = esC.g.epoch r.pos.sender := by
      rw [hO, hother, hep]
    rw [h4 hep']
    simp [accept_st, hneP]
  comp_inv := comp_inv_accept esC.g (2 + Δcka) P _ pos hS.comp_inv
  epoch_S := by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    simp
  cache_gt := by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    simpa [max_epoch_of_other_succ hother] using hS.cache_gt
  ping_pong := by
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esC.g.st P with
        tcur := esC.g.epoch P + 1
        γ := if localCKA mo Δcka (esC.g.epoch P + 1) then some γP' else none
        root := (esC.g.st P.other).root
        vR := vR' }
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    left
    refine ⟨by simp, ?_⟩
    have hroot : ∀ Q, ((esC.g.accept P stC' pos).st Q).root = (esC.g.st P.other).root := fun Q => by
      rcases party_eq_or_eq_other Q P with hQ | hQ
      · rw [hQ]; simp [accept_st, stC']
      · rw [hQ]; simp [accept_st, Party.other_ne]
    exact (hroot .A).trans (hroot .B).symm
  prng_before_tH := by
    have hneP : Party.senderOf (esC.g.epoch P + 1) ≠ P := by
      have hmax := max_epoch_of_other_succ hother
      have hS_ep : esC.g.epoch (Party.senderOf (esC.g.epoch P + 1)) = esC.g.epoch P + 1 := by
        simpa [hmax] using hS.epoch_S
      intro hEq
      rw [hEq] at hS_ep
      omega
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    simp only [max_self, accept_st, Function.update, hneP, ↓reduceDIte]
    simpa [max_epoch_of_other_succ hother] using hS.prng_before_tH
  prng_after_tH := by
    have hneP : Party.senderOf (esC.g.epoch P + 1) ≠ P := by
      have hmax := max_epoch_of_other_succ hother
      have hS_ep : esC.g.epoch (Party.senderOf (esC.g.epoch P + 1)) = esC.g.epoch P + 1 := by
        simpa [hmax] using hS.epoch_S
      intro hEq
      rw [hEq] at hS_ep
      omega
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    simp only [max_self, accept_st, Function.update, hneP, ↓reduceDIte]
    simpa [max_epoch_of_other_succ hother] using hS.prng_after_tH
  prng_at_tStar := by
    dsimp only
    rw [accept_epoch_of_succ _ _ _ _ hpos hother]
    dsimp only
    intro hm hR
    omega

theorem step_deliverE_le (mo : Mode) (hauth : mo.auth = true)
    (P : Party) (c : Header T × E)
    (contL : Option (SM.RecvResult M) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (SM.RecvResult M) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc >>= fun r =>
        contL r.1.1 r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp >>= fun r =>
        contR r.1.1 r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hchall : esP.g.chall = esC.g.chall := eraseSt_chall hS.g_eq
  have hcfg_win : (mo.cfg : SM.Config M).deliverWin = false := by
    simp [Mode.cfg, hauth, SM.Config.auth]
  have hesC_eq : ({ g := esC.g, h := esC.h, abort := false } : EStateC Γ T Sig SS RS M E I) = esC :=
    estate_mk_abort_false hS.abort_C
  have hesP_eq : ({ g := esP.g, h := esP.h, abort := false } : EStateP Γ T Sig SS RS M E K) = esP :=
    estate_mk_abort_false hS.abort_P
  by_cases hwin0 : esC.g.win = true
  · exact step_pure_le (by simp [-Prod.mk.injEq, stepC, implE, deliverE, hS.abort_C, hwin0])
      (by simp [-Prod.mk.injEq, stepP, implE, deliverE, hS.abort_P, hwin, hwin0]) (ih none hS)
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      exact step_pure_le (by simp [-Prod.mk.injEq, stepC, implE, deliverE, hS.abort_C, hwin0, hr])
        (by simp [-Prod.mk.injEq, stepP, implE, deliverE, hS.abort_P, hwin, hwin0, htrans, hr]) (ih none hS)
    | some r =>
      obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
      obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
      rw [hct] at ht1
      rw [hsender] at hsend_other hle_other
      have hsend0 : P.sendsIn c.1.1 = false := by
        rw [ht1]
        have h1 := sendsIn_other P r.pos.epoch
        rw [hsend_other] at h1
        simpa using h1.symm
      have hmax_bound : esC.g.epoch P.other ≤ esC.g.epoch P + 1 := by
        rcases hS.ping_pong with ⟨hR, _⟩ | ⟨_, hR, _⟩
        · have hepP := epoch_eq_of_synced hS.epoch_S hR P
          have hepO := epoch_eq_of_synced hS.epoch_S hR P.other
          omega
        · rcases party_cases_of_epoch (max (esC.g.epoch .A) (esC.g.epoch .B)) P with hP | hP
          · have hO : P.other = Party.receiverOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
              rw [hP, senderOf_other]
            have hS_ep := hS.epoch_S
            rw [← hP] at hS_ep
            rw [← hO] at hR
            omega
          · have hO : P.other = Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)) := by
              rw [hP, receiverOf_other]
            have hS_ep := hS.epoch_S
            rw [← hO] at hS_ep
            rw [← hP] at hR
            omega
      have hle : ¬ (esC.g.epoch P + 1 < c.1.1) := by omega
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      ·
        have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        obtain ⟨hr_ep, hP_eq_R, hO_eq_S, hO_ep, hmax_eq, Tm, Im, hct2, hcC, hST, hSroot,
          hcP, hlast⟩ := hS.deliver_new_info hr hnew
        let p := prng.up (esC.g.st P).root Im
        have hp1 : (prng.up (esC.g.st P).root Im).1 = (esC.g.st P.other).root := hSroot.symm
        let γP' := (cka.receive (esP.g.st P).γ Tm).1
        have hstartC := fun ctx γv =>
          hooksCKA_startRecv_honest cka prng fs Δcka mo ctx P (esC.g.epoch P + 1) γv
            (esC.g.st P).root Tm Im esC.h hcC
        have hstartP : (simulateQ (pImpl prng)
            (((hooksPRNG cka prng fs mo).startRecv esP.g P (esC.g.epoch P + 1)
              (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
            pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h), sp) := by
          simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure,
            simulateQ_pure]
        cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none =>
          exact step_pure_le
            (by simp [-Prod.mk.injEq, stepC, implE, deliverE, vRecv, hS.abort_C, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
              StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesC_eq])
            (by simp [-Prod.mk.injEq, stepP, implE, deliverE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr, hcfg_win,
              hS.id_P P, hS.tcur_P P, hsend0', hnew, hct2, hstartP, hfs,
              StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesP_eq])
            (ih (some .rejected) hS)
        | some vim =>
          rcases vim with ⟨v', i', m'⟩
          let m := esC.g.epoch P + 1
          let vR' := Function.update (Function.update (esC.g.st P).vR m
            (some (fs.initReceiver p.2))) m (some v')
          let γC_final := if localCKA mo Δcka m then some γP' else none
          let stC_final : VP (Option Γ) T Sig SS RS :=
            { esC.g.st P with tcur := m, γ := γC_final, root := (esC.g.st P.other).root, vR := vR' }
          let stP_final : VP Γ T (Option Sig) SS RS :=
            { esP.g.st P with tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
          have hvRP : (esP.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
          have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
              pure ((some (.accepted m i' (if esC.g.chall.contains r.pos then none else some m')),
                { esP with g := esP.g.accept P stP_final r.pos }), sp) := by
            simp [stepP, implE, deliverE, commitE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr,
              hcfg_win, hchall, hS.id_P P, hS.tcur_P P, hsend0', hnew, hct2, hvRP, hstartP, hfs,
              m, vR', stP_final, γP', StateT.run_bind, StateT.run_pure, StateT.run_modify,
              simulateQ_bind, simulateQ_pure]
          by_cases hloc : localCKA mo Δcka (esC.g.epoch P) = true
          · have hloc_m : localCKA mo Δcka m = true := by
              simp only [localCKA, Bool.or_eq_true, decide_eq_true_eq] at hloc ⊢
              rcases hloc with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (by omega)
            have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
              rw [hS.γ_C P, hloc]; rfl
            exact step_pure_le
              (by simp [-Prod.mk.injEq, stepC, implE, deliverE, commitE, vRecv, hS.abort_C, hwin0, hr,
                hcfg_win, hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
                hγC, hloc_m, m, vR', γC_final, stC_final, γP', StateT.run_bind,
                StateT.run_pure, StateT.run_modify, simulateQ_bind, simulateQ_pure]) hP
              (ih _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C
                (fun h => by simp [m, hloc_m] at h)))
          · simp only [Bool.not_eq_true] at hloc
            have hγC : (esC.g.st P).γ = none := by
              rw [hS.γ_C P, hloc]; rfl
            obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
            obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
            have hcanR : sc.canReceive P = true := by
              simp [CKA.GameState.canReceive, hsc_epO, hsc_epP, hO_ep]
            have hlast_eq : sc.lastMsg = some Tm := hlast hloc
            let sc' := sc.afterReceive P γP'
            have htL_none : mo.tL.isNone = false := by
              simp only [localCKA, Bool.or_eq_false_iff] at hloc
              exact hloc.1
            by_cases hfin : mo.tH + Δcka ≤ m
            · have hloc_m : localCKA mo Δcka m = true := by
                simp [localCKA, hfin]
              exact step_pure_le
                (by simp [-Prod.mk.injEq, stepC, implE, deliverE, commitE, liftC, CKA.receiveQuery,
                  CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl, vRecv,
                  hS.abort_C, hwin0, hr, hcfg_win, hS.id_C P, hS.tcur_C P, hsend0', hnew,
                  hct2, hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m,
                  sc', CKA.GameState.afterReceive, CKA.GameState.finished, hsc_epP,
                  m, vR', γC_final, stC_final, γP',
                  StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]) hP
                (ih _ (hS.accept_new (sc' := sc') P γP' vR' r.pos hr_ep hO_ep hS.b_C
                  (fun h => by simp [m, hloc_m] at h)))
            · have hloc_m : localCKA mo Δcka m = false := by
                simp [localCKA, htL_none, hfin]
              refine step_pure_le
                (by simp [-Prod.mk.injEq, stepC, implE, deliverE, commitE, liftC, CKA.receiveQuery,
                  cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv, hS.abort_C, hwin0, hr,
                  hcfg_win, hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
                  hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m, sc', m, vR', γC_final, stC_final,
                  γP', StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]) hP
                (ih _ (hS.accept_new (sc' := sc') P γP' vR' r.pos hr_ep hO_ep hS.b_C fun _ => ?_))
              simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO,
                hsc_epO, hO_ep, m]
      ·
        have hle_ep : r.pos.epoch ≤ esC.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := by rw [hS.vR_eq P]
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          exact step_pure_le
            (by simp [-Prod.mk.injEq, stepC, implE, deliverE, vRecv, hS.abort_C, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_pure, hesC_eq])
            (by simp [-Prod.mk.injEq, stepP, implE, deliverE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr, hcfg_win,
              hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, StateT.run_pure, hesP_eq])
            (ih (some .rejected) hS)
        | some v =>
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            exact step_pure_le
              (by simp [-Prod.mk.injEq, stepC, implE, deliverE, vRecv, hS.abort_C, hwin0, hr, hcfg_win,
                hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, StateT.run_pure, hesC_eq])
              (by simp [-Prod.mk.injEq, stepP, implE, deliverE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr, hcfg_win,
                hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs,
                StateT.run_pure, hesP_eq])
              (ih (some .rejected) hS)
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
            have hvRP_all : (esP.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
            exact step_pure_le
              (by simp [-Prod.mk.injEq, stepC, implE, deliverE, commitE, vRecv, hS.abort_C, hwin0, hr,
                hcfg_win, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, vR',
                StateT.run_pure, StateT.run_modify]; rfl)
              (by simp [-Prod.mk.injEq, stepP, implE, deliverE, commitE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr,
                hcfg_win, hchall, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs,
                hvRP_all, vR', StateT.run_pure, StateT.run_modify])
              (ih _ (hS.accept_old P vR' r.pos hle_ep))

/-! ## Step lemma for `transmitE` -/

theorem sendsIn_of_succ_false {P : Party} {t : ℕ} (h : P.sendsIn (t + 1) = false) :
    P.sendsIn t = true := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

theorem sendsIn_pred_false {P : Party} {t : ℕ} (h : P.sendsIn (t + 1) = true) :
    P.sendsIn t = false := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

@[simp]
lemma hooksCKA_fsSend (mo : Mode) (ctx : Ctx (Option Γ) T Sig SS RS M E) (P : Party) (t : ℕ)
    (v : SS) (h : Header T) (m : M) (pair : Option (M × M)) :
    (hooksCKA cka prng fs Δcka mo).fsSend ctx P t v h m pair =
      pure (some (fs.send v h m)) := rfl

@[simp]
lemma hooksPRNG_fsSend (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t : ℕ)
    (v : SS) (h : Header T) (m : M) (pair : Option (M × M)) :
    (hooksPRNG cka prng fs mo).fsSend ctx P t v h m pair =
      pure (some (fs.send v h m)) := rfl

theorem Sync.record_same_epoch {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) (vS' : Option SS)
    (m_msg : M) (e : E) (hsend : P.sendsIn (esC.g.epoch P) = true) :
    let c : Header T × E := ((esC.g.epoch P, (esC.g.st P).curCkaMsg), e)
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
    Sync prng Δcka mo
      { esC with g := esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false } sc
      { esP with g := esP.g.record (2 + Δcka) P { esP.g.st P with vS := vS' } rcd false } sp := by
  intro c rcd
  refine
    { abort_C := hS.abort_C
      abort_P := hS.abort_P
      b_C := hS.b_C
      b_P := hS.b_P
      g_eq := eraseSt_record hS.g_eq (2 + Δcka) P _ _ rcd false
      id_C := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.id_C]
      id_P := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.id_P]
      tcur_C := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.tcur_C]
      tcur_P := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.tcur_P]
      vS_eq := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.vS_eq]
      vR_eq := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.vR_eq]
      Tcur_eq := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.Tcur_eq]
      γ_C := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.γ_C]
      root_P := fun Q => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simp [SM.GameState.record, Party.other_ne, hS.root_P]
      cka_st := fun Q hloc => by
        rcases party_eq_or_eq_other Q P with rfl | rfl <;>
          simpa [SM.GameState.record, Party.other_ne] using hS.cka_st _ hloc
      trans_inv := fun r hr => by
        simp only [SM.GameState.record, List.mem_cons] at hr
        rcases hr with rfl | hr'
        · refine ⟨rfl, hsend, le_rfl, fun _ => ?_⟩
          simp [SM.GameState.record, rcd, c]
        · obtain ⟨h1, h2, h3, h4⟩ := hS.trans_inv r hr'
          refine ⟨h1, h2, h3, fun hep => ?_⟩
          rw [h4 hep]
          rcases party_eq_or_eq_other r.pos.sender P with hEq | hEq <;>
            simp [hEq, SM.GameState.record, Party.other_ne]
      comp_inv := comp_inv_record esC.g (2 + Δcka) P _ rcd false rfl hS.comp_inv
      epoch_S := hS.epoch_S
      cache_gt := hS.cache_gt
      ping_pong := by
        have hroot : ∀ Q, ((esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).st Q).root =
            (esC.g.st Q).root := fun Q => by
          rcases party_eq_or_eq_other Q P with rfl | rfl <;>
            simp [SM.GameState.record, Party.other_ne]
        have hTcur : ∀ Q, ((esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).st Q).curCkaMsg =
            (esC.g.st Q).curCkaMsg := fun Q => by
          rcases party_eq_or_eq_other Q P with rfl | rfl <;>
            simp [SM.GameState.record, Party.other_ne]
        have hrootP : ∀ Q, ((esP.g.record (2 + Δcka) P { esP.g.st P with vS := vS' } rcd false).st Q).root =
            (esP.g.st Q).root := fun Q => by
          rcases party_eq_or_eq_other Q P with rfl | rfl <;>
            simp [SM.GameState.record, Party.other_ne]
        have hep : (esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).epoch =
            esC.g.epoch := rfl
        simpa [hep, hroot, hTcur, hrootP] using hS.ping_pong
      prng_before_tH := by
        have hep : (esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).epoch =
            esC.g.epoch := rfl
        have hroot : ∀ Q, ((esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).st Q).root =
            (esC.g.st Q).root := fun Q => by
          rcases party_eq_or_eq_other Q P with rfl | rfl <;>
            simp [SM.GameState.record, Party.other_ne]
        simpa [hep, hroot] using hS.prng_before_tH
      prng_after_tH := by
        have hep : (esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).epoch =
            esC.g.epoch := rfl
        have hroot : ∀ Q, ((esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).st Q).root =
            (esC.g.st Q).root := fun Q => by
          rcases party_eq_or_eq_other Q P with rfl | rfl <;>
            simp [SM.GameState.record, Party.other_ne]
        simpa [hep, hroot] using hS.prng_after_tH
      prng_at_tStar := by
        have hep : (esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).epoch =
            esC.g.epoch := rfl
        have hroot : ∀ Q, ((esC.g.record (2 + Δcka) P { esC.g.st P with vS := vS' } rcd false).st Q).root =
            (esC.g.st Q).root := fun Q => by
          rcases party_eq_or_eq_other Q P with rfl | rfl <;>
            simp [SM.GameState.record, Party.other_ne]
        simpa [hep, hroot] using hS.prng_at_tStar }

theorem localCKA_mono (mo : Mode) (Δcka : ℕ) {t₁ t₂ : ℕ}
    (h : localCKA mo Δcka t₁ = true) (hle : t₁ ≤ t₂) :
    localCKA mo Δcka t₂ = true := by
  simp only [localCKA, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with h | h
  · left; exact h
  · right; omega

theorem Sync.ping_pong_synced {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true) :
    esC.g.epoch P.other = esC.g.epoch P ∧
    max (esC.g.epoch .A) (esC.g.epoch .B) = esC.g.epoch P ∧
    (esC.g.st P.other).root = (esC.g.st P).root := by
  have hsend0 : P.sendsIn (esC.g.epoch P) = false := sendsIn_pred_false hsend
  rcases hS.ping_pong with ⟨hR, hrootAB⟩ | ⟨_, hR, _⟩
  · have hepP := epoch_eq_of_synced hS.epoch_S hR P
    have hepO := epoch_eq_of_synced hS.epoch_S hR P.other
    refine ⟨hepO.trans hepP.symm, hepP.symm, ?_⟩
    cases P <;> simp [Party.other, hrootAB]
  · exfalso
    let M := max (esC.g.epoch .A) (esC.g.epoch .B)
    have hS_ep : esC.g.epoch (Party.senderOf M) = M := hS.epoch_S
    rcases party_cases_of_epoch M P with hP | hP
    · have hepP : esC.g.epoch P = M := by rw [hP, hS_ep]
      have hsM : P.sendsIn M = true := by rw [hP]; exact sendsIn_senderOf M
      rw [← hepP] at hsM
      simp [hsM] at hsend0
    · have hepP : esC.g.epoch P + 1 = M := by rw [hP]; exact hR
      have hsM : P.sendsIn M = false := by rw [hP]; exact sendsIn_receiverOf M
      rw [← hepP] at hsM
      simp [hsM] at hsend

def epMgmtNew {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool) :
    SM.GameState St Msg C :=
  let s₁ := if bad && !(g.safeCh Δ P) then g.leak (g.epoch P + 1) else g
  { s₁ with epoch := Function.update s₁.epoch P (s₁.epoch P + 1),
            idx := Function.update s₁.idx P 0 }

theorem epMgmt_eq_epMgmtNew {St Msg C : Type} (g : SM.GameState St Msg C) (Δ qep : ℕ)
    (P : Party) (bad : Bool) (hsend : P.sendsIn (g.epoch P + 1) = true)
    (hqep : ¬ qep < g.epoch P + 1) :
    g.epMgmt Δ qep P bad = some (epMgmtNew g Δ P bad) := by
  simp [SM.GameState.epMgmt, epMgmtNew, hsend, show ¬ qep ≤ g.epoch P by omega]

theorem eraseSt_epMgmtNew {St₁ St₂ Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {g₁ : SM.GameState St₁ Msg C} {g₂ : SM.GameState St₂ Msg C}
    (h : eraseSt g₁ = eraseSt g₂) (Δ : ℕ) (P : Party) (bad : Bool) :
    eraseSt (epMgmtNew g₁ Δ P bad) = eraseSt (epMgmtNew g₂ Δ P bad) := by
  have h1 : eraseSt (if bad && !(g₁.safeCh Δ P) then g₁.leak (g₁.epoch P + 1) else g₁) =
      eraseSt (if bad && !(g₂.safeCh Δ P) then g₂.leak (g₂.epoch P + 1) else g₂) := by
    rw [eraseSt_safeCh h Δ P, eraseSt_epoch h]
    split
    · exact eraseSt_leak h (g₂.epoch P + 1)
    · exact h
  dsimp only [epMgmtNew, eraseSt]
  rw [eraseSt_epoch h1, eraseSt_idx h1, eraseSt_tL h1,
    eraseSt_trans h1, eraseSt_chall h1, eraseSt_comp h1, eraseSt_maxAcc h1, eraseSt_b h1,
    eraseSt_win h1, eraseSt_leaks h1, eraseSt_corrs h1]

@[simp]
theorem epMgmtNew_st {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool) :
    (epMgmtNew g Δ P bad).st = g.st := by
  simp [epMgmtNew, SM.GameState.leak]
  split <;> rfl

@[simp]
theorem epMgmtNew_epoch {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool) :
    (epMgmtNew g Δ P bad).epoch = Function.update g.epoch P (g.epoch P + 1) := by
  have h : (if bad && !(g.safeCh Δ P) then g.leak (g.epoch P + 1) else g).epoch = g.epoch := by
    split <;> rfl
  dsimp only [epMgmtNew]
  rw [h]

@[simp]
theorem epMgmtNew_idx_self {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool) :
    (epMgmtNew g Δ P bad).idx P = 0 := by
  simp [epMgmtNew]

@[simp]
theorem epMgmtNew_trans {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool) :
    (epMgmtNew g Δ P bad).trans = g.trans := by
  simp [epMgmtNew, SM.GameState.leak]
  split <;> rfl

theorem comp_inv_epMgmtNew {St Msg C : Type} (g : SM.GameState St Msg C) (Δ : ℕ) (P : Party) (bad : Bool)
    (hcomp : ∀ pos ∈ g.comp, SM.healedBy g.tL Δ pos.epoch = false) :
    ∀ pos ∈ (epMgmtNew g Δ P bad).comp,
      SM.healedBy (epMgmtNew g Δ P bad).tL Δ pos.epoch = false := by
  intro pos hpos
  dsimp only [epMgmtNew] at hpos ⊢
  split at hpos
  · rename_i hcond
    simp only [hcond, ↓reduceIte, SM.GameState.leak] at hpos ⊢
    exact healedBy_leak_false g.tL (g.epoch P + 1) Δ pos.epoch (hcomp pos hpos)
  · rename_i hcond
    simp only [hcond, ↓reduceIte] at hpos ⊢
    exact hcomp pos hpos

theorem max_epoch_update_succ {ep : Party → ℕ} {P : Party} (hO : ep P.other = ep P) :
    max (Function.update ep P (ep P + 1) .A) (Function.update ep P (ep P + 1) .B) = ep P + 1 := by
  cases P <;> simp [Party.other] at hO ⊢ <;> omega

theorem Sync.record_new_epoch {prng : PRFPRNG KR Sig I K} {Δcka : ℕ} {mo : Mode}
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) (P : Party) (bad : Bool)
    (γP' : Γ) (Tm : T) (Im : I) (v' : SS) (m_msg : M) (e : E)
    (sc' : CKA.GameState Γ T) (sp' : PRFPRNG.GameState Sig I K)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hb_sc' : sc'.b = true) (hb_sp' : sp'.b = false)
    (hcka' : localCKA mo Δcka (esC.g.epoch P) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some Tm)
    (hprng_before : esC.g.epoch P + 1 < mo.tStar →
      (mo.tL.isSome && decide (esC.g.epoch P + 1 < mo.tH)) = true →
      sp'.σ = (prng.up (esC.g.st P).root Im).1 ∧
      sp'.corr = true ∧ sp'.prng = false ∧ sp'.prf = false)
    (hprng_after : esC.g.epoch P + 1 < mo.tStar →
      (mo.tL.isSome && decide (esC.g.epoch P + 1 < mo.tH)) = false →
      sp'.σ = (prng.up (esC.g.st P).root Im).1 ∧
      sp'.corr = false ∧ sp'.prng = false ∧
      (esC.g.epoch P + 1 + 1 < mo.tStar → sp'.prf = false))
    (hprng_at : esC.g.epoch P + 1 = mo.tStar →
      (mo.tL.isSome && decide (mo.tStar = mo.tH)) = false →
      sp'.σ = (esC.g.st P).root ∧ sp'.corr = false ∧ sp'.prng = false) :
    let m := esC.g.epoch P + 1
    let p := prng.up (esC.g.st P).root Im
    let σP' := if knownRoot mo m then some p.1 else none
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esC.g.st P with
        tcur := m
        γ := if localCKA mo Δcka m then some γP' else none
        curCkaMsg := some Tm
        root := p.1
        vS := some v' }
    let stP' : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with
        tcur := m
        γ := γP'
        curCkaMsg := some Tm
        root := σP'
        vS := some v' }
    let c : Header T × E := ((m, some Tm), e)
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, c⟩
    let gC₁ := epMgmtNew esC.g (2 + Δcka) P bad
    let gP₁ := epMgmtNew esP.g (2 + Δcka) P bad
    Sync prng Δcka mo
      { esC with
        g := gC₁.record (2 + Δcka) P stC' rcd false
        h := { cache := Function.update esC.h.cache m (some (Tm, Im)) } } sc'
      { esP with
        g := gP₁.record (2 + Δcka) P stP' rcd false
        h := { cache := Function.update esP.h.cache m (some (Tm, σP', p.2)) } } sp' := by
  intro m p σP' stC' stP' c rcd gC₁ gP₁
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hP_sender : P = Party.senderOf m := eq_senderOf_of_sendsIn hsend
  have hO_recv : P.other = Party.receiverOf m := by
    rw [hP_sender, senderOf_other]
  have hep_eq : esP.g.epoch = esC.g.epoch := eraseSt_epoch hS.g_eq
  have hepP_eq : esP.g.epoch P = esC.g.epoch P := congrFun hep_eq P
  have hmax_m : max (Function.update esC.g.epoch P m .A) (Function.update esC.g.epoch P m .B) = m :=
    max_epoch_update_succ hO_ep
  refine
    { abort_C := hS.abort_C
      abort_P := hS.abort_P
      b_C := hb_sc'
      b_P := hb_sp'
      g_eq := eraseSt_record (eraseSt_epMgmtNew hS.g_eq (2 + Δcka) P bad) (2 + Δcka) P stP' stC' rcd false
      id_C := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gC₁, stC', SM.GameState.record, Party.other_ne, hS.id_C])
      id_P := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gP₁, stP', SM.GameState.record, Party.other_ne, hS.id_P])
      tcur_C := fun Q => by
        have hgC₁ : gC₁.epoch = Function.update esC.g.epoch P m :=
          epMgmtNew_epoch esC.g (2 + Δcka) P bad
        have hgC₁_st : gC₁.st = esC.g.st :=
          epMgmtNew_st esC.g (2 + Δcka) P bad
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [hgC₁, hgC₁_st, stC', m, SM.GameState.record, Party.other_ne, hS.tcur_C])
      tcur_P := fun Q => by
        have hgC₁ : gC₁.epoch = Function.update esC.g.epoch P m :=
          epMgmtNew_epoch esC.g (2 + Δcka) P bad
        have hgP₁_st : gP₁.st = esP.g.st :=
          epMgmtNew_st esP.g (2 + Δcka) P bad
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [hgC₁, hgP₁_st, stP', m, hep_eq, SM.GameState.record, Party.other_ne, hS.tcur_P])
      vS_eq := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gC₁, gP₁, stC', stP', SM.GameState.record, Party.other_ne, hS.vS_eq])
      vR_eq := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gC₁, gP₁, stC', stP', SM.GameState.record, Party.other_ne, hS.vR_eq])
      Tcur_eq := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gC₁, gP₁, stC', stP', SM.GameState.record, Party.other_ne, hS.Tcur_eq])
      γ_C := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gC₁, gP₁, stC', stP', m, SM.GameState.record, Party.other_ne, hS.γ_C])
      root_P := fun Q => by
        rcases party_eq_or_eq_other Q P with hQ | hQ <;>
          (rw [hQ]; simp [gC₁, gP₁, stC', stP', σP', m, SM.GameState.record, Party.other_ne, hS.root_P])
      cka_st := fun Q hloc => by
        dsimp only [gC₁, SM.GameState.record] at hloc ⊢
        rw [epMgmtNew_epoch] at hloc ⊢
        have hloc0 : localCKA mo Δcka (esC.g.epoch P) = false := by
          rcases party_eq_or_eq_other Q P with hQ | hQ
          · rw [hQ] at hloc
            simp only [Function.update_self, Function.update_of_ne (Party.other_ne P), hO_ep] at hloc
            rcases hloc with h | h
            · cases h0 : localCKA mo Δcka (esC.g.epoch P)
              · rfl
              · have := localCKA_mono mo Δcka h0 (Nat.le_succ (esC.g.epoch P))
                simp [m, this] at h
            · exact h
          · rw [hQ] at hloc
            simp only [Party.other_other, Function.update_self,
              Function.update_of_ne (Party.other_ne P), hO_ep] at hloc
            rcases hloc with h | h
            · exact h
            · cases h0 : localCKA mo Δcka (esC.g.epoch P)
              · rfl
              · have := localCKA_mono mo Δcka h0 (Nat.le_succ (esC.g.epoch P))
                simp [m, this] at h
        obtain ⟨h1, h2, h3, h4, _⟩ := hcka' hloc0
        rcases party_eq_or_eq_other Q P with hQ | hQ
        · rw [hQ]; simp [gP₁, stP', SM.GameState.record, h1, h2, m]
        · rw [hQ]; simp [gP₁, stP', SM.GameState.record, Party.other_ne, h3, h4, hO_ep]
      trans_inv := fun r hr => by
        dsimp only [gC₁, SM.GameState.record] at hr ⊢
        rw [epMgmtNew_epoch, epMgmtNew_st]
        rw [epMgmtNew_trans] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · refine ⟨rfl, ?_, ?_, fun _ => ?_⟩
          · simp [rcd, m, hsend]
          · simp [rcd, m]
          · simp [rcd, c, stC']
        · obtain ⟨h1, h2, h3, h4⟩ := hS.trans_inv r hr'
          refine ⟨h1, h2, ?_, fun hep => ?_⟩
          · rcases party_eq_or_eq_other r.pos.sender P with hEq | hEq
            · rw [hEq] at h3 ⊢; simp [m]; omega
            · rw [hEq] at h3 ⊢; simp [Party.other_ne, h3]
          · rcases party_eq_or_eq_other r.pos.sender P with hEq | hEq
            · rw [hEq] at h3 hep
              simp only [Function.update_self] at hep
              omega
            · have hep' : r.pos.epoch = esC.g.epoch r.pos.sender := by
                rw [hEq] at hep ⊢
                simpa [Party.other_ne] using hep
              rw [hEq, Function.update_of_ne (Party.other_ne P), ← hEq]
              exact h4 hep'
      comp_inv := by
        refine comp_inv_record gC₁ (2 + Δcka) P stC' rcd false ?_
          (comp_inv_epMgmtNew esC.g (2 + Δcka) P bad hS.comp_inv)
        simp [gC₁, rcd, m]
      epoch_S := by
        dsimp only [gC₁, SM.GameState.record]
        rw [epMgmtNew_epoch, hmax_m, ← hP_sender]
        simp [m]
      cache_gt := fun t ht => by
        dsimp only [gC₁, SM.GameState.record] at ht ⊢
        rw [epMgmtNew_epoch, hmax_m] at ht
        have hne : t ≠ m := by omega
        have hgt0 : max (esC.g.epoch .A) (esC.g.epoch .B) < t := by omega
        simp [Function.update_of_ne hne, hS.cache_gt t hgt0]
      ping_pong := by
        dsimp only [gC₁, gP₁, SM.GameState.record]
        rw [epMgmtNew_epoch, epMgmtNew_st, epMgmtNew_st, hmax_m]
        right
        refine ⟨by omega, ?_, Tm, Im, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← hO_recv]
          simp [Party.other_ne, hO_ep, m]
        · simp
        · rw [← hP_sender]
          simp [stC']
        · rw [← hP_sender, ← hO_recv]
          simp [stC', Party.other_ne, hroot0, p]
        · rw [← hP_sender, ← hO_recv]
          simp [stP', Party.other_ne, hroot0, p]
        · intro hloc
          have hloc0 : localCKA mo Δcka (esC.g.epoch P) = false := by
            simpa [m] using hloc
          exact (hcka' hloc0).2.2.2.2
      prng_before_tH := by
        dsimp only [gC₁, SM.GameState.record]
        rw [epMgmtNew_epoch, epMgmtNew_st, hmax_m, ← hP_sender]
        simp only [Function.update_self, stC', p]
        exact hprng_before
      prng_after_tH := by
        dsimp only [gC₁, SM.GameState.record]
        rw [epMgmtNew_epoch, epMgmtNew_st, hmax_m, ← hP_sender]
        simp only [Function.update_self, stC', p]
        exact hprng_after
      prng_at_tStar := by
        dsimp only [gC₁, SM.GameState.record]
        rw [epMgmtNew_epoch, epMgmtNew_st, hmax_m]
        intro hm hR hnot_eq
        have hR_eq : Party.receiverOf mo.tStar = P.other := by
          rw [← hm, hO_recv]
        rw [hR_eq]
        simp only [Function.update_of_ne (Party.other_ne P), hroot0]
        exact hprng_at hm hnot_eq }

def postSendC (P : Party) (m_msg : M) (bad : Bool) (esC : EStateC Γ T Sig SS RS M E I)
    (res : Option (Option Γ × T × Sig × SS) × CKAState T I) :
    Option (Header T × E) × EStateC Γ T Sig SS RS M E I :=
  match res.1 with
  | none => (none, { esC with h := res.2, abort := true })
  | some (γ', Tm, σ', ss) =>
    let m := esC.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stC' : VP (Option Γ) T Sig SS RS :=
      { esC.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gC₁ := epMgmtNew esC.g (2 + Δcka) P bad
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), { esC with g := gC₁.record (2 + Δcka) P stC' rcd false, h := res.2 })

def postSendP (P : Party) (m_msg : M) (bad : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (res : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K) :
    Option (Header T × E) × EStateP Γ T Sig SS RS M E K :=
  match res.1 with
  | none => (none, { esP with h := res.2, abort := true })
  | some (γ', Tm, σ', ss) =>
    let m := esP.g.epoch P + 1
    let h : Header T := (m, some Tm)
    let fe := fs.send ss h m_msg
    let stP' : VP Γ T (Option Sig) SS RS :=
      { esP.g.st P with tcur := m, γ := γ', curCkaMsg := some Tm, root := σ', vS := some fe.1 }
    let gP₁ := epMgmtNew esP.g (2 + Δcka) P bad
    let rcd : SM.Record M (Header T × E) := ⟨⟨P, m, 1⟩, m_msg, (h, fe.2)⟩
    (some (h, fe.2), { esP with g := gP₁.record (2 + Δcka) P stP' rcd false, h := res.2 })

theorem stepC_transmit_new (mo : Mode) (P : Party) (m_msg : M) (r : Option CCoins)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T)
    (hab : esC.abort = false) (hwin : esC.g.win = false)
    (hid : (esC.g.st P).id = P) (htcur : (esC.g.st P).tcur = esC.g.epoch P)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hqep : ¬ qep < esC.g.epoch P + 1)
    (hdoom : mo.policy.leakDoom esC.g (epMgmtNew esC.g (2 + Δcka) P r.isSome) = false) :
    stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
      (simulateQ (cImpl cka Δcka mo.tH)
        (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P r.isSome)
          P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root r).run esC.h)).run sc >>=
        fun out => pure (postSendC fs Δcka P m_msg r.isSome esC out.1, out.2) := by
  have hep := epMgmt_eq_epMgmtNew esC.g (2 + Δcka) qep P r.isSome hsend hqep
  simp only [stepC, implE, QueryImpl.add_apply, transmitE, hab, hwin, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hep, hdoom, vSend, epMgmtNew_st, hid, htcur, hsend,
    run_liftH, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, simulateQ_bind]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sc'⟩
  cases ans with
  | none =>
    simp [postSendC, abortE, StateT.run_modify, simulateQ_pure, StateT.run_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendC, FSAEADScheme.send, hid, hab, StateT.run_modify, StateT.run_pure,
      simulateQ_pure, epMgmtNew_st, htcur]

theorem stepP_transmit_new (mo : Mode) (P : Party) (m_msg : M) (r : Option CCoins)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K)
    (hab : esP.abort = false) (hwin : esP.g.win = false)
    (hid : (esP.g.st P).id = P) (htcur : (esP.g.st P).tcur = esP.g.epoch P)
    (hsend : P.sendsIn (esP.g.epoch P + 1) = true)
    (hqep : ¬ qep < esP.g.epoch P + 1)
    (hdoom : mo.policy.leakDoom esP.g (epMgmtNew esP.g (2 + Δcka) P r.isSome) = false) :
    stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
      (simulateQ (pImpl prng)
        (((hooksPRNG cka prng fs mo).startSend (epMgmtNew esP.g (2 + Δcka) P r.isSome)
          P (esP.g.epoch P + 1) (esP.g.st P).γ (esP.g.st P).root r).run esP.h)).run sp >>=
        fun out => pure (postSendP fs Δcka P m_msg r.isSome esP out.1, out.2) := by
  have hep := epMgmt_eq_epMgmtNew esP.g (2 + Δcka) qep P r.isSome hsend hqep
  simp only [stepP, implE, QueryImpl.add_apply, transmitE, hab, hwin, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hep, hdoom, vSend, epMgmtNew_st, hid, htcur, hsend,
    run_liftH, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, simulateQ_bind]
  congr 1
  funext out
  rcases out with ⟨⟨ans, h'⟩, sp'⟩
  cases ans with
  | none =>
    simp [postSendP, abortE, StateT.run_modify, simulateQ_pure, StateT.run_pure]
  | some val =>
    rcases val with ⟨γ', Tm, σ', ss⟩
    simp [postSendP, FSAEADScheme.send, hid, hab, StateT.run_modify, StateT.run_pure,
      simulateQ_pure, epMgmtNew_st, htcur]

theorem tH_le_tStar_of_validGuess (mo : Mode) (Δcka : ℕ)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (htL : mo.tL.isSome = true) :
    mo.tH + Δcka ≤ mo.tStar := by
  cases h : mo.tL with
  | none => simp [h] at htL
  | some l =>
    simp only [SM.lastLeakGuessAdmissible, SM.healedBy, h, decide_eq_true_eq, Mode.tH, healEpoch] at hvalid ⊢
    omega

theorem ih_postSend_new (mo : Mode)
    (P : Party) (m_msg : M) (bad : Bool)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true})
    (γP' : Γ) (Tm : T) (Im : I) (sc' : CKA.GameState Γ T) (sp' : PRFPRNG.GameState Sig I K)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hb_sc' : sc'.b = true) (hb_sp' : sp'.b = false)
    (hcka' : localCKA mo Δcka (esC.g.epoch P) = false →
      sc'.st P = γP' ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some Tm)
    (hprng_before : esC.g.epoch P + 1 < mo.tStar →
      (mo.tL.isSome && decide (esC.g.epoch P + 1 < mo.tH)) = true →
      sp'.σ = (prng.up (esC.g.st P).root Im).1 ∧
      sp'.corr = true ∧ sp'.prng = false ∧ sp'.prf = false)
    (hprng_after : esC.g.epoch P + 1 < mo.tStar →
      (mo.tL.isSome && decide (esC.g.epoch P + 1 < mo.tH)) = false →
      sp'.σ = (prng.up (esC.g.st P).root Im).1 ∧
      sp'.corr = false ∧ sp'.prng = false ∧
      (esC.g.epoch P + 1 + 1 < mo.tStar → sp'.prf = false))
    (hprng_at : esC.g.epoch P + 1 = mo.tStar →
      (mo.tL.isSome && decide (mo.tStar = mo.tH)) = false →
      sp'.σ = (esC.g.st P).root ∧ sp'.corr = false ∧ sp'.prng = false) :
    let m := esC.g.epoch P + 1
    let p := prng.up (esC.g.st P).root Im
    let σP' := if knownRoot mo m then some p.1 else none
    let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
      (some (if localCKA mo Δcka m then some γP' else none, Tm, p.1, fs.initSender p.2),
        { cache := Function.update esC.h.cache m (some (Tm, Im)) })
    let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
      (some (γP', Tm, σP', fs.initSender p.2),
        { cache := Function.update esP.h.cache m (some (Tm, σP', p.2)) })
    let outC := postSendC fs Δcka P m_msg bad esC resC
    let outP := postSendP fs Δcka P m_msg bad esP resP
    𝒟[contL outC.1 outC.2 sc'] {true} ≤
      𝒟[contR outP.1 outP.2 sp'] {true} := by
  intro m p σP' resC resP outC outP
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  let fe := fs.send (fs.initSender p.2) (m, some Tm) m_msg
  have hS' := hS.record_new_epoch P bad γP' Tm Im fe.1 m_msg fe.2 sc' sp' hsend hb_sc' hb_sp'
    hcka' hprng_before hprng_after hprng_at
  dsimp only [outC, outP, resC, resP, postSendC, postSendP]
  simp only [hepP, m]
  exact ih (some ((m, some Tm), fe.2)) hS'

theorem step_transmitE_same_epoch_le (mo : Mode)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (habort : ∀ {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T} (rhs : ℝ≥0∞),
      esC'.abort = true → 𝒟[contL none esC' sc'] {true} ≤ rhs)
    (hS : Sync prng Δcka mo esC sc esP sp)
    (hwin0 : esC.g.win = false)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = false)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc >>= fun res =>
        contL res.1.1 res.1.2 res.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp >>= fun res =>
        contR res.1.1 res.1.2 res.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  have hidxP : esP.g.idx P = esC.g.idx P := congrFun (eraseSt_idx hS.g_eq) P
  have hsend0 : P.sendsIn (esC.g.epoch P) = true := sendsIn_of_succ_false hsend
  by_cases hqep : qep < esC.g.epoch P
  · exact step_pure_le
      (by simp [-Prod.mk.injEq, stepC, implE, transmitE, SM.GameState.epMgmt, hS.abort_C, hwin0, hsend, hqep])
      (by simp [-Prod.mk.injEq, stepP, implE, transmitE, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0, hepP, hsend, hqep])
      (ih none hS)
  · have hld : mo.policy.leakDoom esP.g esP.g = mo.policy.leakDoom esC.g esC.g :=
      eraseSt_leakDoom hS.g_eq hS.g_eq mo.policy
    by_cases hdoom : mo.policy.leakDoom esC.g esC.g
    · exact step_abort_le habort
        (by simp [-Prod.mk.injEq, stepC, implE, transmitE, abortE, SM.GameState.epMgmt, hS.abort_C, hwin0, hsend,
          hqep, hdoom, StateT.run_modify]; rfl)
    · simp only [Bool.not_eq_true] at hdoom
      have hvSP : (esP.g.st P).vS = (esC.g.st P).vS := hS.vS_eq P
      have hTcurP : (esP.g.st P).curCkaMsg = (esC.g.st P).curCkaMsg := hS.Tcur_eq P
      cases hvS : (esC.g.st P).vS with
      | none =>
        have hstC : ({ esC.g.st P with vS := none } : VP (Option Γ) T Sig SS RS) = esC.g.st P := by
          rcases h : esC.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
          rw [h] at hvS; subst hvS; rfl
        have hstP : ({ esP.g.st P with vS := none } : VP Γ T (Option Sig) SS RS) = esP.g.st P := by
          have hvSP0 : (esP.g.st P).vS = none := hvSP.trans hvS
          rcases h : esP.g.st P with ⟨id, root, vS, vR, γ, curCkaMsg, tcur⟩
          rw [h] at hvSP0; subst hvSP0; rfl
        let c : Header T × E := ((esC.g.epoch P, (esC.g.st P).curCkaMsg), default)
        let rcd : SM.Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
        exact step_pure_le
          (by rw [hstC]; simp [-Prod.mk.injEq, stepC, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_C, hwin0,
            hsend, hqep, hdoom, hS.id_C P, hS.tcur_C P, hvS, c, rcd,
            StateT.run_pure, StateT.run_modify])
          (by rw [hstP]; simp [-Prod.mk.injEq, stepP, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0,
            hepP, hidxP, hld, hsend, hqep, hdoom, hS.id_P P, hS.tcur_P P, hvSP, hvS, hTcurP,
            c, rcd, StateT.run_pure, StateT.run_modify])
          (ih (some c) (hS.record_same_epoch P none m_msg default hsend0))
      | some v =>
        let h : Header T := (esC.g.epoch P, (esC.g.st P).curCkaMsg)
        let fe := fs.send v h m_msg
        let c : Header T × E := (h, fe.2)
        let rcd : SM.Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
        exact step_pure_le
          (by simp [-Prod.mk.injEq, stepC, implE, transmitE, vSend, FSAEADScheme.send, SM.GameState.epMgmt, hS.abort_C, hwin0,
            hsend, hqep, hdoom, hS.id_C P, hS.tcur_C P, hvS, h, fe, c, rcd,
            StateT.run_pure, StateT.run_modify])
          (by simp [-Prod.mk.injEq, stepP, implE, transmitE, vSend, FSAEADScheme.send, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0,
            hepP, hidxP, hld, hsend, hqep, hdoom, hS.id_P P, hS.tcur_P P, hvSP, hvS, hTcurP,
            h, fe, c, rcd, StateT.run_pure, StateT.run_modify])
          (ih (some c) (hS.record_same_epoch P (some fe.1) m_msg fe.2 hsend0))

theorem simulateQ_liftM_unif {ι : Type} {tspec : OracleSpec.{0, 0} ι} {S α : Type}
    (impl : QueryImpl tspec (StateT S ProbComp)) (mx : ProbComp α) :
    simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + impl)
      (liftM mx : TComp tspec α) = StateT.lift mx := by
  ext st
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + impl)
    (liftM mx : TComp tspec α)).run st = (mx >>= fun a => pure (a, st))
  rw [← liftComp_eq_liftM]
  induction mx using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t r ih =>
    rw [liftComp_bind, liftComp_liftM_query]
    have hq : (liftM (OracleSpec.query t) : TComp tspec _) =
        (liftM (OracleSpec.query (spec := unifSpec + tspec) (.inl t)) : TComp tspec _) := rfl
    have hrun :
        ((liftM ((QueryImpl.liftTarget (StateT S ProbComp) (QueryImpl.ofLift unifSpec ProbComp) + impl)
          (.inl t)) : StateT S ProbComp (unifSpec.Range t))).run st =
        ((liftM (OracleSpec.query t) : ProbComp _) >>= fun u => pure (u, st)) := rfl
    rw [hq, simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind]
    rw [hrun]
    simp only [bind_assoc, pure_bind, ih]

@[simp]
theorem simulateQ_sampleT_cImpl (tH : ℕ) (α : Type) [SampleableType α] :
    simulateQ (cImpl cka Δcka tH) (sampleT α) = StateT.lift ($ᵗ α : ProbComp α) :=
  simulateQ_liftM_unif _ _

@[simp]
theorem simulateQ_sampleT_pImpl (α : Type) [SampleableType α] :
    simulateQ (pImpl prng) (sampleT α) = StateT.lift ($ᵗ α : ProbComp α) :=
  simulateQ_liftM_unif _ _

def startSendP_body (mo : Mode) (m : ℕ) (γ : Γ) (σv : Option Sig) (coins : CCoins) :
    HM (PRFPRNG.spec Sig I K) (PRNGState T Sig K) (Option (Γ × T × Option Sig × SS)) := do
  let c := cka.send γ coins
  match ← rootPRNG prng mo m c.2.2 σv with
  | none => return none
  | some (σ', k) =>
    modify fun s => { s with cache := Function.update s.cache m (some (c.2.1, σ', k)) }
    return some (c.1, c.2.1, σ', fs.initSender k)

theorem startSendP_some_eq (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (m : ℕ) (γ : Γ) (σv : Option Sig) (coins : CCoins) (h : PRNGState T Sig K) :
    (((hooksPRNG cka prng fs mo).startSend ctx P m γ σv (some coins)).run h) =
      (startSendP_body cka prng fs mo m γ σv coins).run h := rfl

theorem startSendP_none_def (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (m : ℕ) (γ : Γ) (σv : Option Sig) :
    (hooksPRNG cka prng fs mo).startSend ctx P m γ σv none =
      (StateT.lift (sampleT CCoins) >>= fun coins => startSendP_body cka prng fs mo m γ σv coins) := rfl

theorem startSendP_none_eq (mo : Mode) (ctx : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (m : ℕ) (γ : Γ) (σv : Option Sig) (h : PRNGState T Sig K) (sp : PRFPRNG.GameState Sig I K) :
    (simulateQ (pImpl prng)
      (((hooksPRNG cka prng fs mo).startSend ctx P m γ σv none).run h)).run sp =
     ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
      (simulateQ (pImpl prng) ((startSendP_body cka prng fs mo m γ σv coins).run h)).run sp := by
  rw [startSendP_none_def]
  simp [StateT.lift, StateT.run_bind, simulateQ_bind, map_eq_bind_pure_comp, bind_assoc]

theorem startSendP_coins_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M) (bad : Bool)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true})
    (coins : CCoins) (sc' : CKA.GameState Γ T)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (hnot_tH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = false)
    (hb_sc' : sc'.b = true)
    (hcka' : localCKA mo Δcka (esC.g.epoch P) = false →
      sc'.st P = (cka.send (esP.g.st P).γ coins).1 ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esP.g.st P).γ coins).2.1) :
    let m := esC.g.epoch P + 1
    let c_cka := cka.send (esP.g.st P).γ coins
    let p := prng.up (esC.g.st P).root c_cka.2.2
    let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
      (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
        { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
    let outC := postSendC fs Δcka P m_msg bad esC resC
    𝒟[contL outC.1 outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp >>=
        fun out =>
          let outP := postSendP fs Δcka P m_msg bad esP out.1
          contR outP.1 outP.2 out.2] {true} := by
  intro m c_cka p resC outC
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  by_cases hgt_star : mo.tStar < m
  · have hkr0 : knownRoot mo (esC.g.epoch P) = true := by
      simp [knownRoot, show mo.tStar ≤ esC.g.epoch P by omega]
    have hkr_m : knownRoot mo m = true := by
      simp [knownRoot, show mo.tStar ≤ m by omega]
    have hrootP0 : (esP.g.st P).root = some (esC.g.st P).root := by
      simp [hS.root_P P, hkr0]
    let σP' := if knownRoot mo m then some p.1 else none
    let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
      (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
        { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
        pure (resP, sp) := by
      simp [startSendP_body, rootPRNG, hgt_star, hrootP0, hkr_m, c_cka, p, σP', resP,
        StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
    rw [hP, pure_bind]
    exact ih_postSend_new prng fs Δcka mo P m_msg bad contL contR hS ih c_cka.1 c_cka.2.1 c_cka.2.2
      sc' sp hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega) (fun h => by omega)
  · by_cases heq_star : m = mo.tStar
    · have hkr_m : knownRoot mo m = true := by
        simp [knownRoot, heq_star]
      have hlt0 : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
      have hnot_lt0 : (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = false := by
        rw [hmax0]
        cases htL : mo.tL with
        | none => simp
        | some l =>
          have htH_le := tH_le_tStar_of_validGuess mo Δcka hvalid (by simp [htL])
          simp only [htL, Option.isSome_some, Bool.true_and, decide_eq_false_iff_not] at hnot_tH ⊢
          omega
      obtain ⟨hσ, hcorr, hprng, _⟩ := hS.prng_after_tH hlt0 hnot_lt0
      rw [hroot_max] at hσ
      have hnot_tH_star : ¬(mo.tL.isSome = true ∧ mo.tStar = mo.tH) := by
        rw [← heq_star]
        simpa [m, Bool.and_eq_false_iff, decide_eq_false_iff_not] using hnot_tH
      let σP' := if knownRoot mo m then some p.1 else none
      let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
        (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
          { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
      let sp' : PRFPRNG.GameState Sig I K := { sp with prf := true }
      have hP : (simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
          pure (resP, sp') := by
        simp [startSendP_body, rootPRNG, hgt_star, heq_star, hnot_tH_star,
          liftP, PRFPRNG.challPrfQuery, pImpl, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl,
          PRFPRNG.up, knownRoot, hcorr, hprng, hS.b_P, hσ, hkr_m, c_cka, p, σP', resP, sp',
          StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
      rw [hP, pure_bind]
      exact ih_postSend_new prng fs Δcka mo P m_msg bad contL contR hS ih c_cka.1 c_cka.2.1 c_cka.2.2
        sc' sp' hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega)
        (fun _ _ => ⟨hσ, hcorr, hprng⟩)
    · have hlt_star : m < mo.tStar := by omega
      have hlt0 : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
      by_cases hlt_tH : (mo.tL.isSome && decide (m < mo.tH)) = true
      · have hkr_m : knownRoot mo m = true := by
          simp [knownRoot, hlt_tH]
        have hlt_tH0 : (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = true := by
          rw [hmax0]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt_tH ⊢
          exact ⟨hlt_tH.1, by omega⟩
        obtain ⟨hσ, hcorr, hprng, hprf⟩ := hS.prng_before_tH hlt0 hlt_tH0
        rw [hroot_max] at hσ
        let σP' := if knownRoot mo m then some p.1 else none
        let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
          (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
        let sp' : PRFPRNG.GameState Sig I K := { sp with σ := p.1, corr := true }
        have hP : (simulateQ (pImpl prng)
            ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
            pure (resP, sp') := by
          simp [startSendP_body, rootPRNG, processCorr, hgt_star, heq_star,
            show (mo.tL.isSome && (m = mo.tH)) = false by simpa [m] using hnot_tH,
            show (mo.tL.isSome && (m < mo.tH)) = true by simpa [m] using hlt_tH,
            liftP, PRFPRNG.processQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
            PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
            hcorr, hprng, hprf, hσ, hkr_m, c_cka, p, σP', resP, sp',
            StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hP, pure_bind]
        exact ih_postSend_new prng fs Δcka mo P m_msg bad contL contR hS ih c_cka.1 c_cka.2.1 c_cka.2.2
          sc' sp' hsend hb_sc' hS.b_P hcka'
          (fun _ _ => ⟨rfl, rfl, hprng, hprf⟩)
          (fun _ h => by simp [m, hlt_tH] at h)
          (fun h => by omega)
      · simp only [Bool.not_eq_true] at hlt_tH
        have hkr_m : knownRoot mo m = false := by
          simp [knownRoot, hlt_tH, show ¬ mo.tStar ≤ m by omega]
        have hlt_tH0 : (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = false := by
          rw [hmax0]
          cases htL : mo.tL with
          | none => simp
          | some l =>
            simp only [htL, Option.isSome_some, Bool.true_and, decide_eq_false_iff_not] at hnot_tH hlt_tH ⊢
            omega
        obtain ⟨hσ, hcorr, hprng, hprf0⟩ := hS.prng_after_tH hlt0 hlt_tH0
        rw [hroot_max] at hσ
        have hprf : sp.prf = false := hprf0 (by omega)
        let σP' := if knownRoot mo m then some p.1 else none
        let resP : Option (Γ × T × Option Sig × SS) × PRNGState T Sig K :=
          (some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) })
        let sp' : PRFPRNG.GameState Sig I K := { sp with σ := p.1, corr := false }
        have hP : (simulateQ (pImpl prng)
            ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
            pure (resP, sp') := by
          simp [startSendP_body, rootPRNG, hgt_star, heq_star,
            show (mo.tL.isSome && (m = mo.tH)) = false by simpa [m] using hnot_tH,
            show (mo.tL.isSome && (m < mo.tH)) = false by simpa [m] using hlt_tH,
            liftP, PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl,
            PRFPRNG.processImpl, PRFPRNG.samIfNec,
            hcorr, hprng, hprf, hσ, hkr_m, c_cka, p, σP', resP, sp',
            StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hP, pure_bind]
        exact ih_postSend_new prng fs Δcka mo P m_msg bad contL contR hS ih c_cka.1 c_cka.2.1 c_cka.2.2
          sc' sp' hsend hb_sc' hS.b_P hcka'
          (fun _ h => by simp [m, hlt_tH] at h)
          (fun _ _ => ⟨rfl, rfl, hprng, fun _ => hprf⟩)
          (fun h => by omega)

theorem startSendP_chall_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true})
    (coins : CCoins) (sc' : CKA.GameState Γ T)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (htH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = true)
    (hb_sc' : sc'.b = true)
    (hcka' : localCKA mo Δcka (esC.g.epoch P) = false →
      sc'.st P = (cka.send (esP.g.st P).γ coins).1 ∧ sc'.epoch P = esC.g.epoch P + 1 ∧
      sc'.st P.other = (esP.g.st P.other).γ ∧ sc'.epoch P.other = esC.g.epoch P ∧
      sc'.lastMsg = some (cka.send (esP.g.st P).γ coins).2.1) :
    let m := esC.g.epoch P + 1
    let c_cka := cka.send (esP.g.st P).γ coins
    𝒟[($ᵗ I : ProbComp I) >>= fun I₁ =>
        let p := prng.up (esC.g.st P).root I₁
        let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
          (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
            { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) })
        let outC := postSendC fs Δcka P m_msg false esC resC
        contL outC.1 outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp >>=
        fun out =>
          let outP := postSendP fs Δcka P m_msg false esP out.1
          contR outP.1 outP.2 out.2] {true} := by
  intro m c_cka
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with hEq | hEq
    · rw [hEq]
    · rw [hEq, hroot0]
  have htH_split : mo.tL.isSome = true ∧ m = mo.tH := by
    simpa [m, Bool.and_eq_true, decide_eq_true_eq] using htH
  obtain ⟨htL_some, hm_tH⟩ := htH_split
  have hm_le_star : m ≤ mo.tStar := by
    have := tH_le_tStar_of_validGuess mo Δcka hvalid htL_some
    omega
  have hgt_star : ¬ mo.tStar < m := by omega
  have hlt0 : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
  have hlt_tH0 : (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = true := by
    rw [hmax0]
    simp [htL_some, show esC.g.epoch P < mo.tH by omega]
  obtain ⟨hσ, hcorr, hprng, hprf⟩ := hS.prng_before_tH hlt0 hlt_tH0
  rw [hroot_max] at hσ
  by_cases heq_star : m = mo.tStar
  · have hkr_m : knownRoot mo m = true := by
      simp [knownRoot, heq_star]
    have hstar_eq_tH : mo.tStar = mo.tH := heq_star.symm.trans hm_tH
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
        ($ᵗ I : ProbComp I) >>= fun I₁ =>
          let p := prng.up (esC.g.st P).root I₁
          let σP' := if knownRoot mo m then some p.1 else none
          pure ((some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) }),
            { sp with σ := p.1, corr := true, prng := true }) := by
      simp [startSendP_body, rootPRNG, hgt_star, heq_star, htL_some, hstar_eq_tH,
        liftP, PRFPRNG.challPrngQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.challPrngImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
        PRFPRNG.up, knownRoot, hcorr, hprng, hprf, hS.b_P, hσ, hkr_m, c_cka,
        StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
    rw [hP, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun I₁ _ => ?_
    rw [pure_bind]
    exact ih_postSend_new prng fs Δcka mo P m_msg false contL contR hS ih c_cka.1 c_cka.2.1 I₁
      sc' { sp with σ := (prng.up (esC.g.st P).root I₁).1, corr := true, prng := true }
      hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega)
      (fun _ h => by simp [← heq_star, m, htL_some, hm_tH] at h)
  · have hlt_star : m < mo.tStar := by omega
    have hlt_tH : (mo.tL.isSome && decide (m < mo.tH)) = false := by
      simp [hm_tH]
    have hkr_m : knownRoot mo m = false := by
      simp [knownRoot, hlt_tH, show ¬ mo.tStar ≤ m by omega]
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run esP.h)).run sp =
        ($ᵗ I : ProbComp I) >>= fun I₁ =>
          let p := prng.up (esC.g.st P).root I₁
          let σP' := if knownRoot mo m then some p.1 else none
          pure ((some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) }),
            { sp with σ := p.1, corr := false }) := by
      simp [startSendP_body, rootPRNG, hgt_star, heq_star, htL_some, ← hm_tH,
        liftP, PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.processImpl, PRFPRNG.samIfNec,
        hcorr, hprng, hprf, hσ, hkr_m, c_cka,
        StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
    rw [hP, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun I₁ _ => ?_
    rw [pure_bind]
    exact ih_postSend_new prng fs Δcka mo P m_msg false contL contR hS ih c_cka.1 c_cka.2.1 I₁
      sc' { sp with σ := (prng.up (esC.g.st P).root I₁).1, corr := false }
      hsend hb_sc' hS.b_P hcka'
      (fun _ h => by simp [m, hlt_tH] at h)
      (fun _ _ => ⟨rfl, rfl, hprng, fun _ => hprf⟩)
      (fun h => by omega)

theorem step_transmitE_new_epoch_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (habort : ∀ {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T} (rhs : ℝ≥0∞),
      esC'.abort = true → 𝒟[contL none esC' sc'] {true} ≤ rhs)
    (hS : Sync prng Δcka mo esC sc esP sp)
    (hwin0 : esC.g.win = false)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc >>= fun res =>
        contL res.1.1 res.1.2 res.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp >>= fun res =>
        contR res.1.1 res.1.2 res.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  by_cases hqep : qep < esC.g.epoch P + 1
  · have hqep_le : qep ≤ esC.g.epoch P := by omega
    exact step_pure_le
      (by simp [-Prod.mk.injEq, stepC, implE, transmitE, SM.GameState.epMgmt, hS.abort_C, hwin0, hsend, hqep_le])
      (by simp [-Prod.mk.injEq, stepP, implE, transmitE, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0, hepP, hsend, hqep_le])
      (ih none hS)
  · have hld : mo.policy.leakDoom esP.g (epMgmtNew esP.g (2 + Δcka) P r.isSome) =
        mo.policy.leakDoom esC.g (epMgmtNew esC.g (2 + Δcka) P r.isSome) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_epMgmtNew hS.g_eq (2 + Δcka) P r.isSome) mo.policy
    by_cases hdoom : mo.policy.leakDoom esC.g (epMgmtNew esC.g (2 + Δcka) P r.isSome)
    · exact step_abort_le habort
        (by simp [-Prod.mk.injEq, stepC, implE, transmitE, abortE,
          epMgmt_eq_epMgmtNew esC.g (2 + Δcka) qep P r.isSome hsend hqep,
          hS.abort_C, hwin0, hdoom, StateT.run_modify]; rfl)
    · simp only [Bool.not_eq_true] at hdoom
      rw [stepC_transmit_new cka prng fs Δcka qep mo P m_msg r esC sc hS.abort_C hwin0
          (hS.id_C P) (hS.tcur_C P) hsend hqep hdoom,
        stepP_transmit_new cka prng fs Δcka qep mo P m_msg r esP sp hS.abort_P (by rw [hwin, hwin0])
          (hS.id_P P) (by rw [hS.tcur_P P, hepP]) (by rw [hepP]; exact hsend)
          (by rw [hepP]; exact hqep) (by rw [hld, hdoom]),
        bind_assoc, bind_assoc]
      let m := esC.g.epoch P + 1
      by_cases hloc : localCKA mo Δcka (esC.g.epoch P)
      · have hloc_m : localCKA mo Δcka m = true :=
          localCKA_mono mo Δcka hloc (Nat.le_succ _)
        have hnot_tH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = false := by
          simp only [localCKA, Bool.or_eq_true, decide_eq_true_eq] at hloc
          rcases hloc with h | h
          · cases h' : mo.tL <;> simp_all
          · simp [show esC.g.epoch P + 1 ≠ mo.tH by omega]
        have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
          simp [hS.γ_C P, hloc]
        cases r with
        | some coins =>
          let c_cka := cka.send (esP.g.st P).γ coins
          let p := prng.up (esC.g.st P).root c_cka.2.2
          let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
            (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
              { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
          have hC : (simulateQ (cImpl cka Δcka mo.tH)
              (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P true)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
              pure (resC, sc) := by
            simp [hooksCKA, cacheC, hγC, hloc_m, m, c_cka, p, resC,
              StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
          simp only [Option.isSome_some]
          rw [hC, pure_bind, pure_bind, hepP, startSendP_some_eq]
          simpa [m, c_cka, p, resC] using
            startSendP_coins_le cka prng fs Δcka mo hvalid P m_msg true contL contR hS ih coins sc
              hsend hnot_tH hS.b_C (fun h => by simp [hloc] at h)
        | none =>
          have hC : (simulateQ (cImpl cka Δcka mo.tH)
              (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P false)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                let c_cka := cka.send (esP.g.st P).γ coins
                let p := prng.up (esC.g.st P).root c_cka.2.2
                pure ((some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                  { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }), sc) := by
            simp [hooksCKA, cacheC, hγC, hloc_m, m,
              StateT.lift, StateT.run_bind, StateT.run_pure, StateT.run_modify,
              simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
            fun coins _ => ?_
          rw [pure_bind, pure_bind]
          exact startSendP_coins_le cka prng fs Δcka mo hvalid P m_msg false contL contR hS ih coins sc
            hsend hnot_tH hS.b_C (fun h => by simp [hloc] at h)
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esC.g.st P).γ = none := by
          simp [hS.γ_C P, hloc]
        have htL_none : mo.tL.isNone = false := by
          simp only [localCKA, Bool.or_eq_false_iff] at hloc
          exact hloc.1
        have htL_some : mo.tL.isSome = true := by
          cases h' : mo.tL <;> simp_all
        obtain ⟨hsc_stP, hsc_epP⟩ := hS.cka_st P (Or.inl hloc)
        obtain ⟨hsc_stO, hsc_epO⟩ := hS.cka_st P.other (Or.inr (by simpa using hloc))
        obtain ⟨hO_ep, _, _⟩ := hS.ping_pong_synced P hsend
        have hcanS : sc.canSend P = true := by
          simp [CKA.GameState.canSend, hsc_epP, hsc_epO, hO_ep, hsend]
        cases r with
        | some coins =>
          by_cases hbad_ok : mo.tH < esC.g.epoch P + 1 + 2
          · have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P true)
                   P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
                pure ((none, esC.h), sc) := by
              simp [hooksCKA, liftC, CKA.sendWithAdversaryCoinsQuery, cImpl, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl,
                hγC, hcanS, hsc_epP, hbad_ok,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
            simp only [Option.isSome_some]
            rw [hC, pure_bind, pure_bind]
            exact habort _ rfl
          · have hnot_tH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = false := by
              simp [show esC.g.epoch P + 1 ≠ mo.tH by omega]
            have hfin : ¬ (mo.tH + Δcka ≤ m) := by omega
            have hloc_m : localCKA mo Δcka m = false := by
              simp [localCKA, htL_none, hfin]
            let c_cka := cka.send (esP.g.st P).γ coins
            let p := prng.up (esC.g.st P).root c_cka.2.2
            let sc' := sc.afterSend P c_cka.1 c_cka.2.1
            let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
              (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
            have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P true)
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run esC.h)).run sc =
                pure (resC, sc') := by
              simp [hooksCKA, cacheC, liftC, CKA.sendWithAdversaryCoinsQuery, cImpl, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl,
                hγC, hcanS, hsc_epP, hsc_stP, hbad_ok, hfin, hloc_m, m, c_cka, p, sc', resC,
                StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
            simp only [Option.isSome_some]
            rw [hC, pure_bind, pure_bind, hepP, startSendP_some_eq]
            refine startSendP_coins_le cka prng fs Δcka mo hvalid P m_msg true contL contR hS ih coins sc'
              hsend hnot_tH hS.b_C fun _ => ?_
            simp [sc', c_cka, CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep]
        | none =>
          by_cases heq_tH : esC.g.epoch P + 1 = mo.tH
          · have htH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = true := by
              simp [htL_some, heq_tH]
            have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P false)
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins => ($ᵗ I : ProbComp I) >>= fun I₁ =>
                  let c_cka := cka.send (esP.g.st P).γ coins
                  let p := prng.up (esC.g.st P).root I₁
                  pure ((some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                    { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) }),
                    sc.afterSend P c_cka.1 c_cka.2.1) := by
              by_cases hΔ : Δcka = 0
              · simp [hooksCKA, cacheC, liftC, CKA.challQuery, CKA.corrQuery, cImpl, CKA.oracleImpl,
                  CKA.challImpl, CKA.corrImpl, CKA.GameState.afterSend, CKA.GameState.finished,
                  localCKA, htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hS.b_C, hΔ, m,
                  StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
              · simp [hooksCKA, cacheC, liftC, CKA.challQuery, cImpl, CKA.oracleImpl,
                  CKA.challImpl, localCKA, htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hS.b_C, hΔ, m,
                  StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
            simp only [Option.isSome_none]
            rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
              fun coins _ => ?_
            rw [bind_assoc]
            have hstep := startSendP_chall_le cka prng fs Δcka mo hvalid P m_msg contL contR hS ih coins
              (sc.afterSend P (cka.send (esP.g.st P).γ coins).1 (cka.send (esP.g.st P).γ coins).2.1)
              hsend htH hS.b_C (fun _ => by
                simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep])
            simpa [pure_bind] using hstep
          · have hnot_tH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = false := by
              simp [heq_tH]
            have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P false)
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                  let c_cka := cka.send (esP.g.st P).γ coins
                  let p := prng.up (esC.g.st P).root c_cka.2.2
                  pure ((some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1, fs.initSender p.2),
                    { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }),
                    sc.afterSend P c_cka.1 c_cka.2.1) := by
              by_cases hfin : mo.tH + Δcka ≤ m
              · have hloc_m : localCKA mo Δcka m = true := by simp [localCKA, hfin]
                simp [hooksCKA, cacheC, liftC, CKA.sendQuery, CKA.corrQuery, cImpl, CKA.oracleImpl,
                  CKA.sendImpl, CKA.corrImpl, CKA.GameState.afterSend, CKA.GameState.finished,
                  hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin, hloc_m, m,
                  StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
              · have hloc_m : localCKA mo Δcka m = false := by simp [localCKA, htL_none, hfin]
                simp [hooksCKA, cacheC, liftC, CKA.sendQuery, cImpl, CKA.oracleImpl,
                  CKA.sendImpl, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin, hloc_m, m,
                  StateT.lift, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
            simp only [Option.isSome_none]
            rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
              fun coins _ => ?_
            rw [pure_bind, pure_bind]
            refine startSendP_coins_le cka prng fs Δcka mo hvalid P m_msg false contL contR hS ih coins
              (sc.afterSend P (cka.send (esP.g.st P).γ coins).1 (cka.send (esP.g.st P).γ coins).2.1)
              hsend hnot_tH hS.b_C fun _ => ?_
            simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep]

theorem step_transmitE_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (contL : Option (Header T × E) →
      EStateC Γ T Sig SS RS M E I → CKA.GameState Γ T → ProbComp Bool)
    (contR : Option (Header T × E) →
      EStateP Γ T Sig SS RS M E K → PRFPRNG.GameState Sig I K → ProbComp Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (habort : ∀ {esC' : EStateC Γ T Sig SS RS M E I} {sc' : CKA.GameState Γ T} (rhs : ℝ≥0∞),
      esC'.abort = true → 𝒟[contL none esC' sc'] {true} ≤ rhs)
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[contL u esC' sc'] {true} ≤ 𝒟[contR u esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc >>= fun res =>
        contL res.1.1 res.1.2 res.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp >>= fun res =>
        contR res.1.1 res.1.2 res.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  by_cases hwin0 : esC.g.win = true
  · exact step_pure_le
      (by simp [-Prod.mk.injEq, stepC, implE, transmitE, hS.abort_C, hwin0])
      (by simp [-Prod.mk.injEq, stepP, implE, transmitE, hS.abort_P, hwin, hwin0])
      (ih none hS)
  · simp only [Bool.not_eq_true] at hwin0
    by_cases hsend : P.sendsIn (esC.g.epoch P + 1) = true
    · exact step_transmitE_new_epoch_le cka prng fs Δcka qep mo hvalid P m_msg r contL contR
        habort hS hwin0 hsend ih
    · simp only [Bool.not_eq_true] at hsend
      exact step_transmitE_same_epoch_le cka prng fs Δcka qep mo P m_msg r contL contR
        habort hS hwin0 hsend ih

end CryptoGames.SM.Construction.AuthL10
